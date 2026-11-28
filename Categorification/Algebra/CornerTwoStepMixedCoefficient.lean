/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.CornerTwoStepCoefficient
import Categorification.Algebra.InductionAlongAdjunction

set_option backward.isDefEq.respectTransparency false

/-!
# Right multiplication between two two-step induction corners, as a coefficient map

For two factorizations `φ₂ ∘ φ₁`, `φ₂' ∘ φ₁'` of maps `A₀ → A₂` of non-unital rings (through
`A₁` and through `A₁'`), write `ψ = φ₂ ∘ φ₁` and `ψ' = φ₂' ∘ φ₁'`. An element `c ∈ A₂` with
`c ψ'(a) = ψ(a) c ψ'(1)` for all `a` acts from `A₂ e₂ ⊗_{A₁} A₁ e₁` to
`A₂ e₂' ⊗_{A₁'} A₁' e₁'` by `m ⊗ n ↦ m φ₂(n) c ψ'(1) ⊗ e₁'`
(`InductionAlong.Corner.twoStepMixedRightMul`). Its coefficient map on
`A₂ e₂ ⊗_{A₁} (A₁ e₁ ⊗_{A₀} -) ⟶ A₂ e₂' ⊗_{A₁'} (A₁' e₁' ⊗_{A₀} -)` commutes with the shift
(`InductionAlong.Corner.twoStepMixedRightMulNat`). On inductions, any natural transformation
`Ind_{φ₂} Ind_{φ₁} ⟶ Ind_{φ₂'} Ind_{φ₁'}` sending `e₂ ⊗ (e₁ ⊗ n)` to `c (e₂' ⊗ (e₁' ⊗ n))`
sends `m ⊗ (z ⊗ n)` to `m φ₂(z) c ψ'(1) ⊗ (e₁' ⊗ n)`
(`InductionAlong.Corner.app_tmul_tmul_of_unitGen_mixed`).

This is the dg form of the crossing of two black strands of different colours on `𝔉_a 𝔉_b` in
B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.21 (cf. `InductionAlong.Corner.twoStepRightMul` for one colour).

## Main definitions

* `InductionAlong.Corner.twoStepMixedRightMul`,
  `InductionAlong.Corner.twoStepMixedRightMulNat`.

## Main results

* `InductionAlong.Corner.twoStepMixedRightMulNat_commShift`.
* `InductionAlong.Corner.app_tmul_tmul_of_unitGen_mixed`.
-/

open CategoryTheory DG DG.DegreeZero MulOpposite

universe u

noncomputable section

namespace Categorification.InductionAlong.Corner

open TensorProductOver TensorProductOver.RightAction

local instance (X : Type u) [AddCommGroup X] : Fact (∀ m : InDegreeZero X, m ∈ grading 0) :=
  ⟨fun _ => (InDegreeZero.mem_grading_iff (M := X)).mpr (Or.inl rfl)⟩

variable {A₀ A₁ A₁' A₂ : Type u} [Ring A₀] [Ring A₁] [Ring A₁'] [Ring A₂] {φ₁ : A₀ →ₙ+* A₁}
  {φ₂ : A₁ →ₙ+* A₂} {φ₁' : A₀ →ₙ+* A₁'} {φ₂' : A₁' →ₙ+* A₂}
  (c : A₂) (hc : ∀ a, c * φ₂' (φ₁' a) = φ₂ (φ₁ a) * (c * φ₂' (φ₁' 1)))

set_option hygiene false in
local notation "P" =>
  TensorProductOver A₁ (InDegreeZero (Corner φ₂)) (InDegreeZero (Corner φ₁))
set_option hygiene false in
local notation "P'" =>
  TensorProductOver A₁' (InDegreeZero (Corner φ₂')) (InDegreeZero (Corner φ₁'))

variable (φ₁' φ₂') in
/-- The element `m φ₂(n) c ψ'(1)` of `A₂ e₂'`. -/
def twoStepMixedRightElem (m : Corner φ₂) (n : Corner φ₁) : Corner φ₂' :=
  ⟨m.1 * (φ₂ n.1 * (c * φ₂' (φ₁' 1))), by
    change m.1 * (φ₂ n.1 * (c * φ₂' (φ₁' 1))) * φ₂' 1 = m.1 * (φ₂ n.1 * (c * φ₂' (φ₁' 1)))
    rw [mul_assoc, mul_assoc, mul_assoc, ← map_mul, mul_one]⟩

@[simp] theorem twoStepMixedRightElem_val (m : Corner φ₂) (n : Corner φ₁) :
    (twoStepMixedRightElem φ₁' φ₂' c m n).1 = m.1 * (φ₂ n.1 * (c * φ₂' (φ₁' 1))) := rfl

variable (φ₁' φ₂') in
/-- The balanced biadditive map `(m, n) ↦ m φ₂(n) c ψ'(1) ⊗ e₁'`. -/
def twoStepMixedRightAddHom :
    InDegreeZero (Corner φ₂) →+ InDegreeZero (Corner φ₁) →+ P' :=
  AddMonoidHom.mk' (fun m => AddMonoidHom.mk' (fun n =>
      tmul A₁' (show InDegreeZero (Corner φ₂') from twoStepMixedRightElem φ₁' φ₂' c m n)
        (show InDegreeZero (Corner φ₁') from unitGen φ₁')) fun n n' => by
      rw [← add_tmul]
      congr 1
      exact Subtype.ext (by
        change (m : Corner φ₂).1 * (φ₂ ((n : Corner φ₁).1 + (n' : Corner φ₁).1) *
            (c * φ₂' (φ₁' 1))) =
          (m : Corner φ₂).1 * (φ₂ (n : Corner φ₁).1 * (c * φ₂' (φ₁' 1))) +
            (m : Corner φ₂).1 * (φ₂ (n' : Corner φ₁).1 * (c * φ₂' (φ₁' 1)))
        rw [map_add, add_mul, mul_add])) fun m m' => by
    ext n
    simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
    rw [← add_tmul]
    congr 1
    exact Subtype.ext (add_mul _ _ _)

variable (φ₁' φ₂') in
/-- **Right multiplication by `c` from `A₂ e₂ ⊗_{A₁} A₁ e₁` to `A₂ e₂' ⊗_{A₁'} A₁' e₁'`**:
`m ⊗ n ↦ m φ₂(n) c ψ'(1) ⊗ e₁'`, a map of left `A₂`-modules. -/
def twoStepMixedRightMul : P →ₗ[A₂] P' where
  toFun := lift (twoStepMixedRightAddHom φ₁' φ₂' c) fun b m n => by
    change tmul A₁' _ _ = tmul A₁' _ _
    congr 1
    exact Subtype.ext (by
      change (m : Corner φ₂).1 * φ₂ b * (φ₂ (n : Corner φ₁).1 * (c * φ₂' (φ₁' 1))) =
        (m : Corner φ₂).1 * (φ₂ (b * (n : Corner φ₁).1) * (c * φ₂' (φ₁' 1)))
      simp only [map_mul, mul_assoc])
  map_add' := map_add _
  map_smul' a x := by
    induction x using TensorProductOver.induction_on with
    | zero => simp
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    | tmul m n =>
      change tmul A₁' _ _ = a • tmul A₁' _ _
      rw [smul_tmul]
      congr 1
      exact Subtype.ext (by
        change a * (m : Corner φ₂).1 * (φ₂ (n : Corner φ₁).1 * (c * φ₂' (φ₁' 1))) =
          a * ((m : Corner φ₂).1 * (φ₂ (n : Corner φ₁).1 * (c * φ₂' (φ₁' 1))))
        rw [mul_assoc])

theorem twoStepMixedRightMul_tmul (m : Corner φ₂) (n : Corner φ₁) :
    twoStepMixedRightMul φ₁' φ₂' c (tmul A₁ (show InDegreeZero (Corner φ₂) from m)
        (show InDegreeZero (Corner φ₁) from n)) =
      tmul A₁' (show InDegreeZero (Corner φ₂') from twoStepMixedRightElem φ₁' φ₂' c m n)
        (show InDegreeZero (Corner φ₁') from unitGen φ₁') := rfl

include hc in
theorem twoStepMixedRightMul_op_smul (a : A₀) (x : P) :
    twoStepMixedRightMul φ₁' φ₂' c (op a • x) = op a • twoStepMixedRightMul φ₁' φ₂' c x := by
  induction x using TensorProductOver.induction_on with
  | zero => simp
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | tmul m n =>
    change tmul A₁' (show InDegreeZero (Corner φ₂') from
        twoStepMixedRightElem φ₁' φ₂' c m (op a • (n : Corner φ₁)))
      (show InDegreeZero (Corner φ₁') from unitGen φ₁') =
      tmul A₁' (show InDegreeZero (Corner φ₂') from twoStepMixedRightElem φ₁' φ₂' c m n)
        (show InDegreeZero (Corner φ₁') from op a • unitGen φ₁')
    have e : (show InDegreeZero (Corner φ₂') from
        twoStepMixedRightElem φ₁' φ₂' c m (op a • (n : Corner φ₁))) =
        op (φ₁' a) • (show InDegreeZero (Corner φ₂') from twoStepMixedRightElem φ₁' φ₂' c m n) :=
      Subtype.ext (by
        change (m : Corner φ₂).1 * (φ₂ ((n : Corner φ₁).1 * φ₁ a) * (c * φ₂' (φ₁' 1))) =
          (m : Corner φ₂).1 * (φ₂ (n : Corner φ₁).1 * (c * φ₂' (φ₁' 1))) * φ₂' (φ₁' a)
        have h1 : φ₂' (φ₁' 1) * φ₂' (φ₁' a) = φ₂' (φ₁' a) := by
          rw [← map_mul, ← map_mul, one_mul]
        rw [map_mul, mul_assoc (φ₂ (n : Corner φ₁).1), ← hc a, mul_assoc, mul_assoc,
          mul_assoc, h1])
    rw [e, op_smul_tmul]
    congr 1
    exact Subtype.ext (by
      change φ₁' a * φ₁' 1 = φ₁' 1 * φ₁' a
      rw [← map_mul, ← map_mul, mul_one, one_mul])

/-- **Right multiplication by `c` from `A₂ e₂ ⊗_{A₁} (A₁ e₁ ⊗_{A₀} -)` to
`A₂ e₂' ⊗_{A₁'} (A₁' e₁' ⊗_{A₀} -)`**: the coefficient map of
`InductionAlong.Corner.twoStepMixedRightMul`, transported along associativity of the dg tensor
product. -/
def twoStepMixedRightMulNat :
    DGModuleCat.tensorFunctor (B := A₀) A₁ (InDegreeZero (Corner φ₁)) ⋙
        DGModuleCat.tensorFunctor (B := A₁) A₂ (InDegreeZero (Corner φ₂)) ⟶
      DGModuleCat.tensorFunctor (B := A₀) A₁' (InDegreeZero (Corner φ₁')) ⋙
        DGModuleCat.tensorFunctor (B := A₁') A₂ (InDegreeZero (Corner φ₂')) :=
  (DGModuleCat.tensorFunctorCompIso (A := A₁) (B := A₀) (C := A₂)
      (InDegreeZero (Corner φ₁)) (InDegreeZero (Corner φ₂))).hom ≫
    tensorCoeffNat (dgHomOfDegreeZero (twoStepMixedRightMul φ₁' φ₂' c))
      (twoStepMixedRightMul_op_smul c hc) ≫
    (DGModuleCat.tensorFunctorCompIso (A := A₁') (B := A₀) (C := A₂)
      (InDegreeZero (Corner φ₁')) (InDegreeZero (Corner φ₂'))).inv

/-- **The two-step right multiplication between two corners commutes with the shift.** -/
instance twoStepMixedRightMulNat_commShift :
    NatTrans.CommShift (twoStepMixedRightMulNat c hc) ℤ := by
  unfold twoStepMixedRightMulNat
  infer_instance

/-- **A natural transformation `Ind_{φ₂} Ind_{φ₁} ⟶ Ind_{φ₂'} Ind_{φ₁'}` acting by `c` on
generators**, `e₂ ⊗ (e₁ ⊗ n) ↦ c (e₂' ⊗ (e₁' ⊗ n))`, sends `m ⊗ (z ⊗ n)` to
`m φ₂(z) c ψ'(1) ⊗ (e₁' ⊗ n)`. -/
theorem app_tmul_tmul_of_unitGen_mixed
    (θ : functor.{u, u} φ₁ ⋙ functor.{u, u} φ₂ ⟶ functor.{u, u} φ₁' ⋙ functor.{u, u} φ₂')
    (hθ : ∀ (N : ModuleCat.{u} A₀) (n : N),
      (θ.app N).hom (Ind.tmul (unitGen φ₂) (Ind.tmul (unitGen φ₁) n)) =
        c • Ind.tmul (unitGen φ₂') (Ind.tmul (unitGen φ₁') n))
    (N : ModuleCat.{u} A₀) (m : Corner φ₂) (z : Corner φ₁) (n : N) :
    (θ.app N).hom (Ind.tmul m (Ind.tmul z n)) =
      Ind.tmul (twoStepMixedRightElem φ₁' φ₂' c m z) (Ind.tmul (unitGen φ₁') n) := by
  have e : (Ind.tmul m (Ind.tmul z n) : Ind (Ind N φ₁) φ₂) =
      (m.1 * φ₂ z.1) • Ind.tmul (unitGen φ₂) (Ind.tmul (unitGen φ₁) n) := by
    have hz : (Ind.tmul z n : Ind N φ₁) = z.1 • Ind.tmul (unitGen φ₁) n := by
      rw [Ind.smul_tmul, Ind.smul_unitGen]
    rw [hz, ← Ind.op_smul_tmul, Ind.smul_tmul]
    exact congrArg (Ind.tmul · _) (Subtype.ext (by
      change m.1 * φ₂ z.1 = m.1 * φ₂ z.1 * φ₂ 1
      rw [mul_assoc, ← map_mul, mul_one]))
  have h2 : (Ind.tmul (unitGen φ₁') n : Ind N φ₁') = φ₁' 1 • Ind.tmul (unitGen φ₁') n := by
    rw [Ind.smul_tmul]
    exact congrArg (Ind.tmul · n) (Subtype.ext (by
      change φ₁' 1 = φ₁' 1 * φ₁' 1
      rw [← map_mul, one_mul]))
  rw [e, (θ.app N).hom.map_smul, hθ, smul_smul, Ind.smul_tmul]
  conv_lhs => rw [h2, ← Ind.op_smul_tmul]
  exact congrArg (Ind.tmul · _) (Subtype.ext (by
    change m.1 * φ₂ z.1 * c * φ₂' 1 * φ₂' (φ₁' 1) = m.1 * (φ₂ z.1 * (c * φ₂' (φ₁' 1)))
    rw [mul_assoc (m.1 * φ₂ z.1 * c), ← map_mul, one_mul]
    simp only [mul_assoc]))

end Categorification.InductionAlong.Corner
