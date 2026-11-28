/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.RCornerTwoStepCoefficient
import Categorification.Algebra.InductionAlongSigma

set_option backward.isDefEq.respectTransparency false

/-!
# Rouquier's crossing on a two-step induction corner, as a coefficient map

For non-unital ring maps `φ₁ : A₀ → A₁`, `φ₂ : A₁ → A₂` and the corner bimodules `A₁ e₁`,
`A₂ e₂` (`InductionAlong.Corner`), an element `c ∈ A₂` commuting with the image of `φ₂ ∘ φ₁`
acts on `A₂ e₂ ⊗_{A₁} A₁ e₁` by `m ⊗ n ↦ m σ(n) ⊗ e₁`, where `σ(n) = φ₂(n) c φ₂(1)` is the
corner element of Rouquier's rightward crossing (`InductionAlong.sigmaElt`)
(`InductionAlong.Corner.twoStepRightMul`). Its coefficient map on
`(A₂ e₂ ⊗_{A₁} A₁ e₁) ⊗_{A₀} -`, transported to `A₂ e₂ ⊗_{A₁} (A₁ e₁ ⊗_{A₀} -)`, commutes with
the shift (`InductionAlong.Corner.twoStepRightMulNat`). On inductions, the mate of `resAct₂ c`
sends `e₂ ⊗ (z ⊗ n)` to `σ(z) ⊗ (e₁ ⊗ n)` (`InductionAlong.conjugateEquiv_symm_resAct₂_tmul`);
any natural transformation with this value on generators sends `m ⊗ (z ⊗ n)` to
`m σ(z) ⊗ (e₁ ⊗ n)` (`InductionAlong.Corner.app_tmul_tmul_of_unitGen`).

This is the dg form of the crossing on `𝔉_i²` in B. Webster, *Knot invariants and higher
representation theory*, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21 (with `c` the
crossing of the two newest black strands).

## Main definitions

* `InductionAlong.Corner.twoStepRightMul`, `InductionAlong.Corner.twoStepRightMulNat`.

## Main results

* `InductionAlong.Corner.twoStepRightMulNat_commShift`.
* `InductionAlong.Corner.app_tmul_tmul_of_unitGen`.
-/

open CategoryTheory DG DG.DegreeZero MulOpposite

universe u

noncomputable section

namespace Categorification.InductionAlong.Corner

open TensorProductOver TensorProductOver.RightAction

local instance (X : Type u) [AddCommGroup X] : Fact (∀ m : InDegreeZero X, m ∈ grading 0) :=
  ⟨fun _ => (InDegreeZero.mem_grading_iff (M := X)).mpr (Or.inl rfl)⟩

variable {A₀ A₁ A₂ : Type u} [Ring A₀] [Ring A₁] [Ring A₂] {φ₁ : A₀ →ₙ+* A₁} {φ₂ : A₁ →ₙ+* A₂}
  (c : A₂) (hc : ∀ a, c * φ₂ (φ₁ a) = φ₂ (φ₁ a) * c)

set_option hygiene false in
local notation "P" =>
  TensorProductOver A₁ (InDegreeZero (Corner φ₂)) (InDegreeZero (Corner φ₁))

/-- The element `m σ(n) = m φ₂(n) c φ₂(1)` of `A₂ e₂`. -/
def twoStepRightElem (m : Corner φ₂) (n : Corner φ₁) : Corner φ₂ :=
  m.1 • sigmaElt φ₁ φ₂ c n

@[simp] theorem twoStepRightElem_val (m : Corner φ₂) (n : Corner φ₁) :
    (twoStepRightElem c m n).1 = m.1 * (φ₂ n.1 * (c * φ₂ 1)) := rfl

/-- The balanced biadditive map `(m, n) ↦ m σ(n) ⊗ e₁`. -/
def twoStepRightAddHom : InDegreeZero (Corner φ₂) →+ InDegreeZero (Corner φ₁) →+ P :=
  AddMonoidHom.mk' (fun m => AddMonoidHom.mk' (fun n =>
      tmul A₁ (show InDegreeZero (Corner φ₂) from twoStepRightElem c m n)
        (show InDegreeZero (Corner φ₁) from unitGen φ₁)) fun n n' => by
      rw [← add_tmul]
      congr 1
      exact Subtype.ext (by
        change (m : Corner φ₂).1 * (φ₂ ((n : Corner φ₁).1 + (n' : Corner φ₁).1) * (c * φ₂ 1)) =
          (m : Corner φ₂).1 * (φ₂ (n : Corner φ₁).1 * (c * φ₂ 1)) +
            (m : Corner φ₂).1 * (φ₂ (n' : Corner φ₁).1 * (c * φ₂ 1))
        rw [map_add, add_mul, mul_add])) fun m m' => by
    ext n
    simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
    rw [← add_tmul]
    congr 1
    exact Subtype.ext (add_mul _ _ _)

/-- **Rouquier's crossing on `A₂ e₂ ⊗_{A₁} A₁ e₁`**: `m ⊗ n ↦ m σ(n) ⊗ e₁`, a map of
`(A₂, A₀)`-bimodules. -/
def twoStepRightMul : P →ₗ[A₂] P where
  toFun := lift (twoStepRightAddHom c) fun b m n => by
    change tmul A₁ _ _ = tmul A₁ _ _
    congr 1
    exact Subtype.ext (by
      change (m : Corner φ₂).1 * φ₂ b * (φ₂ (n : Corner φ₁).1 * (c * φ₂ 1)) =
        (m : Corner φ₂).1 * (φ₂ (b * (n : Corner φ₁).1) * (c * φ₂ 1))
      simp only [map_mul, mul_assoc])
  map_add' := map_add _
  map_smul' a x := by
    induction x using TensorProductOver.induction_on with
    | zero => simp
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    | tmul m n =>
      change tmul A₁ _ _ = a • tmul A₁ _ _
      rw [smul_tmul]
      congr 1
      exact Subtype.ext (by
        change a * (m : Corner φ₂).1 * (φ₂ (n : Corner φ₁).1 * (c * φ₂ 1)) =
          a * ((m : Corner φ₂).1 * (φ₂ (n : Corner φ₁).1 * (c * φ₂ 1)))
        rw [mul_assoc])

theorem twoStepRightMul_tmul (m : Corner φ₂) (n : Corner φ₁) :
    twoStepRightMul c (tmul A₁ (show InDegreeZero (Corner φ₂) from m)
        (show InDegreeZero (Corner φ₁) from n)) =
      tmul A₁ (show InDegreeZero (Corner φ₂) from twoStepRightElem c m n)
        (show InDegreeZero (Corner φ₁) from unitGen φ₁) := rfl

include hc in
theorem twoStepRightMul_op_smul (a : A₀) (x : P) :
    twoStepRightMul c (op a • x) = op a • twoStepRightMul c x := by
  induction x using TensorProductOver.induction_on with
  | zero => simp
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | tmul m n =>
    change tmul A₁ (show InDegreeZero (Corner φ₂) from
        twoStepRightElem c m (op a • (n : Corner φ₁)))
      (show InDegreeZero (Corner φ₁) from unitGen φ₁) =
      tmul A₁ (show InDegreeZero (Corner φ₂) from twoStepRightElem c m n)
        (show InDegreeZero (Corner φ₁) from op a • unitGen φ₁)
    have e : (show InDegreeZero (Corner φ₂) from twoStepRightElem c m (op a • (n : Corner φ₁))) =
        op (φ₁ a) • (show InDegreeZero (Corner φ₂) from twoStepRightElem c m n) :=
      Subtype.ext (by
        change (m : Corner φ₂).1 * (sigmaElt φ₁ φ₂ c (op a • (n : Corner φ₁))).1 =
          (m : Corner φ₂).1 * (sigmaElt φ₁ φ₂ c n).1 * φ₂ (φ₁ a)
        rw [sigmaElt_op_smul φ₁ φ₂ hc, op_smul_val, mul_assoc])
    rw [e, op_smul_tmul]
    congr 1
    exact Subtype.ext (by
      change φ₁ a * φ₁ 1 = φ₁ 1 * φ₁ a
      rw [← map_mul, ← map_mul, mul_one, one_mul])

/-- **Rouquier's crossing on `A₂ e₂ ⊗_{A₁} (A₁ e₁ ⊗_{A₀} -)`**: the coefficient map of
`InductionAlong.Corner.twoStepRightMul`, transported along associativity of the dg tensor
product. -/
def twoStepRightMulNat :
    DGModuleCat.tensorFunctor (B := A₀) A₁ (InDegreeZero (Corner φ₁)) ⋙
        DGModuleCat.tensorFunctor (B := A₁) A₂ (InDegreeZero (Corner φ₂)) ⟶
      DGModuleCat.tensorFunctor (B := A₀) A₁ (InDegreeZero (Corner φ₁)) ⋙
        DGModuleCat.tensorFunctor (B := A₁) A₂ (InDegreeZero (Corner φ₂)) :=
  (DGModuleCat.tensorFunctorCompIso (A := A₁) (B := A₀) (C := A₂)
      (InDegreeZero (Corner φ₁)) (InDegreeZero (Corner φ₂))).hom ≫
    tensorCoeffNat (dgHomOfDegreeZero (twoStepRightMul c))
      (twoStepRightMul_op_smul c hc) ≫
    (DGModuleCat.tensorFunctorCompIso (A := A₁) (B := A₀) (C := A₂)
      (InDegreeZero (Corner φ₁)) (InDegreeZero (Corner φ₂))).inv

/-- **The two-step crossing commutes with the shift.** -/
instance twoStepRightMulNat_commShift :
    NatTrans.CommShift (twoStepRightMulNat c hc) ℤ := by
  unfold twoStepRightMulNat
  infer_instance

/-- **A natural transformation of `Ind_{φ₂} Ind_{φ₁}` with the value of Rouquier's crossing on
generators**, `e₂ ⊗ (z ⊗ n) ↦ σ(z) ⊗ (e₁ ⊗ n)`, sends `m ⊗ (z ⊗ n)` to `m σ(z) ⊗ (e₁ ⊗ n)`. -/
theorem app_tmul_tmul_of_unitGen
    (θ : functor.{u, u} φ₁ ⋙ functor.{u, u} φ₂ ⟶ functor.{u, u} φ₁ ⋙ functor.{u, u} φ₂)
    (hθ : ∀ (N : ModuleCat.{u} A₀) (z : Corner φ₁) (n : N),
      (θ.app N).hom (Ind.tmul (unitGen φ₂) (Ind.tmul z n)) =
        Ind.tmul (sigmaElt φ₁ φ₂ c z) (Ind.tmul (unitGen φ₁) n))
    (N : ModuleCat.{u} A₀) (m : Corner φ₂) (z : Corner φ₁) (n : N) :
    (θ.app N).hom (Ind.tmul m (Ind.tmul z n)) =
      Ind.tmul (twoStepRightElem c m z) (Ind.tmul (unitGen φ₁) n) := by
  have e : (Ind.tmul m (Ind.tmul z n) : Ind (Ind N φ₁) φ₂) =
      m.1 • Ind.tmul (unitGen φ₂) (Ind.tmul z n) := by
    rw [Ind.smul_tmul]
    exact congrArg (Ind.tmul · _) (Subtype.ext m.2.symm)
  rw [e, (θ.app N).hom.map_smul, hθ, Ind.smul_tmul]
  rfl

end Categorification.InductionAlong.Corner
