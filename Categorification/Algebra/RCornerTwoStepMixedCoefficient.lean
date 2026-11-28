/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.RCornerTwoStepCoefficient

set_option backward.isDefEq.respectTransparency false

/-!
# Left multiplication between two two-step corners, as a coefficient map

For two factorizations `φ₂ ∘ φ₁`, `φ₂' ∘ φ₁'` of maps `A → C` of non-unital rings (through `B`
and through `B'`), an element `c ∈ C` with
`c φ₂(φ₁ a) = φ₂'(φ₁' a) c φ₂(φ₁ 1)` for all `a` acts from `e₁ B ⊗_B e₂ C` to
`e₁' B' ⊗_{B'} e₂' C` by `m ⊗ n ↦ e₁' ⊗ c φ₂(m) n`
(`InductionAlong.RCorner.twoStepMixedLeftMul`). Its coefficient map on
`e₁ B ⊗_B (e₂ C ⊗_C -) ⟶ e₁' B' ⊗_{B'} (e₂' C ⊗_C -)` commutes with the shift
(`InductionAlong.RCorner.twoStepMixedLeftMulNat`). The condition on `c` is what linearity of
left multiplication by `c` between the restrictions says on the regular module
(`InductionAlong.RCorner.intertwines_of_res_app`).

This is the dg form of the crossing of two black strands of different colours on `𝔈_a 𝔈_b` in
B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.21 (cf. `InductionAlong.RCorner.twoStepLeftMul` for one colour).

## Main definitions

* `InductionAlong.RCorner.twoStepMixedLeftMul`, `InductionAlong.RCorner.twoStepMixedLeftMulNat`.

## Main results

* `InductionAlong.RCorner.intertwines_of_res_app`.
-/

open CategoryTheory DG DG.DegreeZero MulOpposite

universe u

noncomputable section

namespace Categorification

namespace InductionAlong

namespace RCorner

open TensorProductOver TensorProductOver.RightAction

local instance (X : Type u) [AddCommGroup X] : Fact (∀ m : InDegreeZero X, m ∈ grading 0) :=
  ⟨fun _ => (InDegreeZero.mem_grading_iff (M := X)).mpr (Or.inl rfl)⟩

variable {A B B' C : Type u} [Ring A] [Ring B] [Ring B'] [Ring C] {φ₁ : A →ₙ+* B}
  {φ₂ : B →ₙ+* C} {φ₁' : A →ₙ+* B'} {φ₂' : B' →ₙ+* C}

/-- **The intertwining condition from a module map on restrictions**: if a natural
transformation between the two restrictions `Res φ₁ ∘ Res φ₂` and `Res φ₁' ∘ Res φ₂'` acts by
`c` on underlying elements, then `c φ₂(φ₁ a) = φ₂'(φ₁' a) c φ₂(φ₁ 1)` (linearity on the
regular module at `φ₂(φ₁ 1)`). -/
theorem intertwines_of_res_app (c : C)
    (θ₀ : resFunctor.{u, u} φ₂ ⋙ resFunctor.{u, u} φ₁ ⟶
      resFunctor.{u, u} φ₂' ⋙ resFunctor.{u, u} φ₁')
    (hθ₀ : ∀ (X : ModuleCat.{u} C) (r : Res φ₁ (Res φ₂ X)),
      ((θ₀.app X).hom r).val.val = c • r.val.val) (a : A) :
    c * φ₂ (φ₁ a) = φ₂' (φ₁' a) * (c * φ₂ (φ₁ 1)) := by
  let X : ModuleCat.{u} C := ModuleCat.of C C
  have h₂ : φ₂ 1 • φ₂ (φ₁ 1) = φ₂ (φ₁ 1) := by
    change φ₂ 1 * φ₂ (φ₁ 1) = φ₂ (φ₁ 1)
    rw [← map_mul, one_mul]
  let r₂ : Res φ₂ X := Res.mk (show X from φ₂ (φ₁ 1)) h₂
  have h₁ : φ₁ 1 • r₂ = r₂ := Res.ext (by
    change φ₂ (φ₁ 1) * φ₂ (φ₁ 1) = φ₂ (φ₁ 1)
    rw [← map_mul, ← map_mul, one_mul])
  let r : Res φ₁ (Res φ₂ X) := Res.mk r₂ h₁
  calc c * φ₂ (φ₁ a) = c * (φ₂ (φ₁ a) * φ₂ (φ₁ 1)) := by rw [← map_mul, ← map_mul, mul_one]
    _ = ((θ₀.app X).hom (a • r)).val.val := (hθ₀ X (a • r)).symm
    _ = (a • (θ₀.app X).hom r).val.val :=
        congrArg (fun z => Res.val (Res.val z)) ((θ₀.app X).hom.map_smul a r)
    _ = φ₂' (φ₁' a) * (c * φ₂ (φ₁ 1)) := by
        change φ₂' (φ₁' a) • ((θ₀.app X).hom r).val.val = _
        rw [hθ₀]
        rfl

variable (c : C) (hc : ∀ a, c * φ₂ (φ₁ a) = φ₂' (φ₁' a) * (c * φ₂ (φ₁ 1)))

set_option hygiene false in
local notation "P" =>
  TensorProductOver B (InDegreeZero (RCorner φ₁)) (InDegreeZero (RCorner φ₂))
set_option hygiene false in
local notation "P'" =>
  TensorProductOver B' (InDegreeZero (RCorner φ₁')) (InDegreeZero (RCorner φ₂'))

include hc in
theorem twoStepMixed_mul_eq (m : RCorner φ₁) (n : C) :
    φ₂' (φ₁' 1) * (c * φ₂ m.1 * n) = c * φ₂ m.1 * n := by
  have hm : φ₂ m.1 = φ₂ (φ₁ 1) * φ₂ m.1 := by rw [← map_mul, m.2]
  have key : c * φ₂ m.1 = φ₂' (φ₁' 1) * (c * φ₂ m.1) :=
    calc c * φ₂ m.1 = c * φ₂ (φ₁ 1) * φ₂ m.1 := by rw [mul_assoc, ← hm]
      _ = φ₂' (φ₁' 1) * (c * φ₂ (φ₁ 1)) * φ₂ m.1 := by rw [← hc 1]
      _ = φ₂' (φ₁' 1) * (c * φ₂ m.1) := by rw [mul_assoc, mul_assoc, ← hm]
  conv_rhs => rw [key]
  exact (mul_assoc _ _ _).symm

include hc in
/-- The element `c φ₂(m) n` of `e₂' C`. -/
def twoStepMixedElem (m : RCorner φ₁) (n : RCorner φ₂) : RCorner φ₂' :=
  ⟨c * φ₂ m.1 * n.1, by
    have := twoStepMixed_mul_eq c hc m n.1
    rw [mem_rIdeal]
    rw [← this, ← mul_assoc, ← map_mul, one_mul]⟩

/-- The balanced biadditive map `(m, n) ↦ e₁' ⊗ c φ₂(m) n`. -/
def twoStepMixedAddHom : InDegreeZero (RCorner φ₁) →+ InDegreeZero (RCorner φ₂) →+ P' :=
  AddMonoidHom.mk' (fun m => AddMonoidHom.mk' (fun n =>
      tmul B' (show InDegreeZero (RCorner φ₁') from gen φ₁')
        (show InDegreeZero (RCorner φ₂') from twoStepMixedElem c hc m n)) fun n n' => by
      rw [← tmul_add]
      congr 1
      exact Subtype.ext (mul_add _ _ _)) fun m m' => by
    ext n
    simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
    rw [← tmul_add]
    congr 1
    exact Subtype.ext (by
      change c * φ₂ (m.1 + m'.1) * n.1 = c * φ₂ m.1 * n.1 + c * φ₂ m'.1 * n.1
      rw [map_add, mul_add, add_mul])

/-- **Left multiplication by `c` from `e₁ B ⊗_B e₂ C` to `e₁' B' ⊗_{B'} e₂' C`**:
`m ⊗ n ↦ e₁' ⊗ c φ₂(m) n`, a map of `(A, C)`-bimodules. -/
def twoStepMixedLeftMul : P →ₗ[A] P' where
  toFun := lift (twoStepMixedAddHom c hc) fun b m n => by
    change tmul B' _ _ = tmul B' _ _
    congr 1
    exact Subtype.ext (by
      change c * φ₂ (m.1 * b) * n.1 = c * φ₂ m.1 * (φ₂ b * n.1)
      simp only [map_mul, mul_assoc])
  map_add' := map_add _
  map_smul' a x := by
    induction x using TensorProductOver.induction_on with
    | zero => simp
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    | tmul m n =>
      change tmul B' _ _ = a • tmul B' _ _
      rw [smul_tmul]
      have hg : (a • (show InDegreeZero (RCorner φ₁') from gen φ₁') :
          InDegreeZero (RCorner φ₁')) =
          op (φ₁' a) • (show InDegreeZero (RCorner φ₁') from gen φ₁') :=
        Subtype.ext (by
          change φ₁' a * φ₁' 1 = φ₁' 1 * φ₁' a
          rw [← map_mul, ← map_mul, mul_one, one_mul])
      rw [hg, op_smul_tmul]
      congr 1
      exact Subtype.ext (by
        change c * φ₂ (φ₁ a * m.1) * n.1 = φ₂' (φ₁' a) * (c * φ₂ m.1 * n.1)
        have hm : φ₂ m.1 = φ₂ (φ₁ 1) * φ₂ m.1 := by rw [← map_mul, m.2]
        rw [map_mul, ← mul_assoc, hc a]
        conv_rhs => rw [hm]
        simp only [mul_assoc])

theorem twoStepMixedLeftMul_tmul (m : RCorner φ₁) (n : RCorner φ₂) :
    twoStepMixedLeftMul c hc (tmul B (show InDegreeZero (RCorner φ₁) from m)
        (show InDegreeZero (RCorner φ₂) from n)) =
      tmul B' (show InDegreeZero (RCorner φ₁') from gen φ₁')
        (show InDegreeZero (RCorner φ₂') from twoStepMixedElem c hc m n) := rfl

theorem twoStepMixedLeftMul_op_smul (c' : C) (x : P) :
    twoStepMixedLeftMul c hc (op c' • x) = op c' • twoStepMixedLeftMul c hc x := by
  induction x using TensorProductOver.induction_on with
  | zero => simp
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | tmul m n =>
    change tmul B' _ _ = tmul B' _ _
    congr 1
    exact Subtype.ext (by
      change c * φ₂ m.1 * (n.1 * c') = c * φ₂ m.1 * n.1 * c'
      simp only [mul_assoc])

/-- **The two-step left multiplication by `c` from `e₁ B ⊗_B (e₂ C ⊗_C -)` to
`e₁' B' ⊗_{B'} (e₂' C ⊗_C -)`**: the coefficient map of
`InductionAlong.RCorner.twoStepMixedLeftMul`, transported along associativity of the dg tensor
product. -/
def twoStepMixedLeftMulNat :
    DGModuleCat.tensorFunctor (B := C) B (InDegreeZero (RCorner φ₂)) ⋙
        DGModuleCat.tensorFunctor (B := B) A (InDegreeZero (RCorner φ₁)) ⟶
      DGModuleCat.tensorFunctor (B := C) B' (InDegreeZero (RCorner φ₂')) ⋙
        DGModuleCat.tensorFunctor (B := B') A (InDegreeZero (RCorner φ₁')) :=
  (DGModuleCat.tensorFunctorCompIso (A := B) (B := C) (C := A)
      (InDegreeZero (RCorner φ₂)) (InDegreeZero (RCorner φ₁))).hom ≫
    tensorCoeffNat (dgHomOfDegreeZero (twoStepMixedLeftMul c hc))
      (twoStepMixedLeftMul_op_smul c hc) ≫
    (DGModuleCat.tensorFunctorCompIso (A := B') (B := C) (C := A)
      (InDegreeZero (RCorner φ₂')) (InDegreeZero (RCorner φ₁'))).inv

/-- **The two-step left multiplication between two corners commutes with the shift.** -/
instance twoStepMixedLeftMulNat_commShift :
    NatTrans.CommShift (twoStepMixedLeftMulNat c hc) ℤ := by
  unfold twoStepMixedLeftMulNat
  infer_instance

end RCorner

end InductionAlong

end Categorification
