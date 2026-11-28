/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DerivedTensorCompCommShift
import Categorification.Algebra.InductionAlongDerived

set_option backward.isDefEq.respectTransparency false

/-!
# Left multiplication on a two-step corner, as a coefficient map

For non-unital ring maps `φ₁ : A → B`, `φ₂ : B → C` and the corner bimodules `e₁ B`, `e₂ C`
(`InductionAlong.RCorner`), an element `c ∈ C` with `φ₂(1) c = c` that commutes with the image
of `φ₂ ∘ φ₁` acts on `e₁ B ⊗_B e₂ C` by `m ⊗ n ↦ e₁ ⊗ c φ₂(m) n`
(`InductionAlong.RCorner.twoStepLeftMul`); under `e₁ B ⊗_B e₂ C ≅ e₂φ₂(e₁) C` this is left
multiplication by `c`. Its coefficient map on `(e₁ B ⊗_B e₂ C) ⊗_C -`, transported to
`e₁ B ⊗_B (e₂ C ⊗_C -)`, commutes with the shift (`InductionAlong.RCorner.twoStepLeftMulNat`).

This is the dg form of the crossing on `𝔈_i²` in B. Webster, *Knot invariants and higher
representation theory*, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21 (with `c` the
crossing of the two newest black strands).

## Main definitions

* `Categorification.dgHomOfDegreeZero`: a linear map between dg modules concentrated in degree
  `0` is a dg map.
* `InductionAlong.RCorner.twoStepLeftMul`, `InductionAlong.RCorner.twoStepLeftMulNat`.
-/

open CategoryTheory DG DG.DegreeZero MulOpposite

universe u

noncomputable section

namespace Categorification

section DegreeZero

variable {A : Type u} [Ring A] {X X' : Type u} [AddCommGroup X] [DGAddCommGroup X]
  [AddCommGroup X'] [DGAddCommGroup X']
  [hX : Fact (∀ m : X, m ∈ grading 0)] [hX' : Fact (∀ m : X', m ∈ grading 0)]

theorem eq_zero_of_mem_grading_of_degreeZero {i : ℤ} (hi : i ≠ 0) {x : X}
    (hx : x ∈ grading i) : x = 0 := by
  have h₁ := DirectSum.decompose_of_mem_same (grading (M := X)) hx
  have h₂ := DirectSum.decompose_of_mem_ne (grading (M := X)) (hX.out x) (Ne.symm hi)
  rw [h₂] at h₁
  exact h₁.symm

theorem d_eq_zero_of_degreeZero (x : X) : d x = 0 :=
  eq_zero_of_mem_grading_of_degreeZero (i := 0 + 1) (by decide) (d_mem (hX.out x))

variable [Module A X] [Module A X']

/-- **A linear map between dg modules concentrated in degree `0` is a dg map.** -/
def dgHomOfDegreeZero (f : X →ₗ[A] X') : X →ᵈᵍ[A] X' where
  toFun := f
  map_add' := map_add f
  map_smul' := f.map_smul
  map_mem' {i x} hx := by
    by_cases hi : i = 0
    · subst hi; exact hX'.out _
    · rw [eq_zero_of_mem_grading_of_degreeZero hi hx, map_zero]; exact zero_mem _
  map_d' x := by
    rw [d_eq_zero_of_degreeZero, d_eq_zero_of_degreeZero, map_zero]

@[simp] theorem dgHomOfDegreeZero_apply (f : X →ₗ[A] X') (x : X) :
    dgHomOfDegreeZero f x = f x := rfl

end DegreeZero

namespace InductionAlong

namespace RCorner

open TensorProductOver TensorProductOver.RightAction

local instance (X : Type u) [AddCommGroup X] : Fact (∀ m : InDegreeZero X, m ∈ grading 0) :=
  ⟨fun _ => (InDegreeZero.mem_grading_iff (M := X)).mpr (Or.inl rfl)⟩

variable {A B C : Type u} [Ring A] [Ring B] [Ring C] {φ₁ : A →ₙ+* B} {φ₂ : B →ₙ+* C}
  (c : C) (hc₁ : φ₂ 1 * c = c) (hc : ∀ a, c * φ₂ (φ₁ a) = φ₂ (φ₁ a) * c)

set_option hygiene false in
local notation "P" =>
  TensorProductOver B (InDegreeZero (RCorner φ₁)) (InDegreeZero (RCorner φ₂))

include hc₁ in
/-- The element `c φ₂(m) n` of `e₂ C`. -/
def twoStepElem (m : RCorner φ₁) (n : RCorner φ₂) : RCorner φ₂ :=
  ⟨c * φ₂ m.1 * n.1, by rw [mem_rIdeal, ← mul_assoc, ← mul_assoc, hc₁]⟩

/-- The balanced biadditive map `(m, n) ↦ e₁ ⊗ c φ₂(m) n`. -/
def twoStepAddHom : InDegreeZero (RCorner φ₁) →+ InDegreeZero (RCorner φ₂) →+ P :=
  AddMonoidHom.mk' (fun m => AddMonoidHom.mk' (fun n =>
      tmul B (show InDegreeZero (RCorner φ₁) from gen φ₁)
        (show InDegreeZero (RCorner φ₂) from twoStepElem c hc₁ m n)) fun n n' => by
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

include hc in
/-- **Left multiplication by `c` on `e₁ B ⊗_B e₂ C`**: `m ⊗ n ↦ e₁ ⊗ c φ₂(m) n`, a map of
`(A, C)`-bimodules. -/
def twoStepLeftMul : P →ₗ[A] P where
  toFun := lift (twoStepAddHom c hc₁) fun b m n => by
    change tmul B _ _ = tmul B _ _
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
      change tmul B _ _ = a • tmul B _ _
      rw [smul_tmul]
      have hg : (a • (show InDegreeZero (RCorner φ₁) from gen φ₁) : InDegreeZero (RCorner φ₁)) =
          op (φ₁ a) • (show InDegreeZero (RCorner φ₁) from gen φ₁) :=
        Subtype.ext (by
          change φ₁ a * φ₁ 1 = φ₁ 1 * φ₁ a
          rw [← map_mul, ← map_mul, mul_one, one_mul])
      rw [hg, op_smul_tmul]
      congr 1
      exact Subtype.ext (by
        change c * φ₂ (φ₁ a * m.1) * n.1 = φ₂ (φ₁ a) * (c * φ₂ m.1 * n.1)
        rw [map_mul, ← mul_assoc, ← mul_assoc, ← mul_assoc, hc])

theorem twoStepLeftMul_tmul (m : RCorner φ₁) (n : RCorner φ₂) :
    twoStepLeftMul c hc₁ hc (tmul B (show InDegreeZero (RCorner φ₁) from m)
        (show InDegreeZero (RCorner φ₂) from n)) =
      tmul B (show InDegreeZero (RCorner φ₁) from gen φ₁)
        (show InDegreeZero (RCorner φ₂) from twoStepElem c hc₁ m n) := rfl

theorem twoStepLeftMul_op_smul (c' : C) (x : P) :
    twoStepLeftMul c hc₁ hc (op c' • x) = op c' • twoStepLeftMul c hc₁ hc x := by
  induction x using TensorProductOver.induction_on with
  | zero => simp
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | tmul m n =>
    change tmul B _ _ = tmul B _ _
    congr 1
    exact Subtype.ext (by
      change c * φ₂ m.1 * (n.1 * c') = c * φ₂ m.1 * n.1 * c'
      simp only [mul_assoc])

/-- **The two-step left multiplication by `c` on `e₁ B ⊗_B (e₂ C ⊗_C -)`**: the coefficient map
of `InductionAlong.RCorner.twoStepLeftMul`, transported along associativity of the dg tensor
product. -/
def twoStepLeftMulNat :
    DGModuleCat.tensorFunctor (B := C) B (InDegreeZero (RCorner φ₂)) ⋙
        DGModuleCat.tensorFunctor (B := B) A (InDegreeZero (RCorner φ₁)) ⟶
      DGModuleCat.tensorFunctor (B := C) B (InDegreeZero (RCorner φ₂)) ⋙
        DGModuleCat.tensorFunctor (B := B) A (InDegreeZero (RCorner φ₁)) :=
  (DGModuleCat.tensorFunctorCompIso (A := B) (B := C) (C := A)
      (InDegreeZero (RCorner φ₂)) (InDegreeZero (RCorner φ₁))).hom ≫
    tensorCoeffNat (dgHomOfDegreeZero (twoStepLeftMul c hc₁ hc))
      (twoStepLeftMul_op_smul c hc₁ hc) ≫
    (DGModuleCat.tensorFunctorCompIso (A := B) (B := C) (C := A)
      (InDegreeZero (RCorner φ₂)) (InDegreeZero (RCorner φ₁))).inv

/-- **The two-step left multiplication commutes with the shift.** -/
instance twoStepLeftMulNat_commShift :
    NatTrans.CommShift (twoStepLeftMulNat c hc₁ hc) ℤ := by
  unfold twoStepLeftMulNat
  infer_instance

end RCorner

end InductionAlong

end Categorification
