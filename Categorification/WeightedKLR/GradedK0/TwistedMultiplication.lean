/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.GradedK0.Algebra
import Categorification.QuantumGroup.PreF
import Categorification.WeightedKLR.Mackey.Swap

/-!
# The twisted multiplication on the tensor square of weighted graded K₀

Webster, arXiv:1209.2463v4, §2.4, Theorem 2.19. The weight of the
second input block crosses the weight of the third block. Its Laurent shift
is the sum of their pairwise crossing degrees. The tensor-square calculation
follows the ordinary KLR construction in Khovanov–Lauda I, Proposition 3.2.
-/

noncomputable section

namespace Categorification.WeightedKLR.GradingDatum

open Categorification.Graded Categorification.QuantumGroup LaurentPolynomial
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {𝕜 : Type*}
  {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}
  (G : GradingDatum Γ)

local notation "LP" => LaurentPolynomial ℤ

/-- The total degree of the crossings between two blocks. -/
def crossingDegree (μ ν : I →₀ ℕ) : ℤ :=
  wdot G.pairDeg μ.toMultiset ν.toMultiset

@[simp] theorem crossingDegree_zero_left (ν : I →₀ ℕ) : G.crossingDegree 0 ν = 0 := by
  simp [crossingDegree]

@[simp] theorem crossingDegree_zero_right (μ : I →₀ ℕ) : G.crossingDegree μ 0 = 0 := by
  simp [crossingDegree]

theorem crossingDegree_add_left (μ μ' ν : I →₀ ℕ) :
    G.crossingDegree (μ + μ') ν = G.crossingDegree μ ν + G.crossingDegree μ' ν := by
  simp [crossingDegree, wdot_add_left]

theorem crossingDegree_add_right (μ ν ν' : I →₀ ℕ) :
    G.crossingDegree μ (ν + ν') = G.crossingDegree μ ν + G.crossingDegree μ ν' := by
  simp [crossingDegree, wdot_add_right]

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- Multiplication by `q^{λ ⋄ |x|}` on homogeneous `x`:
`x ↦ q^{∑_{a ∈ λ, c ∈ |x|} pairDeg(a, c)} x`. -/
def twistOp (l : (I →₀ ℕ)) : G.K0W →ₗ[LP] G.K0W :=
  DirectSum.toModule LP ((I →₀ ℕ)) _ fun μ =>
    (T (G.crossingDegree l μ) : LP) • DirectSum.lof LP ((I →₀ ℕ)) G.K0fam μ

theorem twistOp_of (l μ : (I →₀ ℕ)) (y : K0 (G.klrGrade μ)) :
    G.twistOp l (DirectSum.of G.K0fam μ y) =
      (T (G.crossingDegree l μ) : LP) • DirectSum.of G.K0fam μ y := by
  rw [twistOp, ← DirectSum.lof_eq_of LP, DirectSum.toModule_lof, LinearMap.smul_apply]

/-- The bilinear map behind `twMul`: `x₁ ↦ x₂ ↦ (y₁ ⊗ y₂ ↦ x₁ τ_{|x₂|}(y₁) ⊗ x₂ y₂)`. -/
def twMulAux : G.K0W →ₗ[LP] G.K0W →ₗ[LP] Module.End LP (G.K0W ⊗[LP] G.K0W) :=
  (DirectSum.toModule LP ((I →₀ ℕ)) _ fun μ₂ =>
    ((TensorProduct.mapBilinear (RingHom.id LP) G.K0W G.K0W G.K0W G.K0W ∘ₗ
        LinearMap.lcomp LP G.K0W (G.twistOp μ₂) ∘ₗ LinearMap.mul LP G.K0W).compl₂
      (LinearMap.mul LP G.K0W ∘ₗ DirectSum.lof LP ((I →₀ ℕ)) G.K0fam μ₂)).flip).flip

/-- **The twisted multiplication (3.1) on `K₀(R) ⊗ K₀(R)`**:
`(x₁ ⊗ x₂)(x₁' ⊗ x₂') = q^{|x₂| ⋄ |x₁'|} x₁x₁' ⊗ x₂x₂'` for homogeneous `x₂`, `x₁'`, where
`μ ⋄ μ' = ∑_{a ∈ μ, c ∈ μ'} pairDeg(a, c)` (for the KL I grading, `q^{-|x₂|·|x₁'|}`). -/
def twMul : G.K0W ⊗[LP] G.K0W →ₗ[LP] G.K0W ⊗[LP] G.K0W →ₗ[LP] G.K0W ⊗[LP] G.K0W :=
  TensorProduct.lift G.twMulAux

theorem twMul_tmul_of (x₁ : G.K0W) (μ₂ : (I →₀ ℕ)) (b : K0 (G.klrGrade μ₂)) (y₁ y₂ : G.K0W) :
    G.twMul (x₁ ⊗ₜ DirectSum.of G.K0fam μ₂ b) (y₁ ⊗ₜ y₂) =
      (x₁ * G.twistOp μ₂ y₁) ⊗ₜ (DirectSum.of G.K0fam μ₂ b * y₂) := by
  rw [twMul, TensorProduct.lift.tmul, twMulAux, LinearMap.flip_apply, ← DirectSum.lof_eq_of LP,
    DirectSum.toModule_lof]
  rfl

/-- `(x₁ ⊗ x₂)(x₁' ⊗ x₂') = q^{|x₂| ⋄ |x₁'|} x₁x₁' ⊗ x₂x₂'` for homogeneous `x₂`, `x₁'`. -/
theorem twMul_tmul (x₁ : G.K0W) {μ₂ μ₁' : (I →₀ ℕ)} (b : K0 (G.klrGrade μ₂))
    (a' : K0 (G.klrGrade μ₁')) (y₂ : G.K0W) :
    G.twMul (x₁ ⊗ₜ DirectSum.of G.K0fam μ₂ b) (DirectSum.of G.K0fam μ₁' a' ⊗ₜ y₂) =
      (T (G.crossingDegree μ₂ μ₁') : LP) •
        ((x₁ * DirectSum.of G.K0fam μ₁' a') ⊗ₜ (DirectSum.of G.K0fam μ₂ b * y₂)) := by
  rw [twMul_tmul_of, twistOp_of, mul_smul_comm, TensorProduct.smul_tmul']

/-- Induction on `K₀(R) ⊗ K₀(R)` through homogeneous pure tensors. -/
theorem induction_homog {motive : G.K0W ⊗[LP] G.K0W → Prop} (Z : G.K0W ⊗[LP] G.K0W)
    (zero : motive 0) (add : ∀ Z Z', motive Z → motive Z' → motive (Z + Z'))
    (of : ∀ (μ μ' : (I →₀ ℕ)) (a : K0 (G.klrGrade μ)) (b : K0 (G.klrGrade μ')),
      motive (DirectSum.of G.K0fam μ a ⊗ₜ DirectSum.of G.K0fam μ' b)) : motive Z := by
  induction Z using TensorProduct.inductionOn with
  | add Z Z' hZ hZ' => exact add Z Z' hZ hZ'
  | tmul x y =>
    induction x using DirectSum.induction_on with
    | zero => rw [TensorProduct.zero_tmul]; exact zero
    | add x x' hx hx' => rw [TensorProduct.add_tmul]; exact add _ _ hx hx'
    | of i a =>
      induction y using DirectSum.induction_on with
      | zero => rw [TensorProduct.tmul_zero]; exact zero
      | add y y' hy hy' => rw [TensorProduct.tmul_add]; exact add _ _ hy hy'
      | of j b => exact of i j a b

theorem twistOp_zero : G.twistOp 0 = LinearMap.id :=
  DirectSum.linearMap_ext LP fun μ => LinearMap.ext fun y => by
    rw [LinearMap.comp_apply, DirectSum.lof_eq_of, twistOp_of, crossingDegree_zero_left, T_zero, one_smul]
    rfl

theorem twistOp_one (l : (I →₀ ℕ)) : G.twistOp l 1 = 1 := by
  rw [K0W_one, twistOp_of, crossingDegree_zero_right, T_zero, one_smul]

/-- `1 ⊗ 1` is a left unit for the twisted multiplication. -/
theorem twMul_one_left (X : G.K0W ⊗[LP] G.K0W) : G.twMul (1 ⊗ₜ 1) X = X := by
  induction X using TensorProduct.inductionOn with
  | add X X' hX hX' => rw [LinearMap.map_add, hX, hX']
  | tmul y₁ y₂ =>
    rw [show (1 : G.K0W) ⊗ₜ[LP] (1 : G.K0W) =
        1 ⊗ₜ DirectSum.of G.K0fam 0 (K0.of (GProj.regular (G.klrGrade 0))) from rfl, twMul_tmul_of,
      ← K0W_one, twistOp_zero, LinearMap.id_apply, one_mul, one_mul]

/-- `1 ⊗ 1` is a right unit for the twisted multiplication. -/
theorem twMul_one_right (X : G.K0W ⊗[LP] G.K0W) : G.twMul X (1 ⊗ₜ 1) = X := by
  induction X using G.induction_homog with
  | zero => rw [LinearMap.map_zero, LinearMap.zero_apply]
  | add X X' hX hX' => rw [LinearMap.map_add, LinearMap.add_apply, hX, hX']
  | of μ μ' a b => rw [twMul_tmul_of, twistOp_one, mul_one, mul_one]

/-- **The twisted multiplication (3.1) is associative.** -/
theorem twMul_assoc (X Y Z : G.K0W ⊗[LP] G.K0W) :
    G.twMul (G.twMul X Y) Z = G.twMul X (G.twMul Y Z) := by
  induction X using G.induction_homog with
  | zero => simp only [LinearMap.map_zero, LinearMap.zero_apply]
  | add X X' hX hX' => simp only [LinearMap.map_add, LinearMap.add_apply, hX, hX']
  | of μ₁ μ₂ a₁ a₂ =>
    induction Y using G.induction_homog with
    | zero => simp only [LinearMap.map_zero, LinearMap.zero_apply]
    | add Y Y' hY hY' => simp only [LinearMap.map_add, LinearMap.add_apply, hY, hY']
    | of μ₃ μ₄ a₃ a₄ =>
      induction Z using G.induction_homog with
      | zero => simp only [LinearMap.map_zero]
      | add Z Z' hZ hZ' => simp only [LinearMap.map_add, hZ, hZ']
      | of μ₅ μ₆ a₅ a₆ =>
        rw [twMul_tmul, K0W_of_mul_of G a₂ a₄, LinearMap.map_smul, LinearMap.smul_apply,
          twMul_tmul, twMul_tmul, K0W_of_mul_of G a₃ a₅, LinearMap.map_smul, twMul_tmul,
          ← K0W_of_mul_of G a₂ a₄, ← K0W_of_mul_of G a₃ a₅, smul_smul, smul_smul, ← T_add,
          ← T_add, mul_assoc, mul_assoc]
        congr 2
        rw [crossingDegree_add_left, crossingDegree_add_right]
        ring

end Categorification.WeightedKLR.GradingDatum
