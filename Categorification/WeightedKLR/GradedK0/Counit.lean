/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.GradedK0.Algebra
import Categorification.Algebra.Graded.ScalarK0
import Categorification.WeightedKLR.GradedK0.ZeroAlgebra

/-!
# The counit of the graded weighted Grothendieck algebra

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4,
§2.4, proof of Theorem 2.19, p. 12. The counit projects onto the zero-weight
Grothendieck group, which is the Laurent-polynomial scalar ring over a field.
-/

noncomputable section

namespace Categorification.WeightedKLR

open GalleryAlgebra Categorification.Graded

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜]

namespace GradingDatum

section Field

variable {k : Type*} [Field k] {Γ : WeightedGraph I 𝕜 k}
variable (G : GradingDatum Γ)

local notation "A" => WeightedKLRAlgebra k Γ (0 : I →₀ ℕ)
local notation "R" => LaurentPolynomial ℤ

/-- Every element of the zero-strand block has grading degree zero. -/
theorem mem_klrGrade_zero (a : A) : a ∈ G.klrGrade 0 0 :=
  mem_scalarGrade (G.klrGrade 0) weightedKLRZeroEquiv a

/-- At weight zero the class of the regular projective freely generates the
Grothendieck group over the Laurent-polynomial scalars. -/
def K0zeroEquiv : G.K0fam 0 ≃ₗ[R] R :=
  scalarK0Equiv (G.klrGrade 0) weightedKLRZeroEquiv

@[simp] theorem K0zeroEquiv_symm_apply (p : R) : G.K0zeroEquiv.symm p = p • G.K0one :=
  rfl

@[simp] theorem K0zeroEquiv_one : G.K0zeroEquiv G.K0one = 1 := by
  apply G.K0zeroEquiv.symm.injective
  rw [LinearEquiv.symm_apply_apply, K0zeroEquiv_symm_apply, one_smul]

/-- Inclusion of the zero-weight block is the scalar map under its identification
with the Laurent-polynomial ring. -/
theorem K0W_of_zero_eq_algebraMap (x : G.K0fam 0) : DirectSum.of G.K0fam 0 x =
    algebraMap R G.K0W (G.K0zeroEquiv x) := by
  rw [K0W_algebraMap, ← K0one, ← K0zeroEquiv_symm_apply, LinearEquiv.symm_apply_apply]

/-- Webster's counit (arXiv:1209.2463v4, §2.4, proof of Theorem 2.19) is the
weight-zero projection followed by the scalar identification. -/
def counitK0 : G.K0W →ₗ[R] R :=
  G.K0zeroEquiv.toLinearMap.comp (DirectSum.component R (I →₀ ℕ) G.K0fam 0)

@[simp] theorem counitK0_of_zero (x : G.K0fam 0) :
    G.counitK0 (DirectSum.of G.K0fam 0 x) = G.K0zeroEquiv x := by
  rw [counitK0, LinearMap.comp_apply, ← DirectSum.lof_eq_of R,
    DirectSum.component.lof_self]
  rfl

theorem counitK0_of_ne {ν : I →₀ ℕ} (h : ν ≠ 0) (x : G.K0fam ν) :
    G.counitK0 (DirectSum.of G.K0fam ν x) = 0 := by
  rw [counitK0, LinearMap.comp_apply, ← DirectSum.lof_eq_of R,
    DirectSum.component.of, dite_eq_right h, map_zero]

@[simp] theorem counitK0_one : G.counitK0 1 = 1 := by
  rw [K0W_one, counitK0_of_zero]
  exact G.K0zeroEquiv_one

@[simp] theorem counitK0_algebraMap (p : R) : G.counitK0 (algebraMap R G.K0W p) = p := by
  rw [K0W_algebraMap, counitK0_of_zero, ← K0one, map_smul, K0zeroEquiv_one, smul_eq_mul, mul_one]

/-- The weight-zero projection is multiplicative for graded induction. -/
theorem counitK0_mul (x y : G.K0W) : G.counitK0 (x * y) = G.counitK0 x * G.counitK0 y := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [add_mul, map_add, hx, hx']
  | of ν x =>
    by_cases hν : ν = 0
    · subst ν
      rw [G.K0W_of_zero_eq_algebraMap x, ← Algebra.smul_def, map_smul,
        counitK0_algebraMap, smul_eq_mul]
    · rw [counitK0_of_ne _ hν, zero_mul]
      induction y using DirectSum.induction_on with
      | zero => simp
      | add y y' hy hy' => simp only [mul_add, map_add, hy, hy', add_zero]
      | of μ y =>
        have h : ν + μ ≠ 0 := fun h => hν ((Finsupp.add_eq_zero_iff ν μ).mp h).1
        rw [K0W_of_mul_of, counitK0_of_ne _ h]

/-- The counit as a Laurent-polynomial algebra homomorphism. -/
def counitK0Alg : G.K0W →ₐ[R] R :=
  AlgHom.ofLinearMap G.counitK0 G.counitK0_one G.counitK0_mul

@[simp] theorem counitK0Alg_apply (x : G.K0W) : G.counitK0Alg x = G.counitK0 x :=
  rfl

end Field

end GradingDatum

end Categorification.WeightedKLR
