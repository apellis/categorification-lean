/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Simple
import Categorification.WeightedKLR.RedStrands.Reduced
import Categorification.KLR.Crystal.SimpleTensor

/-!
# Nilpotent dots on finite-dimensional graded weighted modules

The positive-degree argument accompanying Khovanov–Lauda I,
arXiv:0803.4121v2, §2.5, Proposition 2.12: an operator of positive degree
acts nilpotently on a finite-dimensional graded module. Together with
weighted finite-dimensionality (Webster arXiv:1209.2463v4, §2.4,
Theorem 2.19, roadmap A0), this supplies nilpotent dots for graded simples,
as required by the local-chart route to roadmap A.
-/

noncomputable section

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

namespace Categorification.WeightedKLR

open MvPolynomial DirectSum Categorification.Graded GalleryAlgebra

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [Field k] {Γ : WeightedGraph I 𝕜 k}
  {ν : I →₀ ℕ}

namespace GradingDatum

/-- A dot on a fixed labelled strand is homogeneous for Webster's grading
(arXiv:1209.2463v4, §2.1). -/
theorem reducedDot_mem_grade (G : GradingDatum Γ) (s : Strand ν) :
    reducedDot k Γ ν s ∈ G.klrGrade ν (G.wt s) := by
  change rankIdem k Γ ν * poly (X s) * rankIdem k Γ ν ∈ G.grade ν (G.wt s)
  simpa only [zero_add, add_zero] using
    SetLike.mul_mem_graded (SetLike.mul_mem_graded (rankIdem_mem_grade G ν)
      (G.poly_mem_grade (isWeightedHomogeneous_X k G.wt s))) (rankIdem_mem_grade G ν)

variable {M : Type*} [AddCommGroup M] [Module k M]
  [Module (WeightedKLRAlgebra k Γ ν) M]
  {ℳ : ℤ → Submodule k M} [Decomposition ℳ]

/-- Positive-degree dots act nilpotently on finite-dimensional graded weighted
modules, by the degree-bound argument of KL I arXiv:0803.4121v2,
§2.5, Proposition 2.12. No simplicity hypothesis is needed for this step. -/
theorem smulNilpotent_reducedDot_of_graded (G : GradingDatum Γ)
    [SetLike.GradedSMul (G.klrGrade ν) ℳ] [FiniteDimensional k M]
    (s : Strand ν) (hG : 0 < G.wt s) : KLR.SmulNilpotent (reducedDot k Γ ν s) M := by
  obtain ⟨L, U, hLU⟩ := Graded.exists_bounds (ℳ := ℳ)
  let N := (U - L + 1).toNat
  refine ⟨N, fun v => ?_⟩
  have hhom : ∀ (d : ℤ) (w : M), w ∈ ℳ d → (reducedDot k Γ ν s) ^ N • w = 0 := by
    intro d w hw
    by_cases hd : L ≤ d ∧ d ≤ U
    · have hNZ : (N : ℤ) = U - L + 1 := by simp only [N]; omega
      have hmem := SetLike.GradedSMul.smul_mem
        (SetLike.pow_mem_graded N (G.reducedDot_mem_grade s)) hw
      rw [hLU _ (Or.inr (by rw [vadd_eq_add, nsmul_eq_mul]; nlinarith)),
        Submodule.mem_bot] at hmem
      exact hmem
    · have : ℳ d = ⊥ := hLU d (by omega)
      rw [this, Submodule.mem_bot] at hw
      rw [hw, smul_zero]
  induction v using DirectSum.Decomposition.inductionOn ℳ with
  | zero => rw [smul_zero]
  | homogeneous w => exact hhom _ w w.2
  | add v w hv hw => rw [smul_add, hv, hw, add_zero]

variable (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hS : Γ.Standing)
  [IsScalarTower k (WeightedKLRAlgebra k Γ ν) M]
  [SetLike.GradedSMul (hS.gradingDatum.klrGrade ν) ℳ]

include hD hZ in
/-- Every dot acts nilpotently on a graded simple weighted KLR module.
This combines the KL I arXiv:0803.4121v2, Proposition 2.12 degree argument
with roadmap A0 finite-dimensionality for Webster arXiv:1209.2463v4,
Theorem 2.19, and supplies the nilpotent-dot input to roadmap A. -/
theorem smulNilpotent_reducedDot_of_isGradedSimple
    (hM : IsGradedSimple (hS.gradingDatum.klrGrade ν) ℳ) (s : Strand ν) :
    KLR.SmulNilpotent (reducedDot k Γ ν s) M := by
  have := finiteDimensional_of_isGradedSimple hD hZ hS hM
  exact smulNilpotent_reducedDot_of_graded (ℳ := ℳ) hS.gradingDatum s (hS.wt_pos s)

end GradingDatum
end Categorification.WeightedKLR
