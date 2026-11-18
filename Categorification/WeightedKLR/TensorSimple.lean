/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.AbsoluteSimple
import Categorification.WeightedKLR.SimpleGrading
import Categorification.WeightedKLR.GradedK0.CoproductK0

/-!
# The graded tensor comparison for weighted KLR algebras without zero-weight loops

Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4,
§2.4, Theorem 2.19, roadmap A0 and A. Finite-dimensionality of graded simple
tops and the local-chart scalar-endomorphism theorem supply all five fields
of the tensor comparison. The graded coproduct Mackey formula consequently
needs no tensor-comparison hypothesis for graphs without zero-weight loops over any field.
The grading datum is arbitrary subject to the existing `HasGdim` assumption;
`SimpleGrading.lean` derives the positive dot degrees needed by A0 from it.
The quantum Serre relations, quantum-group map, and antipode are separate
roadmap items and are not asserted here.
-/

noncomputable section

namespace Categorification.WeightedKLR

open DirectSum Categorification.Graded GalleryAlgebra Juxtapose
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [Field k] {Γ : WeightedGraph I 𝕜 k}

namespace GradingDatum

/-- The scalar-endomorphism assertion of Webster arXiv:1209.2463v4,
Theorem 2.19, roadmap A, for any grading with finite-dimensional pieces bounded
below. Positive dot degrees follow from that assumption; the coefficient field
and standing polynomials are arbitrary, and the graph has no zero-weight loops (loops of nonzero weight are allowed). -/
theorem exists_eq_smul_of_isGradedSimple_of_hasGdim (G : GradingDatum Γ)
    (hD : Γ.Dagger) (hS : Γ.Standing)
    (hZ : Γ.NoZeroLoops) (hl : ∀ i, Γ.loop i = none)
    {ν : I →₀ ℕ} [HasGdim (G.klrGrade ν)]
    {M : Type*} [AddCommGroup M] [Module k M]
    [Module (WeightedKLRAlgebra k Γ ν) M] [IsScalarTower k (WeightedKLRAlgebra k Γ ν) M]
    {ℳ : ℤ → Submodule k M} [Decomposition ℳ]
    [SetLike.GradedSMul (G.klrGrade ν) ℳ]
    (hM : IsGradedSimple (G.klrGrade ν) ℳ)
    (φ : M →ₗ[WeightedKLRAlgebra k Γ ν] M) : ∃ c : k, ∀ m, φ m = c • m := by
  have := G.finiteDimensional_of_isGradedSimple_of_hasGdim hD hZ hS hM
  have := hM.isSimpleModule
  exact WeightedKLR.exists_eq_smul_of_isSimpleModule hD hS hZ hl
    (G.smulNilpotent_reducedDot_of_isGradedSimple_of_hasGdim hD hZ hS hM) φ

/-- All tensor-comparison hypotheses for weighted KLR algebras without zero-weight loops,
Webster arXiv:1209.2463v4, Theorem 2.19, roadmap A0/A. This is the weighted
counterpart of the inputs supplied by KL I arXiv:0803.4121v2, Proposition 2.12
and Corollary 3.19. There is no restriction on colour multiplicities, cycles,
characteristic, or standing polynomials. -/
theorem tensorK0Hyp (G : GradingDatum Γ) (hD : Γ.Dagger) (hS : Γ.Standing)
    (hZ : Γ.NoZeroLoops) (hl : ∀ i, Γ.loop i = none)
    (ν μ : I →₀ ℕ) [HasGdim (G.klrGrade ν)] [HasGdim (G.klrGrade μ)] :
    TensorK0Hyp (G.klrGrade ν) (G.klrGrade μ) where
  fdA b := G.finiteDimensional_top_of_hasGdim hD hZ hS b
  fdB b := G.finiteDimensional_top_of_hasGdim hD hZ hS b
  endA b φ := by
    obtain ⟨c, hc⟩ := G.exists_eq_smul_of_isGradedSimple_of_hasGdim hD hS hZ hl
      (GProj.IndecClass.isGradedSimple_top b) φ
    exact ⟨c, LinearMap.ext hc⟩
  endB b φ := by
    obtain ⟨c, hc⟩ := G.exists_eq_smul_of_isGradedSimple_of_hasGdim hD hS hZ hl
      (GProj.IndecClass.isGradedSimple_top b) φ
    exact ⟨c, LinearMap.ext hc⟩
  fdC b := G.finiteDimensional_top_tensor_of_hasGdim hD hZ hS b

end GradingDatum

variable {ν' ν'' ν₁ ν₂ : I →₀ ℕ}

/-- The graded coproduct Mackey formula of Webster arXiv:1209.2463v4,
Theorem 2.19, over any field for graphs without zero-weight loops under the standing hypothesis.
The tensor comparison is proved by `GradingDatum.tensorK0Hyp`, so no route
hypothesis is required. The earlier statement allowing graphs with loops is
`exists_coproductK0_indK0_eq_sum_graded_of_tensorK0Hyp`. -/
theorem exists_coproductK0_indK0_eq_sum_graded (G : GradingDatum Γ) (hD : Γ.Dagger)
    (hS : Γ.Standing)
    (hZ : Γ.NoZeroLoops) (hl : ∀ i, Γ.loop i = none)
    (hν : ν₁ + ν₂ = ν' + ν'')
    [∀ μ : I →₀ ℕ, HasGdim (G.klrGrade μ)] :
    ∃ (n : ℕ) (L : Fin n → ShuffleLayout ν' ν'' ν₁ ν₂),
      Function.Injective (fun i => ⇑(L i).c) ∧
      Set.range (fun i => ⇑(L i).c) = Set.range (shuffleType (ν := ν' + ν'') ν' ν₁) ∧
      ∀ (x : K0 (G.klrGrade ν')) (y : K0 (G.klrGrade ν'')),
        G.coproductK0 hD hZ hS ν₁ ν₂
          (G.tensorK0Hyp hD hS hZ hl ν₁ ν₂) (K0.map (castW k Γ hν.symm)
            (fun _ _ h => G.castW_symm_mem_klrGrade hν.symm h) (G.indK0 ν' ν'' x y)) =
          ∑ i, (LaurentPolynomial.T (middleShift G (L i).a (L i).b (L i).c (L i).d) :
              LaurentPolynomial ℤ) •
            (L i).twistedMulK0Graded G
              (G.coproductK0 hD hZ hS (L i).a (L i).b
                (G.tensorK0Hyp hD hS hZ hl _ _)
                  (K0.map (castW k Γ (L i).hab).symm
                    (fun _ _ h => G.castW_mem_klrGrade (L i).hab h) x) ⊗ₜ
                G.coproductK0 hD hZ hS (L i).c (L i).d
                  (G.tensorK0Hyp hD hS hZ hl _ _)
                  (K0.map (castW k Γ (L i).hcd).symm
                    (fun _ _ h => G.castW_mem_klrGrade (L i).hcd h) y)) := by
  exact exists_coproductK0_indK0_eq_sum_graded_of_tensorK0Hyp G hD
    hZ hS hν (fun μ μ' => G.tensorK0Hyp hD hS hZ hl μ μ')

end Categorification.WeightedKLR
