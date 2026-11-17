/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Local.StarChartAction
import Categorification.WeightedKLR.Local.Endomorphisms
import Categorification.WeightedKLR.SimpleDots

/-!
# Scalar endomorphisms of weighted KLR simple modules

The absolute-irreducibility input for Webster,
*Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.4,
Theorem 2.19 (roadmap A). The local-chart argument chooses a
minimum-norm point in the closed supported chambers. The algebra of its local
zero-weight graph acts as the entire supporting corner. The ordinary KLR
result, Khovanov–Lauda I, arXiv:0803.4121v2, §3.2, Corollary 3.19, therefore
detects scalar endomorphisms of weighted simples.

The intermediate ungraded statement assumes finite dimension and nilpotent
dots. For graded simples these follow from A0 and positive dot degrees.
-/

noncomputable section

namespace Categorification.WeightedKLR

open GalleryAlgebra DirectSum Categorification.Graded

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [Field k] {Γ : WeightedGraph I 𝕜 k}
  {ν : I →₀ ℕ} {M : Type*} [AddCommGroup M] [Module k M]
  [Module (WeightedKLRAlgebra k Γ ν) M] [IsScalarTower k (WeightedKLRAlgebra k Γ ν) M]

/-- Scalar endomorphisms of finite-dimensional simple weighted modules with
nilpotent dots, supporting Webster arXiv:1209.2463v4, Theorem 2.19, roadmap A.
Finite dimension and dot nilpotence are intermediate hypotheses; the graph is
loop-free, with arbitrary standing polynomials over any field. -/
theorem exists_eq_smul_of_isSimpleModule
    (hD : Γ.Dagger) (hS : Γ.Standing)
    (hne : ∀ e, Γ.head e ≠ Γ.tail e) (hl : ∀ i, Γ.loop i = none)
    [IsSimpleModule (WeightedKLRAlgebra k Γ ν) M] [FiniteDimensional k M]
    (hnil : ∀ s : Strand ν, KLR.SmulNilpotent (reducedDot k Γ ν s) M)
    (φ : M →ₗ[WeightedKLRAlgebra k Γ ν] M) : ∃ c : k, ∀ m, φ m = c • m := by
  classical
  have : Nontrivial M := IsSimpleModule.nontrivial (WeightedKLRAlgebra k Γ ν) M
  have hZ : Γ.NoZeroLoops := fun e he => (hne e he).elim
  obtain ⟨p, C, hCs, hC, hpC, hmin⟩ := exists_chamberSupport_minimum (k := k) (Γ := Γ) (ν := ν) (M := M)
  have hp : ∀ d : Diag ν, 0 ≤ d.val p := hpC.diag_nonneg hC
  let Φ := Local.weightedHom p hp hD hZ hS
  have hunit : ∃ m : M, m ≠ 0 ∧ Φ 1 • m = m := by
    obtain ⟨m, hm⟩ := (mem_chamberSupport_rank_iff hC).1 hCs
    refine ⟨rankE k hC • m, hm, ?_⟩
    change Local.weightedHom p hp hD hZ hS 1 • (rankE k hC • m) = _
    rw [Local.weightedHom_one, ← mul_smul, Local.starIdemW_mul_rankE p hC hpC]
  apply Local.exists_eq_smul_of_zeroWeight_chart
    (Local.standing p hS) (Local.dagger p hD)
    (fun e he => hne e.1 (congrArg Prod.fst he))
    (Local.loop_eq_none p hl) (Local.graph_weight p) Φ
    (Local.weightedHom_map_smul p hp hD hZ hS) hunit ?_ ?_ hnil φ
  · exact Local.exists_weightedHom_action_of_support_minimum p hp hD hZ hS hmin
  · intro t
    refine ⟨Local.strandEquiv p t, ?_⟩
    exact (Local.weightedHom_reducedDot p hp hD hZ hS t).trans
      (congrArg (fun x => reducedDot k Γ ν (Local.strandEquiv p t) * x)
        (Local.weightedHom_one p hp hD hZ hS).symm)

namespace GradingDatum

/-- Graded simple weighted KLR modules have scalar endomorphisms over any field,
for loop-free graphs under Webster's standing hypothesis. This supplies the
absolute-irreducibility input of arXiv:1209.2463v4, Theorem 2.19, roadmap A,
corresponding to KL I arXiv:0803.4121v2, Corollary 3.19. No restriction on colour
multiplicities, cycles, or standing polynomials is imposed. -/
theorem exists_eq_smul_of_isGradedSimple
    (hD : Γ.Dagger) (hS : Γ.Standing)
    (hne : ∀ e, Γ.head e ≠ Γ.tail e) (hl : ∀ i, Γ.loop i = none)
    {ℳ : ℤ → Submodule k M} [Decomposition ℳ]
    [SetLike.GradedSMul (hS.gradingDatum.klrGrade ν) ℳ]
    (hM : IsGradedSimple (hS.gradingDatum.klrGrade ν) ℳ)
    (φ : M →ₗ[WeightedKLRAlgebra k Γ ν] M) : ∃ c : k, ∀ m, φ m = c • m := by
  have hZ : Γ.NoZeroLoops := fun e he => (hne e he).elim
  have := finiteDimensional_of_isGradedSimple hD hZ hS hM
  have := hM.isSimpleModule
  exact WeightedKLR.exists_eq_smul_of_isSimpleModule hD hS hne hl
    (smulNilpotent_reducedDot_of_isGradedSimple hD hZ hS hM) φ

end GradingDatum
end Categorification.WeightedKLR
