/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.ZeroWeightSimple

/-!
# Scalar endomorphisms detected by a zero-weight local chart

The algebraic assembly step of the local-chart proof for Webster,
*Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.4,
Theorem 2.19, roadmap A. A nonzero chart restriction is simple when its image
acts as the entire supporting corner. Preservation of dots transfers
nilpotence to this restriction. The zero-weight case of the scalar theorem,
deduced from KL I arXiv:0803.4121v2, §3.2, Corollary 3.19, then detects scalar
endomorphisms of the original module.

The chart, corner-action, and dot-image properties are explicit hypotheses of
this supporting criterion; this file does not assert their construction.
-/

noncomputable section

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

namespace Categorification.WeightedKLR.Local

open GalleryAlgebra InductionAlong

universe u v

variable {I : Type u} {J : Type v} [DecidableEq I] [DecidableEq J]
  {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  {k : Type*} [Field k] {Γ : WeightedGraph I 𝕜 k} {Λ : WeightedGraph J 𝕜 k}
  {ν : I →₀ ℕ} {μ : J →₀ ℕ}
  {M : Type*} [AddCommGroup M] [Module k M]
  [Module (WeightedKLRAlgebra k Γ ν) M] [IsScalarTower k (WeightedKLRAlgebra k Γ ν) M]
  [IsSimpleModule (WeightedKLRAlgebra k Γ ν) M] [FiniteDimensional k M]

/-- A zero-weight chart with full supporting-corner action and compatible dots
detects scalar endomorphisms. This is an explicit conditional assembly
criterion for the local-chart proof of Webster arXiv:1209.2463v4,
Theorem 2.19, roadmap A, using KL I arXiv:0803.4121v2, Corollary 3.19
on the local zero-weight algebra. -/
theorem exists_eq_smul_of_zeroWeight_chart
    (hS : Λ.Standing) (hD : Λ.Dagger) (hE : ∀ e, Λ.head e ≠ Λ.tail e)
    (hl : ∀ i, Λ.loop i = none) (h0 : ∀ e, Λ.weight e = 0)
    (φ : WeightedKLRAlgebra k Λ μ →ₙ+* WeightedKLRAlgebra k Γ ν)
    (hφsmul : ∀ (c : k) (a : WeightedKLRAlgebra k Λ μ), φ (c • a) = c • φ a)
    (hunit : ∃ m : M, m ≠ 0 ∧ φ 1 • m = m)
    (hcorner : ∀ a : WeightedKLRAlgebra k Γ ν,
      ∃ r : WeightedKLRAlgebra k Λ μ, ∀ m : Res φ M,
        φ r • m.val = φ 1 • (a • m.val))
    (hdot : ∀ t : Strand μ, ∃ s : Strand ν,
      φ (reducedDot k Λ μ t) = reducedDot k Γ ν s * φ 1)
    (hnil : ∀ s : Strand ν, KLR.SmulNilpotent (reducedDot k Γ ν s) M)
    (ψ : M →ₗ[WeightedKLRAlgebra k Γ ν] M) : ∃ c : k, ∀ m, ψ m = c • m := by
  let N := Res φ M
  have : IsSimpleModule (WeightedKLRAlgebra k Λ μ) N :=
    Res.isSimpleModule_of_corner_action hunit hcorner
  let : Module k N := Module.compHom N (algebraMap k (WeightedKLRAlgebra k Λ μ))
  have : IsScalarTower k (WeightedKLRAlgebra k Λ μ) N := IsScalarTower.of_compHom _ _ _
  have hval_smul : ∀ (c : k) (m : N), (c • m).val = c • m.val := by
    intro c m
    change φ (algebraMap k (WeightedKLRAlgebra k Λ μ) c) • m.val = c • m.val
    rw [Algebra.algebraMap_eq_smul_one, hφsmul, smul_assoc, m.prop]
  let L : N →ₗ[k] M :=
    { toFun := Res.val
      map_add' := Res.val_add
      map_smul' := hval_smul }
  have : FiniteDimensional k N := FiniteDimensional.of_injective L (fun _ _ h => Res.ext h)
  have hnilN : ∀ t : Strand μ, KLR.SmulNilpotent (reducedDot k Λ μ t) N := by
    intro t
    obtain ⟨s, hs⟩ := hdot t
    obtain ⟨n, hn⟩ := hnil s
    have hact : ∀ m : N, (reducedDot k Λ μ t • m).val = reducedDot k Γ ν s • m.val := by
      intro m
      change φ (reducedDot k Λ μ t) • m.val = _
      rw [hs, mul_smul, m.prop]
    have hpow : ∀ (j : ℕ) (m : N), ((reducedDot k Λ μ t) ^ j • m).val =
        (reducedDot k Γ ν s) ^ j • m.val := by
      intro j
      induction j with
      | zero => intro m; simp
      | succ j ih =>
        intro m
        rw [pow_succ', mul_smul, hact, ih, ← mul_smul, ← pow_succ']
    refine ⟨n, fun m => Res.ext ?_⟩
    rw [hpow, hn]
    rfl
  apply Res.exists_eq_smul_of_scalar_endomorphisms hunit ?_ ψ
  intro f
  obtain ⟨c, hc⟩ := exists_eq_smul_of_isSimpleModule_zeroWeight_finsupp
    hS hD hE hl h0 hnilN f
  refine ⟨c, fun m => ?_⟩
  rw [hc, hval_smul]

end Categorification.WeightedKLR.Local
