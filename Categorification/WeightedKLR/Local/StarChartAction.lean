/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Local.StarAction
import Categorification.WeightedKLR.Local.WeightedChart
import Categorification.WeightedKLR.Local.WeightedBasisImage
import Categorification.Algebra.InductionAlongRes

/-!
# The local chart supplies the action of a minimum support star

Supporting the local-chart proof of B. Webster,
*Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.4,
Theorem 2.19, roadmap A. This file assembles the chamber-corner action into the
local weighted chart action on the subspace fixed by the chart unit. A supported
incident chamber also supplies a nonzero fixed vector. These are supporting
lemmas for the local-chart argument rather than statements printed in the source.
-/

noncomputable section

namespace Categorification.WeightedKLR.Local

open GalleryAlgebra InductionAlong

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [Field k] {Γ : WeightedGraph I 𝕜 k}
  {ν : I →₀ ℕ} {M : Type*} [AddCommGroup M]
  [Module (WeightedKLRAlgebra k Γ ν) M]

/-- Incident rank-ordered chambers, viewed as a subtype of rank-ordered chambers. -/
def rankIncidentEquivRankChamber (p : Strand ν → 𝕜) :
    RankIncident (Γ := Γ) p ≃ {C : RankChamber Γ ν // C.1.Incident p} where
  toFun C := ⟨⟨C.1, C.2.1⟩, C.2.2⟩
  invFun C := ⟨C.1.1, C.1.2, C.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The finite set of incident rank-ordered chambers. -/
def incidentRankChambers (p : Strand ν → 𝕜) : Finset (RankChamber Γ ν) := by
  classical
  exact Finset.univ.filter fun C => C.1.Incident p

/-- The incident-chamber finite sum is the unit image of the weighted chart. -/
theorem sum_incident_rankE_eq_starIdemW (p : Strand ν → 𝕜) :
    (∑ C ∈ incidentRankChambers (Γ := Γ) p, rankE k C.2) =
      starIdemW (Γ := Γ) (k := k) p := by
  classical
  calc
    _ = ∑ C : {C : RankChamber Γ ν // C.1.Incident p}, rankE k C.1.2 :=
      Finset.sum_subtype _ (by simp [incidentRankChambers]) _
    _ = ∑ C : RankIncident (Γ := Γ) p, rankE k C.2.1 :=
      ((rankIncidentEquivRankChamber p).sum_comp (fun C => rankE k C.1.2)).symm
    _ = _ := rfl

/-- A supported rank-ordered incident chamber gives a nonzero vector fixed by the
unit image of the local weighted chart. -/
theorem exists_nonzero_weightedHom_unit_fixed
    (p : Strand ν → 𝕜) (hp : ∀ d : Diag ν, 0 ≤ d.val p)
    (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hS : Γ.Standing)
    {C : FullChamber Γ ν} (hRank : C.IsRankOrdered) (hincident : C.Incident p)
    (hC : C ∈ chamberSupport M) :
    ∃ m : M, m ≠ 0 ∧ weightedHom p hp hD hZ hS 1 • m = m := by
  obtain ⟨m, hm⟩ := (mem_chamberSupport_rank_iff hRank).1 hC
  refine ⟨rankE k hRank • m, hm, ?_⟩
  rw [weightedHom_one, ← mul_smul, starIdemW_mul_rankE p hRank hincident]

/-- At a minimum support configuration, the local weighted chart supplies the entire
original corner action on the subspace fixed by its unit image. This is the concrete
corner-action input for the scalar-endomorphism criterion of the local-chart proof. -/
theorem exists_weightedHom_action_of_support_minimum
    (p : Strand ν → 𝕜) (hp : ∀ d : Diag ν, 0 ≤ d.val p)
    (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hS : Γ.Standing)
    (hmin : ∀ E : FullChamber Γ ν, E ∈ chamberSupport M → ∀ x, E.Incident x →
      Geometry.squaredNorm p ≤ Geometry.squaredNorm x)
    (a : WeightedKLRAlgebra k Γ ν) :
    ∃ r : WeightedKLRAlgebra k (graph Γ p) (weight p),
      ∀ m : Res (weightedHom p hp hD hZ hS) M,
        weightedHom p hp hD hZ hS r • m.val =
          weightedHom p hp hD hZ hS 1 • (a • m.val) := by
  classical
  let T := incidentRankChambers (Γ := Γ) p
  have hincident : ∀ C ∈ T, C.1.Incident p := by
    intro C hC
    exact (Finset.mem_filter.1 hC).2
  obtain ⟨r, hr⟩ := exists_rankStar_action_of_stabilizer_terms hD hZ hS hmin T hincident
    (weightedLinearMap p hp hD hZ hS) (fun C hC D hDt P hP g hg f =>
      exists_weighted_cornerElt_mul_poly_preimage p hp hD hZ hS hP C.2 D.2
        (hincident C hC) (hincident D hDt) g hg f) a
  refine ⟨r, fun m => ?_⟩
  have haction := hr m.val
  change weightedHom p hp hD hZ hS r • m.val = _ at haction
  rw [sum_incident_rankE_eq_starIdemW] at haction
  rw [haction, mul_smul, mul_smul, ← weightedHom_one p hp hD hZ hS, m.prop]

end Categorification.WeightedKLR.Local
