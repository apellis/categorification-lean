/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Local.Support
import Categorification.WeightedKLR.Local.BasisSegments

/-!
# The action of a supporting chamber corner

For the local-chart argument toward Webster arXiv:1209.2463v4, Theorem 2.19,
roadmap A, the basis theorem reduces a chamber-corner action to permutations
fixing a minimum support point. The other terms have an unsupported gallery
prefix and annihilate the module. This file isolates that reduction from the
construction of the local algebra map; its stabilizer-image assumption is an
explicit intermediate hypothesis.
-/

noncomputable section

namespace Categorification.WeightedKLR.GalleryAlgebra

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [Field k] {Γ : WeightedGraph I 𝕜 k}
  {ν : I →₀ ℕ} {M : Type*} [AddCommGroup M]
  [Module (WeightedKLRAlgebra k Γ ν) M]
  {R : Type*} [AddCommGroup R] [Module k R]

/-- If the stabilizing gallery terms lie in a given linear image, that image
already supplies the entire action of each incident chamber corner. -/
theorem exists_corner_action_of_stabilizer_terms
    (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hS : Γ.Standing)
    {p : Strand ν → 𝕜}
    (hmin : ∀ E : FullChamber Γ ν, E ∈ chamberSupport M → ∀ x, E.Incident x →
      Geometry.squaredNorm p ≤ Geometry.squaredNorm x)
    {C D : FullChamber Γ ν} (hp : C.Incident p) (hq : D.Incident p)
    (hRank : D.IsRankOrdered) (F : R →ₗ[k] WeightedKLRAlgebra k Γ ν)
    (hlocal : ∀ P : FullChamber Γ ν → FullChamber Γ ν →
        (Strand ν → 𝕜) × (Strand ν → 𝕜),
      (∀ A E, IsChamberSegment A E (P A E)) → ∀ g : ColPerm ν, act g p = p →
      ∀ f : PolyRing ν k, ∃ r : R,
        F r = colourSymCornerProjection (cornerElt P D C g * poly f))
    (a : cornerSpace k D C) :
    ∃ r : R, ∀ m : M, F r • m = colourSymCornerProjection a.1 • m := by
  classical
  let := ColPerm.fintype (ν := ν)
  obtain ⟨P, hP, hbad⟩ := exists_adapted_chamberSegments_of_rankOrdered
    (chamberSupport M) hmin hD hZ hp hq hRank
  let B := cornerPolyEquivOfStanding hP hD hZ hS D C
  obtain ⟨f, rfl⟩ := B.surjective a
  have hterms : ∀ g : ColPerm ν, ∃ r : R, ∀ m : M,
      F r • m = colourSymCornerProjection (cornerElt P D C g * poly (f g)) • m := by
    intro g
    by_cases hg : act g p = p
    · obtain ⟨r, hr⟩ := hlocal P hP g hg (f g)
      exact ⟨r, fun m => by rw [hr]⟩
    · obtain ⟨j, hj⟩ := hbad g hg
      refine ⟨0, fun m => ?_⟩
      rw [map_zero, zero_smul]
      symm
      apply smul_eq_zero_of_galList_prefix_unsupported C
        (Segment.word (hypAff (Γ := Γ)) (P C (g⁻¹ • D)).1 (P C (g⁻¹ • D)).2) j hj
        (colourSymCornerProjection (cornerElt P D C g * poly (f g)))
        (rankIdem k Γ ν * r g (g⁻¹ • D)) (poly (f g) * rankIdem k Γ ν) ?_ m
      change rankIdem k Γ ν * (cornerElt P D C g * poly (f g)) * rankIdem k Γ ν = _
      simp only [cornerElt, segGallery, mul_assoc]
  choose r hr using hterms
  refine ⟨∑ g, r g, fun m => ?_⟩
  have ha : (B f).1 = ∑ g, cornerElt P D C g * poly (f g) :=
    cornerPolyEquivOfStanding_apply hP hD hZ hS D C f
  rw [ha, map_sum, map_sum, Finset.sum_smul, Finset.sum_smul]
  exact Finset.sum_congr rfl (fun g _ => hr g m)

end Categorification.WeightedKLR.GalleryAlgebra
