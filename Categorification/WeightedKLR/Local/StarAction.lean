/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Local.CornerAction

/-!
# Assembling the action of a chamber star

Supporting finite-sum algebra for the local-chart proof of B. Webster,
*Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.4,
Theorem 2.19, roadmap A. Lifts of the actions of individual incident chamber
corners add to a lift of the whole star-corner action. The stabilizer-term image
condition is an explicit intermediate assumption; constructing those local
images is a separate step. These are supporting lemmas, not printed source statements.
-/

namespace Categorification.WeightedKLR.Local

section FiniteSandwich

variable {k A R M ι : Type*} [CommRing k] [Ring A] [Algebra k A]
  [AddCommGroup R] [Module k R] [AddCommGroup M] [Module A M] [Fintype ι]

/-- Lifts of every matrix block action add to a lift of the finite sum corner action. -/
theorem exists_finite_sandwich_action (e : ι → A) (F : R →ₗ[k] A)
    (hlift : ∀ i j : ι, ∀ a : A, ∃ r : R,
      ∀ m : M, F r • m = (e i * a * e j) • m) (a : A) :
    ∃ r : R, ∀ m : M, F r • m = ((∑ i, e i) * a * (∑ i, e i)) • m := by
  classical
  choose r hr using (fun i j => hlift i j a)
  refine ⟨∑ i, ∑ j, r i j, fun m => ?_⟩
  have he : (∑ i, e i) * a * (∑ i, e i) = ∑ i, ∑ j, e i * a * e j := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [he, map_sum, Finset.sum_smul]
  simp only [map_sum, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_congr rfl (fun j _ => hr i j m)

end FiniteSandwich

end Categorification.WeightedKLR.Local

namespace Categorification.WeightedKLR.GalleryAlgebra

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [Field k] {Γ : WeightedGraph I 𝕜 k}
  {ν : I →₀ ℕ} {M : Type*} [AddCommGroup M] [Module k M]
  [Module (WeightedKLRAlgebra k Γ ν) M] [IsScalarTower k (WeightedKLRAlgebra k Γ ν) M]
  {R : Type*} [AddCommGroup R] [Module k R]

omit [Module k M] [IsScalarTower k (WeightedKLRAlgebra k Γ ν) M] in
/-- Pairwise chamber-corner action lifts assemble to a lift of the finite chamber-star action. -/
theorem exists_rankStar_action_of_corner_actions
    (T : Finset (RankChamber Γ ν)) (F : R →ₗ[k] WeightedKLRAlgebra k Γ ν)
    (hlift : ∀ C ∈ T, ∀ D ∈ T, ∀ a : WeightedKLRAlgebra k Γ ν, ∃ r : R,
      ∀ m : M, F r • m = (rankE k D.2 * a * rankE k C.2) • m)
    (a : WeightedKLRAlgebra k Γ ν) :
    ∃ r : R, ∀ m : M,
      F r • m = ((∑ C ∈ T, rankE k C.2) * a * (∑ C ∈ T, rankE k C.2)) • m := by
  classical
  have h := Local.exists_finite_sandwich_action (M := M)
    (fun C : T => rankE k C.1.2) F
    (fun D C a => hlift C.1 C.2 D.1 D.2 a) a
  have he : (∑ C : T, rankE k C.1.2) = ∑ C ∈ T, rankE k C.2 :=
    Finset.sum_coe_sort T (fun C => rankE k C.2)
  simpa only [he] using h

omit [Module k M] [IsScalarTower k (WeightedKLRAlgebra k Γ ν) M] in
/-- Stabilizer-term images in each pair of incident chambers suffice to lift the
entire finite star-corner action. This retains the explicit local-image intermediate
hypothesis from `exists_corner_action_of_stabilizer_terms`. -/
theorem exists_rankStar_action_of_stabilizer_terms
    (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hS : Γ.Standing)
    {p : Strand ν → 𝕜}
    (hmin : ∀ E : FullChamber Γ ν, E ∈ chamberSupport M → ∀ x, E.Incident x →
      Geometry.squaredNorm p ≤ Geometry.squaredNorm x)
    (T : Finset (RankChamber Γ ν)) (hincident : ∀ C ∈ T, C.1.Incident p)
    (F : R →ₗ[k] WeightedKLRAlgebra k Γ ν)
    (hlocal : ∀ C ∈ T, ∀ D ∈ T,
      ∀ P : FullChamber Γ ν → FullChamber Γ ν → (Strand ν → 𝕜) × (Strand ν → 𝕜),
      (∀ A E, IsChamberSegment A E (P A E)) → ∀ g : ColPerm ν, act g p = p →
      ∀ f : PolyRing ν k, ∃ r : R,
        F r = colourSymCornerProjection (cornerElt P D.1 C.1 g * poly f))
    (a : WeightedKLRAlgebra k Γ ν) :
    ∃ r : R, ∀ m : M,
      F r • m = ((∑ C ∈ T, rankE k C.2) * a * (∑ C ∈ T, rankE k C.2)) • m := by
  apply exists_rankStar_action_of_corner_actions T F ?_ a
  intro C hC D hDt b
  let x : cornerSpace k D.1 C.1 :=
    ⟨e D.1 * b.1 * e C.1, ⟨b.1, by simp only [sandwich_apply]⟩⟩
  obtain ⟨r, hr⟩ := exists_corner_action_of_stabilizer_terms hD hZ hS hmin
    (hincident C hC) (hincident D hDt) D.2 F (hlocal C hC D hDt) x
  refine ⟨r, fun m => ?_⟩
  have he : colourSymCornerProjection x.1 = rankE k D.2 * b * rankE k C.2 :=
    colourSymCornerProjection_coe (rankE k D.2 * b * rankE k C.2)
  rw [← he]
  exact hr m

end Categorification.WeightedKLR.GalleryAlgebra
