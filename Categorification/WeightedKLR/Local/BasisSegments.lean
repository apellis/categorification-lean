/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Local.SupportSegments
import Categorification.WeightedKLR.Mackey.ShufflePattern

/-!
# A segment family adapted to the minimum configuration

Supporting basis choices for the local-chart proof of B. Webster,
*Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.4,
Theorem 2.19, roadmap A, using the segment basis of Theorem 2.8. For a fixed pair
of incident chambers, the target being rank ordered makes the relabelled target
chambers distinct. One can therefore choose a single segment family whose basis
galleries for all permutations moving the minimum configuration pass through
unsupported chambers. This is supporting algebraic geometry, not a printed source statement.
-/

namespace Categorification.WeightedKLR

open Categorification.WeightedKLR.Geometry

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}
  {ν : I →₀ ℕ}

omit [DecidableEq I] in
/-- The inverse translates of a rank-ordered chamber have distinct permutation labels. -/
theorem FullChamber.inverse_smul_injective_of_isRankOrdered {D : FullChamber Γ ν}
    (hD : D.IsRankOrdered) : Function.Injective (fun g : ColPerm ν => g⁻¹ • D) := by
  intro g h he
  change g⁻¹ • D = h⁻¹ • D at he
  have hfix : (h * g⁻¹) • D = D := by
    rw [mul_smul, he, smul_inv_smul]
  have hrank : ((h * g⁻¹) • D).IsRankOrdered := by rwa [hfix]
  have hone := FullChamber.eq_one_of_isRankOrdered_smul hD hrank
  exact (mul_inv_eq_one.1 hone).symm

/-- Choose all chamber segments at once so that every moving permutation in the fixed
corner has a gallery with an unsupported prefix. The rank order of the target ensures
that the separately chosen adapted segments impose consistent requirements. -/
theorem exists_adapted_chamberSegments_of_rankOrdered
    (S : Set (FullChamber Γ ν)) {p : Strand ν → 𝕜}
    (hmin : ∀ E ∈ S, ∀ x : Strand ν → 𝕜, E.Incident x → squaredNorm p ≤ squaredNorm x)
    (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) {C D : FullChamber Γ ν}
    (hp : C.Incident p) (hq : D.Incident p) (hRank : D.IsRankOrdered) :
    ∃ P : FullChamber Γ ν → FullChamber Γ ν →
        (Strand ν → 𝕜) × (Strand ν → 𝕜),
      (∀ A E, GalleryAlgebra.IsChamberSegment A E (P A E)) ∧
      ∀ g : ColPerm ν, act g p ≠ p →
        ∃ j : ℕ, C.flips ((Segment.word (hypAff (Γ := Γ))
          (P C (g⁻¹ • D)).1 (P C (g⁻¹ • D)).2).take j) ∉ S := by
  classical
  have hadapt : ∀ g : ColPerm ν, ∃ pq : (Strand ν → 𝕜) × (Strand ν → 𝕜),
      GalleryAlgebra.IsChamberSegment C (g⁻¹ • D) pq ∧
      (act g p ≠ p → ∃ j : ℕ, C.flips
        ((Segment.word (hypAff (Γ := Γ)) pq.1 pq.2).take j) ∉ S) := by
    intro g
    by_cases hg : act g p = p
    · obtain ⟨pq, hpq⟩ := GalleryAlgebra.exists_isChamberSegment hD hZ C (g⁻¹ • D)
      exact ⟨pq, hpq, fun hn => (hn hg).elim⟩
    · obtain ⟨pq, hpq, hprefix⟩ :=
        exists_chamberSegment_unsupported_prefix_of_not_fix S hmin hD hZ hp hq g hg
      exact ⟨pq, hpq, fun _ => hprefix⟩
  choose q hqseg hqprefix using hadapt
  have hinj := FullChamber.inverse_smul_injective_of_isRankOrdered hRank
  have hrow : ∀ E : FullChamber Γ ν, ∃ pq : (Strand ν → 𝕜) × (Strand ν → 𝕜),
      GalleryAlgebra.IsChamberSegment C E pq ∧
      ∀ g : ColPerm ν, g⁻¹ • D = E → act g p ≠ p →
        ∃ j : ℕ, C.flips ((Segment.word (hypAff (Γ := Γ)) pq.1 pq.2).take j) ∉ S := by
    intro E
    by_cases he : ∃ g : ColPerm ν, g⁻¹ • D = E
    · obtain ⟨g, hg⟩ := he
      refine ⟨q g, ?_, ?_⟩
      · simpa only [← hg] using hqseg g
      · intro h hh hmove
        have heq : h = g := hinj (hh.trans hg.symm)
        subst h
        exact hqprefix g hmove
    · obtain ⟨pq, hpq⟩ := GalleryAlgebra.exists_isChamberSegment hD hZ C E
      exact ⟨pq, hpq, fun g hg _ => (he ⟨g, hg⟩).elim⟩
  choose row hrowseg hrowprefix using hrow
  choose base hbase using GalleryAlgebra.exists_isChamberSegment hD hZ
  let P : FullChamber Γ ν → FullChamber Γ ν →
      (Strand ν → 𝕜) × (Strand ν → 𝕜) := fun A E =>
    if A = C then row E else base A E
  refine ⟨P, ?_, ?_⟩
  · intro A E
    dsimp only [P]
    split_ifs with hAC
    · subst A
      exact hrowseg E
    · exact hbase A E
  · intro g hg
    simpa only [P, ite_true] using hrowprefix (g⁻¹ • D) g rfl hg

end Categorification.WeightedKLR
