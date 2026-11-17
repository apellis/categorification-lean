/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Local.StarRelabel
import Categorification.WeightedKLR.Local.AdaptedSegment
import Categorification.WeightedKLR.GallerySpan.Spanning

/-!
# Segments leaving a minimum-norm chamber support

Supporting geometry for the local-chart proof of B. Webster,
*Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.4,
Theorem 2.19, roadmap A. A strand permutation moving a minimum-norm configuration
admits an adapted simple segment whose gallery passes through an unsupported chamber.
This is a supporting lemma for the local-chart argument, not a printed source statement.
The argument uses strict convexity and finite perturbation over any ordered field.
-/

namespace Categorification.WeightedKLR

open Categorification.WeightedKLR.Geometry

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}
  {ν : I →₀ ℕ}

omit [DecidableEq I] in
/-- The midpoint between a minimum-norm configuration and a distinct relabelling lies
outside every closed chamber in the support. -/
theorem support_minimum_midpoint_not_incident
    (S : Set (FullChamber Γ ν)) {p : Strand ν → 𝕜}
    (hmin : ∀ E ∈ S, ∀ x : Strand ν → 𝕜, E.Incident x → squaredNorm p ≤ squaredNorm x)
    (g : ColPerm ν) (hmove : act g p ≠ p) :
    ∀ E ∈ S, ¬E.Incident (Segment.segPt p (act g⁻¹ p) (1 / 2 : 𝕜)) := by
  have hne : p ≠ act g⁻¹ p := by
    intro he
    have he' := congrArg (act g) he
    rw [← act_mul, mul_inv_cancel, act_one] at he'
    exact hmove he'
  have hlt := squaredNorm_midpoint_lt hne (squaredNorm_act g⁻¹ p).symm
  intro E hE hi
  exact (not_lt_of_ge (hmin E hE _ hi)) hlt

/-- A moving relabelling of a minimum-norm configuration has a simple chamber segment
with generic midpoint outside every supported closed chamber. -/
theorem exists_chamberSegment_midpoint_outside_of_not_fix
    (S : Set (FullChamber Γ ν)) {p : Strand ν → 𝕜}
    (hmin : ∀ E ∈ S, ∀ x : Strand ν → 𝕜, E.Incident x → squaredNorm p ≤ squaredNorm x)
    (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) {C D : FullChamber Γ ν}
    (hp : C.Incident p) (hq : D.Incident p) (g : ColPerm ν) (hmove : act g p ≠ p) :
    ∃ pq : (Strand ν → 𝕜) × (Strand ν → 𝕜),
      GalleryAlgebra.IsChamberSegment C (g⁻¹ • D) pq ∧
      IsGeneric Γ (Segment.segPt pq.1 pq.2 (1 / 2 : 𝕜)) ∧
      ∀ E ∈ S, ¬E.Incident (Segment.segPt pq.1 pq.2 (1 / 2 : 𝕜)) := by
  obtain ⟨x, y, hs, hx, hy, hgen, hout⟩ := exists_simple_incident_midpoint_outside
    hD hZ hp (hq.smul g⁻¹) S (support_minimum_midpoint_not_incident S hmin g hmove)
  exact ⟨(x, y), ⟨hs, hx, hy⟩, hgen, hout⟩

/-- A generic point outside all supported closed chambers gives an unsupported prefix
chamber of a simple segment. -/
theorem exists_unsupported_prefix_of_generic_midpoint
    (S : Set (FullChamber Γ ν)) {C D : FullChamber Γ ν}
    {pq : (Strand ν → 𝕜) × (Strand ν → 𝕜)}
    (hpq : GalleryAlgebra.IsChamberSegment C D pq)
    (hgen : IsGeneric Γ (Segment.segPt pq.1 pq.2 (1 / 2 : 𝕜)))
    (hout : ∀ E ∈ S, ¬E.Incident (Segment.segPt pq.1 pq.2 (1 / 2 : 𝕜))) :
    ∃ j : ℕ, C.flips ((Segment.word (hypAff (Γ := Γ)) pq.1 pq.2).take j) ∉ S := by
  obtain ⟨j, hj⟩ := Segment.exists_prefix_of_generic_segPt hpq.1
    (t := (1 / 2 : 𝕜)) (by positivity) (by norm_num) hgen
  have hw := (GalleryAlgebra.goodWord_flips_word hpq.1 hpq.2.1).1
  have htake : GoodWord C.1 ((Segment.word (hypAff (Γ := Γ)) pq.1 pq.2).take j) := by
    apply GoodWord.of_append (b := (Segment.word (hypAff (Γ := Γ)) pq.1 pq.2).drop j)
    simpa only [List.take_append_drop] using hw
  refine ⟨j, fun hS => ?_⟩
  apply hout _ hS
  apply FullChamber.incident_of_signs
  rw [FullChamber.flips_val htake]
  change fullSigns (Segment.segPt pq.1 pq.2 (1 / 2 : 𝕜)) = _ at hj
  simpa only [signs_hypAff, hpq.2.1] using hj

/-- A strand permutation moving the minimum configuration admits a simple segment from
`C` to the inverse-relabelled `D` whose crossing gallery has an unsupported prefix. -/
theorem exists_chamberSegment_unsupported_prefix_of_not_fix
    (S : Set (FullChamber Γ ν)) {p : Strand ν → 𝕜}
    (hmin : ∀ E ∈ S, ∀ x : Strand ν → 𝕜, E.Incident x → squaredNorm p ≤ squaredNorm x)
    (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) {C D : FullChamber Γ ν}
    (hp : C.Incident p) (hq : D.Incident p) (g : ColPerm ν) (hmove : act g p ≠ p) :
    ∃ pq : (Strand ν → 𝕜) × (Strand ν → 𝕜),
      GalleryAlgebra.IsChamberSegment C (g⁻¹ • D) pq ∧
      ∃ j : ℕ, C.flips ((Segment.word (hypAff (Γ := Γ)) pq.1 pq.2).take j) ∉ S := by
  obtain ⟨pq, hpq, hgen, hout⟩ :=
    exists_chamberSegment_midpoint_outside_of_not_fix S hmin hD hZ hp hq g hmove
  exact ⟨pq, hpq, exists_unsupported_prefix_of_generic_midpoint S hpq hgen hout⟩

end Categorification.WeightedKLR
