/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Local.Chambers
import Categorification.WeightedKLR.Gallery

/-!
# Galleries in the chamber star

Supporting geometry for the local-chart proof of the absolute-irreducibility
input of Webster, *Weighted Khovanov–Lauda–Rouquier algebras*,
arXiv:1209.2463v4, §2.4, Theorem 2.19 (roadmap A). Galleries crossing only
hyperplanes through the base point stay in the chamber star and lift to the
refined zero-weight graph. This is the geometric basis-range input; no scalar
endomorphism conclusion is asserted in this module.
-/

noncomputable section

namespace Categorification.WeightedKLR

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k]
  {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

namespace FullChamber

omit [IsStrictOrderedRing 𝕜] in
/-- An invalid crossing leaves the chamber unchanged. -/
theorem flipH_of_not {C : FullChamber Γ ν} {h : Hyp Γ ν}
    (hr : ¬∃ q, IsGeneric Γ q ∧ fullSigns q = flipSign C.1 h) : C.flipH h = C :=
  dite_eq_right_of_eq_false (eq_false hr)

omit [IsStrictOrderedRing 𝕜] in
/-- Crossing a hyperplane through the base point preserves chamber incidence,
including the convention that an invalid flip stays in the original chamber. -/
theorem Incident.flipH {C : FullChamber Γ ν} {p : Strand ν → 𝕜}
    (hC : C.Incident p) {h : Hyp Γ ν} (hh : h.val p = 0) :
    (C.flipH h).Incident p := by
  classical
  by_cases hr : ∃ q, IsGeneric Γ q ∧ fullSigns q = flipSign C.1 h
  · rw [flipH_of hr]
    intro a
    change (if FullChamber.flipSign C.1 h a then 0 ≤ a.val p else a.val p ≤ 0)
    by_cases ha : a = h
    · subst a
      rw [hh]
      split_ifs <;> exact le_rfl
    · simpa [FullChamber.flipSign, ha] using hC a
  · rw [flipH_of_not hr]
    exact hC

omit [IsStrictOrderedRing 𝕜] in
/-- A word consisting of hyperplanes through the base point stays in the chamber star. -/
theorem Incident.flips {C : FullChamber Γ ν} {p : Strand ν → 𝕜}
    (hC : C.Incident p) {w : List (Hyp Γ ν)} (hw : ∀ h ∈ w, h.val p = 0) :
    (C.flips w).Incident p := by
  induction w generalizing C with
  | nil => exact hC
  | cons h w ih =>
    exact ih (hC.flipH (hw h List.mem_cons_self))
      (fun a ha => hw a (List.mem_cons_of_mem h ha))

end FullChamber

namespace Local

/-- Local flips and original flips of active hyperplanes agree. -/
theorem chamber_flipH (p : Strand ν → 𝕜)
    (C : FullChamber (graph Γ p) (weight p)) (h : Hyp (graph Γ p) (weight p)) :
    chamber p (C.flipH h) = (chamber p C).flipH (hyp p h) := by
  classical
  by_cases hloc : ∃ q, IsGeneric (graph Γ p) q ∧
      fullSigns q = FullChamber.flipSign C.1 h
  · have ha : C.Adjacent (C.flipH h) h := by
      apply FullChamber.adjacent_iff_eq_flipSign.2
      rw [FullChamber.flipH_of hloc]
    exact (FullChamber.flipH_eq_of_adjacent
      ((adjacent_chamber_iff p C (C.flipH h) h).2 ha)).symm
  · have horig : ¬∃ q, IsGeneric Γ q ∧
        fullSigns q = FullChamber.flipSign (chamber p C).1 (hyp p h) := by
      rintro ⟨q, hq, hs⟩
      let D := FullChamber.ofPoint q hq
      have ha : (chamber p C).Adjacent D (hyp p h) :=
        FullChamber.adjacent_iff_eq_flipSign.2 hs
      have hD : D.Incident p := by
        rw [← FullChamber.flipH_eq_of_adjacent ha]
        exact (chamber_incident p C).flipH (hyp_val_base p h)
      obtain ⟨D', hD'⟩ := (show D ∈ Set.range (chamber (Γ := Γ) p) by
        rw [range_chamber]
        exact hD)
      have hlocal : C.Adjacent D' h :=
        (adjacent_chamber_iff p C D' h).1 (hD'.symm ▸ ha)
      exact hloc ((FullChamber.adjacent_iff_eq_flipSign.1 hlocal) ▸ D'.2)
    rw [FullChamber.flipH_of_not hloc, FullChamber.flipH_of_not horig]

/-- The chamber-star map preserves all gallery endpoints. -/
theorem chamber_flips (p : Strand ν → 𝕜)
    (C : FullChamber (graph Γ p) (weight p)) (w : List (Hyp (graph Γ p) (weight p))) :
    chamber p (C.flips w) = (chamber p C).flips (w.map (hyp p)) := by
  induction w generalizing C with
  | nil => rfl
  | cons h w ih =>
    simpa only [FullChamber.flips_cons, List.map_cons, chamber_flipH] using ih (C.flipH h)

/-- Every original word consisting of active hyperplanes has a refined word. -/
theorem exists_word_lift (p : Strand ν → 𝕜) (w : List (Hyp Γ ν))
    (hw : ∀ h ∈ w, h.val p = 0) :
    ∃ v : List (Hyp (graph Γ p) (weight p)), v.map (hyp p) = w := by
  induction w with
  | nil => exact ⟨[], rfl⟩
  | cons h w ih =>
    have hh := hw h List.mem_cons_self
    obtain ⟨v, hv⟩ := ih (fun a ha => hw a (List.mem_cons_of_mem h ha))
    refine ⟨(hypEquiv p).symm ⟨h, hh⟩ :: v, ?_⟩
    rw [List.map_cons, hv]
    congr 1
    exact congrArg Subtype.val ((hypEquiv p).apply_symm_apply ⟨h, hh⟩)

/-- A gallery starting in the star and crossing only active hyperplanes lifts
with its entire endpoint to the local graph. -/
theorem exists_gallery_lift {p : Strand ν → 𝕜} {C : FullChamber Γ ν}
    (hC : C.Incident p) (w : List (Hyp Γ ν)) (hw : ∀ h ∈ w, h.val p = 0) :
    ∃ (D : FullChamber (graph Γ p) (weight p)) (v : List (Hyp (graph Γ p) (weight p))),
      chamber p D = C ∧ v.map (hyp p) = w ∧ chamber p (D.flips v) = C.flips w := by
  obtain ⟨D, hD⟩ := (show C ∈ Set.range (chamber (Γ := Γ) p) by
    rw [range_chamber]
    exact hC)
  obtain ⟨v, hv⟩ := exists_word_lift p w hw
  exact ⟨D, v, hD, hv, by rw [chamber_flips, hv, hD]⟩

omit [IsStrictOrderedRing 𝕜] in
/-- A segment between chambers incident to one point crosses only hyperplanes
through that point. Thus its gallery is in the range of the local chart. -/
theorem mem_word_active {p a b : Strand ν → 𝕜} {C D : FullChamber Γ ν}
    (hC : C.Incident p) (hD : D.Incident p) (ha : fullSigns a = C.1)
    (hb : fullSigns b = D.1) (h : Hyp Γ ν)
    (hh : h ∈ Segment.word (hypAff (Γ := Γ)) a b) : h.val p = 0 := by
  by_contra hne
  have hsign : fullSigns a h = fullSigns b h := by
    rw [ha, hb, hC.sign_eq h hne, hD.sign_eq h hne]
  have hs : (0 < (hypAff h) a) ↔ (0 < (hypAff h) b) :=
    decide_eq_decide.1 hsign
  exact (Segment.mem_word.1 hh) (propext hs)

end Local

end Categorification.WeightedKLR

namespace Categorification.WeightedKLR.Local

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k]
  {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

open GalleryAlgebra

/-- A chart preserving the idempotents and steps preserves gallery words.
The generator-image equalities are explicit inputs; the local-chart
construction supplies them in the application to Webster Theorem 2.19 (A). -/
theorem map_galList (p : Strand ν → 𝕜)
    (φ : GalleryAlgebra k (graph Γ p) (weight p) →ₙ+* GalleryAlgebra k Γ ν)
    (he : ∀ C, φ (e C) = e (chamber p C))
    (ht : ∀ C D, φ (t C D) = t (chamber p C) (chamber p D))
    (C : FullChamber (graph Γ p) (weight p)) (w : List (Hyp (graph Γ p) (weight p))) :
    φ (galList k C w) = galList k (chamber p C) (w.map (hyp p)) := by
  induction w generalizing C with
  | nil => exact he C
  | cons h w ih =>
    rw [galList_cons, map_mul, ih, ht, List.map_cons, galList_cons, chamber_flipH]

/-- The gallery of any original word of active hyperplanes is in the image
of a chart preserving the idempotents and steps. This is the basis-range
input for the local-chart route to Webster Theorem 2.19 (A). -/
theorem exists_galList_preimage {p : Strand ν → 𝕜}
    (φ : GalleryAlgebra k (graph Γ p) (weight p) →ₙ+* GalleryAlgebra k Γ ν)
    (he : ∀ C, φ (e C) = e (chamber p C))
    (ht : ∀ C D, φ (t C D) = t (chamber p C) (chamber p D))
    {C : FullChamber Γ ν} (hC : C.Incident p)
    (w : List (Hyp Γ ν)) (hw : ∀ h ∈ w, h.val p = 0) :
    ∃ z : GalleryAlgebra k (graph Γ p) (weight p), φ z = galList k C w := by
  obtain ⟨D, v, hD, hv, _⟩ := exists_gallery_lift hC w hw
  exact ⟨galList k D v, by rw [map_galList p φ he ht, hv, hD]⟩

end Categorification.WeightedKLR.Local

namespace Categorification.WeightedKLR.Local

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k]
  {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

open GalleryAlgebra

/-- Relabellings stabilizing the base point lift through a chart with the
specified relabelling images. This supports the local basis-range argument
for Webster arXiv:1209.2463v4, §2.4, Theorem 2.19 (A). -/
theorem exists_r_preimage {p : Strand ν → 𝕜}
    (φ : GalleryAlgebra k (graph Γ p) (weight p) →ₙ+* GalleryAlgebra k Γ ν)
    (hr : ∀ g C, φ (r g C) = r (perm p g) (chamber p C))
    {E : FullChamber Γ ν} (hE : E.Incident p) (g : ColPerm ν) (hg : act g p = p) :
    ∃ z : GalleryAlgebra k (graph Γ p) (weight p), φ z = r g E := by
  obtain ⟨h, hh⟩ := exists_perm_eq p g hg
  obtain ⟨D, hD⟩ := (show E ∈ Set.range (chamber (Γ := Γ) p) by
    rw [range_chamber]
    exact hE)
  exact ⟨r h D, by rw [hr, hh, hD]⟩

/-- A polynomial gallery term whose relabelling fixes the point and whose
hyperplanes are active lifts through the local chart. The generator-image
conditions are explicit intermediate inputs to the local route for Webster
arXiv:1209.2463v4, §2.4, Theorem 2.19 (A). -/
theorem exists_term_preimage {p : Strand ν → 𝕜}
    (φ : GalleryAlgebra k (graph Γ p) (weight p) →ₙ+* GalleryAlgebra k Γ ν)
    (he : ∀ C, φ (e C) = e (chamber p C))
    (ht : ∀ C D, φ (t C D) = t (chamber p C) (chamber p D))
    (hr : ∀ g C, φ (r g C) = r (perm p g) (chamber p C))
    (hpoly : ∀ (f : PolyRing ν k) (D : FullChamber (graph Γ p) (weight p)),
      ∃ f' : PolyRing (weight p) k, φ (poly f' * e D) = poly f * e (chamber p D))
    {C E : FullChamber Γ ν} (hC : C.Incident p) (hE : E.Incident p)
    (g : ColPerm ν) (hg : act g p = p) (w : List (Hyp Γ ν))
    (hw : ∀ h ∈ w, h.val p = 0) (f : PolyRing ν k) :
    ∃ z : GalleryAlgebra k (graph Γ p) (weight p),
      φ z = r g E * galList k C w * poly f := by
  obtain ⟨a, ha⟩ := exists_r_preimage φ hr hE g hg
  obtain ⟨b, hb⟩ := exists_galList_preimage φ he ht hC w hw
  obtain ⟨D, hD⟩ := (show C ∈ Set.range (chamber (Γ := Γ) p) by
    rw [range_chamber]
    exact hC)
  obtain ⟨f', hf⟩ := hpoly f D
  refine ⟨a * b * (poly f' * e D), ?_⟩
  rw [map_mul, map_mul, ha, hb, hf, hD]
  calc
    r g E * galList k C w * (poly f * e C) =
        r g E * (galList k C w * e C) * poly f := by
      rw [← e_mul_poly C f]
      simp only [mul_assoc]
    _ = r g E * galList k C w * poly f := by rw [galList_mul_e]

end Categorification.WeightedKLR.Local
