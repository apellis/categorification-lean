/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.GallerySpan.Flip
import Categorification.WeightedKLR.Segment.Chain
import Categorification.WeightedKLR.Segment.Extension

/-!
# Straight-line galleries span the gallery algebra

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, Theorem 2.8,
spanning half. Choose for each pair of full chambers `C, E` a simple segment from a generic
point of `C` to a generic point of `E`, and let `seg C E` be the gallery of its word. Under (†)
(`Γ.Dagger`) and the absence of loops of weight `0` (`Γ.NoZeroLoops`), the elements
`poly f * r g E * seg C E` span the gallery algebra over `k`.

The proof follows Webster's: by induction on the number of steps it suffices that one more step
`t E E₁ * seg C E` is a combination of such elements with one more step. If the hyperplane
between `E` and `E₁` does not separate `C` and `E`, the new gallery is the gallery of a simple
segment from `C` to `E₁`. Otherwise it contains a bigon, which the bigon relations remove. In
both cases the galleries of two simple segments between the same chambers differ by an element
with fewer steps (`GalleryAlgebra.galList_reflTransGen`).

## Main definitions

* `GalleryAlgebra.IsChamberSegment C E pq`: `pq` is a simple segment from `C` to `E`.

## Main results

* `GalleryAlgebra.span_segGallery`: for any choice of simple segments, the elements
  `poly f * r g E * galList C (word pq)` span the gallery algebra.
* `GalleryAlgebra.exists_span_segGallery`: such a choice exists.
-/

namespace Categorification.WeightedKLR

open Segment FullChamber

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

namespace GalleryAlgebra

/-- `pq` is a simple segment from a generic point of `C` to a generic point of `E`. -/
def IsChamberSegment (C E : FullChamber Γ ν) (pq : (Strand ν → 𝕜) × (Strand ν → 𝕜)) : Prop :=
  Simple (hypAff (Γ := Γ)) pq.1 pq.2 ∧ fullSigns pq.1 = C.1 ∧ fullSigns pq.2 = E.1

theorem exists_isChamberSegment (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (C E : FullChamber Γ ν) :
    ∃ pq, IsChamberSegment C E pq := by
  obtain ⟨p, hp, hpC⟩ := C.2
  obtain ⟨q, hq, hqE⟩ := E.2
  obtain ⟨p', q', hs, h1, h2⟩ := exists_simple (f := hypAff (Γ := Γ)) (hdist hD hZ) hp hq
  exact ⟨(p', q'), hs, h1.trans hpC, h2.trans hqE⟩

/-- The word of a simple segment starting in `C` is good from `C`, and its gallery ends in the
chamber of the end point. -/
theorem goodWord_flips_word {C : FullChamber Γ ν} {p q : Strand ν → 𝕜}
    (hs : Simple (hypAff (Γ := Γ)) p q) (hp : fullSigns p = C.1) :
    GoodWord C.1 (word (hypAff (Γ := Γ)) p q) ∧
      (C.flips (word (hypAff (Γ := Γ)) p q)).1 = fullSigns q := by
  have hw : GoodWord C.1 (word (hypAff (Γ := Γ)) p q) := hp ▸ goodWord_word hs
  refine ⟨hw, ?_⟩
  rw [flips_val hw, ← hp]
  exact flipSigns_word (f := hypAff (Γ := Γ))

omit [IsStrictOrderedRing 𝕜] in
/-- A word of length less than two admits no flip. -/
theorem eq_of_reflTransGen_of_length_lt {σ : Hyp Γ ν → Bool} {w w' : List (Hyp Γ ν)}
    (hr : Relation.ReflTransGen (Flip (hypAff (Γ := Γ)) σ) w w') (hl : w.length < 2) :
    w = w' := by
  induction hr with
  | refl => rfl
  | tail _ hf ih =>
    obtain ⟨a, B, c, e, -, hB, -⟩ := hf
    subst ih
    rw [e] at hl
    simp only [List.length_append] at hl
    omega

/-- One step after the difference of the galleries of two words related by flips. -/
theorem mul_galList_sub_mem (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) {C : FullChamber Γ ν}
    {w w' : List (Hyp Γ ν)} (hw : GoodWord C.1 w)
    (hr : Relation.ReflTransGen (Flip (hypAff (Γ := Γ)) C.1) w w') {y : GalleryAlgebra k Γ ν}
    (hy : y ∈ stepFilt k Γ ν 1) :
    y * (galList k C w - galList k C w') ∈ stepFilt k Γ ν (w.length - 1) := by
  by_cases hl : w.length < 2
  · rw [eq_of_reflTransGen_of_length_lt hr hl, sub_self, mul_zero]
    exact Submodule.zero_mem _
  · exact stepFilt_mono (by omega) (mul_mem_stepFilt hy (galList_reflTransGen hD hZ hw hr))

/-- The galleries of two simple segments between the same chambers differ by an element with
fewer steps. -/
theorem galList_word_sub_mem (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) {C : FullChamber Γ ν}
    {p q p' q' : Strand ν → 𝕜} (hs : Simple (hypAff (Γ := Γ)) p q)
    (hs' : Simple (hypAff (Γ := Γ)) p' q') (hp : fullSigns p = C.1) (hp' : fullSigns p' = C.1)
    (hq : fullSigns (Γ := Γ) q' = fullSigns q) :
    Relation.ReflTransGen (Flip (hypAff (Γ := Γ)) C.1) (word (hypAff (Γ := Γ)) p q)
        (word (hypAff (Γ := Γ)) p' q') ∧
      (word (hypAff (Γ := Γ)) p q).length = (word (hypAff (Γ := Γ)) p' q').length ∧
      galList k C (word (hypAff (Γ := Γ)) p q) - galList k C (word (hypAff (Γ := Γ)) p' q') ∈
        stepFilt k Γ ν ((word (hypAff (Γ := Γ)) p q).length - 2) := by
  have hr := reflTransGen_flip_of_simple (f := hypAff (Γ := Γ)) (hdist hD hZ) hs hs'
    (show fullSigns p' = fullSigns p by rw [hp, hp']) hq
  have hr' : Relation.ReflTransGen (Flip (hypAff (Γ := Γ)) C.1) (word (hypAff (Γ := Γ)) p q)
      (word (hypAff (Γ := Γ)) p' q') := by
    rw [← hp]; exact hr
  exact ⟨hr', (reflTransGen_flip_perm hr').length_eq,
    galList_reflTransGen (k := k) hD hZ (goodWord_flips_word hs hp).1 hr'⟩

/-- The two bigon relations, applied to a spanning set. -/
theorem bigon_mul_mem {S : FullChamber Γ ν → FullChamber Γ ν → GalleryAlgebra k Γ ν}
    {L : FullChamber Γ ν → FullChamber Γ ν → ℕ} {m : ℕ} {E E₁ : FullChamber Γ ν}
    {h : Hyp Γ ν} (hh : E₁.Adjacent E h) {x : GalleryAlgebra k Γ ν} (hx : x ∈ segSpan S L m)
    (htx : t E₁ E * x ∈ segSpan S L m) : t E E₁ * (t E₁ E * x) ∈ segSpan S L m := by
  rw [← mul_assoc]
  cases h with
  | inl w =>
    have hb : (t E E₁ * t E₁ E : GalleryAlgebra k Γ ν) = poly w.factor * e E₁ := by
      have := rel (Rel.wall_bigon (k := k) E₁ E w hh)
      rw [map_mul, map_mul] at this
      exact this
    rw [hb, mul_assoc]
    exact poly_mul_mem_segSpan _ (e_mul_mem_segSpan _ hx)
  | inr d =>
    have hb := rel (Rel.diag_bigon (k := k) E₁ E d hh)
    rw [map_mul] at hb
    rcases hP : Γ.loop d.fst.1 with _ | P
    · simp only [hP, map_zero] at hb
      rw [show (t E E₁ * t E₁ E : GalleryAlgebra k Γ ν) = 0 from hb, zero_mul]
      exact Submodule.zero_mem _
    · simp only [hP, map_mul, mk_fp, mk_fr, mk_ft] at hb
      rw [show (t E E₁ * t E₁ E : GalleryAlgebra k Γ ν) = _ from hb, mul_assoc, mul_assoc]
      exact poly_mul_mem_segSpan _ (r_mul_mem_segSpan _ _ htx)

section Choice

variable (P : FullChamber Γ ν → FullChamber Γ ν → (Strand ν → 𝕜) × (Strand ν → 𝕜))

/-- The gallery of the chosen segment from `C` to `E`. -/
noncomputable def segGallery (C E : FullChamber Γ ν) : GalleryAlgebra k Γ ν :=
  galList k C (word (hypAff (Γ := Γ)) (P C E).1 (P C E).2)

/-- The number of steps of the chosen gallery from `C` to `E`. -/
noncomputable def segLength (C E : FullChamber Γ ν) : ℕ :=
  (word (hypAff (Γ := Γ)) (P C E).1 (P C E).2).length

variable {P} (hP : ∀ C E, IsChamberSegment C E (P C E))
include hP

theorem flips_segWord (C E : FullChamber Γ ν) :
    C.flips (word (hypAff (Γ := Γ)) (P C E).1 (P C E).2) = E :=
  Subtype.ext ((goodWord_flips_word (hP C E).1 (hP C E).2.1).2.trans (hP C E).2.2)

theorem segGallery_mem_segSpan {m : ℕ} {C E : FullChamber Γ ν} (hl : segLength P C E ≤ m) :
    segGallery (k := k) P C E ∈ segSpan (segGallery P) (segLength P) m := by
  have := gen_mem_segSpan (seg := segGallery (k := k) P) (len := segLength P) 1 1 hl
  rw [← polyHom_apply, map_one, one_mul, r_one] at this
  have he : e E * segGallery (k := k) P C E = segGallery P C E := by
    have h0 := e_mul_galList (k := k) C (word (hypAff (Γ := Γ)) (P C E).1 (P C E).2)
    rw [flips_segWord hP C E] at h0
    exact h0
  rwa [he] at this

/-- A gallery of a simple segment from `C` to `E` lies in the span of the chosen galleries,
modulo elements with fewer steps. -/
theorem galList_sub_segGallery (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) {C E : FullChamber Γ ν}
    {p q : Strand ν → 𝕜} (hs : Simple (hypAff (Γ := Γ)) p q) (hp : fullSigns p = C.1)
    (hq : fullSigns q = E.1) :
    galList k C (word (hypAff (Γ := Γ)) p q) - segGallery P C E ∈
        stepFilt k Γ ν ((word (hypAff (Γ := Γ)) p q).length - 2) ∧
      segLength P C E = (word (hypAff (Γ := Γ)) p q).length := by
  obtain ⟨-, hlen, hmem⟩ := galList_word_sub_mem (k := k) hD hZ hs (hP C E).1 hp (hP C E).2.1
    ((hP C E).2.2.trans hq.symm)
  exact ⟨hmem, hlen.symm⟩

theorem one_mem_segSpan :
    (1 : GalleryAlgebra k Γ ν) ∈ segSpan (segGallery P) (segLength P) 0 := by
  rw [← sum_e]
  refine Submodule.sum_mem _ fun C _ => ?_
  have hnil : word (hypAff (Γ := Γ)) (P C C).1 (P C C).2 = [] := by
    refine List.eq_nil_iff_forall_not_mem.2 fun h hm => ?_
    have hsep := (mem_word (f := hypAff (Γ := Γ))).1 hm
    have he : Segment.signs (hypAff (Γ := Γ)) (P C C).2 =
        Segment.signs (hypAff (Γ := Γ)) (P C C).1 :=
      (hP C C).2.2.trans (hP C C).2.1.symm
    exact ((separates_congr_right (f := hypAff (Γ := Γ)) he h).1 hsep) rfl
  have := segGallery_mem_segSpan (k := k) hP (m := 0) (C := C) (E := C)
    (by rw [segLength, hnil]; rfl)
  rwa [segGallery, hnil, galList_nil] at this

/-- The inductive step: one more step on a chosen gallery. -/
theorem t_mul_segGallery_mem (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (m : ℕ)
    (hm : stepFilt k Γ ν m ≤ segSpan (segGallery P) (segLength P) m)
    (C E E₁ : FullChamber Γ ν) (hl : segLength P C E ≤ m) :
    t E E₁ * segGallery P C E ∈ segSpan (segGallery P) (segLength P) (m + 1) := by
  have hm' : stepFilt k Γ ν m ≤ segSpan (segGallery P) (segLength P) (m + 1) :=
    hm.trans (segSpan_mono (Nat.le_succ m))
  by_cases hadj : ∃ h, E.Adjacent E₁ h
  swap
  · push Not at hadj
    rw [t_eq_zero hadj, zero_mul]
    exact Submodule.zero_mem _
  obtain ⟨h, hh⟩ := hadj
  obtain ⟨p, hpg, hpC⟩ := C.2
  obtain ⟨e, heg, heE⟩ := E.2
  obtain ⟨e₁, he₁g, he₁E⟩ := E₁.2
  -- the chosen word from `C` to `E`
  set w := word (hypAff (Γ := Γ)) (P C E).1 (P C E).2 with hw
  have hgw : GoodWord C.1 w := (goodWord_flips_word (hP C E).1 (hP C E).2.1).1
  have hlw : w.length ≤ m := hl
  by_cases hsep : C.1 h = E.1 h
  · -- `h` does not separate `C` and `E`: the new gallery is straight
    obtain ⟨p₀, q, q', s₀, s₁, s₂, hs, hs', hword⟩ := exists_word_append
      (f := hypAff (Γ := Γ)) (hdist hD hZ) hpg heg he₁g
      (show fullSigns e h ≠ fullSigns e₁ h by rw [heE, he₁E]; exact hh.1)
      (fun g hg => show fullSigns e g = fullSigns e₁ g by rw [heE, he₁E]; exact hh.2 g hg)
      (show fullSigns p h = fullSigns e h by rw [hpC, heE]; exact hsep)
    have hp₀ : fullSigns p₀ = C.1 := s₀.trans hpC
    have hq : fullSigns q = E.1 := s₁.trans heE
    have hq' : fullSigns q' = E₁.1 := s₂.trans he₁E
    have fl : C.flips (word (hypAff (Γ := Γ)) p₀ q) = E :=
      Subtype.ext ((goodWord_flips_word hs hp₀).2.trans hq)
    have hG' : galList k C (word (hypAff (Γ := Γ)) p₀ q') =
        t E E₁ * galList k C (word (hypAff (Γ := Γ)) p₀ q) := by
      rw [hword, galList_append, fl, galList_cons, galList_nil, flipH_eq_of_adjacent hh,
        e_mul_t]
    obtain ⟨hr, hlen, -⟩ := galList_word_sub_mem (k := k) hD hZ (hP C E).1 hs (hP C E).2.1 hp₀
      (hq.trans (hP C E).2.2.symm)
    obtain ⟨d₁, l₁⟩ := galList_sub_segGallery (k := k) hP hD hZ hs' hp₀ hq'
    have hlen' : (word (hypAff (Γ := Γ)) p₀ q').length = segLength P C E + 1 := by
      rw [hword, List.length_append, ← hlen]; rfl
    have hdec : t E E₁ * segGallery P C E =
        t E E₁ * (galList k C w - galList k C (word (hypAff (Γ := Γ)) p₀ q)) +
          (galList k C (word (hypAff (Γ := Γ)) p₀ q') - segGallery P C E₁) + segGallery P C E₁ := by
      rw [hG', mul_sub, segGallery]; abel
    rw [hdec]
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_)
      (segGallery_mem_segSpan hP (by rw [l₁, hlen']; omega))
    · exact hm' (stepFilt_mono (by omega)
        (mul_galList_sub_mem hD hZ hgw hr (t_mem_stepFilt _ _ le_rfl)))
    · exact hm' (stepFilt_mono (by rw [hlen']; omega) d₁)
  · -- `h` separates `C` and `E`: a bigon
    have hsep₁ : C.1 h = E₁.1 h := by
      have := hh.1
      revert hsep this
      cases C.1 h <;> cases E.1 h <;> cases E₁.1 h <;> simp
    obtain ⟨p₀, q, q', s₀, s₁, s₂, hs, hs', hword⟩ := exists_word_append
      (f := hypAff (Γ := Γ)) (hdist hD hZ) hpg he₁g heg
      (show fullSigns e₁ h ≠ fullSigns e h by rw [heE, he₁E]; exact hh.1.symm)
      (fun g hg => show fullSigns e₁ g = fullSigns e g by
        rw [heE, he₁E]; exact (hh.2 g hg).symm)
      (show fullSigns p h = fullSigns e₁ h by rw [hpC, he₁E]; exact hsep₁)
    have hp₀ : fullSigns p₀ = C.1 := s₀.trans hpC
    have hq : fullSigns q = E₁.1 := s₁.trans he₁E
    have hq' : fullSigns q' = E.1 := s₂.trans heE
    have fl : C.flips (word (hypAff (Γ := Γ)) p₀ q) = E₁ :=
      Subtype.ext ((goodWord_flips_word hs hp₀).2.trans hq)
    have hG' : galList k C (word (hypAff (Γ := Γ)) p₀ q') =
        t E₁ E * galList k C (word (hypAff (Γ := Γ)) p₀ q) := by
      rw [hword, galList_append, fl, galList_cons, galList_nil, flipH_eq_of_adjacent hh.symm,
        e_mul_t]
    obtain ⟨hr, hlen, -⟩ := galList_word_sub_mem (k := k) hD hZ (hP C E).1 hs' (hP C E).2.1 hp₀
      (hq'.trans (hP C E).2.2.symm)
    obtain ⟨d₁, l₁⟩ := galList_sub_segGallery (k := k) hP hD hZ hs hp₀ hq
    obtain ⟨d₂, l₂⟩ := galList_sub_segGallery (k := k) hP hD hZ hs' hp₀ hq'
    have hlen' :
        (word (hypAff (Γ := Γ)) p₀ q').length = (word (hypAff (Γ := Γ)) p₀ q).length + 1 := by
      rw [hword, List.length_append]; rfl
    have hdec : t E E₁ * segGallery P C E =
        t E E₁ * (galList k C w - galList k C (word (hypAff (Γ := Γ)) p₀ q')) +
          t E E₁ * (t E₁ E * galList k C (word (hypAff (Γ := Γ)) p₀ q)) := by
      rw [← hG', ← mul_add, sub_add_cancel]; rfl
    rw [hdec]
    refine Submodule.add_mem _ ?_ (segSpan_mono (Nat.le_succ m) (bigon_mul_mem hh.symm ?_ ?_))
    · exact hm' (stepFilt_mono (by omega)
        (mul_galList_sub_mem hD hZ hgw hr (t_mem_stepFilt _ _ le_rfl)))
    · rw [← sub_add_cancel (galList k C (word (hypAff (Γ := Γ)) p₀ q)) (segGallery P C E₁)]
      exact Submodule.add_mem _ (hm (stepFilt_mono (by omega) d₁))
        (segGallery_mem_segSpan hP (by omega))
    · rw [← hG', ← sub_add_cancel (galList k C (word (hypAff (Γ := Γ)) p₀ q')) (segGallery P C E)]
      exact Submodule.add_mem _ (hm (stepFilt_mono (by omega) d₂))
        (segGallery_mem_segSpan hP hl)

/-- **Webster, Theorem 2.8, spanning half.** Under (†) and the absence of loops of weight `0`,
for any choice of simple segments between the full chambers, the elements
`poly f * r g E * galList C (word pq)`, `pq` the segment from `C` to `E`, span the gallery
algebra. -/
theorem span_segGallery (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) :
    Submodule.span k {x : GalleryAlgebra k Γ ν | ∃ (f : PolyRing ν k) (g : ColPerm ν)
      (C E : FullChamber Γ ν), poly f * r g E * segGallery P C E = x} = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun x => ?_
  obtain ⟨n, hn⟩ := exists_mem_stepFilt (k := k) x
  have := stepFilt_le_segSpan (one_mem_segSpan hP)
    (fun m hm C E E₁ hl => t_mul_segGallery_mem hP hD hZ m hm C E E₁ hl) n hn
  refine Submodule.span_mono ?_ this
  rintro _ ⟨f, g, C, E, -, hx⟩
  exact ⟨f, g, C, E, hx⟩

end Choice

/-- **Webster, Theorem 2.8, spanning half**, with a choice of segments. -/
theorem exists_span_segGallery (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) :
    ∃ P : FullChamber Γ ν → FullChamber Γ ν → (Strand ν → 𝕜) × (Strand ν → 𝕜),
      (∀ C E, IsChamberSegment C E (P C E)) ∧
      Submodule.span k {x : GalleryAlgebra k Γ ν | ∃ (f : PolyRing ν k) (g : ColPerm ν)
        (C E : FullChamber Γ ν), poly f * r g E * segGallery P C E = x} = ⊤ := by
  choose P hP using exists_isChamberSegment hD hZ
  exact ⟨P, hP, span_segGallery hP hD hZ⟩

end GalleryAlgebra

end Categorification.WeightedKLR
