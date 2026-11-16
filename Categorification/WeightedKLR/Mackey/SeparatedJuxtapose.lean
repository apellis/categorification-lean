/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Mackey.Separated
import Categorification.WeightedKLR.Steadied

/-!
# Separated chambers are juxtapositions

A step of the proof of B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*,
arXiv:1209.2463v4, Theorem 2.19 (the Mackey filtration of §2.4, after Khovanov–Lauda,
arXiv:0803.4121v2, Proposition 2.18). A full chamber of `ν' + ν''` in which the strands of `ν'`
lie to the left of those of `ν''` (`IsSeparated` for `Strand.IsLeft ν'`) is the juxtaposition
`C' ∘ C''` of its restrictions to the two parts (`Juxtapose.eq_chamber_of_isSeparated`), and every
juxtaposition is separated (`Juxtapose.isSeparated_chamber`). So the chambers met by the pieces
of a minimal gallery that rearrange the two blocks separately are juxtapositions, the form in
which these pieces are images of the induction map.

## Main definitions

* `StrandEmbedding.restrict j C`: the chamber of `ν₁` cut out by a strand embedding
  `j : ν₁ → ν` from a chamber of `ν`.

## Main results

* `StrandEmbedding.exists_hyp_eq`: a hyperplane between two image strands is an image hyperplane.
* `Juxtapose.crossSign_eq`: on a hyperplane joining the two parts, `crossSign` is the side of the
  strand of `ν'`.
* `Juxtapose.eq_chamber_of_isSeparated`, `Juxtapose.isSeparated_chamber`.
-/

namespace Categorification.WeightedKLR

variable {I : Type*} {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}

namespace StrandEmbedding

variable {ν₁ ν : I →₀ ℕ} (j : StrandEmbedding ν₁ ν)

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem lo_hyp (h : Hyp Γ ν₁) : (j.hyp h).lo = j h.lo := by
  rcases h with _ | _ <;> rfl

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem hi_hyp (h : Hyp Γ ν₁) : (j.hyp h).hi = j h.hi := by
  rcases h with _ | _ <;> rfl

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- A hyperplane whose two strands are image strands is an image hyperplane. -/
theorem exists_hyp_eq {h : Hyp Γ ν} {a b : Strand ν₁} (ha : h.lo = j a) (hb : h.hi = j b) :
    ∃ h', j.hyp h' = h := by
  rcases h with ⟨⟨e, s, t⟩, hw⟩ | ⟨⟨s, t⟩, hd⟩
  · change s = j a at ha
    change t = j b at hb
    subst ha hb
    refine ⟨.inl ⟨(e, a, b), ?_, ?_, fun hab => hw.2.2 (congrArg j hab)⟩, rfl⟩
    · have := hw.1
      simp only [Strand.label, j.colour] at this
      exact this
    · have := hw.2.1
      simp only [Strand.label, j.colour] at this
      exact this
  · change s = j a at ha
    change t = j b at hb
    subst ha hb
    have hc : a.1 = b.1 := Subtype.ext (by rw [← j.colour, ← j.colour b, hd.1])
    exact ⟨.inr ⟨(a, b), hc, (j.rank_lt_iff hc).1 hd.2⟩, rfl⟩

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem isGeneric_comp {q : Strand ν → 𝕜} (hq : IsGeneric Γ q) : IsGeneric Γ (q ∘ j) :=
  fun h => by rw [← j.val_hyp]; exact hq _

/-- The chamber of `ν₁` cut out from a chamber of `ν` by a strand embedding. -/
noncomputable def restrict (C : FullChamber Γ ν) : FullChamber Γ ν₁ :=
  FullChamber.ofPoint (Juxtapose.point C ∘ j) (j.isGeneric_comp (Juxtapose.isGeneric_point C))

omit [IsStrictOrderedRing 𝕜] in
theorem restrict_apply (C : FullChamber Γ ν) (h : Hyp Γ ν₁) :
    (j.restrict C).1 h = C.1 (j.hyp h) := by
  show fullSigns _ h = _
  rw [← Juxtapose.fullSigns_point C]
  simp only [fullSigns, j.val_hyp]

end StrandEmbedding

namespace Juxtapose

variable {ν' ν'' : I →₀ ℕ}

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem isLeft_inlStrand (s : Strand ν') : Strand.IsLeft ν' (inlStrand ν' ν'' s) := s.2.2

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem not_isLeft_inrStrand (s : Strand ν'') : ¬ Strand.IsLeft ν' (inrStrand ν' ν'' s) := by
  show ¬ (ν' (s.1 : I) + s.2.val < ν' (s.1 : I))
  omega

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem exists_inlStrand_eq {t : Strand (ν' + ν'')} (h : Strand.IsLeft ν' t) :
    ∃ s, inlStrand ν' ν'' s = t := by
  obtain ⟨x | x, rfl⟩ := (strandEquiv ν' ν'').surjective t
  · exact ⟨x, rfl⟩
  · exact absurd h (not_isLeft_inrStrand x)

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem exists_inrStrand_eq {t : Strand (ν' + ν'')} (h : ¬ Strand.IsLeft ν' t) :
    ∃ s, inrStrand ν' ν'' s = t := by
  obtain ⟨x | x, rfl⟩ := (strandEquiv ν' ν'').surjective t
  · exact absurd (isLeft_inlStrand x) h
  · exact ⟨x, rfl⟩

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- A hyperplane whose two strands lie on the same side is in the image of one of the two
embeddings. -/
theorem mem_range_of_isLeft_iff {h : Hyp Γ (ν' + ν'')}
    (hlr : decide (Strand.IsLeft ν' h.lo) = decide (Strand.IsLeft ν' h.hi)) :
    h ∈ Set.range ((leftEmb ν' ν'').hyp (Γ := Γ)) ∨
      h ∈ Set.range ((rightEmb ν' ν'').hyp (Γ := Γ)) := by
  by_cases hl : Strand.IsLeft ν' h.lo
  · have hh : Strand.IsLeft ν' h.hi := by simpa [hl] using hlr
    obtain ⟨a, ha⟩ := exists_inlStrand_eq (ν'' := ν'') hl
    obtain ⟨b, hb⟩ := exists_inlStrand_eq (ν'' := ν'') hh
    exact .inl ((leftEmb ν' ν'').exists_hyp_eq ha.symm hb.symm)
  · have hh : ¬ Strand.IsLeft ν' h.hi := by simpa [hl] using hlr
    obtain ⟨a, ha⟩ := exists_inrStrand_eq (ν'' := ν'') hl
    obtain ⟨b, hb⟩ := exists_inrStrand_eq (ν'' := ν'') hh
    exact .inr ((rightEmb ν' ν'').exists_hyp_eq ha.symm hb.symm)

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- On a hyperplane joining the two parts, `crossSign` is positive exactly when the first strand
is from `ν'`. -/
theorem crossSign_eq {h : Hyp Γ (ν' + ν'')}
    (hlr : decide (Strand.IsLeft ν' h.lo) ≠ decide (Strand.IsLeft ν' h.hi)) :
    crossSign h = decide (Strand.IsLeft ν' h.lo) := by
  rcases h with w | d
  · show ((strandEquiv ν' ν'').symm w.tgt).isRight = decide (Strand.IsLeft ν' w.src)
    change decide (Strand.IsLeft ν' w.src) ≠ decide (Strand.IsLeft ν' w.tgt) at hlr
    by_cases ht : Strand.IsLeft ν' w.tgt
    · obtain ⟨s, hs⟩ := exists_inlStrand_eq (ν'' := ν'') ht
      rw [← hs, strandEquiv_symm_inl]
      simp only [Sum.isRight_inl]
      simpa [ht] using hlr
    · obtain ⟨s, hs⟩ := exists_inrStrand_eq (ν'' := ν'') ht
      rw [← hs, strandEquiv_symm_inr]
      simp only [Sum.isRight_inr]
      simpa [ht] using hlr
  · show true = decide (Strand.IsLeft ν' d.fst)
    change decide (Strand.IsLeft ν' d.fst) ≠ decide (Strand.IsLeft ν' d.snd) at hlr
    by_contra hf
    have hf' : ¬ Strand.IsLeft ν' d.fst := by simpa using fun h => hf (by simp [h])
    have hs : ¬ Strand.IsLeft ν' d.snd := by
      obtain ⟨⟨⟨a, i⟩, ⟨b, j⟩⟩, hab, hij⟩ := d
      change a = b at hab
      subst hab
      unfold Strand.IsLeft at hf' ⊢
      change ¬ (i : ℕ) < ν' a at hf'
      change ¬ (j : ℕ) < ν' a
      change (i : ℕ) < j at hij
      omega
    exact hlr (by simp [hf', hs])

/-- A juxtaposition is separated by the strands of `ν'`. -/
theorem isSeparated_chamber (C' : FullChamber Γ ν') (C'' : FullChamber Γ ν'') :
    FullChamber.IsSeparated (fun t => decide (Strand.IsLeft ν' t)) (chamber C' C'') := by
  intro h hlr
  have hl : h ∉ Set.range ((leftEmb ν' ν'').hyp (Γ := Γ)) := by
    rintro ⟨h', rfl⟩
    rw [StrandEmbedding.lo_hyp, StrandEmbedding.hi_hyp] at hlr
    exact hlr (by simp [show (leftEmb ν' ν'' : Strand ν' → _) = inlStrand ν' ν'' from rfl,
      isLeft_inlStrand])
  have hr : h ∉ Set.range ((rightEmb ν' ν'').hyp (Γ := Γ)) := by
    rintro ⟨h', rfl⟩
    rw [StrandEmbedding.lo_hyp, StrandEmbedding.hi_hyp] at hlr
    exact hlr (by simp [show (rightEmb ν' ν'' : Strand ν'' → _) = inrStrand ν' ν'' from rfl,
      not_isLeft_inrStrand])
  rw [chamber_cross _ _ hl hr, crossSign_eq hlr]

/-- **Separated chambers are juxtapositions.** A chamber of `ν' + ν''` in which the strands of
`ν'` lie to the left of those of `ν''` is the juxtaposition of its restrictions. -/
theorem eq_chamber_of_isSeparated {C : FullChamber Γ (ν' + ν'')}
    (hC : FullChamber.IsSeparated (fun t => decide (Strand.IsLeft ν' t)) C) :
    C = chamber ((leftEmb ν' ν'').restrict C) ((rightEmb ν' ν'').restrict C) := by
  apply Subtype.ext
  funext h
  by_cases hl : h ∈ Set.range ((leftEmb ν' ν'').hyp (Γ := Γ))
  · obtain ⟨h', rfl⟩ := hl
    rw [chamber_left, StrandEmbedding.restrict_apply]
  by_cases hr : h ∈ Set.range ((rightEmb ν' ν'').hyp (Γ := Γ))
  · obtain ⟨h', rfl⟩ := hr
    rw [chamber_right, StrandEmbedding.restrict_apply]
  have hlr : decide (Strand.IsLeft ν' h.lo) ≠ decide (Strand.IsLeft ν' h.hi) := fun e =>
    (mem_range_of_isLeft_iff e).elim hl hr
  rw [chamber_cross _ _ hl hr, crossSign_eq hlr, hC h hlr]

end Juxtapose

end Categorification.WeightedKLR
