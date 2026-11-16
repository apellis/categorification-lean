/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Mackey.FourBlockLayout

/-!
# Separation and restriction of chambers

Auxiliary facts for the comparison of the layouts `a b c d` and `a c b d` in the proof of
B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, Theorem 2.19.

## Main results

* `StrandEmbedding.isSeparated_restrict`: restriction preserves separation.
* `Juxtapose.isSeparated_chamber_of`: a juxtaposition is separated by a labelling separating
  both sides and compatible with their order.
* `StrandEmbedding.smul_apply_hyp`: a relabelling `ρ` with `j' = ρ ∘ j` reads the hyperplanes of
  `j'` as those of `j`.
* `FullChamber.isSeparated_shuffleTop_and`, `FullChamber.isSeparated_shuffleTop_or`: moving the
  strands of `Z` to the left keeps the separation by `X ∧ Z` and by `X ∨ Z`.
* `Juxtapose.castChamber_eq_restrict`: transport of chambers is restriction along the transport
  of strands.
-/

namespace Categorification.WeightedKLR

open FullChamber

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}

namespace StrandEmbedding

variable {ν₁ ν : I →₀ ℕ}

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
/-- Restricting a chamber separated by `Y` gives a chamber separated by `Y ∘ j`. -/
theorem isSeparated_restrict {j : StrandEmbedding ν₁ ν} {Y : Strand ν → Bool}
    {X : Strand ν₁ → Bool} {C : FullChamber Γ ν} (hC : IsSeparated Y C)
    (hY : ∀ s, Y (j s) = X s) : IsSeparated X (j.restrict C) := by
  intro h hh
  rw [restrict_apply, hC _ (by rw [lo_hyp, hi_hyp, hY, hY]; exact hh), lo_hyp, hY]

omit [DecidableEq I] in
/-- If `j' = ρ ∘ j`, the relabelled chamber `ρ • E` takes on the hyperplanes of `j'` the values
of `E` on those of `j`. -/
theorem smul_apply_hyp {j j' : StrandEmbedding ν₁ ν} {ρ : ColPerm ν}
    (hρ : ∀ s, j' s = ρ.1 (j s)) (E : FullChamber Γ ν) (h : Hyp Γ ν₁) :
    (ρ • E).1 (j'.hyp h) = E.1 (j.hyp h) := by
  rw [FullChamber.smul_apply, reverses_hyp hρ, comap_hyp hρ]
  rfl

omit [DecidableEq I] in
/-- `shuffleTop Z C` agrees with `C` on the hyperplanes of an embedding on whose strands `Z`
is constant. -/
theorem shuffleTop_apply_hyp {j : StrandEmbedding ν₁ ν} {Z : Strand ν → Bool}
    (hZ : ∀ s s', Z (j s) = Z (j s')) (C : FullChamber Γ ν) (h : Hyp Γ ν₁) :
    (shuffleTop Z C).1 (j.hyp h) = C.1 (j.hyp h) := by
  simp only [shuffleTop_apply, lo_hyp, hi_hyp, hZ h.lo h.hi, ↓reduceIte]

end StrandEmbedding

namespace FullChamber

variable {ν : I →₀ ℕ}

omit [DecidableEq I] in
/-- Moving the strands of `Z` to the left of a chamber separated by `X` gives a chamber
separated by `X ∧ Z`. -/
theorem isSeparated_shuffleTop_and {X Z : Strand ν → Bool} {C : FullChamber Γ ν}
    (hC : IsSeparated X C) : IsSeparated (fun t => X t && Z t) (shuffleTop Z C) := by
  intro h hh
  rw [shuffleTop_apply]
  have hX := hC h
  beta_reduce at hh ⊢
  revert hh hX
  generalize X h.lo = x₁
  generalize X h.hi = x₂
  generalize Z h.lo = z₁
  generalize Z h.hi = z₂
  generalize C.1 h = c
  revert x₁ x₂ z₁ z₂ c
  decide

omit [DecidableEq I] in
/-- Moving the strands of `Z` to the left of a chamber separated by `X` gives a chamber
separated by `X ∨ Z`. -/
theorem isSeparated_shuffleTop_or {X Z : Strand ν → Bool} {C : FullChamber Γ ν}
    (hC : IsSeparated X C) : IsSeparated (fun t => X t || Z t) (shuffleTop Z C) := by
  intro h hh
  rw [shuffleTop_apply]
  have hX := hC h
  beta_reduce at hh ⊢
  revert hh hX
  generalize X h.lo = x₁
  generalize X h.hi = x₂
  generalize Z h.lo = z₁
  generalize Z h.hi = z₂
  generalize C.1 h = c
  revert x₁ x₂ z₁ z₂ c
  decide

end FullChamber

namespace Juxtapose

variable {ν' ν'' : I →₀ ℕ}

omit [DecidableEq I] in
/-- A juxtaposition `C' ∘ C''` is separated by `W` if `C'` and `C''` are separated by the
restrictions of `W`, and every strand of `ν'` that `W` distinguishes from a strand of `ν''` is
labelled `true`. -/
theorem isSeparated_chamber_of {W : Strand (ν' + ν'') → Bool} {C' : FullChamber Γ ν'}
    {C'' : FullChamber Γ ν''} (h' : IsSeparated (fun s => W (inlStrand ν' ν'' s)) C')
    (h'' : IsSeparated (fun s => W (inrStrand ν' ν'' s)) C'')
    (hc : ∀ s t, W (inlStrand ν' ν'' s) ≠ W (inrStrand ν' ν'' t) →
      W (inlStrand ν' ν'' s) = true) :
    IsSeparated W (chamber C' C'') := by
  intro h hh
  by_cases hl : h ∈ Set.range ((leftEmb ν' ν'').hyp (Γ := Γ))
  · obtain ⟨y, rfl⟩ := hl
    rw [StrandEmbedding.lo_hyp, StrandEmbedding.hi_hyp] at hh
    rw [chamber_left, h' y hh, StrandEmbedding.lo_hyp]
    rfl
  by_cases hr : h ∈ Set.range ((rightEmb ν' ν'').hyp (Γ := Γ))
  · obtain ⟨y, rfl⟩ := hr
    rw [StrandEmbedding.lo_hyp, StrandEmbedding.hi_hyp] at hh
    rw [chamber_right, h'' y hh, StrandEmbedding.lo_hyp]
    rfl
  have hlr : decide (Strand.IsLeft ν' h.lo) ≠ decide (Strand.IsLeft ν' h.hi) := fun e =>
    (mem_range_of_isLeft_iff e).elim hl hr
  rw [chamber_cross _ _ hl hr, crossSign_eq hlr]
  by_cases hlo : Strand.IsLeft ν' h.lo
  · have hhi : ¬ Strand.IsLeft ν' h.hi := by simpa [hlo] using hlr
    obtain ⟨s, hs⟩ := exists_inlStrand_eq (ν'' := ν'') hlo
    obtain ⟨t, ht⟩ := exists_inrStrand_eq (ν'' := ν'') hhi
    rw [← hs] at hh ⊢
    rw [← ht] at hh
    simp only [hc s t hh, isLeft_inlStrand, decide_true]
  · have hhi : Strand.IsLeft ν' h.hi := by simpa [hlo] using hlr
    obtain ⟨t, ht⟩ := exists_inrStrand_eq (ν'' := ν'') hlo
    obtain ⟨s, hs⟩ := exists_inlStrand_eq (ν'' := ν'') hhi
    rw [← ht] at hh ⊢
    rw [← hs] at hh
    have := hc s t (Ne.symm hh)
    simp only [not_isLeft_inrStrand, decide_false]
    revert hh this
    cases W (inrStrand ν' ν'' t) <;> cases W (inlStrand ν' ν'' s) <;> simp

omit [DecidableEq I] in
/-- The transport of strands along `ν₀ = ν`, as a strand embedding. -/
def castStrandEmb {ν₀ ν : I →₀ ℕ} (h : ν₀ = ν) : StrandEmbedding ν₀ ν where
  toFun := castStrand h
  injective := by subst h; exact fun _ _ e => e
  colour := castStrand_colour h
  rank_lt s t _ hlt := by rw [castStrand_rank, castStrand_rank]; exact hlt

omit [DecidableEq I] in
@[simp] theorem castStrandEmb_apply {ν₀ ν : I →₀ ℕ} (h : ν₀ = ν) (s : Strand ν₀) :
    castStrandEmb h s = castStrand h s := rfl

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
/-- Transporting a chamber back along `ν₀ = ν` is restricting along the transport of
strands. -/
theorem castChamber_eq_restrict {ν₀ ν : I →₀ ℕ} (h : ν₀ = ν) (S : FullChamber Γ ν) :
    castChamber h.symm S = (castStrandEmb h).restrict S := by
  subst h
  refine Subtype.ext (funext fun x => ?_)
  rw [StrandEmbedding.restrict_apply]
  rcases x with _ | _ <;> rfl

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem castChamber_castChamber {ν₀ ν : I →₀ ℕ} (h : ν₀ = ν) (S : FullChamber Γ ν) :
    castChamber h (castChamber h.symm S) = S := by
  subst h
  rfl

end Juxtapose

end Categorification.WeightedKLR
