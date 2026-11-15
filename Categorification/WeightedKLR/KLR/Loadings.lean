/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Arrangement
import Categorification.KLR.Basic

/-!
# The evenly spaced loadings `B_s`

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, Proposition 2.14.

For a sequence `i = (i_1, …, i_m)` of colours and a spacing `s`, the loading `B_s(i)` puts the
strand coloured `i_a` at the point `s · a`. If `s` exceeds every `|ϑ_e|`, a ghost never comes
between two strands, so a strand lies to the right of a ghost exactly when it lies to the right
of the strand casting it. Proposition 2.14 of the paper compares the weighted KLR algebra on the
loadings `B_s` with the ordinary KLR algebra; this file sets up the loadings and their chambers.

## Encoding

A sequence of weight `ν` is a `KLR.Seq ν` (`ν : Multiset I`); the loadings live on the strands
of the weight `ν.toFinsupp`. The strand at position `a` of `i` is the one of colour `i_a` whose
rank is the number of earlier positions with the same colour (`Seq.strandAt`). This is a
bijection `Seq.strandEquiv` from positions to strands, increasing on each colour.

## Main definitions and results

* `Seq.strandEquiv i : Fin (card ν) ≃ Strand ν.toFinsupp`.
* `Seq.spacedPos s i`: the configuration `B_s(i)`, strand ↦ `s ·` its position.
* `Seq.isAdmissible_spacedPos`: for `0 < s` and `|ϑ_e| < s` for every edge, `B_s(i)` is a
  generic loading (`Seq.spacedLoading`).
* `Seq.signs_spacedPos`: the side of a wall on which `B_s(i)` lies is the relative order of its
  two strands; so the chamber `Seq.spacedChamber i` does not depend on `s`
  (`Seq.spacedLoading_chamber`).
* `Seq.spacedChamber_eq_iff`: two sequences give the same chamber iff every pair of
  interacting strands is in the same order in both.
-/

namespace Categorification.KLR.Seq

open Categorification.WeightedKLR

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}
  {ν : Multiset I}

/-- The rank at position `a` of `i`: the number of earlier positions with the same colour. -/
def rank (i : Seq ν) (a : Fin (Multiset.card ν)) : ℕ :=
  (Finset.univ.filter fun b => b < a ∧ i.1 b = i.1 a).card

theorem count_eq_card (i : Seq ν) (c : I) :
    ν.count c = (Finset.univ.filter fun b => i.1 b = c).card := by
  conv_lhs => rw [← i.2]
  rw [Multiset.count_map, Finset.card, Finset.filter_val]
  congr 1
  exact Multiset.filter_congr fun b _ => eq_comm

theorem rank_lt_count (i : Seq ν) (a : Fin (Multiset.card ν)) :
    i.rank a < ν.count (i.1 a) := by
  rw [count_eq_card, rank]
  refine Finset.card_lt_card ⟨fun b hb => ?_, fun h => ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    exact hb.2
  · have := h (by simp : a ∈ Finset.univ.filter fun b => i.1 b = i.1 a)
    simp at this

theorem rank_lt_rank (i : Seq ν) {a b : Fin (Multiset.card ν)} (hab : a < b)
    (hc : i.1 a = i.1 b) : i.rank a < i.rank b := by
  rw [rank, rank]
  refine Finset.card_lt_card ⟨fun c hc' => ?_, fun h => ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc' ⊢
    exact ⟨hc'.1.trans hab, hc'.2.trans hc⟩
  · have := h (by simp [hab, hc] : a ∈ Finset.univ.filter fun c => c < b ∧ i.1 c = i.1 b)
    simp at this

theorem mem_support (i : Seq ν) (a : Fin (Multiset.card ν)) :
    i.1 a ∈ (Multiset.toFinsupp ν).support := by
  rw [Multiset.toFinsupp_support]
  exact Multiset.mem_toFinset.2 (i.mem a)

/-- The strand at position `a` of `i`: colour `i_a`, rank `i.rank a`. -/
def strandAt (i : Seq ν) (a : Fin (Multiset.card ν)) : Strand (Multiset.toFinsupp ν) :=
  ⟨⟨i.1 a, i.mem_support a⟩, ⟨i.rank a, by
    rw [Multiset.toFinsupp_apply]; exact i.rank_lt_count a⟩⟩

@[simp] theorem label_strandAt (i : Seq ν) (a : Fin (Multiset.card ν)) :
    (i.strandAt a).label = i.1 a := rfl

theorem strandAt_injective (i : Seq ν) : Function.Injective i.strandAt := by
  intro a b h
  have hc : i.1 a = i.1 b := congrArg (fun t : Strand _ => (t.1 : I)) h
  have hr : i.rank a = i.rank b := congrArg (fun t : Strand _ => t.2.val) h
  rcases lt_trichotomy a b with hab | hab | hab
  · exact absurd hr (i.rank_lt_rank hab hc).ne
  · exact hab
  · exact absurd hr.symm (i.rank_lt_rank hab hc.symm).ne

theorem card_strand : Fintype.card (Strand (Multiset.toFinsupp ν)) = Multiset.card ν := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  simp only [Multiset.toFinsupp_apply]
  rw [Finset.sum_coe_sort (Multiset.toFinsupp ν).support (fun c => ν.count c),
    Multiset.toFinsupp_support, Multiset.toFinset_sum_count_eq]

/-- Positions of `i` correspond to strands. -/
noncomputable def strandEquiv (i : Seq ν) :
    Fin (Multiset.card ν) ≃ Strand (Multiset.toFinsupp ν) :=
  Equiv.ofBijective i.strandAt ((Fintype.bijective_iff_injective_and_card _).2
    ⟨i.strandAt_injective, by rw [card_strand, Fintype.card_fin]⟩)

@[simp] theorem strandEquiv_apply (i : Seq ν) (a : Fin (Multiset.card ν)) :
    i.strandEquiv a = i.strandAt a := rfl

/-- The position of a strand. -/
noncomputable def posOf (i : Seq ν) (t : Strand (Multiset.toFinsupp ν)) :
    Fin (Multiset.card ν) :=
  i.strandEquiv.symm t

@[simp] theorem strandAt_posOf (i : Seq ν) (t : Strand (Multiset.toFinsupp ν)) :
    i.strandAt (i.posOf t) = t := i.strandEquiv.apply_symm_apply t

@[simp] theorem posOf_strandAt (i : Seq ν) (a : Fin (Multiset.card ν)) :
    i.posOf (i.strandAt a) = a := i.strandEquiv.symm_apply_apply a

theorem posOf_injective (i : Seq ν) : Function.Injective i.posOf :=
  i.strandEquiv.symm.injective

theorem label_posOf (i : Seq ν) (t : Strand (Multiset.toFinsupp ν)) :
    i.1 (i.posOf t) = t.label := by
  conv_rhs => rw [← i.strandAt_posOf t]
  rfl

theorem rank_posOf (i : Seq ν) (t : Strand (Multiset.toFinsupp ν)) :
    i.rank (i.posOf t) = t.2.val := by
  conv_rhs => rw [← i.strandAt_posOf t]
  rfl

/-- Strands of one colour are placed in rank order. -/
theorem posOf_lt_posOf (i : Seq ν) {t u : Strand (Multiset.toFinsupp ν)} (hc : t.1 = u.1)
    (hr : t.2.val < u.2.val) : i.posOf t < i.posOf u := by
  by_contra h
  push Not at h
  rcases h.lt_or_eq with h | h
  · have hl : i.1 (i.posOf u) = i.1 (i.posOf t) := by
      rw [label_posOf, label_posOf, Strand.label, Strand.label, hc]
    have := i.rank_lt_rank h hl
    rw [rank_posOf, rank_posOf] at this
    omega
  · have := congrArg i.strandAt h
    rw [strandAt_posOf, strandAt_posOf] at this
    subst this
    omega

/-- The configuration `B_s(i)`: the strand at position `a` sits at `s · a`. -/
noncomputable def spacedPos (s : 𝕜) (i : Seq ν) : Strand (Multiset.toFinsupp ν) → 𝕜 :=
  fun t => s * ((i.posOf t : ℕ) : 𝕜)

theorem spacedPos_lt_spacedPos {s : 𝕜} (hs : 0 < s) (i : Seq ν)
    {t u : Strand (Multiset.toFinsupp ν)} :
    spacedPos s i t < spacedPos s i u ↔ i.posOf t < i.posOf u := by
  rw [spacedPos, spacedPos, mul_lt_mul_iff_right₀ hs, Nat.cast_lt, Fin.lt_def]

/-- The value of a wall at `B_s(i)` has the sign of the relative order of the two strands:
the gap between distinct strands is at least `s`, and `|ϑ_e| < s`. -/
theorem val_spacedPos_pos_iff {s : 𝕜} (hs : ∀ e, |Γ.weight e| < s) (i : Seq ν)
    (w : Wall Γ (Multiset.toFinsupp ν)) :
    0 < w.val (spacedPos s i) ↔ i.posOf w.src < i.posOf w.tgt := by
  have hne : i.posOf w.src ≠ i.posOf w.tgt :=
    fun h => w.2.2.2 (i.posOf_injective h)
  have hϑ := abs_lt.1 (hs w.edge)
  simp only [Wall.val, spacedPos]
  constructor
  · intro h
    by_contra h'
    push Not at h'
    have h'' : ((i.posOf w.tgt : ℕ) : 𝕜) + 1 ≤ ((i.posOf w.src : ℕ) : 𝕜) := by
      exact_mod_cast (lt_of_le_of_ne h' (Ne.symm hne))
    nlinarith
  · intro h
    have h'' : ((i.posOf w.src : ℕ) : 𝕜) + 1 ≤ ((i.posOf w.tgt : ℕ) : 𝕜) := by
      exact_mod_cast h
    nlinarith

theorem val_spacedPos_ne_zero {s : 𝕜} (hs : ∀ e, |Γ.weight e| < s) (i : Seq ν)
    (w : Wall Γ (Multiset.toFinsupp ν)) : w.val (spacedPos s i) ≠ 0 := by
  have hne : i.posOf w.src ≠ i.posOf w.tgt :=
    fun h => w.2.2.2 (i.posOf_injective h)
  have hϑ := abs_lt.1 (hs w.edge)
  simp only [Wall.val, spacedPos]
  rcases lt_or_gt_of_ne hne with h | h
  · have h'' : ((i.posOf w.src : ℕ) : 𝕜) + 1 ≤ ((i.posOf w.tgt : ℕ) : 𝕜) := by
      exact_mod_cast h
    nlinarith
  · have h'' : ((i.posOf w.tgt : ℕ) : 𝕜) + 1 ≤ ((i.posOf w.src : ℕ) : 𝕜) := by
      exact_mod_cast h
    nlinarith

variable (Γ) in
/-- `B_s(i)` is a generic loading when `0 < s` and `|ϑ_e| < s` for every edge. -/
theorem isAdmissible_spacedPos {s : 𝕜} (hs0 : 0 < s) (hs : ∀ e, |Γ.weight e| < s)
    (i : Seq ν) : IsAdmissible Γ (spacedPos s i) := by
  refine ⟨fun t u h => ?_, fun t u hc hr => ?_, val_spacedPos_ne_zero hs i⟩
  · apply i.posOf_injective
    have h' : ((i.posOf t : ℕ) : 𝕜) = ((i.posOf u : ℕ) : 𝕜) :=
      mul_left_cancel₀ hs0.ne' h
    exact Fin.ext (by exact_mod_cast h')
  · exact (spacedPos_lt_spacedPos hs0 i).2 (i.posOf_lt_posOf hc hr)

/-- The side of each wall on which `B_s(i)` lies: the order of the two strands. -/
theorem signs_spacedPos {s : 𝕜} (hs : ∀ e, |Γ.weight e| < s) (i : Seq ν) :
    signs (Γ := Γ) (spacedPos s i) = fun w => decide (i.posOf w.src < i.posOf w.tgt) := by
  funext w
  simp only [signs, val_spacedPos_pos_iff hs]

variable (Γ) in
/-- The loading `B_s(i)`. -/
noncomputable def spacedLoading {s : 𝕜} (hs0 : 0 < s) (hs : ∀ e, |Γ.weight e| < s)
    (i : Seq ν) : Loading Γ (Multiset.toFinsupp ν) :=
  ⟨spacedPos s i, isAdmissible_spacedPos Γ hs0 hs i⟩

/-- The chamber of the loadings `B_s(i)`: a wall is positive exactly when the strand meeting the
ghost is to the right of the strand casting it. This uses that some spacing exists, which holds
as `Γ` has finitely many edges. -/
noncomputable def spacedChamber (Γ : WeightedGraph I 𝕜 k) (i : Seq ν) :
    Chamber Γ (Multiset.toFinsupp ν) :=
  ⟨fun w => decide (i.posOf w.src < i.posOf w.tgt), by
    obtain ⟨s, hs0, hs⟩ : ∃ s : 𝕜, 0 < s ∧ ∀ e, |Γ.weight e| < s :=
      ⟨1 + ∑ e, |Γ.weight e|, by
        have := Finset.sum_nonneg fun e (_ : e ∈ Finset.univ) => abs_nonneg (Γ.weight e)
        linarith, fun e => by
        have := Finset.single_le_sum (fun e (_ : e ∈ Finset.univ) => abs_nonneg (Γ.weight e))
          (Finset.mem_univ e)
        linarith⟩
    exact ⟨spacedPos s i, isAdmissible_spacedPos Γ hs0 hs i, signs_spacedPos hs i⟩⟩

/-- The chamber of `B_s(i)` is `spacedChamber Γ i`, for every admissible spacing `s`. -/
theorem spacedLoading_chamber {s : 𝕜} (hs0 : 0 < s) (hs : ∀ e, |Γ.weight e| < s)
    (i : Seq ν) : (spacedLoading Γ hs0 hs i).chamber = spacedChamber Γ i :=
  Subtype.ext (signs_spacedPos hs i)

/-- Two sequences give the same chamber exactly when every strand meeting a ghost is on the same
side of the strand casting it. -/
theorem spacedChamber_eq_iff (i j : Seq ν) :
    spacedChamber Γ i = spacedChamber Γ j ↔
      ∀ w : Wall Γ (Multiset.toFinsupp ν),
        (i.posOf w.src < i.posOf w.tgt ↔ j.posOf w.src < j.posOf w.tgt) := by
  constructor
  · intro h w
    have := congrArg (fun c : Chamber Γ _ => c.1 w) h
    simpa [spacedChamber] using this
  · intro h
    apply Subtype.ext
    funext w
    simp [spacedChamber, h w]

/-- The full chamber of `B_s(i)`: rank ordered, with the wall signs of `spacedChamber`. -/
theorem toFull_spacedChamber_apply_inl (i : Seq ν) (w : Wall Γ (Multiset.toFinsupp ν)) :
    (spacedChamber Γ i).toFull.1 (.inl w) = decide (i.posOf w.src < i.posOf w.tgt) := rfl

end Categorification.KLR.Seq
