/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapTraceCutWindowLoading
import Categorification.WeightedKLR.Rigidity.CupCapTraceCutStdLoading
import Categorification.WeightedKLR.Rigidity.CupCapMidCornerWords

/-!
# The cut loading and the window loading of a red-ordered loading are red-ordered

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, trace half, step L5 (membership side
conditions of the corners of ordered loadings).

For a loading `s` of `λ` with its red strands in order, the red strands left of
`p = midPos s` carry labels `< j` and those from `p` on carry labels `≥ j`
(`red_lt_of_lt_midPos`, `le_red_of_midPos_le`). Inserting a red-ordered window `w` at `p`,
with its red strands relabelled as the strands `j, j + 1` of `λ⁺`, keeps the red strands in order
(`isRedOrdered_insertSeq_midPos`). Hence the window loading `l⁺_w` and the cut loading `l` lie
in `cutOrderedLoadings` (`windowLoading_mem_cutOrderedLoadings`,
`cutLoading_mem_cutOrderedLoadings`), as `cutLoadingIndLayerEquiv` requires.

Webster's proof does not spell this out. No new hypothesis.

## Main results

* `Stendhal.CupCap.exists_eq_inr_of_sum_map`, `Stendhal.CupCap.isRedOrdered_insertSeq_midPos`.
* `Stendhal.CupCap.isRedOrdered_cutLoading`, `Stendhal.CupCap.cutLoading_mem_cutOrderedLoadings`,
  `Stendhal.CupCap.isRedOrdered_windowLoading`,
  `Stendhal.CupCap.windowLoading_mem_cutOrderedLoadings`.
-/

namespace Categorification.Stendhal.CupCap

open KLR

/-- A value of `Sum.map f g` that is `inr R` comes from some `inr r` with `R = g r`. -/
theorem exists_eq_inr_of_sum_map {α β γ δ : Type*} {f : α → γ} {g : β → δ} {x : α ⊕ β}
    {R : δ} (h : Sum.map f g x = .inr R) : ∃ r, x = .inr r ∧ R = g r := by
  rcases x with a | r
  · simp at h
  · exact ⟨r, rfl, (Sum.inr_injective h).symm⟩

section Order

variable {I : Type*} {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ} {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)

/-- **Inserting a red-ordered window at `midPos s`** into a red-ordered loading `s` gives a
red-ordered loading of `λ⁺`. -/
theorem isRedOrdered_insertSeq_midPos {s : Seq (stendhalWeight ℓ ν)} (hs : IsRedOrdered s)
    {t : Seq (stendhalWeight 2 ν₀)} (ht : IsRedOrdered t) :
    IsRedOrdered (insertSeq (j := j) (hj := hj) s (midPos j s) (midPos_le j s)
      (Seq.map (cupColour j hj) t)) := by
  intro c c' R R' hcc' hc hc'
  obtain ⟨x, rfl⟩ : ∃ x, c = Fin.cast (card_plus j hj ν ν₀).symm
      (insertPos _ _ (midPos j s) (midPos_le j s) x) :=
    ⟨(insertPos _ _ _ _).symm (Fin.cast (card_plus j hj ν ν₀) c),
      by rw [Equiv.apply_symm_apply]; exact Fin.ext rfl⟩
  obtain ⟨x', rfl⟩ : ∃ x, c' = Fin.cast (card_plus j hj ν ν₀).symm
      (insertPos _ _ (midPos j s) (midPos_le j s) x) :=
    ⟨(insertPos _ _ _ _).symm (Fin.cast (card_plus j hj ν ν₀) c'),
      by rw [Equiv.apply_symm_apply]; exact Fin.ext rfl⟩
  have hpos := Fin.lt_def.1 hcc'
  rw [Fin.lt_def]
  rcases x with a | b <;> rcases x' with a' | b'
  · rw [insertSeq_lbl_old] at hc hc'
    obtain ⟨r, hr, rfl⟩ := exists_eq_inr_of_sum_map hc
    obtain ⟨r', hr', rfl⟩ := exists_eq_inr_of_sum_map hc'
    simp only [Fin.val_cast, insertPos_inl_val] at hpos
    have haa : a < a' := by rw [Fin.lt_def]; split_ifs at hpos <;> omega
    have hrr := Fin.lt_def.1 (hs a a' r r' haa hr hr')
    simp only [oldRed, insertPos_inl_val]
    split_ifs <;> omega
  · rw [insertSeq_lbl_old] at hc
    rw [insertSeq_lbl_new, Seq.map_lbl] at hc'
    obtain ⟨r, hr, rfl⟩ := exists_eq_inr_of_sum_map hc
    obtain ⟨r', -, rfl⟩ := exists_eq_inr_of_sum_map hc'
    simp only [Fin.val_cast, insertPos_inl_val, insertPos_inr_val] at hpos
    have ha : a.val < midPos j s := by split_ifs at hpos <;> omega
    have hr0 := red_lt_of_lt_midPos (j := j) hs hr ha
    simp only [oldRed, cupRed, insertPos_inl_val, insertPos_inr_val]
    split_ifs
    omega
  · rw [insertSeq_lbl_new, Seq.map_lbl] at hc
    rw [insertSeq_lbl_old] at hc'
    obtain ⟨r, -, rfl⟩ := exists_eq_inr_of_sum_map hc
    obtain ⟨r', hr', rfl⟩ := exists_eq_inr_of_sum_map hc'
    simp only [Fin.val_cast, insertPos_inl_val, insertPos_inr_val] at hpos
    have ha : midPos j s ≤ a'.val := by split_ifs at hpos <;> omega
    have hr0 := le_red_of_midPos_le (j := j) hs hr' ha
    have := r.2
    simp only [oldRed, cupRed, insertPos_inl_val, insertPos_inr_val]
    split_ifs <;> omega
  · rw [insertSeq_lbl_new, Seq.map_lbl] at hc hc'
    obtain ⟨r, hr, rfl⟩ := exists_eq_inr_of_sum_map hc
    obtain ⟨r', hr', rfl⟩ := exists_eq_inr_of_sum_map hc'
    simp only [Fin.val_cast, insertPos_inr_val] at hpos
    have hrr := Fin.lt_def.1 (ht _ _ r r' (Fin.lt_def.2 (by simp only [Fin.val_cast]; omega))
      hr hr')
    simp only [cupRed, insertPos_inr_val]
    omega

end Order

section Loadings

variable {I : Type} {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ} {θ γ ν₀ : Multiset I}

/-- **The cut loading of a red-ordered loading is red-ordered.** -/
theorem isRedOrdered_cutLoading {s : Seq (stendhalWeight ℓ (θ + γ))} (hs : IsRedOrdered s) :
    IsRedOrdered (cutLoading j hj θ γ s) := by
  intro x x' R R' hxx hx hx'
  have hcard : Multiset.card
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ) +
        Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ)) =
      Multiset.card (stendhalWeight ℓ (θ + γ)) := by
    simp [stendhalWeight]; omega
  have hy := x.2
  have hy' := x'.2
  rw [show (cutLoading j hj θ γ s).lbl x = (cutLoading j hj θ γ s).1 x from rfl,
    cutLoading_apply s x ⟨x.val, by omega⟩ rfl] at hx
  rw [show (cutLoading j hj θ γ s).lbl x' = (cutLoading j hj θ γ s).1 x' from rfl,
    cutLoading_apply s x' ⟨x'.val, by omega⟩ rfl] at hx'
  obtain ⟨r, hr, rfl⟩ := exists_eq_inr_of_sum_map hx
  obtain ⟨r', hr', rfl⟩ := exists_eq_inr_of_sum_map hx'
  have := Fin.lt_def.1 (hs _ _ r r' (Fin.lt_def.2 (Fin.lt_def.1 hxx)) hr hr')
  rw [Fin.lt_def]
  simpa only [Fin.val_cast] using this

open Classical in
/-- **The cut loading lies in `cutOrderedLoadings`** when `s` is red-ordered. -/
theorem cutLoading_mem_cutOrderedLoadings {s : Seq (stendhalWeight ℓ (θ + γ))}
    (hs : IsRedOrdered s) :
    cutLoading j hj θ γ s ∈ cutOrderedLoadings (a := j) (r := ℓ - j) θ γ :=
  Finset.mem_filter.2 ⟨Finset.mem_univ _, isRedOrdered_cutLoading hs⟩

/-- **The window loading of red-ordered `s` and `w` is red-ordered.** -/
theorem isRedOrdered_windowLoading {s : Seq (stendhalWeight ℓ (θ + γ))} (hs : IsRedOrdered s)
    {w : Seq (stendhalWeight 2 ν₀)} (hw : IsRedOrdered w) :
    IsRedOrdered (windowLoading j hj θ γ ν₀ s w) := by
  intro x x' R R' hxx hx hx'
  have hcard := card_windowLoading_weight (I := I) (hj := hj) (θ := θ) (γ := γ) (ν₀ := ν₀)
  have hy := x.2
  have hy' := x'.2
  rw [show (windowLoading j hj θ γ ν₀ s w).lbl x = (windowLoading j hj θ γ ν₀ s w).1 x from rfl,
    windowLoading_lbl s w x ⟨x.val, by omega⟩ rfl] at hx
  rw [show (windowLoading j hj θ γ ν₀ s w).lbl x' =
      (windowLoading j hj θ γ ν₀ s w).1 x' from rfl,
    windowLoading_lbl s w x' ⟨x'.val, by omega⟩ rfl] at hx'
  obtain ⟨r, hr, rfl⟩ := exists_eq_inr_of_sum_map hx
  obtain ⟨r', hr', rfl⟩ := exists_eq_inr_of_sum_map hx'
  have := Fin.lt_def.1 (isRedOrdered_insertSeq_midPos (hj := hj) hs hw _ _ r r'
    (Fin.lt_def.2 (Fin.lt_def.1 hxx)) hr hr')
  rw [Fin.lt_def]
  simpa only [Fin.val_cast] using this

open Classical in
/-- **The window loading lies in `cutOrderedLoadings`** when `s` and `w` are red-ordered. -/
theorem windowLoading_mem_cutOrderedLoadings {s : Seq (stendhalWeight ℓ (θ + γ))}
    (hs : IsRedOrdered s) {w : Seq (stendhalWeight 2 ν₀)} (hw : IsRedOrdered w) :
    windowLoading j hj θ γ ν₀ s w ∈ cutOrderedLoadings (a := j) (r := 2 + (ℓ - j)) θ (ν₀ + γ) :=
  Finset.mem_filter.2 ⟨Finset.mem_univ _, isRedOrdered_windowLoading hs hw⟩

end Loadings

end Categorification.Stendhal.CupCap
