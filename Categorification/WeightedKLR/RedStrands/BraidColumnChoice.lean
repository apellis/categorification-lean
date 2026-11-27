/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidColumnBottomPermutation
import Categorification.WeightedKLR.RedStrands.LoadingChoiceExpansion

/-!
# The eligible indices of a braid column as choices of blocks

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, proof of
Lemma 6.11. An eligible wiring `φ` of a red-ordered loading `t` (`ProjectiveBlockIndex`) sends
the bottom blocks, each led by a red strand, to the top. Recording for each top strand the block
it comes from gives an admissible choice of the loading (`isAdmissibleChoice_blockChoice`), the
words of the bottom blocks are the words of this choice (`choiceRows_blockChoice`), and the
choice determines the block sizes and the wiring (`blockChoice_injective`).
-/

namespace Categorification.Stendhal

open KLR KLRAlgebra Equiv FirstWeight
open scoped BigOperators

variable {ℓ : ℕ}

/-! ### Positions of the blocks -/

theorem braidBlockPositions_val (n : Fin ℓ → ℕ) {m : ℕ} (hn : (∑ r, (n r + 1)) = m)
    (r : Fin ℓ) (a : Fin (n r + 1)) :
    (braidBlockPositions n hn ⟨r, a⟩).val =
      (∑ x : Fin r.val, (n (Fin.castLE r.isLt.le x) + 1)) + a.val := by
  simp only [braidBlockPositions, Equiv.trans_apply, finCongr_apply, Fin.val_cast,
    finSigmaFinEquiv_apply]

private theorem blockPrefix_le (n : Fin ℓ → ℕ) {r r' : Fin ℓ} (h : r < r') :
    (∑ x : Fin r.val, (n (Fin.castLE r.isLt.le x) + 1)) + (n r + 1) ≤
      ∑ x : Fin r'.val, (n (Fin.castLE r'.isLt.le x) + 1) := by
  let g : ℕ → ℕ := fun i => if hi : i < ℓ then n ⟨i, hi⟩ + 1 else 0
  have hs (q : Fin ℓ) : (∑ x : Fin q.val, (n (Fin.castLE q.isLt.le x) + 1)) =
      ∑ i ∈ Finset.range q.val, g i := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [g, show x.val < ℓ by omega, dite_true]
    rfl
  rw [hs, hs]
  have hr : n r + 1 = g r.val := by simp [g]
  rw [hr, ← Finset.sum_range_succ]
  exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (by rw [Fin.lt_def] at h; omega))

theorem braidBlockPositions_lt_of_lt (n : Fin ℓ → ℕ) {m : ℕ} (hn : (∑ r, (n r + 1)) = m)
    {r r' : Fin ℓ} (h : r < r') (a : Fin (n r + 1)) (b : Fin (n r' + 1)) :
    braidBlockPositions n hn ⟨r, a⟩ < braidBlockPositions n hn ⟨r', b⟩ := by
  rw [Fin.lt_def, braidBlockPositions_val, braidBlockPositions_val]
  have := blockPrefix_le n h
  omega

theorem braidBlockPositions_lt_iff (n : Fin ℓ → ℕ) {m : ℕ} (hn : (∑ r, (n r + 1)) = m)
    (r : Fin ℓ) (a b : Fin (n r + 1)) :
    braidBlockPositions n hn ⟨r, a⟩ < braidBlockPositions n hn ⟨r, b⟩ ↔ a < b := by
  rw [Fin.lt_def, braidBlockPositions_val, braidBlockPositions_val, Fin.lt_def]
  omega

/-- The positions of the blocks, block by block, are all positions in order. -/
theorem flatMap_braidBlockPositions (n : Fin ℓ → ℕ) {m : ℕ} (hn : (∑ r, (n r + 1)) = m) :
    (List.finRange ℓ).flatMap (fun r => List.ofFn fun a : Fin (n r + 1) =>
      braidBlockPositions n hn ⟨r, a⟩) = List.finRange m := by
  refine List.Pairwise.eq_of_mem_iff (r := (· < ·)) ?_ (List.pairwise_lt_finRange m) ?_
  · rw [List.pairwise_flatMap]
    refine ⟨fun r _ => List.pairwise_ofFn.2 fun a b h =>
      (braidBlockPositions_lt_iff n hn r a b).2 h, ?_⟩
    refine (List.pairwise_lt_finRange ℓ).imp fun {r r'} h x hx y hy => ?_
    obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hx
    obtain ⟨b, rfl⟩ := List.mem_ofFn.1 hy
    exact braidBlockPositions_lt_of_lt n hn h a b
  · intro x
    simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_ofFn, iff_true]
    refine ⟨((braidBlockPositions n hn).symm x).1, ((braidBlockPositions n hn).symm x).2, ?_⟩
    exact (braidBlockPositions n hn).apply_symm_apply x

/-! ### Counting the reds before a strand -/

theorem redsBefore_eq_card {J : Type*} {I : Type} : ∀ {m : ℕ} (f : Fin m → I ⊕ J) (x : ℕ),
    redsBefore f x = (Finset.univ.filter fun y : Fin m => y.val < x ∧ (f y).isRight).card
  | 0, f, x => by simp [redsBefore]
  | m + 1, f, x => by
    rw [Finset.card_filter, Fin.sum_univ_castSucc, ← Finset.card_filter]
    rcases le_or_gt x m with hx | hx
    · rw [redsBefore_castSucc f hx, redsBefore_eq_card _ x]
      have : ¬ m < x := by omega
      simp [this]
    · rw [redsBefore, List.take_of_length_le (by simp; omega), List.ofFn_succ_last,
        List.countP_append, ← List.take_of_length_le (l := List.ofFn _) (i := x) (by simp; omega)]
      rw [← redsBefore, redsBefore_eq_card _ x]
      simp only [Fin.val_castSucc, Fin.val_last, show m < x from hx, true_and]
      cases f (Fin.last m) <;> simp

variable {I : Type} [DecidableEq I] {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card μ

theorem redsBefore_lbl (t : Seq μ) (x : ℕ) :
    redsBefore t.lbl x = (Finset.univ.filter fun r : Fin ℓ => (redPos t r).val < x).card := by
  rw [redsBefore_eq_card]
  have hinj : Function.Injective (redPos t) := fun r r' h => by
    have := congrArg t.lbl h
    rw [lbl_redPos, lbl_redPos] at this
    exact Sum.inr_injective this
  rw [← Finset.card_image_of_injective _ hinj]
  congr 1
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨hy, hr⟩
    rcases hl : t.lbl y with i | r
    · rw [hl] at hr; exact absurd hr (by simp)
    · exact ⟨r, by rw [← eq_redPos hl]; exact hy, (eq_redPos hl).symm⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨hr, by rw [lbl_redPos]; rfl⟩

theorem redsBefore_redPos {t : Seq μ} (ht : IsRedOrdered t) (r : Fin ℓ) :
    redsBefore t.lbl (redPos t r) = r.val := by
  rw [redsBefore_lbl]
  have : (Finset.univ.filter fun r' : Fin ℓ => (redPos t r').val < (redPos t r).val) =
      Finset.Iio r := by
    ext r'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
    exact redPos_lt_iff ht
  rw [this, Fin.card_Iio]

theorem lt_redsBefore {t : Seq μ} (ht : IsRedOrdered t) {r : Fin ℓ} {x : ℕ}
    (h : (redPos t r).val < x) : r.val < redsBefore t.lbl x := by
  rw [redsBefore_lbl]
  have : Finset.Iic r ⊆ Finset.univ.filter fun r' : Fin ℓ => (redPos t r').val < x := by
    intro r' hr'
    simp only [Finset.mem_Iic] at hr'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hr'.lt_or_eq with h' | rfl
    · exact lt_trans (Fin.lt_def.1 ((redPos_lt_iff ht).2 h')) h
    · exact h
  have := Finset.card_le_card this
  rw [Fin.card_Iic] at this
  omega

theorem countP_ofFn_lbl (t : Seq μ) : ((List.ofFn t.lbl).countP fun a => a.isRight) = ℓ := by
  have h := redsBefore_lbl t m
  rw [redsBefore, List.take_of_length_le (by simp)] at h
  rw [h, Finset.filter_true_of_mem (fun r _ => (redPos t r).isLt), Finset.card_univ,
    Fintype.card_fin]

/-! ### The choice of an eligible wiring -/

/-- The block of the bottom from which the top strand `x` comes. -/
def blockChoice (n : Fin ℓ → ℕ) {d : ℕ} (hn : (∑ r, (n r + 1)) = d) (φ : Perm (Fin d))
    (x : Fin d) : ℕ :=
  ((braidBlockPositions n hn).symm (φ⁻¹ x)).1.val

/-- The word of the bottom block `r` of a wiring. -/
def blockRow (t : Seq μ) (n : Fin ℓ → ℕ) (hn : (∑ r, (n r + 1)) = m) (φ : Perm (Fin m))
    (r : Fin ℓ) : List I :=
  (List.ofFn fun a : Fin (n r + 1) =>
    (φ⁻¹ • t).lbl (braidBlockPositions n hn ⟨r, a⟩)).filterMap Sum.getLeft?

omit [DecidableEq I] in
theorem lbl_inv_smul (φ : Perm (Fin m)) (t : Seq μ) (a : Fin m) :
    (φ⁻¹ • t).lbl a = t.lbl (φ a) := by
  rw [BraidedStendhalAlgebra.lbl_smul, inv_inv]

private theorem perm_apply_inv {d : ℕ} (φ : Perm (Fin d)) (x : Fin d) : φ (φ⁻¹ x) = x :=
  φ.apply_symm_apply x

private theorem perm_inv_apply {d : ℕ} (φ : Perm (Fin d)) (x : Fin d) : φ⁻¹ (φ x) = x :=
  φ.symm_apply_apply x

section Eligible

variable {t : Seq (stendhalWeight ℓ ν)} {n : Fin ℓ → ℕ}
  {hn : (∑ r, (n r + 1)) = Multiset.card (stendhalWeight ℓ ν)}
  {φ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν)))}

theorem eq_zero_of_lbl_inr
    (hred : ∀ r : Fin ℓ, (φ⁻¹ • t).lbl (braidBlockPositions n hn ⟨r, 0⟩) = Sum.inr r)
    {r : Fin ℓ} {a : Fin (n r + 1)} {q : Fin ℓ}
    (h : (φ⁻¹ • t).lbl (braidBlockPositions n hn ⟨r, a⟩) = Sum.inr q) : a = 0 := by
  have := (braidBlockPositions n hn).injective (lbl_eq_inr_unique h (hred q))
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.1 this
  exact eq_of_heq h2

theorem exists_lbl_inl
    (hred : ∀ r : Fin ℓ, (φ⁻¹ • t).lbl (braidBlockPositions n hn ⟨r, 0⟩) = Sum.inr r)
    {r : Fin ℓ} {a : Fin (n r + 1)} (ha : a ≠ 0) :
    ∃ i, (φ⁻¹ • t).lbl (braidBlockPositions n hn ⟨r, a⟩) = Sum.inl i := by
  rcases h : (φ⁻¹ • t).lbl (braidBlockPositions n hn ⟨r, a⟩) with i | q
  · exact ⟨i, rfl⟩
  · exact absurd (eq_zero_of_lbl_inr hred h) ha

theorem redPos_inv_smul
    (hred : ∀ r : Fin ℓ, (φ⁻¹ • t).lbl (braidBlockPositions n hn ⟨r, 0⟩) = Sum.inr r)
    (r : Fin ℓ) : redPos (φ⁻¹ • t) r = braidBlockPositions n hn ⟨r, 0⟩ :=
  (eq_redPos (hred r)).symm

theorem apply_braidBlockPositions_zero
    (hred : ∀ r : Fin ℓ, (φ⁻¹ • t).lbl (braidBlockPositions n hn ⟨r, 0⟩) = Sum.inr r)
    (r : Fin ℓ) : φ (braidBlockPositions n hn ⟨r, 0⟩) = redPos t r :=
  eq_redPos (by rw [← lbl_inv_smul]; exact hred r)

/-- An eligible wiring is increasing on each bottom block. -/
theorem strictMono_apply_braidBlockPositions (hφ : ProjectiveBlockIndex t φ)
    (hred : ∀ r : Fin ℓ, (φ⁻¹ • t).lbl (braidBlockPositions n hn ⟨r, 0⟩) = Sum.inr r)
    (r : Fin ℓ) : StrictMono fun a : Fin (n r + 1) => φ (braidBlockPositions n hn ⟨r, a⟩) := by
  intro a b hab
  obtain ⟨i', hi'⟩ := exists_lbl_inl hred (r := r) (a := b) (fun h => by
    rw [h] at hab; exact absurd hab (Fin.not_lt_zero _))
  rcases Nat.eq_zero_or_pos a.val with ha | ha
  · have ha0 : a = 0 := Fin.ext ha
    subst ha0
    dsimp only
    rw [apply_braidBlockPositions_zero hred]
    exact hφ.only_rightwards _ _ _ hi' (by
      rw [redPos_inv_smul hred]; exact (braidBlockPositions_lt_iff n hn r 0 b).2 hab)
  · obtain ⟨i, hi⟩ := exists_lbl_inl hred (r := r) (a := a) (fun h => by
      rw [h] at ha; exact absurd ha (lt_irrefl _))
    refine hφ.bottom_block_order _ _ _ _ hi hi' ((braidBlockPositions_lt_iff n hn r a b).2 hab)
      fun q ⟨h1, h2⟩ => ?_
    rw [redPos_inv_smul hred] at h1 h2
    rcases lt_trichotomy q r with hq | rfl | hq
    · exact absurd h1 (lt_asymm (braidBlockPositions_lt_of_lt n hn hq 0 a))
    · exact absurd ((braidBlockPositions_lt_iff n hn q a 0).1 h1) (Fin.not_lt_zero _)
    · exact absurd h2 (lt_asymm (braidBlockPositions_lt_of_lt n hn hq b 0))

/-- **The top strands coming from a bottom block** are its images, in order. -/
theorem filter_blockChoice (hφ : ProjectiveBlockIndex t φ)
    (hred : ∀ r : Fin ℓ, (φ⁻¹ • t).lbl (braidBlockPositions n hn ⟨r, 0⟩) = Sum.inr r)
    (r : Fin ℓ) :
    (List.finRange m).filter (fun x => blockChoice n hn φ x = r.val) =
      List.ofFn fun a : Fin (n r + 1) => φ (braidBlockPositions n hn ⟨r, a⟩) := by
  refine List.Pairwise.eq_of_mem_iff (r := (· < ·)) ((List.pairwise_lt_finRange m).filter _)
    (List.pairwise_ofFn.2 fun a b h => strictMono_apply_braidBlockPositions hφ hred r h)
    fun x => ?_
  simp only [List.mem_filter, List.mem_finRange, true_and, List.mem_ofFn]
  constructor
  · intro h
    replace h := of_decide_eq_true h
    rw [blockChoice] at h
    obtain ⟨⟨q, a⟩, hq⟩ : ∃ p, (braidBlockPositions n hn).symm (φ⁻¹ x) = p := ⟨_, rfl⟩
    rw [hq] at h
    obtain rfl : q = r := Fin.ext h
    refine ⟨a, ?_⟩
    rw [← hq, Equiv.apply_symm_apply, perm_apply_inv]
  · rintro ⟨a, rfl⟩
    refine decide_eq_true ?_
    rw [blockChoice, perm_inv_apply, Equiv.symm_apply_apply]

/-- **An eligible wiring gives an admissible choice.** -/
theorem isAdmissibleChoice_blockChoice (hφ : ProjectiveBlockIndex t φ)
    (hred : ∀ r : Fin ℓ, (φ⁻¹ • t).lbl (braidBlockPositions n hn ⟨r, 0⟩) = Sum.inr r)
    (ht : IsRedOrdered t) : IsAdmissibleChoice t.lbl (blockChoice n hn φ) where
  black x hx := by
    obtain ⟨⟨r, a⟩, hq⟩ : ∃ p, (braidBlockPositions n hn).symm (φ⁻¹ x) = p := ⟨_, rfl⟩
    have hx' : φ⁻¹ x = braidBlockPositions n hn ⟨r, a⟩ := by rw [← hq, Equiv.apply_symm_apply]
    rw [blockChoice, hq]
    rcases hl : t.lbl x with i | q
    · have hb : (φ⁻¹ • t).lbl (φ⁻¹ x) = Sum.inl i := by
        rw [lbl_inv_smul, perm_apply_inv, hl]
      have ha : a ≠ 0 := by
        rintro rfl
        rw [hx', hred] at hb
        exact Sum.inr_ne_inl hb
      apply lt_redsBefore ht
      have := hφ.only_rightwards _ _ r hb (by
        rw [redPos_inv_smul hred, hx']
        exact (braidBlockPositions_lt_iff n hn r 0 a).2 (Fin.pos_iff_ne_zero.2 ha))
      rw [perm_apply_inv] at this
      exact this
    · rw [hl] at hx; simp at hx
  red x hx := by
    rcases hl : t.lbl x with i | q
    · rw [hl] at hx; simp at hx
    · have hb : (φ⁻¹ • t).lbl (φ⁻¹ x) = Sum.inr q := by
        rw [lbl_inv_smul, perm_apply_inv, hl]
      have h1 : φ⁻¹ x = braidBlockPositions n hn ⟨q, 0⟩ := lbl_eq_inr_unique hb (hred q)
      rw [blockChoice, h1, Equiv.symm_apply_apply, eq_redPos hl, redsBefore_redPos ht]

/-- **The words of the choice of an eligible wiring are the words of its bottom blocks.** -/
theorem choiceRows_blockChoice (hφ : ProjectiveBlockIndex t φ)
    (hred : ∀ r : Fin ℓ, (φ⁻¹ • t).lbl (braidBlockPositions n hn ⟨r, 0⟩) = Sum.inr r)
    (ht : IsRedOrdered t) (r : Fin ℓ) :
    choiceRows (List.ofFn t.lbl) (List.ofFn (blockChoice n hn φ)).reverse ℓ r =
      blockRow t n hn φ r := by
  rw [choiceRows_ofFn_of_eq _ _ (isAdmissibleChoice_blockChoice hφ hred ht) (countP_ofFn_lbl t)]
  have : (List.finRange m).filterMap (fun x => choiceLetter r.val (t.lbl x, blockChoice n hn φ x))
      = ((List.finRange m).filter (fun x => blockChoice n hn φ x = r.val)).filterMap
          fun x => (t.lbl x).getLeft? := by
    rw [List.filterMap_filter]
    refine List.filterMap_congr fun x _ => ?_
    rcases t.lbl x with i | q
    · by_cases h : blockChoice n hn φ x = r.val <;> simp [choiceLetter, h]
    · simp [choiceLetter]
  rw [this, filter_blockChoice hφ hred, blockRow]
  simp only [lbl_inv_smul]
  show _ = List.filterMap Sum.getLeft?
    (List.ofFn (t.lbl ∘ fun a : Fin (n r + 1) => φ (braidBlockPositions n hn ⟨r, a⟩)))
  rw [← List.map_ofFn, List.filterMap_map]
  rfl

/-- **The choice of an eligible wiring determines the blocks and the wiring.** -/
theorem blockChoice_injective {n n' : Fin ℓ → ℕ}
    {hn : (∑ r, (n r + 1)) = Multiset.card (stendhalWeight ℓ ν)}
    {hn' : (∑ r, (n' r + 1)) = Multiset.card (stendhalWeight ℓ ν)}
    {φ φ' : Perm (Fin (Multiset.card (stendhalWeight ℓ ν)))}
    (hφ : ProjectiveBlockIndex t φ)
    (hred : ∀ r : Fin ℓ, (φ⁻¹ • t).lbl (braidBlockPositions n hn ⟨r, 0⟩) = Sum.inr r)
    (hφ' : ProjectiveBlockIndex t φ')
    (hred' : ∀ r : Fin ℓ, (φ'⁻¹ • t).lbl (braidBlockPositions n' hn' ⟨r, 0⟩) = Sum.inr r)
    (h : blockChoice n hn φ = blockChoice n' hn' φ') : n = n' ∧ φ = φ' := by
  have hl (r : Fin ℓ) : (List.ofFn fun a : Fin (n r + 1) => φ (braidBlockPositions n hn ⟨r, a⟩))
      = List.ofFn fun a : Fin (n' r + 1) => φ' (braidBlockPositions n' hn' ⟨r, a⟩) := by
    rw [← filter_blockChoice hφ hred, ← filter_blockChoice hφ' hred', h]
  have hnn : n = n' := funext fun r => by
    have := congrArg List.length (hl r)
    simpa using this
  subst hnn
  refine ⟨rfl, Equiv.ext fun x => ?_⟩
  obtain ⟨⟨r, a⟩, rfl⟩ : ∃ p, braidBlockPositions n hn p = x :=
    ⟨_, Equiv.apply_symm_apply _ _⟩
  exact congrFun (List.ofFn_injective (hl r)) a

end Eligible

end Categorification.Stendhal
