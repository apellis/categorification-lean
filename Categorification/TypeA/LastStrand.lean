/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TypeA.DoubleCoset
import Categorification.TypeA.NormalForm

/-!
# Shuffles sorted by the block of their last strand

Combinatorics for B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v3, §5.1, proof of **Proposition 5.5**, and for the restriction of an induced
KLR module to its last strand (Khovanov–Lauda I, arXiv:0803.4121v2, §2.6, Proposition 2.18, for
the two double cosets of `(S_{m-1} × S_1) \ S_m / (S_n × S_{n'})`).

Let `n + n' = m = m₀ + 1`. A shuffle `u` for the blocks `(n, n')` (`IsShuffle h u`: `u⁻¹` is
increasing on each block) sends the last position `m₀` either to the last position of the first
block or to the last position `m₀` of the second block.

* If `n' = n₀' + 1`, the shuffles with `u m₀ = m₀` are exactly the permutations `v × 1`
  (`extPerm`), for `v` a shuffle for the blocks `(n, n₀')` of `m₀`.
* If `n = n₀ + 1`, the shuffles with `u m₀ = n₀` are exactly the permutations `d⁻¹ (v × 1)` for
  `v` a shuffle for the blocks `(n₀, n')` of `m₀`, where `d` is the minimal double coset
  representative of `(S_{m₀} × S_1) \ S_m / (S_n × S_{n'})` with `n'` crossing strands (the cycle
  `n₀ ↦ m₀ ↦ m₀ - 1 ↦ ⋯ ↦ n₀`).

## Main definitions and results

* `TypeA.extPerm` : `v ↦ v × 1`.
* `TypeA.lastShuffleEquiv` : `Shuffle hB ⊕ Shuffle hA ≃ Shuffle h`.
* `TypeA.isReduced_canWord_ext`, `TypeA.isReduced_topWord` : reduced words for the two kinds of
  shuffles, `canWord v` and `(canWord d)ʳᵉᵛ ++ canWord v`.
-/

namespace Categorification.TypeA

open Equiv

variable {n n' m m₀ : ℕ} (h : n + n' = m) (hm : m₀ + 1 = m)

/-! ### Extension by a fixed last strand -/

/-- `v ↦ v × 1 ∈ S_m`, fixing the last position. -/
def extPerm (v : Perm (Fin m₀)) : Perm (Fin m) := blockPerm hm v 1

/-- The last position `m₀` of `Fin m`. -/
def lastPos : Fin m := ⟨m₀, hm ▸ Nat.lt_succ_self m₀⟩

@[simp] theorem lastPos_val : (lastPos hm).val = m₀ := rfl

theorem extPerm_val (v : Perm (Fin m₀)) (p : Fin m) :
    (extPerm hm v p).val = if hp : p.val < m₀ then (v ⟨p.val, hp⟩).val else p.val := by
  split_ifs with hp
  · have e : p = blockEquiv hm (Sum.inl ⟨p.val, hp⟩) := Fin.ext rfl
    have := congrArg Fin.val (blockPerm_inl hm v 1 ⟨p.val, hp⟩)
    rw [← e, blockEquiv_inl_val] at this
    exact this
  · have e : p = blockEquiv hm (Sum.inr ⟨0, by omega⟩) := by
      ext; simp only [blockEquiv_inr_val]; omega
    rw [extPerm, e, blockPerm_inr, Perm.one_apply]

theorem extPerm_inv (v : Perm (Fin m₀)) : (extPerm hm v)⁻¹ = extPerm hm v⁻¹ := by
  rw [extPerm, extPerm, blockPerm_inv, inv_one]

theorem extPerm_mul (v v' : Perm (Fin m₀)) : extPerm hm v * extPerm hm v' = extPerm hm (v * v') := by
  rw [extPerm, extPerm, extPerm, blockPerm_mul, one_mul]

theorem extPerm_one : extPerm hm (1 : Perm (Fin m₀)) = 1 := blockPerm_one hm

theorem extPerm_injective : Function.Injective (extPerm (m := m) hm) := fun _ _ he =>
  (blockPerm_injective hm he).1

theorem extPerm_last (v : Perm (Fin m₀)) : extPerm hm v (lastPos hm) = lastPos hm := by
  ext; rw [extPerm_val]; simp

/-- A permutation fixing the last position is an extension. -/
theorem exists_extPerm_eq {w : Perm (Fin m)} (hw : w (lastPos hm) = lastPos hm) :
    ∃ v : Perm (Fin m₀), extPerm hm v = w := by
  have hlt : ∀ x : Fin m₀, (w ⟨x.val, by omega⟩).val < m₀ := by
    intro x
    have hne : w ⟨x.val, by omega⟩ ≠ w (lastPos hm) := fun he => by
      have := congrArg Fin.val (w.injective he); simp at this; omega
    rw [hw] at hne
    have := (w ⟨x.val, by omega⟩).2
    have : (w ⟨x.val, by omega⟩).val ≠ m₀ := fun he => hne (Fin.ext he)
    omega
  let f : Fin m₀ → Fin m₀ := fun x => ⟨(w ⟨x.val, by omega⟩).val, hlt x⟩
  have hf : Function.Injective f := fun x y he => by
    have he' : w ⟨x.val, by omega⟩ = w ⟨y.val, by omega⟩ :=
      Fin.ext (congrArg Fin.val he :)
    exact Fin.ext (by simpa using congrArg Fin.val (w.injective he'))
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf), ?_⟩
  ext p
  rw [extPerm_val]
  split_ifs with hp
  · rfl
  · have hp' : p = lastPos hm := Fin.ext (by have := p.2; simp only [lastPos_val]; omega)
    rw [hp', hw]

/-! ### The last strand of a shuffle -/

/-- The last position of a shuffle comes from the last position of one of the two blocks. -/
theorem IsShuffle.val_last {u : Perm (Fin m)} (hu : IsShuffle h u) :
    (u (lastPos hm)).val + 1 = n ∨ (u (lastPos hm)).val = m₀ := by
  set x := u (lastPos hm)
  have hx : u⁻¹ x = lastPos hm := by simp [x]
  have hmax : ∀ y : Fin m, u⁻¹ y ≤ u⁻¹ x := fun y => by
    rw [hx]; exact Fin.mk_le_mk.2 (by have := (u⁻¹ y).2; omega)
  by_cases hxn : x.val < n
  · left
    by_contra hne
    have hlt : x.val + 1 < n := by omega
    have := (isShuffle_iff_forall h).1 hu x.val (by omega) (Or.inl hlt)
    exact absurd (hmax ⟨x.val + 1, by omega⟩) (not_le.2 this)
  · right
    by_contra hne
    have hlt : x.val + 1 < m := by have := x.2; omega
    have := (isShuffle_iff_forall h).1 hu x.val hlt (Or.inr (by omega))
    exact absurd (hmax ⟨x.val + 1, hlt⟩) (not_le.2 this)

section Bottom

variable {n₀' : ℕ} (hB : n + n₀' = m₀)
include hB

theorem isShuffle_extPerm_iff (v : Perm (Fin m₀)) :
    IsShuffle h (extPerm hm v) ↔ IsShuffle hB v := by
  rw [isShuffle_iff_forall h, isShuffle_iff_forall hB, extPerm_inv]
  constructor
  · intro H j hj hb
    have := H j (by omega) (by omega)
    rw [Fin.lt_def, extPerm_val, extPerm_val] at this
    simp only [show j < m₀ by omega, show j + 1 < m₀ by omega,
      ↓reduceDIte] at this
    exact this
  · intro H j hj hb
    rw [Fin.lt_def, extPerm_val, extPerm_val]
    have hj0 : j < m₀ := by omega
    by_cases hj' : j + 1 < m₀
    · simp only [hj0, hj', ↓reduceDIte]
      exact H j hj' (by omega)
    · simp only [hj0, hj', ↓reduceDIte]
      have := (v⁻¹ ⟨j, hj0⟩).2
      omega

/-- The shuffles whose last strand comes from the second block. -/
def extShuffle (v : Shuffle hB) : Shuffle h :=
  ⟨extPerm hm v.1, (isShuffle_extPerm_iff h hm hB v.1).2 v.2⟩

theorem extShuffle_val (v : Shuffle hB) : (extShuffle h hm hB v).1 = extPerm hm v.1 := rfl

theorem extShuffle_injective : Function.Injective (extShuffle h hm hB) := fun _ _ he =>
  Subtype.ext (extPerm_injective hm (congrArg Subtype.val he))

theorem exists_extShuffle_eq {u : Shuffle h} (hu : u.1 (lastPos hm) = lastPos hm) :
    ∃ v, extShuffle h hm hB v = u := by
  obtain ⟨v, hv⟩ := exists_extPerm_eq hm hu
  refine ⟨⟨v, (isShuffle_extPerm_iff h hm hB v).1 (hv ▸ u.2)⟩, Subtype.ext hv⟩

end Bottom

section Top

variable {n₀ : ℕ} (hA : n₀ + n' = m₀) {d : Perm (Fin m)}
  (hd : IsDoubleShuffle hm h d) (hc : crossCount m₀ n d = n')
include h hm hA hd hc

omit hm hd in
/-- All strands of the second bottom block of `d` end below the last top position. -/
theorem dval_lt_of_le (p : Fin m) (hp : n ≤ p.val) : (d p).val < m₀ := by
  by_contra hge
  have hnm : n < m := lt_of_le_of_lt hp p.2
  have hS : (Finset.univ.filter fun q : Fin m => n ≤ q.val ∧ (d q).val < m₀) ⊆
      (Finset.Ici (⟨n, hnm⟩ : Fin m)).erase p := by
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    simp only [Finset.mem_erase, Finset.mem_Ici, Fin.le_def]
    exact ⟨fun he => by subst he; omega, hq.1⟩
  have hcard := Finset.card_le_card hS
  rw [Finset.card_erase_of_mem (by simp only [Finset.mem_Ici, Fin.le_def]; exact hp),
    Fin.card_Ici] at hcard
  have hc' : (Finset.univ.filter fun q : Fin m => n ≤ q.val ∧ (d q).val < m₀).card = n' := hc
  simp only at hcard
  omega

/-- The minimal double coset representative with `n'` crossings: `n₀ ↦ m₀`, the positions
`(n₀, m₀]` move down by one, the others are fixed. -/
theorem dval (p : Fin m) :
    (d p).val = if p.val < n₀ then p.val else if p.val = n₀ then m₀ else p.val - 1 := by
  have key : ∀ q : Fin m, q.val < n₀ → (d q).val = q.val := fun q hq => by
    obtain ⟨h1, h2, -, -⟩ := hd.val_eq hm h q
    rw [hc] at h2
    by_cases hlt : (d q).val < m₀
    · exact h1 (by omega) hlt
    · have := h2 (by omega) (by omega); have := (d q).2; omega
  have high : ∀ q : Fin m, n ≤ q.val → (d q).val = q.val - 1 := fun q hq => by
    obtain ⟨-, -, -, h4⟩ := hd.val_eq hm h q
    rw [hc] at h4
    have := h4 hq (dval_lt_of_le h hA hc q hq)
    omega
  split_ifs with h1 h2
  · exact key p h1
  · -- the value `m₀` is attained, and only possibly at `n₀`
    obtain ⟨-, h2', -, -⟩ := hd.val_eq hm h p
    rw [hc] at h2'
    by_contra hne
    have hlt : (d p).val < m₀ := by
      by_contra hge
      exact hne (by have := h2' (by omega) (by omega); omega)
    obtain ⟨-, -⟩ := And.intro hlt hne
    set q := d⁻¹ (lastPos hm) with hq
    have hdq : (d q).val = m₀ := by simp [q]
    rcases lt_trichotomy q.val n₀ with hq' | hq' | hq'
    · have := key q hq'; omega
    · have hqp : q = p := Fin.ext (by omega)
      rw [hqp] at hdq; omega
    · have := dval_lt_of_le h hA hc q (by omega); omega
  · exact high p (by omega)

theorem d_top : d ⟨n₀, by omega⟩ = lastPos hm := by
  ext; rw [dval h hm hA hd hc]; simp

theorem isShuffle_topPerm (v : Perm (Fin m₀)) (hv : IsShuffle hA v) :
    IsShuffle h (d⁻¹ * extPerm hm v) := by
  rw [isShuffle_iff_forall h]
  intro j hj hb
  rw [mul_inv_rev, inv_inv, extPerm_inv, Perm.mul_apply, Perm.mul_apply, Fin.lt_def,
    extPerm_val, extPerm_val, dval h hm hA hd hc, dval h hm hA hd hc]
  have hv' := (isShuffle_iff_forall hA).1 hv
  rcases hb with hb | hb
  · have h1 : j < n₀ := by omega
    simp only [h1, ite_true]
    by_cases h2 : j + 1 < n₀
    · simp only [h2, ite_true, dite_eq_left (show j < m₀ by omega), dite_eq_left (show j + 1 < m₀ by omega)]
      exact hv' j (by omega) (Or.inl h2)
    · have h3 : j + 1 = n₀ := by omega
      simp only [ite_false, h3, ite_true, dite_eq_left (show j < m₀ by omega), lt_irrefl, dite_eq_right,
        not_false_eq_true]
      exact (v⁻¹ _).2
  · have h1 : ¬ j < n₀ := by omega
    have h2 : j ≠ n₀ := by omega
    have h3 : ¬ j + 1 < n₀ := by omega
    have h4 : j + 1 ≠ n₀ := by omega
    simp only [h1, h2, h3, h4, ite_false, dite_eq_left (show j - 1 < m₀ by omega),
      dite_eq_left (show j + 1 - 1 < m₀ by omega)]
    have := hv' (j - 1) (by omega) (Or.inr (by omega))
    simpa [show j - 1 + 1 = j + 1 - 1 by omega] using this

/-- The shuffles whose last strand comes from the first block. -/
def topShuffle (v : Shuffle hA) : Shuffle h :=
  ⟨d⁻¹ * extPerm hm v.1, isShuffle_topPerm h hm hA hd hc v.1 v.2⟩

theorem topShuffle_val (v : Shuffle hA) :
    (topShuffle h hm hA hd hc v).1 = d⁻¹ * extPerm hm v.1 := rfl

theorem topShuffle_last (v : Shuffle hA) :
    (topShuffle h hm hA hd hc v).1 (lastPos hm) = ⟨n₀, by omega⟩ := by
  rw [topShuffle_val, Perm.mul_apply, extPerm_last, Perm.inv_eq_iff_eq,
    d_top h hm hA hd hc]

theorem topShuffle_injective : Function.Injective (topShuffle h hm hA hd hc) := fun _ _ he =>
  Subtype.ext (extPerm_injective hm (mul_left_cancel (congrArg Subtype.val he)))

theorem exists_topShuffle_eq {u : Shuffle h} (hu : u.1 (lastPos hm) = ⟨n₀, by omega⟩) :
    ∃ v, topShuffle h hm hA hd hc v = u := by
  have hw : (d * u.1) (lastPos hm) = lastPos hm := by
    rw [Perm.mul_apply, hu, d_top h hm hA hd hc]
  obtain ⟨v, hv⟩ := exists_extPerm_eq hm hw
  have hv' : d⁻¹ * extPerm hm v = u.1 := by rw [hv, inv_mul_cancel_left]
  have hsh : IsShuffle hA v := by
    rw [isShuffle_iff_forall hA]
    intro j hj hb
    have H := (isShuffle_iff_forall h).1 u.2
    rw [← hv', mul_inv_rev, inv_inv, extPerm_inv] at H
    rcases hb with hb | hb
    · have := H j (by omega) (Or.inl (by omega))
      rw [Perm.mul_apply, Perm.mul_apply, Fin.lt_def, extPerm_val, extPerm_val,
        dval h hm hA hd hc, dval h hm hA hd hc] at this
      simp only [show j < n₀ by omega, show j + 1 < n₀ by omega, ite_true,
        dite_eq_left (show j < m₀ by omega), dite_eq_left (show j + 1 < m₀ by omega)] at this
      exact this
    · have := H (j + 1) (by omega) (Or.inr (by omega))
      rw [Perm.mul_apply, Perm.mul_apply, Fin.lt_def, extPerm_val, extPerm_val,
        dval h hm hA hd hc, dval h hm hA hd hc] at this
      simp only [show ¬ j + 1 < n₀ by omega, show j + 1 ≠ n₀ by omega,
        show ¬ j + 1 + 1 < n₀ by omega, show j + 1 + 1 ≠ n₀ by omega, ite_false,
        dite_eq_left (show j + 1 - 1 < m₀ by omega), dite_eq_left (show j + 1 + 1 - 1 < m₀ by omega)] at this
      simpa using this
  exact ⟨⟨v, hsh⟩, Subtype.ext hv'⟩

end Top

/-! ### The decomposition -/

section Equiv

variable {n₀ n₀' : ℕ} (hB : n + n₀' = m₀) (hA : n₀ + n' = m₀)
  {d : Perm (Fin m)} (hd : IsDoubleShuffle hm h d) (hc : crossCount m₀ n d = n')
include hB hA hd hc

theorem extShuffle_ne_topShuffle (v : Shuffle hB) (v' : Shuffle hA) :
    extShuffle h hm hB v ≠ topShuffle h hm hA hd hc v' := fun he => by
  have := congrArg (fun u : Shuffle h => (u.1 (lastPos hm)).val) he
  simp only [extShuffle_val, extPerm_last, topShuffle_last h hm hA hd hc, lastPos_val] at this
  omega

/-- **The shuffles for `(n, n')`, sorted by the block of their last strand.** -/
noncomputable def lastShuffleEquiv : Shuffle hB ⊕ Shuffle hA ≃ Shuffle h :=
  Equiv.ofBijective (Sum.elim (extShuffle h hm hB) (topShuffle h hm hA hd hc)) <| by
    refine ⟨?_, fun u => ?_⟩
    · rintro (v | v) (w | w) he
      · exact congrArg Sum.inl (extShuffle_injective h hm hB he)
      · exact absurd he (extShuffle_ne_topShuffle h hm hB hA hd hc v w)
      · exact absurd he.symm (extShuffle_ne_topShuffle h hm hB hA hd hc w v)
      · exact congrArg Sum.inr (topShuffle_injective h hm hA hd hc he)
    · rcases u.2.val_last h hm with hl | hl
      · obtain ⟨v, hv⟩ := exists_topShuffle_eq h hm hA hd hc (u := u)
          (Fin.ext (by simp only; omega))
        exact ⟨Sum.inr v, hv⟩
      · obtain ⟨v, hv⟩ := exists_extShuffle_eq h hm hB (u := u) (Fin.ext hl)
        exact ⟨Sum.inl v, hv⟩

@[simp] theorem lastShuffleEquiv_inl (v : Shuffle hB) :
    lastShuffleEquiv h hm hB hA hd hc (Sum.inl v) = extShuffle h hm hB v := rfl

@[simp] theorem lastShuffleEquiv_inr (v : Shuffle hA) :
    lastShuffleEquiv h hm hB hA hd hc (Sum.inr v) = topShuffle h hm hA hd hc v := rfl

end Equiv

/-! ### Reduced words -/

include hm in
theorem isReduced_canWord_ext (v : Perm (Fin m₀)) : IsReduced m (canWord m₀ v) := by
  refine ⟨(validWord_canWord m₀ v).of_le (by omega), ?_⟩
  rw [wordProd_eq_blockPerm_left hm (validWord_canWord m₀ v), wordProd_canWord,
    length_blockPerm, length_one, add_zero, length_canWord]

theorem wordProd_canWord_ext (v : Perm (Fin m₀)) : wordProd m (canWord m₀ v) = extPerm hm v := by
  rw [wordProd_eq_blockPerm_left hm (validWord_canWord m₀ v), wordProd_canWord, extPerm]

theorem wordProd_topWord (d : Perm (Fin m)) (v : Perm (Fin m₀)) :
    wordProd m ((canWord m d).reverse ++ canWord m₀ v) = d⁻¹ * extPerm hm v := by
  rw [wordProd_append, wordProd_reverse, wordProd_canWord, wordProd_canWord_ext]

include hm in
theorem isReduced_topWord {d : Perm (Fin m)} (hd : IsShuffle hm d) (v : Perm (Fin m₀)) :
    IsReduced m ((canWord m d).reverse ++ canWord m₀ v) := by
  refine ⟨validWord_append.2 ⟨validWord_reverse.2 (validWord_canWord m d),
    (validWord_canWord m₀ v).of_le (by omega)⟩, ?_⟩
  rw [wordProd_topWord hm, ← length_inv, mul_inv_rev, inv_inv, extPerm_inv, extPerm,
    length_blockPerm_mul hm _ _ hd, length_one, add_zero, List.length_append, List.length_reverse,
    length_canWord, length_canWord, length_inv, add_comm]

end Categorification.TypeA
