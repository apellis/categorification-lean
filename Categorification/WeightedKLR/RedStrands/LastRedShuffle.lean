/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Crystal.Kleshchev
import Categorification.WeightedKLR.RedStrands.Stendhal

/-!
# Shuffles of a final one-red factor

In the standardization construction in Webster, arXiv:1309.3796v2, §5,
shuffling two nonviolating words keeps the first strand red. When the final
factor starts with its red strand, its furthest possible position singles
out the identity shuffle.
-/

namespace Categorification.Stendhal

open KLR TypeA Equiv

variable {n r m : ℕ} (h : n + r = m) (u : Shuffle h)

/-- If the first strand of the second group reaches position `n`, both
groups stay in their original positions. -/
theorem lastRedShuffle_eq_one (hr : 0 < r)
    (hc : n ≤ (u.1⁻¹ (blockEquiv h (.inr ⟨0, hr⟩))).val) : u.1 = 1 := by
  let f (j : Fin r) := u.1⁻¹ (blockEquiv h (.inr j))
  have hf : StrictMono f := u.2.2
  have hbound (j : Fin r) : n ≤ (f j).val := hc.trans (hf.monotone (show (⟨0,hr⟩ : Fin r) ≤ j from Nat.zero_le _))
  let g (j : Fin r) : Fin r := ⟨(f j).val - n, by have := (f j).isLt; omega⟩
  have hg : StrictMono g := by
    intro x y hxy
    have hlt := (hf hxy : (f x).val < (f y).val)
    change (f x).val - n < (f y).val - n
    have := hbound x
    omega
  have hfixR (j : Fin r) : f j = blockEquiv h (.inr j) := by
    have he := congrArg Fin.val (congrFun hg.eq_id j)
    change (f j).val - n = j.val at he
    apply Fin.ext
    rw [blockEquiv_inr_val]
    have := hbound j
    omega
  let l (j : Fin n) := u.1⁻¹ (blockEquiv h (.inl j))
  have hlb (j : Fin n) : (l j).val < n := by
    by_contra! hj
    let t : Fin r := ⟨(l j).val - n, by have := (l j).isLt; omega⟩
    have hh : l j = f t := by
      rw [hfixR]
      apply Fin.ext
      rw [blockEquiv_inr_val]
      change (l j).val = n + ((l j).val - n)
      omega
    have := (blockEquiv h).injective (u.1⁻¹.injective hh)
    contradiction
  let z (j : Fin n) : Fin n := ⟨(l j).val, hlb j⟩
  have hz : StrictMono z := fun _ _ hxy => u.2.1 hxy
  have hinv : u.1⁻¹ = 1 := by
    ext a
    obtain ⟨b, rfl⟩ := (blockEquiv h).surjective a
    cases b with
    | inl j =>
      change (l j).val = j.val
      exact congrArg Fin.val (congrFun hz.eq_id j)
    | inr j => exact congrArg Fin.val (hfixR j)
  rw [← inv_inv u.1, hinv, inv_one]

/-- The first place in a shuffle is occupied by the first strand of one of
the input groups. This includes an empty first or second group. -/
theorem shuffle_first (hm : 0 < m) :
    (∃ hn : 0 < n, u.1 ⟨0, hm⟩ = blockEquiv h (.inl ⟨0, hn⟩)) ∨
    ∃ hr : 0 < r, u.1 ⟨0, hm⟩ = blockEquiv h (.inr ⟨0, hr⟩) := by
  obtain ⟨x, hx⟩ := (blockEquiv h).surjective (u.1 ⟨0,hm⟩)
  cases x with
  | inl j =>
    have he : u.1⁻¹ (blockEquiv h (.inl j)) = ⟨0,hm⟩ := by rw [hx]; exact u.1.symm_apply_apply _
    have hb := strictMono_fin_ge u.2.1 j
    simp only [he, Fin.val_mk, Nat.le_zero] at hb
    exact Or.inl ⟨by omega, hx.symm.trans (congrArg (fun a => blockEquiv h (.inl a)) (Fin.ext hb))⟩
  | inr j =>
    have he : u.1⁻¹ (blockEquiv h (.inr j)) = ⟨0,hm⟩ := by rw [hx]; exact u.1.symm_apply_apply _
    have hb := strictMono_fin_ge u.2.2 j
    simp only [he, Fin.val_mk, Nat.le_zero] at hb
    exact Or.inr ⟨by omega, hx.symm.trans (congrArg (fun a => blockEquiv h (.inr a)) (Fin.ext hb))⟩

private theorem sadj_lt_of_not_pair {j : ℕ} (hj : j + 1 < m) {a b : Fin m}
    (hab : a < b) (hne : ¬ (a.val = j ∧ b.val = j+1)) :
    sadj m j a < sadj m j b := by
  change a.val < b.val at hab
  rw [Fin.lt_def, sadj_val_of_lt hj, sadj_val_of_lt hj]
  simp only [swapNat]
  split_ifs <;> omega

/-- Exchanging two consecutive letters that come from the second and then
the first input group preserves the shuffle and drops its length by one. -/
theorem shuffle_right_descent {j : ℕ} (hj : j + 1 < m)
    {x : Fin n} {y : Fin r} (hr : u.1 ⟨j, by omega⟩ = blockEquiv h (.inr y))
    (hl : u.1 ⟨j+1,hj⟩ = blockEquiv h (.inl x)) :
    IsShuffle h (u.1 * sadj m j) ∧ length m (u.1 * sadj m j) + 1 = length m u.1 := by
  refine ⟨?_, length_mul_sadj_of_gt hj (by rw [hl, hr]; exact blockEquiv_inl_lt_inr h x y)⟩
  constructor
  · intro a b hab
    simp only [mul_inv_rev, sadj_inv, Perm.mul_apply]
    apply sadj_lt_of_not_pair hj (u.2.1 hab)
    rintro ⟨ha, _⟩
    have he : u.1⁻¹ (blockEquiv h (.inl a)) = ⟨j, by omega⟩ := Fin.ext ha
    have hh := congrArg u.1 he
    rw [show ∀ v, u.1 (u.1⁻¹ v) = v from u.1.apply_symm_apply, hr] at hh
    cases (blockEquiv h).injective hh
  · intro a b hab
    simp only [mul_inv_rev, sadj_inv, Perm.mul_apply]
    apply sadj_lt_of_not_pair hj (u.2.2 hab)
    rintro ⟨_, hb⟩
    have he : u.1⁻¹ (blockEquiv h (.inr b)) = ⟨j+1,hj⟩ := Fin.ext hb
    have hh := congrArg u.1 he
    rw [show ∀ v, u.1 (u.1⁻¹ v) = v from u.1.apply_symm_apply, hl] at hh
    cases (blockEquiv h).injective hh

/-- A shuffle summand of two nonviolating inputs has no black strand at the
extreme left, before imposing the order on red strands. -/
theorem shuffle_not_violated {I : Type*} {ℓ : ℕ} {α β : Multiset (I ⊕ Fin ℓ)}
    {s : Seq (α+β)} (a : Seq α) (b : Seq β) (ha : ¬ IsViolated a) (hb : ¬ IsViolated b)
    (u : Shuffle (Seq.card_add' α β)) (hu : u.1 • s = a.append b) : ¬ IsViolated s := by
  rintro ⟨hn, hblack⟩
  have hlabel : s.lbl ⟨0,hn⟩ = (a.append b).lbl (u.1 ⟨0,hn⟩) := by
    rw [← hu]
    change s.1 _ = s.1 (u.1.symm (u.1 _))
    rw [Equiv.symm_apply_apply]
  rcases shuffle_first (Seq.card_add' α β) u hn with ⟨hα, hx⟩ | ⟨hβ, hx⟩
  · apply ha
    refine ⟨hα, ?_⟩
    change u.1 ⟨0,hn⟩ = Seq.posL β ⟨0,hα⟩ at hx
    rw [hlabel, hx] at hblack
    change ((a.append b).1 (Seq.posL β ⟨0,hα⟩)).isLeft = true at hblack
    rw [Seq.append_posL] at hblack
    exact hblack
  · apply hb
    refine ⟨hβ, ?_⟩
    change u.1 ⟨0,hn⟩ = Seq.posR α ⟨0,hβ⟩ at hx
    rw [hlabel, hx] at hblack
    change ((a.append b).1 (Seq.posR α ⟨0,hβ⟩)).isLeft = true at hblack
    rw [Seq.append_posR] at hblack
    exact hblack

end Categorification.Stendhal
