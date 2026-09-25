/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TypeA.Inversions
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Maximal parabolic subgroups `S_n × S_{n'} ⊆ S_{n + n'}`

Combinatorics of the Young subgroup `S_n × S_{n'}` of `S_m`, `m = n + n'`, used for
induction and restriction of KLR algebras (Khovanov–Lauda I, arXiv:0803.4121v2, §2.6,
proof of Proposition 2.16).

Positions `0, …, n - 1` form the first block and `n, …, m - 1` the second; `blockEquiv h`
identifies `Fin n ⊕ Fin n'` with `Fin m` accordingly (`h : n + n' = m`), and
`blockPerm h a b` is the permutation acting by `a` on the first block and by `b` on the
second.

## Main results

* `TypeA.wordProd_append_shiftWord` : the word `α ++ (n + β)` represents
  `blockPerm h (wordProd n α) (wordProd n' β)`.
* `TypeA.length_blockPerm` : `length m (blockPerm h a b) = length n a + length n' b`; hence
  concatenating reduced words of the two blocks gives a reduced word
  (`TypeA.IsReduced.append_shiftWord`).
* `TypeA.IsShuffle` : `u` is a *shuffle* (a minimal length representative of the coset
  `(S_n × S_{n'}) u`) if `u⁻¹` is increasing on each block.
* `TypeA.parabolicEquiv` : every `w ∈ S_m` factors uniquely as `w = blockPerm h a b * u`
  with `u` a shuffle, and then (`TypeA.length_blockPerm_mul`)
  `length m w = length n a + length n' b + length m u`.
* `TypeA.IsReduced.parabolic` : concatenating reduced words for `a`, `b` (shifted) and `u`
  gives a reduced word for `blockPerm h a b * u`.
-/

namespace Categorification.TypeA

open Equiv

variable {n n' m : ℕ} (h : n + n' = m)

/-! ### Blocks -/

/-- `Fin n ⊕ Fin n' ≃ Fin m`: the first block `0, …, n - 1`, followed by the second block
`n, …, m - 1`. -/
def blockEquiv : Fin n ⊕ Fin n' ≃ Fin m := finSumFinEquiv.trans (finCongr h)

@[simp] theorem blockEquiv_inl_val (x : Fin n) : (blockEquiv h (Sum.inl x)).val = x.val := rfl

@[simp] theorem blockEquiv_inr_val (y : Fin n') : (blockEquiv h (Sum.inr y)).val = n + y.val :=
  rfl

theorem blockEquiv_inl_lt_inl {x x' : Fin n} :
    blockEquiv h (Sum.inl x) < blockEquiv h (Sum.inl x') ↔ x < x' := Iff.rfl

theorem blockEquiv_inr_lt_inr {y y' : Fin n'} :
    blockEquiv h (Sum.inr y) < blockEquiv h (Sum.inr y') ↔ y < y' := by
  rw [Fin.lt_iff_val_lt_val, Fin.lt_iff_val_lt_val, blockEquiv_inr_val, blockEquiv_inr_val]
  omega

theorem blockEquiv_inl_lt_inr (x : Fin n) (y : Fin n') :
    blockEquiv h (Sum.inl x) < blockEquiv h (Sum.inr y) := by
  simp only [Fin.lt_iff_val_lt_val, blockEquiv_inl_val, blockEquiv_inr_val]; omega

theorem not_blockEquiv_inr_lt_inl (x : Fin n) (y : Fin n') :
    ¬ blockEquiv h (Sum.inr y) < blockEquiv h (Sum.inl x) :=
  not_lt.2 (blockEquiv_inl_lt_inr h x y).le

/-- The permutation acting by `a` on the first block and by `b` on the second. -/
def blockPerm (a : Perm (Fin n)) (b : Perm (Fin n')) : Perm (Fin m) :=
  (blockEquiv h).permCongr (Perm.sumCongr a b)

@[simp] theorem blockPerm_inl (a : Perm (Fin n)) (b : Perm (Fin n')) (x : Fin n) :
    blockPerm h a b (blockEquiv h (Sum.inl x)) = blockEquiv h (Sum.inl (a x)) := by
  simp [blockPerm]

@[simp] theorem blockPerm_inr (a : Perm (Fin n)) (b : Perm (Fin n')) (y : Fin n') :
    blockPerm h a b (blockEquiv h (Sum.inr y)) = blockEquiv h (Sum.inr (b y)) := by
  simp [blockPerm]

theorem blockPerm_mul (a a' : Perm (Fin n)) (b b' : Perm (Fin n')) :
    blockPerm h a b * blockPerm h a' b' = blockPerm h (a * a') (b * b') := by
  ext v
  obtain ⟨s, rfl⟩ := (blockEquiv h).surjective v
  cases s <;> simp

@[simp] theorem blockPerm_one : blockPerm h (1 : Perm (Fin n)) (1 : Perm (Fin n')) = 1 := by
  ext v
  obtain ⟨s, rfl⟩ := (blockEquiv h).surjective v
  cases s <;> simp

theorem blockPerm_inv (a : Perm (Fin n)) (b : Perm (Fin n')) :
    (blockPerm h a b)⁻¹ = blockPerm h a⁻¹ b⁻¹ := by
  rw [inv_eq_iff_mul_eq_one, blockPerm_mul]; simp

theorem blockPerm_injective {a a' : Perm (Fin n)} {b b' : Perm (Fin n')}
    (he : blockPerm h a b = blockPerm h a' b') : a = a' ∧ b = b' := by
  constructor
  · refine Equiv.ext fun x => ?_
    have := congrArg (fun p : Perm (Fin m) => p (blockEquiv h (Sum.inl x))) he
    simpa using this
  · refine Equiv.ext fun y => ?_
    have := congrArg (fun p : Perm (Fin m) => p (blockEquiv h (Sum.inr y))) he
    simpa using this

/-! ### Words -/

/-- Shift all letters of a word by `n` (moving it to the second block). -/
def shiftWord (n : ℕ) (β : List ℕ) : List ℕ := β.map (n + ·)

@[simp] theorem length_shiftWord (β : List ℕ) : (shiftWord n β).length = β.length := by
  simp [shiftWord]

theorem ValidWord.of_le {α : List ℕ} (hα : ValidWord n α) (hnm : n ≤ m) : ValidWord m α :=
  fun k hk => by have := hα k hk; omega

include h in
theorem ValidWord.shiftWord {β : List ℕ} (hβ : ValidWord n' β) : ValidWord m (shiftWord n β) := by
  intro k hk
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hk
  have := hβ j hj; omega

theorem sadj_eq_blockPerm_left {k : ℕ} (hk : k + 1 < n) :
    sadj m k = blockPerm h (sadj n k) 1 := by
  ext v
  obtain ⟨s, rfl⟩ := (blockEquiv h).surjective v
  have hkm : k + 1 < m := by omega
  cases s with
  | inl x =>
    simp only [blockPerm_inl, blockEquiv_inl_val]
    rw [sadj_val_of_lt hkm, sadj_val_of_lt hk, blockEquiv_inl_val]
  | inr y =>
    simp only [blockPerm_inr, blockEquiv_inr_val, Perm.one_apply]
    rw [sadj_val_of_lt hkm, blockEquiv_inr_val]
    unfold swapNat; split_ifs <;> omega

theorem sadj_eq_blockPerm_right {k : ℕ} (hk : k + 1 < n') :
    sadj m (n + k) = blockPerm h 1 (sadj n' k) := by
  ext v
  obtain ⟨s, rfl⟩ := (blockEquiv h).surjective v
  have hkm : n + k + 1 < m := by omega
  cases s with
  | inl x =>
    simp only [blockPerm_inl, blockEquiv_inl_val, Perm.one_apply]
    rw [sadj_val_of_lt hkm, blockEquiv_inl_val]
    have := x.2
    unfold swapNat; split_ifs <;> omega
  | inr y =>
    simp only [blockPerm_inr, blockEquiv_inr_val]
    rw [sadj_val_of_lt hkm, sadj_val_of_lt hk, blockEquiv_inr_val]
    unfold swapNat; split_ifs <;> omega

theorem wordProd_eq_blockPerm_left {α : List ℕ} (hα : ValidWord n α) :
    wordProd m α = blockPerm h (wordProd n α) 1 := by
  induction α with
  | nil => simp
  | cons k α ih =>
    rw [validWord_cons] at hα
    rw [wordProd_cons, wordProd_cons, ih hα.2, sadj_eq_blockPerm_left h hα.1, blockPerm_mul,
      one_mul]

theorem wordProd_shiftWord {β : List ℕ} (hβ : ValidWord n' β) :
    wordProd m (shiftWord n β) = blockPerm h 1 (wordProd n' β) := by
  induction β with
  | nil => simp [shiftWord]
  | cons k β ih =>
    rw [validWord_cons] at hβ
    have : shiftWord n (k :: β) = (n + k) :: shiftWord n β := rfl
    rw [this, wordProd_cons, wordProd_cons, ih hβ.2, sadj_eq_blockPerm_right h hβ.1,
      blockPerm_mul, one_mul]

/-- The word `α ++ (n + β)` represents `a × b`. -/
theorem wordProd_append_shiftWord {α β : List ℕ} (hα : ValidWord n α) (hβ : ValidWord n' β) :
    wordProd m (α ++ shiftWord n β) = blockPerm h (wordProd n α) (wordProd n' β) := by
  rw [wordProd_append, wordProd_eq_blockPerm_left h hα, wordProd_shiftWord h hβ, blockPerm_mul,
    mul_one, one_mul]

/-! ### Inversions and length -/

private theorem card_filter_eq_sum {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card = ∑ x, if p x then 1 else 0 := by
  rw [Finset.card_filter]

private theorem invCount_eq_sum (w : Perm (Fin m)) :
    invCount m w = ∑ p : Fin m, ∑ q : Fin m, if p < q ∧ w q < w p then 1 else 0 := by
  rw [invCount, invSet, card_filter_eq_sum, Fintype.sum_prod_type]

/-- Inversions of `g * (a × b)` when `g` is increasing on both blocks. -/
private theorem invCount_mul_blockPerm_aux (g : Perm (Fin m)) (a : Perm (Fin n))
    (b : Perm (Fin n')) (hg₁ : StrictMono fun x => g (blockEquiv h (Sum.inl x)))
    (hg₂ : StrictMono fun y => g (blockEquiv h (Sum.inr y))) :
    invCount m (g * blockPerm h a b) = invCount n a + invCount n' b +
      ∑ x : Fin n, ∑ y : Fin n',
        if g (blockEquiv h (Sum.inr y)) < g (blockEquiv h (Sum.inl x)) then 1 else 0 := by
  rw [invCount_eq_sum, ← (blockEquiv h).sum_comp, Fintype.sum_sum_type]
  simp only [← (blockEquiv h).sum_comp, Fintype.sum_sum_type, Perm.mul_apply, blockPerm_inl,
    blockPerm_inr, blockEquiv_inl_lt_inl, blockEquiv_inr_lt_inr, hg₁.lt_iff_lt, hg₂.lt_iff_lt,
    not_blockEquiv_inr_lt_inl, blockEquiv_inl_lt_inr, true_and, false_and, if_false,
    Finset.sum_const_zero, add_zero]
  rw [invCount_eq_sum, invCount_eq_sum]
  have hcross : (∑ x : Fin n, ∑ y : Fin n',
      if g (blockEquiv h (Sum.inr (b y))) < g (blockEquiv h (Sum.inl (a x))) then 1 else 0) =
      ∑ x : Fin n, ∑ y : Fin n',
        if g (blockEquiv h (Sum.inr y)) < g (blockEquiv h (Sum.inl x)) then 1 else 0 := by
    rw [← Equiv.sum_comp a (fun x => ∑ y : Fin n',
      if g (blockEquiv h (Sum.inr y)) < g (blockEquiv h (Sum.inl x)) then 1 else 0)]
    refine Finset.sum_congr rfl fun x _ => ?_
    exact Equiv.sum_comp b (fun y =>
      if g (blockEquiv h (Sum.inr y)) < g (blockEquiv h (Sum.inl (a x))) then 1 else 0)
  simp only [Finset.sum_add_distrib, zero_add]
  rw [hcross]
  ring

/-- Inversions of `g * (a × b)` when `g` is increasing on both blocks. -/
theorem invCount_mul_blockPerm (g : Perm (Fin m)) (a : Perm (Fin n)) (b : Perm (Fin n'))
    (hg₁ : StrictMono fun x => g (blockEquiv h (Sum.inl x)))
    (hg₂ : StrictMono fun y => g (blockEquiv h (Sum.inr y))) :
    invCount m (g * blockPerm h a b) = invCount n a + invCount n' b + invCount m g := by
  have h1 := invCount_mul_blockPerm_aux h g a b hg₁ hg₂
  have h2 := invCount_mul_blockPerm_aux h g 1 1 hg₁ hg₂
  rw [blockPerm_one, mul_one, invCount_one, invCount_one, zero_add, zero_add] at h2
  rw [h1, h2]

/-- **Length of a Young subgroup element**: `ℓ(a × b) = ℓ(a) + ℓ(b)`. -/
theorem length_blockPerm (a : Perm (Fin n)) (b : Perm (Fin n')) :
    length m (blockPerm h a b) = length n a + length n' b := by
  have := invCount_mul_blockPerm h 1 a b
    (fun x x' hx => by simpa [blockEquiv_inl_lt_inl] using hx)
    (fun y y' hy => by simpa [blockEquiv_inr_lt_inr] using hy)
  rw [one_mul, invCount_one, add_zero] at this
  rw [length_eq_invCount, length_eq_invCount, length_eq_invCount, this]

include h in
/-- Concatenating a reduced word of `S_n` with a shifted reduced word of `S_{n'}` gives a
reduced word of `S_m`. -/
theorem IsReduced.append_shiftWord {α β : List ℕ} (hα : IsReduced n α) (hβ : IsReduced n' β) :
    IsReduced m (α ++ shiftWord n β) := by
  refine ⟨validWord_append.2 ⟨hα.1.of_le (by omega), hβ.1.shiftWord h⟩, ?_⟩
  rw [wordProd_append_shiftWord h hα.1 hβ.1, length_blockPerm, List.length_append,
    length_shiftWord, hα.2, hβ.2]

/-! ### Shuffles and the parabolic factorisation -/

/-- `u` is a *shuffle*: `u⁻¹` is increasing on each block. Equivalently, `u` is the minimal
length element of its coset `(S_n × S_{n'}) u` (see `length_blockPerm_mul`). -/
def IsShuffle (u : Perm (Fin m)) : Prop :=
  StrictMono (fun x => u⁻¹ (blockEquiv h (Sum.inl x))) ∧
    StrictMono (fun y => u⁻¹ (blockEquiv h (Sum.inr y)))

/-- The set of shuffles. -/
abbrev Shuffle : Type := {u : Perm (Fin m) // IsShuffle h u}

theorem isShuffle_one : IsShuffle h (1 : Perm (Fin m)) :=
  ⟨fun x x' hx => by simpa [blockEquiv_inl_lt_inl] using hx,
    fun y y' hy => by simpa [blockEquiv_inr_lt_inr] using hy⟩

/-- **Length additivity**: `ℓ((a × b) u) = ℓ(a) + ℓ(b) + ℓ(u)` for a shuffle `u`. -/
theorem length_blockPerm_mul (a : Perm (Fin n)) (b : Perm (Fin n')) {u : Perm (Fin m)}
    (hu : IsShuffle h u) :
    length m (blockPerm h a b * u) = length n a + length n' b + length m u := by
  have := invCount_mul_blockPerm h u⁻¹ a⁻¹ b⁻¹ hu.1 hu.2
  rw [← length_inv, mul_inv_rev, blockPerm_inv, ← length_inv a, ← length_inv b, ← length_inv u]
  simp only [length_eq_invCount]
  exact this

/-- Existence of the parabolic factorisation `w = (a × b) u` with `u` a shuffle. -/
theorem exists_blockPerm_mul (w : Perm (Fin m)) :
    ∃ (a : Perm (Fin n)) (b : Perm (Fin n')) (u : Perm (Fin m)),
      IsShuffle h u ∧ blockPerm h a b * u = w := by
  let f₁ : Fin n → Fin m := fun x => w⁻¹ (blockEquiv h (Sum.inl x))
  let f₂ : Fin n' → Fin m := fun y => w⁻¹ (blockEquiv h (Sum.inr y))
  refine ⟨Tuple.sort f₁, Tuple.sort f₂, (blockPerm h (Tuple.sort f₁) (Tuple.sort f₂))⁻¹ * w,
    ⟨?_, ?_⟩, by rw [mul_inv_cancel_left]⟩
  · have hs := (Tuple.monotone_sort f₁).strictMono_of_injective
      ((w⁻¹.injective.comp ((blockEquiv h).injective.comp Sum.inl_injective)).comp
        (Tuple.sort f₁).injective)
    intro x x' hx
    have := hs hx
    simpa [f₁, mul_inv_rev] using this
  · have hs := (Tuple.monotone_sort f₂).strictMono_of_injective
      ((w⁻¹.injective.comp ((blockEquiv h).injective.comp Sum.inr_injective)).comp
        (Tuple.sort f₂).injective)
    intro y y' hy
    have := hs hy
    simpa [f₂, mul_inv_rev] using this

private theorem eq_one_of_strictMono {c : Perm (Fin n)} (hc : StrictMono c) : c = 1 := by
  have := Subsingleton.elim (hc.orderIsoOfSurjective c c.surjective) (OrderIso.refl _)
  ext x
  exact congrArg Fin.val (congrArg (fun φ : Fin n ≃o Fin n => φ x) this)

/-- Uniqueness of the parabolic factorisation. -/
theorem blockPerm_mul_injective {a a' : Perm (Fin n)} {b b' : Perm (Fin n')}
    {u u' : Perm (Fin m)} (hu : IsShuffle h u) (hu' : IsShuffle h u')
    (he : blockPerm h a b * u = blockPerm h a' b' * u') : a = a' ∧ b = b' ∧ u = u' := by
  -- `u⁻¹ = u'⁻¹ * (c × d)` with `c = a'⁻¹ a`, `d = b'⁻¹ b`.
  have hinv : u⁻¹ = u'⁻¹ * blockPerm h (a'⁻¹ * a) (b'⁻¹ * b) := by
    rw [← blockPerm_mul, ← blockPerm_inv, ← mul_assoc, ← mul_inv_rev, ← he, mul_inv_rev,
      inv_mul_cancel_right]
  have hc : StrictMono (a'⁻¹ * a) := by
    intro x x' hx
    have := hu.1 hx
    simp only [hinv, Perm.mul_apply, blockPerm_inl] at this
    exact hu'.1.lt_iff_lt.1 this
  have hd : StrictMono (b'⁻¹ * b) := by
    intro y y' hy
    have := hu.2 hy
    simp only [hinv, Perm.mul_apply, blockPerm_inr] at this
    exact hu'.2.lt_iff_lt.1 this
  have ha : a = a' := by
    have := eq_one_of_strictMono hc
    rwa [inv_mul_eq_one, eq_comm] at this
  have hb : b = b' := by
    have := eq_one_of_strictMono hd
    rwa [inv_mul_eq_one, eq_comm] at this
  subst ha hb
  exact ⟨rfl, rfl, mul_left_cancel he⟩

/-- **Parabolic factorisation**: `S_n × S_{n'} × {shuffles} ≃ S_m`, `(a, b, u) ↦ (a × b) u`. -/
noncomputable def parabolicEquiv : Perm (Fin n) × Perm (Fin n') × Shuffle h ≃ Perm (Fin m) :=
  Equiv.ofBijective (fun p => blockPerm h p.1 p.2.1 * p.2.2.1)
    ⟨fun p q he => by
      obtain ⟨a, b, u, hu⟩ := p
      obtain ⟨a', b', u', hu'⟩ := q
      obtain ⟨rfl, rfl, rfl⟩ := blockPerm_mul_injective h hu hu' he
      rfl,
     fun w => by
      obtain ⟨a, b, u, hu, rfl⟩ := exists_blockPerm_mul h w
      exact ⟨(a, b, ⟨u, hu⟩), rfl⟩⟩

@[simp] theorem parabolicEquiv_apply (p : Perm (Fin n) × Perm (Fin n') × Shuffle h) :
    parabolicEquiv h p = blockPerm h p.1 p.2.1 * p.2.2.1 := rfl

/-- Reduced words for `a`, `b` and a shuffle `u` concatenate to a reduced word for
`(a × b) u`. -/
theorem IsReduced.parabolic {α β σ : List ℕ} (hα : IsReduced n α) (hβ : IsReduced n' β)
    (hσ : IsReduced m σ) (hu : IsShuffle h (wordProd m σ)) :
    IsReduced m (α ++ shiftWord n β ++ σ) ∧
      wordProd m (α ++ shiftWord n β ++ σ) =
        blockPerm h (wordProd n α) (wordProd n' β) * wordProd m σ := by
  have hw : wordProd m (α ++ shiftWord n β ++ σ) =
      blockPerm h (wordProd n α) (wordProd n' β) * wordProd m σ := by
    rw [wordProd_append, wordProd_append_shiftWord h hα.1 hβ.1]
  refine ⟨⟨validWord_append.2 ⟨(hα.append_shiftWord h hβ).1, hσ.1⟩, ?_⟩, hw⟩
  rw [hw, length_blockPerm_mul h _ _ hu, List.length_append, List.length_append,
    length_shiftWord, hα.2, hβ.2, hσ.2]

end Categorification.TypeA
