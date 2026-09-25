/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TypeA.Parabolic
import Categorification.TypeA.Matsumoto

/-!
# Double cosets of maximal parabolic subgroups and the Mackey decomposition of `S_m`

Combinatorics for the Mackey filtration of KLR algebras (Khovanov–Lauda I,
arXiv:0803.4121v2, §2.6, Proposition 2.18): the double cosets
`(S_n × S_{n'}) \ S_m / (S_{n''} × S_{n'''})` with `n + n' = n'' + n''' = m`.

We think of `w ∈ S_m` as a braid-like diagram whose strand starting at the bottom position
`p` ends at the top position `w p` (this is the convention of `ψw ρ * e i`, which has
bottom sequence `i` and top sequence `wordProd ρ • i`). The *top* Young subgroup
`S_n × S_{n'}` acts on the left and the *bottom* Young subgroup `S_{n''} × S_{n'''}` on the
right.

## Main definitions

* `TypeA.subProds m γ` — the set of permutations represented by the subwords (sublists) of a
  word `γ`. It is invariant under braid moves (`TypeA.BraidEquiv.subProds_eq`), which makes
  it the right bookkeeping device for rewriting products of crossings in KLR algebras.
* `TypeA.rk w i j` — the rank function `#{p < i | j ≤ w p}`.
* `TypeA.crossCount n n'' w = #{p | n'' ≤ p ∧ w p < n}` — the number of strands going from
  the second bottom block to the first top block. This is `|λ|` in the notation of KL I,
  Proposition 2.18, where `λ` is the weight of these strands.
* `TypeA.IsDoubleShuffle hJ hK d` — `d` is the minimal length element of its double coset.

## Main results

* `TypeA.rk_wordProd_sublist_le` — **subword property of the rank function**: if `γ` is a
  reduced word and `δ` is a subword, then `rk (wordProd δ) ≤ rk (wordProd γ)` pointwise.
  (This is the rank-matrix half of the subword property of the Bruhat order.)
* `TypeA.crossCount_le_of_mem_subProds` — hence `crossCount` does not increase when passing to
  subwords of a reduced word.
* `TypeA.crossCount_mul_left`, `TypeA.crossCount_mul_right` — `crossCount` is constant on
  double cosets.
* `TypeA.mackey_factorisation` — every `w` factors as `w = (a × b) d (y × y')` with `d` a
  minimal double coset representative and lengths adding up.
* `TypeA.IsDoubleShuffle.eq_of_crossCount_eq` — a minimal double coset representative is
  determined by its `crossCount` (`TypeA.IsDoubleShuffle.val_eq`, `val_lt_iff` describe it
  explicitly); `TypeA.crossCount_eq_iff_mem_doubleCoset` — two permutations lie in the same
  double coset iff they have the same `crossCount`; `TypeA.exists_isDoubleShuffle_iff` — the
  values that occur are exactly `max(0, n - n'') ≤ c ≤ min(n, n''')`. So the double cosets are
  indexed by `|λ|`, i.e. (for fixed weights) by the data `λ` of KL I, Proposition 2.18.
* `TypeA.IsDoubleShuffle.mem_invSet_iff` — the crossings of the minimal representative `d`:
  exactly the strands from `[n - |λ|, n'')` (to the second top block) cross the `|λ|` strands
  from the second bottom block (to `[n - |λ|, n)`).
-/

namespace Categorification.TypeA

open Equiv

variable {m : ℕ}

/-! ### Products of subwords -/

theorem ValidWord.sublist {γ δ : List ℕ} (hγ : ValidWord m γ) (h : δ.Sublist γ) :
    ValidWord m δ :=
  fun j hj => hγ j (h.subset hj)

/-- The set of permutations represented by the subwords (sublists) of a word `γ`. -/
def subProds (m : ℕ) (γ : List ℕ) : Set (Perm (Fin m)) :=
  {w | ∃ δ, δ.Sublist γ ∧ wordProd m δ = w}

theorem mem_subProds {γ : List ℕ} {w : Perm (Fin m)} :
    w ∈ subProds m γ ↔ ∃ δ, δ.Sublist γ ∧ wordProd m δ = w := Iff.rfl

theorem wordProd_mem_subProds (γ : List ℕ) : wordProd m γ ∈ subProds m γ :=
  ⟨γ, List.Sublist.refl γ, rfl⟩

theorem one_mem_subProds (γ : List ℕ) : (1 : Perm (Fin m)) ∈ subProds m γ :=
  ⟨[], List.nil_sublist γ, rfl⟩

theorem subProds_mono {δ γ : List ℕ} (h : δ.Sublist γ) : subProds m δ ⊆ subProds m γ :=
  fun _ ⟨δ', h', hw⟩ => ⟨δ', h'.trans h, hw⟩

theorem mem_subProds_nil {w : Perm (Fin m)} : w ∈ subProds m [] ↔ w = 1 := by
  simp only [mem_subProds, List.sublist_nil]
  constructor
  · rintro ⟨δ, rfl, rfl⟩; rfl
  · rintro rfl; exact ⟨[], rfl, rfl⟩

theorem mem_subProds_cons {j : ℕ} {γ : List ℕ} {w : Perm (Fin m)} :
    w ∈ subProds m (j :: γ) ↔ w ∈ subProds m γ ∨ ∃ v ∈ subProds m γ, w = sadj m j * v := by
  simp only [mem_subProds, List.sublist_cons_iff]
  constructor
  · rintro ⟨δ, h | ⟨r, rfl, hr⟩, rfl⟩
    · exact Or.inl ⟨δ, h, rfl⟩
    · exact Or.inr ⟨_, ⟨r, hr, rfl⟩, by rw [wordProd_cons]⟩
  · rintro (⟨δ, h, rfl⟩ | ⟨_, ⟨r, hr, rfl⟩, rfl⟩)
    · exact ⟨δ, Or.inl h, rfl⟩
    · exact ⟨j :: r, Or.inr ⟨r, rfl, hr⟩, by rw [wordProd_cons]⟩

theorem mem_subProds_append {α β : List ℕ} {w : Perm (Fin m)} :
    w ∈ subProds m (α ++ β) ↔ ∃ u ∈ subProds m α, ∃ v ∈ subProds m β, w = u * v := by
  simp only [mem_subProds, List.sublist_append_iff]
  constructor
  · rintro ⟨_, ⟨l₁, l₂, rfl, h₁, h₂⟩, rfl⟩
    exact ⟨_, ⟨l₁, h₁, rfl⟩, _, ⟨l₂, h₂, rfl⟩, by rw [wordProd_append]⟩
  · rintro ⟨_, ⟨l₁, h₁, rfl⟩, _, ⟨l₂, h₂, rfl⟩, rfl⟩
    exact ⟨l₁ ++ l₂, ⟨l₁, l₂, rfl, h₁, h₂⟩, by rw [wordProd_append]⟩

theorem subProds_append_congr (α β : List ℕ) {x x' : List ℕ}
    (h : subProds m x = subProds m x') :
    subProds m (α ++ x ++ β) = subProds m (α ++ x' ++ β) := by
  ext w
  simp only [mem_subProds_append, h]

theorem subProds_pair_comm {a b : ℕ} (h : a + 1 < b) :
    subProds m [a, b] = subProds m [b, a] := by
  have hc := sadj_comm m (Or.inl h)
  ext w
  simp only [mem_subProds_cons, mem_subProds_nil, or_and_right, exists_or, exists_eq_left,
    mul_one, hc]
  tauto

theorem subProds_braid {a : ℕ} (h : a + 2 < m) :
    subProds m [a, a + 1, a] = subProds m [a + 1, a, a + 1] := by
  have hb : sadj m a * (sadj m (a + 1) * sadj m a) =
      sadj m (a + 1) * (sadj m a * sadj m (a + 1)) := by
    simpa only [mul_assoc] using sadj_braid h
  have h1 : sadj m a * sadj m a = 1 := sadj_mul_self m a
  have h2 : sadj m (a + 1) * sadj m (a + 1) = 1 := sadj_mul_self m (a + 1)
  ext w
  simp only [mem_subProds_cons, mem_subProds_nil, or_and_right, exists_or, exists_eq_left,
    mul_one, h1, h2, hb]
  tauto

/-- A braid move between valid words does not change the set of subword products. -/
theorem BraidStep.subProds_eq {ρ σ : List ℕ} (h : BraidStep ρ σ) (hv : ValidWord m ρ) :
    subProds m ρ = subProds m σ := by
  cases h with
  | comm α β h => exact subProds_append_congr α β (subProds_pair_comm h)
  | braid α β a =>
    have ha : a + 2 < m := by
      have := hv (a + 1) (by simp)
      omega
    exact subProds_append_congr α β (subProds_braid ha)

/-- Braid-equivalent valid words have the same subword products. -/
theorem BraidEquiv.subProds_eq {ρ σ : List ℕ} (h : BraidEquiv ρ σ) (hv : ValidWord m ρ) :
    subProds m ρ = subProds m σ := by
  induction h with
  | rel _ _ h => exact h.subProds_eq hv
  | refl => rfl
  | symm _ _ h ih => exact (ih ((BraidEquiv.validWord_iff h).2 hv)).symm
  | trans _ _ _ h₁ _ ih₁ ih₂ =>
    exact (ih₁ hv).trans (ih₂ ((BraidEquiv.validWord_iff h₁).1 hv))

/-! ### The rank function and the subword property -/

/-- The rank function `rk w i j = #{p | p < i ∧ j ≤ w p}`: the number of strands with bottom
end among the first `i` positions and top end at a position `≥ j`. -/
def rk (w : Perm (Fin m)) (i j : ℕ) : ℕ :=
  (Finset.univ.filter fun p : Fin m => p.val < i ∧ j ≤ (w p).val).card

theorem rk_eq_sum (w : Perm (Fin m)) (i j : ℕ) :
    rk w i j = ∑ p, if p.val < i ∧ j ≤ (w p).val then 1 else 0 :=
  Finset.card_filter _ _

private theorem sum_ite_eq_inv (v : Perm (Fin m)) (c : Fin m) (i : ℕ) :
    (∑ p : Fin m, if (v p).val = c.val ∧ p.val < i then 1 else 0 : ℕ) =
      if (v⁻¹ c).val < i then 1 else 0 := by
  have key : ∀ p : Fin m, ((v p).val = c.val ∧ p.val < i) ↔ (p = v⁻¹ c ∧ (v⁻¹ c).val < i) := by
    intro p
    rw [← Fin.ext_iff, Perm.eq_inv_iff_eq]
    constructor
    · rintro ⟨h, h'⟩; subst h; simpa using h'
    · rintro ⟨h, h'⟩; subst h; simpa using h'
  simp only [key, ite_and]
  rw [Finset.sum_ite_eq']
  simp

/-- Peeling off the value `j`. -/
theorem rk_eq_rk_succ_add (w : Perm (Fin m)) (i : ℕ) {j : ℕ} (hj : j < m) :
    rk w i j = rk w i (j + 1) + if (w⁻¹ ⟨j, hj⟩).val < i then 1 else 0 := by
  rw [rk_eq_sum, rk_eq_sum, ← sum_ite_eq_inv w ⟨j, hj⟩ i, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Fin.val_mk] at *
  split_ifs <;> omega

theorem le_sadj_val_iff_of_ne {a j : ℕ} (hj : j ≠ a + 1) (x : Fin m) :
    j ≤ (sadj m a x).val ↔ j ≤ x.val := by
  rw [sadj_val]
  split_ifs
  · have := swapNat_cases a x
    generalize swapNat a x = y at *
    omega
  · rfl

theorem succ_le_sadj_val_iff {a : ℕ} (ha : a + 1 < m) (x : Fin m) :
    a + 1 ≤ (sadj m a x).val ↔ a + 2 ≤ x.val ∨ x.val = a := by
  rw [sadj_val_of_lt ha]
  have := swapNat_cases a x
  generalize swapNat a x = y at *
  omega

theorem rk_sadj_mul_of_ne (v : Perm (Fin m)) (i : ℕ) {a j : ℕ} (hj : j ≠ a + 1) :
    rk (sadj m a * v) i j = rk v i j := by
  simp only [rk, Perm.mul_apply, le_sadj_val_iff_of_ne hj]

theorem rk_sadj_mul_succ (v : Perm (Fin m)) (i : ℕ) {a : ℕ} (ha : a + 1 < m) :
    rk (sadj m a * v) i (a + 1) =
      rk v i (a + 2) + if (v⁻¹ ⟨a, by omega⟩).val < i then 1 else 0 := by
  rw [rk_eq_sum, rk_eq_sum, ← sum_ite_eq_inv v ⟨a, by omega⟩ i, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Perm.mul_apply, succ_le_sadj_val_iff ha]
  simp only [Fin.val_mk] at *
  split_ifs <;> omega

/-- If `s_a w > w` then `rk w ≤ rk (s_a w)`. -/
theorem rk_le_rk_sadj_mul {a : ℕ} (ha : a + 1 < m) {w : Perm (Fin m)}
    (hw : w⁻¹ ⟨a, by omega⟩ < w⁻¹ ⟨a + 1, ha⟩) (i j : ℕ) :
    rk w i j ≤ rk (sadj m a * w) i j := by
  by_cases hj : j = a + 1
  · subst hj
    rw [rk_sadj_mul_succ w i ha, rk_eq_rk_succ_add w i ha, show a + 1 + 1 = a + 2 from rfl]
    rw [Fin.lt_iff_val_lt_val] at hw
    split_ifs <;> omega
  · rw [rk_sadj_mul_of_ne w i hj]

/-- The lifting step: if `s_a w > w` and `rk v ≤ rk w`, then `rk (s_a v) ≤ rk (s_a w)`. -/
theorem rk_sadj_mul_le {a : ℕ} (ha : a + 1 < m) {v w : Perm (Fin m)}
    (hw : w⁻¹ ⟨a, by omega⟩ < w⁻¹ ⟨a + 1, ha⟩) (hvw : ∀ i j, rk v i j ≤ rk w i j) (i j : ℕ) :
    rk (sadj m a * v) i j ≤ rk (sadj m a * w) i j := by
  by_cases hj : j = a + 1
  · subst hj
    rw [rk_sadj_mul_succ v i ha, rk_sadj_mul_succ w i ha]
    have h1 := hvw i (a + 2)
    have h2 := hvw i a
    rw [rk_eq_rk_succ_add v i (j := a) (by omega), rk_eq_rk_succ_add v i ha,
      rk_eq_rk_succ_add w i (j := a) (by omega), rk_eq_rk_succ_add w i ha,
      show a + 1 + 1 = a + 2 from rfl] at h2
    rw [Fin.lt_iff_val_lt_val] at hw
    split_ifs at h2 ⊢ <;> omega
  · rw [rk_sadj_mul_of_ne v i hj, rk_sadj_mul_of_ne w i hj]
    exact hvw i j

/-- The tail of a reduced word is reduced, and its first letter is a left ascent of the tail. -/
theorem IsReduced.cons_inv {a : ℕ} {γ : List ℕ} (h : IsReduced m (a :: γ)) :
    ∃ ha : a + 1 < m, IsReduced m γ ∧
      (wordProd m γ)⁻¹ ⟨a, by omega⟩ < (wordProd m γ)⁻¹ ⟨a + 1, ha⟩ := by
  obtain ⟨hv, hl⟩ := h
  rw [validWord_cons] at hv
  refine ⟨hv.1, ?_, ?_⟩
  · have h1 := length_sadj_mul_le a (wordProd m γ)
    have h2 := length_wordProd_le (m := m) hv.2
    rw [wordProd_cons] at hl
    simp only [List.length_cons] at hl
    exact ⟨hv.2, by omega⟩
  · have hne : (wordProd m γ)⁻¹ ⟨a, by omega⟩ ≠ (wordProd m γ)⁻¹ ⟨a + 1, hv.1⟩ :=
      (wordProd m γ)⁻¹.injective.ne (by simp [Fin.ext_iff])
    refine lt_of_le_of_ne (not_lt.1 fun hgt => ?_) hne
    have h1 := length_sadj_mul_of_gt hv.1 hgt
    have h2 := length_wordProd_le (m := m) hv.2
    rw [wordProd_cons] at hl
    simp only [List.length_cons] at hl
    omega

/-- **Subword property of the rank function.** If `γ` is reduced and `δ` is a subword of `γ`,
then `rk (wordProd δ) ≤ rk (wordProd γ)` pointwise. -/
theorem rk_wordProd_sublist_le {γ : List ℕ} (hγ : IsReduced m γ) {δ : List ℕ}
    (hδ : δ.Sublist γ) (i j : ℕ) : rk (wordProd m δ) i j ≤ rk (wordProd m γ) i j := by
  induction γ generalizing δ i j with
  | nil =>
    rw [List.sublist_nil.1 hδ]
  | cons a γ ih =>
    obtain ⟨ha, hγ', hasc⟩ := hγ.cons_inv
    rw [wordProd_cons]
    rcases List.sublist_cons_iff.1 hδ with h | ⟨r, rfl, hr⟩
    · exact (ih hγ' h i j).trans (rk_le_rk_sadj_mul ha hasc i j)
    · rw [wordProd_cons]
      exact rk_sadj_mul_le ha hasc (fun i j => ih hγ' hr i j) i j

theorem rk_le_of_mem_subProds {γ : List ℕ} (hγ : IsReduced m γ) {v : Perm (Fin m)}
    (hv : v ∈ subProds m γ) (i j : ℕ) : rk v i j ≤ rk (wordProd m γ) i j := by
  obtain ⟨δ, hδ, rfl⟩ := hv
  exact rk_wordProd_sublist_le hγ hδ i j

/-! ### The number of strands crossing between the blocks -/

/-- `crossCount n n'' w = #{p | n'' ≤ p ∧ w p < n}`: the number of strands of `w` going from
the second bottom block (positions `≥ n''`) to the first top block (positions `< n`).
In KL I, Proposition 2.18 this is `|λ|`. -/
def crossCount (n n'' : ℕ) (w : Perm (Fin m)) : ℕ :=
  (Finset.univ.filter fun p : Fin m => n'' ≤ p.val ∧ (w p).val < n).card

private theorem sum_val_lt {N : ℕ} (hN : N ≤ m) :
    (∑ p : Fin m, if p.val < N then 1 else 0 : ℕ) = N := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < N then 1 else 0 : ℕ → ℕ),
    show m = N + (m - N) by omega, Finset.sum_range_add]
  rw [Finset.sum_congr rfl (g := fun _ => (1 : ℕ)) (fun i hi => if_pos (Finset.mem_range.1 hi)),
    Finset.sum_congr rfl (g := fun _ => (0 : ℕ)) (fun i _ => if_neg (by omega))]
  simp

/-- `crossCount` in terms of the rank function: `|λ| + n'' = rk w n'' n + n`. -/
theorem crossCount_add {n n'' : ℕ} (hn : n ≤ m) (hn'' : n'' ≤ m) (w : Perm (Fin m)) :
    crossCount n n'' w + n'' = rk w n'' n + n := by
  have e1 := sum_val_lt (m := m) hn''
  have e2 : (∑ p : Fin m, if (w p).val < n then 1 else 0 : ℕ) = n := by
    rw [Equiv.sum_comp w (fun x : Fin m => if x.val < n then 1 else 0)]
    exact sum_val_lt hn
  rw [crossCount, rk, Finset.card_filter, Finset.card_filter, ← e1, ← e2,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  split_ifs <;> omega

/-- Every permutation has at most `n` strands ending in the top positions `< n`. -/
theorem crossCount_le {n n'' : ℕ} (w : Perm (Fin m)) (hn : n ≤ m) : crossCount n n'' w ≤ n := by
  have h1 : crossCount n n'' w ≤ (Finset.univ.filter fun p : Fin m => (w p).val < n).card :=
    Finset.card_le_card fun p hp => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢; exact hp.2
  have h2 : (Finset.univ.filter fun p : Fin m => (w p).val < n).card = n := by
    rw [Finset.card_filter, Equiv.sum_comp w (fun x : Fin m => if x.val < n then 1 else 0)]
    exact sum_val_lt hn
  omega

/-- At least `n - n''` strands go from the bottom positions `≥ n''` to the top positions `< n`. -/
theorem le_crossCount {n n'' : ℕ} (w : Perm (Fin m)) (hn : n ≤ m) (hn'' : n'' ≤ m) :
    n ≤ crossCount n n'' w + n'' := by
  have := crossCount_add (n := n) (n'' := n'') hn hn'' w
  omega

/-- `crossCount` does not increase when passing to a subword of a reduced word. -/
theorem crossCount_le_of_mem_subProds {n n'' : ℕ} (hn : n ≤ m) (hn'' : n'' ≤ m)
    {γ : List ℕ} (hγ : IsReduced m γ) {v : Perm (Fin m)} (hv : v ∈ subProds m γ) :
    crossCount n n'' v ≤ crossCount n n'' (wordProd m γ) := by
  have h1 := crossCount_add hn hn'' v
  have h2 := crossCount_add hn hn'' (wordProd m γ)
  have := rk_le_of_mem_subProds hγ hv n'' n
  omega

/-- `crossCount` is invariant under left multiplication by permutations preserving the first
top block. -/
theorem crossCount_mul_left {n n'' : ℕ} (g w : Perm (Fin m))
    (hg : ∀ x : Fin m, (g x).val < n ↔ x.val < n) :
    crossCount n n'' (g * w) = crossCount n n'' w := by
  simp only [crossCount, Perm.mul_apply, hg]

/-- `crossCount` is invariant under right multiplication by permutations preserving the
second bottom block. -/
theorem crossCount_mul_right {n n'' : ℕ} (w g : Perm (Fin m))
    (hg : ∀ p : Fin m, n'' ≤ (g p).val ↔ n'' ≤ p.val) :
    crossCount n n'' (w * g) = crossCount n n'' w := by
  rw [crossCount, crossCount, Finset.card_filter, Finset.card_filter,
    ← Equiv.sum_comp g (fun q : Fin m => if n'' ≤ q.val ∧ (w q).val < n then 1 else 0)]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Perm.mul_apply, hg]

/-- An adjacent transposition inside the blocks `[0, n)`, `[n, m)` preserves `[0, n)`. -/
theorem sadj_val_lt_iff {n j : ℕ} (hj : j + 1 < n ∨ n ≤ j) (x : Fin m) :
    (sadj m j x).val < n ↔ x.val < n := by
  rw [sadj_val]
  split_ifs
  · have := swapNat_cases j x
    generalize swapNat j x = y at *
    omega
  · rfl

theorem crossCount_sadj_mul {n n'' j : ℕ} (hj : j + 1 < n ∨ n ≤ j) (w : Perm (Fin m)) :
    crossCount n n'' (sadj m j * w) = crossCount n n'' w :=
  crossCount_mul_left _ _ (sadj_val_lt_iff hj)

theorem crossCount_mul_sadj {n n'' j : ℕ} (hj : j + 1 < n'' ∨ n'' ≤ j) (w : Perm (Fin m)) :
    crossCount n n'' (w * sadj m j) = crossCount n n'' w :=
  crossCount_mul_right _ _ fun p => by
    have := sadj_val_lt_iff (m := m) hj p
    omega

/-- Left multiplication by a word in the letters of the top Young subgroup. -/
theorem crossCount_wordProd_mul {n n'' : ℕ} {α : List ℕ} (hα : ∀ j ∈ α, j + 1 < n ∨ n ≤ j)
    (w : Perm (Fin m)) : crossCount n n'' (wordProd m α * w) = crossCount n n'' w := by
  induction α with
  | nil => simp
  | cons j α ih =>
    rw [wordProd_cons, mul_assoc, crossCount_sadj_mul (hα j (by simp)),
      ih fun j' hj' => hα j' (List.mem_cons_of_mem _ hj')]

/-- Right multiplication by a word in the letters of the bottom Young subgroup. -/
theorem crossCount_mul_wordProd {n n'' : ℕ} {β : List ℕ} (hβ : ∀ j ∈ β, j + 1 < n'' ∨ n'' ≤ j)
    (w : Perm (Fin m)) : crossCount n n'' (w * wordProd m β) = crossCount n n'' w := by
  induction β generalizing w with
  | nil => simp
  | cons j β ih =>
    rw [wordProd_cons, ← mul_assoc, ih fun j' hj' => hβ j' (List.mem_cons_of_mem _ hj'),
      crossCount_mul_sadj (hβ j (by simp))]

theorem crossCount_blockPerm_mul {n n' : ℕ} (hJ : n + n' = m) (n'' : ℕ) (a : Perm (Fin n))
    (b : Perm (Fin n')) (w : Perm (Fin m)) :
    crossCount n n'' (blockPerm hJ a b * w) = crossCount n n'' w := by
  refine crossCount_mul_left _ _ fun x => ?_
  obtain ⟨s, rfl⟩ := (blockEquiv hJ).surjective x
  cases s with
  | inl x => simp only [blockPerm_inl, blockEquiv_inl_val, Fin.is_lt]
  | inr y => simp only [blockPerm_inr, blockEquiv_inr_val]; omega

theorem crossCount_mul_blockPerm {n'' n''' : ℕ} (hK : n'' + n''' = m) (n : ℕ) (w : Perm (Fin m))
    (a : Perm (Fin n'')) (b : Perm (Fin n''')) :
    crossCount n n'' (w * blockPerm hK a b) = crossCount n n'' w := by
  refine crossCount_mul_right _ _ fun x => ?_
  obtain ⟨s, rfl⟩ := (blockEquiv hK).surjective x
  cases s with
  | inl x => simp only [blockPerm_inl, blockEquiv_inl_val]; have := x.2; have := (a x).2; omega
  | inr y => simp only [blockPerm_inr, blockEquiv_inr_val]; omega

/-! ### Minimal double coset representatives and the Mackey factorisation -/

section Mackey

variable {n n' n'' n''' : ℕ}

private theorem strictMono_of_succ {N : ℕ} {f : Fin N → Fin m}
    (h : ∀ i (hi : i + 1 < N), f ⟨i, by omega⟩ < f ⟨i + 1, hi⟩) : StrictMono f := by
  rcases N with _ | N
  · intro a; exact a.elim0
  · exact Fin.strictMono_iff_lt_succ.2 fun i => h i.val (by omega)

/-- `u` is a shuffle iff every adjacent pair of positions inside a block is an ascent of
`u⁻¹`. -/
theorem isShuffle_iff_forall (hJ : n + n' = m) {u : Perm (Fin m)} :
    IsShuffle hJ u ↔ ∀ j (hj : j + 1 < m), (j + 1 < n ∨ n ≤ j) →
      u⁻¹ ⟨j, by omega⟩ < u⁻¹ ⟨j + 1, hj⟩ := by
  constructor
  · rintro ⟨h1, h2⟩ j hj hb
    rcases hb with hb | hb
    · have := h1 (show (⟨j, by omega⟩ : Fin n) < ⟨j + 1, hb⟩ by
        simp [Fin.lt_iff_val_lt_val])
      exact this
    · have := h2 (show (⟨j - n, by omega⟩ : Fin n') < ⟨j - n + 1, by omega⟩ by
        simp [Fin.lt_iff_val_lt_val])
      have e1 : blockEquiv hJ (Sum.inr ⟨j - n, by omega⟩) = ⟨j, by omega⟩ := by
        ext; simp only [blockEquiv_inr_val]; omega
      have e2 : blockEquiv hJ (Sum.inr ⟨j - n + 1, by omega⟩) = ⟨j + 1, hj⟩ := by
        ext; simp only [blockEquiv_inr_val]; omega
      simpa only [e1, e2] using this
  · intro h
    constructor
    · refine strictMono_of_succ fun i hi => ?_
      exact h i (by omega) (Or.inl hi)
    · refine strictMono_of_succ fun i hi => ?_
      have e1 : blockEquiv hJ (Sum.inr ⟨i, by omega⟩) = ⟨n + i, by omega⟩ := rfl
      have e2 : blockEquiv hJ (Sum.inr ⟨i + 1, hi⟩) = ⟨n + i + 1, by omega⟩ := rfl
      simp only [e1, e2]
      exact h (n + i) (by omega) (Or.inr (by omega))

/-- `d` is a *minimal double coset representative* for
`(S_n × S_{n'}) \ S_m / (S_{n''} × S_{n'''})`: `d` is the minimal element both of its left coset
`(S_n × S_{n'}) d` and of its right coset `d (S_{n''} × S_{n'''})`. -/
def IsDoubleShuffle (hJ : n + n' = m) (hK : n'' + n''' = m) (d : Perm (Fin m)) : Prop :=
  IsShuffle hJ d ∧ IsShuffle hK d⁻¹

/-- **Mackey factorisation.** Every `w ∈ S_m` factors as `w = (a × b) · d · (y × y')` with `d`
a minimal double coset representative, and then
`ℓ(w) = ℓ(a) + ℓ(b) + ℓ(d) + ℓ(y) + ℓ(y')`. -/
theorem mackey_factorisation (hJ : n + n' = m) (hK : n'' + n''' = m) (w : Perm (Fin m)) :
    ∃ (a : Perm (Fin n)) (b : Perm (Fin n')) (d : Perm (Fin m)) (y : Perm (Fin n''))
      (y' : Perm (Fin n''')), IsDoubleShuffle hJ hK d ∧
      w = blockPerm hJ a b * d * blockPerm hK y y' ∧
      length m w = length n a + length n' b + length m d + (length n'' y + length n''' y') := by
  obtain ⟨a, b, u, hu, rfl⟩ := exists_blockPerm_mul hJ w
  obtain ⟨c, c', v, hv, hcv⟩ := exists_blockPerm_mul hK u⁻¹
  have hu_eq : u = v⁻¹ * blockPerm hK c⁻¹ c'⁻¹ := by
    rw [← blockPerm_inv, ← mul_inv_rev, hcv, inv_inv]
  have hlu : length m u = length m v⁻¹ + (length n'' c⁻¹ + length n''' c'⁻¹) := by
    rw [← length_inv u, ← hcv, length_blockPerm_mul hK c c' hv, length_inv, length_inv,
      length_inv]
    ring
  refine ⟨a, b, v⁻¹, c⁻¹, c'⁻¹, ⟨?_, by rwa [inv_inv]⟩, by rw [mul_assoc, ← hu_eq], ?_⟩
  · rw [isShuffle_iff_forall]
    intro j hj hb
    by_contra hcon
    have hne : v⁻¹⁻¹ ⟨j + 1, hj⟩ ≠ v⁻¹⁻¹ ⟨j, by omega⟩ :=
      v⁻¹⁻¹.injective.ne (by simp [Fin.ext_iff])
    have hlt := lt_of_le_of_ne (not_lt.1 hcon) hne
    have h1 := length_sadj_mul_of_gt hj hlt
    have h3 := length_sadj_mul_of_lt hj ((isShuffle_iff_forall hJ).1 hu j hj hb)
    have h4 : length m (sadj m j * u) ≤
        length m (sadj m j * v⁻¹) + length m (blockPerm hK c⁻¹ c'⁻¹) := by
      rw [hu_eq, ← mul_assoc]; exact length_mul_le _ _
    rw [length_blockPerm] at h4
    omega
  · rw [length_blockPerm_mul hJ a b hu, hlu]
    ring

end Mackey

/-! ### Minimal double coset representatives are classified by `crossCount` -/

section Classification

variable {n n' n'' n''' : ℕ}

private theorem card_val_lt {N : ℕ} (hN : N ≤ m) :
    (Finset.univ.filter fun q : Fin m => q.val < N).card = N := by
  rw [Finset.card_filter]; exact sum_val_lt hN

private theorem card_Ico {a b : ℕ} (hab : a ≤ b) (hb : b ≤ m) :
    (Finset.univ.filter fun q : Fin m => a ≤ q.val ∧ q.val < b).card = b - a := by
  have h1 := sum_val_lt (m := m) hb
  have h2 := sum_val_lt (m := m) (hab.trans hb)
  have : (∑ q : Fin m, if q.val < b then 1 else 0 : ℕ) =
      (∑ q : Fin m, if q.val < a then 1 else 0) +
        ∑ q : Fin m, if a ≤ q.val ∧ q.val < b then 1 else 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    split_ifs <;> omega
  rw [Finset.card_filter]
  omega

/-- The value `d p` of a permutation is the number of `q` with `d q < d p`. -/
private theorem val_eq_card (d : Perm (Fin m)) (p : Fin m) :
    (d p).val = (Finset.univ.filter fun q : Fin m => d q < d p).card := by
  rw [Finset.card_filter, Equiv.sum_comp d (fun x : Fin m => if x < d p then 1 else 0)]
  simp only [Fin.lt_iff_val_lt_val]
  exact (sum_val_lt (d p).2.le).symm

/-- A shuffle preserves the relative order inside each top block. -/
theorem IsShuffle.inv_lt_inv_iff (hJ : n + n' = m) {u : Perm (Fin m)} (hu : IsShuffle hJ u)
    {x y : Fin m} (hxy : x.val < n ↔ y.val < n) : u⁻¹ x < u⁻¹ y ↔ x < y := by
  by_cases hx : x.val < n
  · have hy : y.val < n := hxy.1 hx
    have ex : blockEquiv hJ (Sum.inl ⟨x.val, hx⟩) = x := Fin.ext rfl
    have ey : blockEquiv hJ (Sum.inl ⟨y.val, hy⟩) = y := Fin.ext rfl
    rw [← ex, ← ey, hu.1.lt_iff_lt, blockEquiv_inl_lt_inl]
  · have hy : ¬ y.val < n := fun h => hx (hxy.2 h)
    have ex : blockEquiv hJ (Sum.inr ⟨x.val - n, by omega⟩) = x := by
      ext; simp only [blockEquiv_inr_val]; omega
    have ey : blockEquiv hJ (Sum.inr ⟨y.val - n, by omega⟩) = y := by
      ext; simp only [blockEquiv_inr_val]; omega
    rw [← ex, ← ey, hu.2.lt_iff_lt, blockEquiv_inr_lt_inr]

variable (hJ : n + n' = m) (hK : n'' + n''' = m) {d : Perm (Fin m)}

include hJ in
/-- Inside a top block, a shuffle `d⁻¹` is increasing: `q < p ↔ d q < d p`. -/
private theorem lt_iff_of_top (hd : IsShuffle hJ d) {p q : Fin m}
    (hpq : (d q).val < n ↔ (d p).val < n) : q < p ↔ d q < d p := by
  have := hd.inv_lt_inv_iff hJ hpq
  simpa using this

include hK in
/-- Inside a bottom block, `d` is increasing. -/
private theorem lt_iff_of_bot (hd : IsShuffle hK d⁻¹) {p q : Fin m}
    (hpq : q.val < n'' ↔ p.val < n'') : d q < d p ↔ q < p := by
  have := hd.inv_lt_inv_iff hK hpq
  simpa using this

include hJ hK in
private theorem card_top_left (hn : n ≤ m) (d : Perm (Fin m)) :
    (Finset.univ.filter fun q : Fin m => q.val < n'' ∧ (d q).val < n).card +
      crossCount n n'' d = n := by
  have e2 : (∑ p : Fin m, if (d p).val < n then 1 else 0 : ℕ) = n := by
    rw [Equiv.sum_comp d (fun x : Fin m => if x.val < n then 1 else 0)]
    exact sum_val_lt hn
  rw [crossCount, Finset.card_filter, Finset.card_filter, ← e2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  split_ifs <;> omega

/-- The explicit form of a minimal double coset representative with `c = crossCount d`:
positions `p < n''` go to `p` or `p + c`, positions `p ≥ n''` go to `p - n'' + n - c` or `p`,
according to whether they end in the first top block. -/
theorem IsDoubleShuffle.val_eq (hd : IsDoubleShuffle hJ hK d) (p : Fin m) :
    (p.val < n'' → (d p).val < n → (d p).val = p.val) ∧
    (p.val < n'' → n ≤ (d p).val → (d p).val = p.val + crossCount n n'' d) ∧
    (n'' ≤ p.val → n ≤ (d p).val → (d p).val = p.val) ∧
    (n'' ≤ p.val → (d p).val < n → (d p).val + n'' + crossCount n n'' d = p.val + n) := by
  have hn : n ≤ m := by omega
  have hn'' : n'' ≤ m := by omega
  have hsplit : (d p).val =
      (∑ q : Fin m, if q.val < n'' ∧ d q < d p then 1 else 0) +
        ∑ q : Fin m, if n'' ≤ q.val ∧ d q < d p then 1 else 0 := by
    rw [val_eq_card, Finset.card_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    split_ifs <;> omega
  have htl := card_top_left hJ hK hn d
  rw [Finset.card_filter] at htl
  have hcc : crossCount n n'' d = ∑ q : Fin m, if n'' ≤ q.val ∧ (d q).val < n then 1 else 0 :=
    Finset.card_filter _ _
  have hlt := fun q => lt_iff_of_top hJ hd.1 (p := p) (q := q)
  have hbt := fun q => lt_iff_of_bot hK hd.2 (p := p) (q := q)
  refine ⟨fun hp hdp => ?_, fun hp hdp => ?_, fun hp hdp => ?_, fun hp hdp => ?_⟩
  · -- `p < n''`, `d p < n`
    have h1 : (∑ q : Fin m, if q.val < n'' ∧ d q < d p then 1 else 0 : ℕ) =
        ∑ q : Fin m, if q.val < p.val then 1 else 0 := by
      refine Finset.sum_congr rfl fun q _ => ?_
      by_cases hq : q.val < n''
      · have := hbt q (by omega); simp only [hq, true_and, this, Fin.lt_iff_val_lt_val]
      · simp only [hq, false_and, if_false]; rw [if_neg (by omega)]
    have h2 : (∑ q : Fin m, if n'' ≤ q.val ∧ d q < d p then 1 else 0 : ℕ) = 0 := by
      refine Finset.sum_eq_zero fun q _ => if_neg ?_
      rintro ⟨hq, hdq⟩
      have := (hlt q (by rw [Fin.lt_iff_val_lt_val] at hdq; omega)).2 hdq
      rw [Fin.lt_iff_val_lt_val] at this; omega
    rw [hsplit, h1, h2, sum_val_lt (by omega)]; rfl
  · -- `p < n''`, `n ≤ d p`
    have h1 : (∑ q : Fin m, if q.val < n'' ∧ d q < d p then 1 else 0 : ℕ) =
        ∑ q : Fin m, if q.val < p.val then 1 else 0 := by
      refine Finset.sum_congr rfl fun q _ => ?_
      by_cases hq : q.val < n''
      · have := hbt q (by omega); simp only [hq, true_and, this, Fin.lt_iff_val_lt_val]
      · simp only [hq, false_and, if_false]; rw [if_neg (by omega)]
    have h2 : (∑ q : Fin m, if n'' ≤ q.val ∧ d q < d p then 1 else 0 : ℕ) =
        crossCount n n'' d := by
      rw [hcc]
      refine Finset.sum_congr rfl fun q _ => ?_
      by_cases hq : n'' ≤ q.val
      · by_cases hdq : (d q).val < n
        · rw [if_pos ⟨hq, by rw [Fin.lt_iff_val_lt_val]; omega⟩, if_pos ⟨hq, hdq⟩]
        · rw [if_neg (fun h => ?_), if_neg (fun h => hdq h.2)]
          have := (hlt q (by omega)).2 h.2
          rw [Fin.lt_iff_val_lt_val] at this; omega
      · simp [hq]
    rw [hsplit, h1, h2, sum_val_lt (by omega)]
  · -- `n'' ≤ p`, `n ≤ d p`
    have h1 : (∑ q : Fin m, if q.val < n'' ∧ d q < d p then 1 else 0 : ℕ) = n'' := by
      refine (Finset.sum_congr rfl fun q _ => ?_).trans (sum_val_lt hn'')
      by_cases hq : q.val < n''
      · have hlt' : d q < d p := by
          by_cases hdq : (d q).val < n
          · rw [Fin.lt_iff_val_lt_val]; omega
          · exact (hlt q (by omega)).1 (by rw [Fin.lt_iff_val_lt_val]; omega)
        rw [if_pos ⟨hq, hlt'⟩, if_pos hq]
      · simp [hq]
    have h2 : (∑ q : Fin m, if n'' ≤ q.val ∧ d q < d p then 1 else 0 : ℕ) = p.val - n'' := by
      rw [← Finset.card_filter, ← card_Ico hp p.2.le]
      congr 1; ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hq, hdq⟩
        exact ⟨hq, by have := (hbt q (by omega)).1 hdq; rwa [Fin.lt_iff_val_lt_val] at this⟩
      · rintro ⟨hq, hqp⟩
        exact ⟨hq, (hbt q (by omega)).2 (by rw [Fin.lt_iff_val_lt_val]; exact hqp)⟩
    rw [hsplit, h1, h2]; omega
  · -- `n'' ≤ p`, `d p < n`
    have h1 : (∑ q : Fin m, if q.val < n'' ∧ d q < d p then 1 else 0 : ℕ) =
        ∑ q : Fin m, if q.val < n'' ∧ (d q).val < n then 1 else 0 := by
      refine Finset.sum_congr rfl fun q _ => ?_
      by_cases hq : q.val < n''
      · by_cases hdq : (d q).val < n
        · rw [if_pos ⟨hq, (hlt q (by omega)).1 (by rw [Fin.lt_iff_val_lt_val]; omega)⟩,
            if_pos ⟨hq, hdq⟩]
        · rw [if_neg (fun h => ?_), if_neg (fun h => hdq h.2)]
          rw [Fin.lt_iff_val_lt_val] at h; exact hdq (by omega)
      · simp [hq]
    have h2 : (∑ q : Fin m, if n'' ≤ q.val ∧ d q < d p then 1 else 0 : ℕ) = p.val - n'' := by
      rw [← Finset.card_filter, ← card_Ico hp p.2.le]
      congr 1; ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hq, hdq⟩
        exact ⟨hq, by have := (hbt q (by omega)).1 hdq; rwa [Fin.lt_iff_val_lt_val] at this⟩
      · rintro ⟨hq, hqp⟩
        exact ⟨hq, (hbt q (by omega)).2 (by rw [Fin.lt_iff_val_lt_val]; exact hqp)⟩
    rw [hsplit, h1, h2]; omega

/-- Which strands of a minimal double coset representative end in the first top block. -/
theorem IsDoubleShuffle.val_lt_iff (hd : IsDoubleShuffle hJ hK d) (p : Fin m) :
    ((d p).val < n ↔ if p.val < n'' then p.val + crossCount n n'' d < n
      else p.val < n'' + crossCount n n'' d) := by
  have hn : n ≤ m := by omega
  have hn'' : n'' ≤ m := by omega
  have hbt := fun (p q : Fin m) => lt_iff_of_bot hK hd.2 (p := p) (q := q)
  have htl := card_top_left hJ hK hn d
  split_ifs with hp
  · constructor
    · intro hdp
      -- `{q | q ≤ p}` lies in `{q < n'' | d q < n}`
      have hsub : (Finset.univ.filter fun q : Fin m => q.val < p.val + 1) ⊆
          Finset.univ.filter fun q : Fin m => q.val < n'' ∧ (d q).val < n := by
        intro q hq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
        refine ⟨by omega, ?_⟩
        rcases Nat.lt_or_ge q.val p.val with h | h
        · have := (hbt p q (by omega)).2 (by rw [Fin.lt_iff_val_lt_val]; exact h)
          rw [Fin.lt_iff_val_lt_val] at this; omega
        · rw [show q = p from Fin.ext (by omega)]; exact hdp
      have := Finset.card_le_card hsub
      rw [card_val_lt (by omega)] at this
      omega
    · intro hc
      by_contra hdp
      have hsub : (Finset.univ.filter fun q : Fin m => q.val < n'' ∧ (d q).val < n) ⊆
          Finset.univ.filter fun q : Fin m => q.val < p.val := by
        intro q hq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
        by_contra hqp
        rcases Nat.lt_or_ge p.val q.val with h | h
        · have := (hbt q p (by omega)).2 (by rw [Fin.lt_iff_val_lt_val]; exact h)
          rw [Fin.lt_iff_val_lt_val] at this; omega
        · rw [show q = p from Fin.ext (by omega)] at hq; exact hdp hq.2
      have := Finset.card_le_card hsub
      rw [card_val_lt (by omega)] at this
      omega
  · constructor
    · intro hdp
      have hsub : (Finset.univ.filter fun q : Fin m => n'' ≤ q.val ∧ q.val < p.val + 1) ⊆
          Finset.univ.filter fun q : Fin m => n'' ≤ q.val ∧ (d q).val < n := by
        intro q hq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
        refine ⟨hq.1, ?_⟩
        rcases Nat.lt_or_ge q.val p.val with h | h
        · have := (hbt p q (by omega)).2 (by rw [Fin.lt_iff_val_lt_val]; exact h)
          rw [Fin.lt_iff_val_lt_val] at this; omega
        · rw [show q = p from Fin.ext (by omega)]; exact hdp
      have := Finset.card_le_card hsub
      rw [card_Ico (by omega) (by omega)] at this
      change _ ≤ crossCount n n'' d at this
      omega
    · intro hc
      by_contra hdp
      have hsub : (Finset.univ.filter fun q : Fin m => n'' ≤ q.val ∧ (d q).val < n) ⊆
          Finset.univ.filter fun q : Fin m => n'' ≤ q.val ∧ q.val < p.val := by
        intro q hq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
        refine ⟨hq.1, ?_⟩
        by_contra hqp
        rcases Nat.lt_or_ge p.val q.val with h | h
        · have := (hbt q p (by omega)).2 (by rw [Fin.lt_iff_val_lt_val]; exact h)
          rw [Fin.lt_iff_val_lt_val] at this; omega
        · rw [show q = p from Fin.ext (by omega)] at hq; exact hdp hq.2
      have := Finset.card_le_card hsub
      rw [card_Ico (by omega) (by omega)] at this
      change crossCount n n'' d ≤ _ at this
      omega

/-- **Minimal double coset representatives are determined by `|λ|`.** -/
theorem IsDoubleShuffle.eq_of_crossCount_eq {d d' : Perm (Fin m)} (hd : IsDoubleShuffle hJ hK d)
    (hd' : IsDoubleShuffle hJ hK d') (hc : crossCount n n'' d = crossCount n n'' d') :
    d = d' := by
  ext p
  have e := hd.val_eq hJ hK p
  have e' := hd'.val_eq hJ hK p
  have l := hd.val_lt_iff hJ hK p
  have l' := hd'.val_lt_iff hJ hK p
  rw [← hc] at e' l'
  by_cases hp : p.val < n''
  · simp only [hp, if_true] at l l'
    by_cases h' : p.val + crossCount n n'' d < n
    · rw [e.1 hp (l.2 h'), e'.1 hp (l'.2 h')]
    · rw [e.2.1 hp (not_lt.1 fun h => h' (l.1 h)), e'.2.1 hp (not_lt.1 fun h => h' (l'.1 h))]
  · simp only [hp, if_false] at l l'
    by_cases h' : p.val < n'' + crossCount n n'' d
    · have := e.2.2.2 (not_lt.1 hp) (l.2 h')
      have := e'.2.2.2 (not_lt.1 hp) (l'.2 h')
      omega
    · rw [e.2.2.1 (not_lt.1 hp) (not_lt.1 fun h => h' (l.1 h)),
        e'.2.2.1 (not_lt.1 hp) (not_lt.1 fun h => h' (l'.1 h))]

/-- **Double cosets are classified by `|λ|`**: two permutations lie in the same double coset
`(S_n × S_{n'}) w (S_{n''} × S_{n'''})` iff they have the same `crossCount`. -/
theorem crossCount_eq_iff_mem_doubleCoset (w w' : Perm (Fin m)) :
    crossCount n n'' w = crossCount n n'' w' ↔ ∃ (a : Perm (Fin n)) (b : Perm (Fin n'))
      (y : Perm (Fin n'')) (y' : Perm (Fin n''')),
      w' = blockPerm hJ a b * w * blockPerm hK y y' := by
  constructor
  · intro hc
    obtain ⟨a, b, d, y, y', hd, rfl, -⟩ := mackey_factorisation hJ hK w
    obtain ⟨a', b', d', z, z', hd', rfl, -⟩ := mackey_factorisation hJ hK w'
    rw [crossCount_mul_blockPerm, crossCount_blockPerm_mul, crossCount_mul_blockPerm,
      crossCount_blockPerm_mul] at hc
    obtain rfl := hd.eq_of_crossCount_eq hJ hK hd' hc
    refine ⟨a' * a⁻¹, b' * b⁻¹, y⁻¹ * z, y'⁻¹ * z', ?_⟩
    rw [← blockPerm_mul, ← blockPerm_mul]
    simp only [← blockPerm_inv, mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left]
  · rintro ⟨a, b, y, y', rfl⟩
    rw [crossCount_mul_blockPerm, crossCount_blockPerm_mul]

end Classification

/-! ### Existence: every admissible value of `|λ|` occurs -/

section Existence

variable {n n' n'' n''' : ℕ}

/-- At most `m - n''` strands start in the second bottom block. -/
theorem crossCount_le_right (n : ℕ) {n'' : ℕ} (hn'' : n'' ≤ m) (w : Perm (Fin m)) :
    crossCount n n'' w + n'' ≤ m := by
  have h1 : crossCount n n'' w ≤
      (Finset.univ.filter fun p : Fin m => n'' ≤ p.val ∧ p.val < m).card :=
    Finset.card_le_card fun p hp => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢; exact ⟨hp.1, p.2⟩
  rw [card_Ico hn'' le_rfl] at h1
  omega

/-- The explicit block permutation with `c` strands from `[n'', m)` to `[0, n)`. -/
private def blockSwapFun (n n'' c : ℕ) (p : ℕ) : ℕ :=
  if p < n'' then (if p + c < n then p else p + c)
  else (if p < n'' + c then p - n'' + n - c else p)

private theorem blockSwapFun_lt {n n'' c : ℕ} (h1 : n ≤ c + n'') (h2 : c ≤ n) (h3 : n'' + c ≤ m)
    (p : Fin m) : blockSwapFun n n'' c p.val < m := by
  have := p.2
  unfold blockSwapFun; split_ifs <;> omega

private theorem blockSwapFun_injective {n n'' c : ℕ} (h1 : n ≤ c + n'') (h2 : c ≤ n)
    {p q : ℕ} (h : blockSwapFun n n'' c p = blockSwapFun n n'' c q) : p = q := by
  unfold blockSwapFun at h; split_ifs at h <;> omega

/-- **Every admissible `|λ|` occurs**: for `n - n'' ≤ c ≤ min(n, m - n'')` there is a
permutation with exactly `c` strands from the second bottom block to the first top block. -/
theorem exists_crossCount_eq {n n'' c : ℕ} (h1 : n ≤ c + n'') (h2 : c ≤ n) (h3 : n'' + c ≤ m) :
    ∃ w : Perm (Fin m), crossCount n n'' w = c := by
  let f : Fin m → Fin m := fun p => ⟨blockSwapFun n n'' c p.val, blockSwapFun_lt h1 h2 h3 p⟩
  have hf : Function.Injective f := fun p q h =>
    Fin.ext (blockSwapFun_injective h1 h2 (congrArg Fin.val h))
  let w : Perm (Fin m) := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf)
  refine ⟨w, ?_⟩
  have hc := card_Ico (m := m) (a := n'') (b := n'' + c) (by omega) h3
  rw [show n'' + c - n'' = c by omega] at hc
  rw [crossCount, ← hc]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, w, Equiv.ofBijective_apply, f]
  unfold blockSwapFun
  split_ifs <;> omega

variable (hJ : n + n' = m) (hK : n'' + n''' = m)

/-- **Minimal double coset representatives and `λ`.** `crossCount` is a bijection from the
minimal double coset representatives onto the admissible values
`max(0, n - n'') ≤ c ≤ min(n, n''')`. -/
theorem exists_isDoubleShuffle_iff (c : ℕ) :
    (∃ d, IsDoubleShuffle hJ hK d ∧ crossCount n n'' d = c) ↔
      n ≤ c + n'' ∧ c ≤ n ∧ c ≤ n''' := by
  constructor
  · rintro ⟨d, -, rfl⟩
    have := crossCount_le_right n (show n'' ≤ m by omega) d
    exact ⟨le_crossCount d (by omega) (by omega), crossCount_le d (by omega), by omega⟩
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨w, hw⟩ := exists_crossCount_eq (m := m) h1 h2 (by omega)
    obtain ⟨a, b, d, y, y', hd, rfl, -⟩ := mackey_factorisation hJ hK w
    refine ⟨d, hd, ?_⟩
    rwa [crossCount_mul_blockPerm, crossCount_blockPerm_mul] at hw

end Existence

/-! ### The crossings of a minimal double coset representative -/

section Crossings

variable {n n' n'' n''' : ℕ} (hJ : n + n' = m) (hK : n'' + n''' = m)

/-- **The crossings of a minimal double coset representative** `d`: two strands cross iff one
of them goes from the first bottom block to the second top block and the other one from the
second bottom block to the first top block. So `ψ_d` is the diagram of the proof of KL I,
Proposition 2.18, in which the `|λ|` strands ending in `[n - |λ|, n)` cross the strands
starting in `[n - |λ|, n'')`, and no other strands cross. -/
theorem IsDoubleShuffle.mem_invSet_iff {d : Perm (Fin m)} (hd : IsDoubleShuffle hJ hK d)
    (x : Fin m × Fin m) : x ∈ invSet m d ↔
      x.1.val < n'' ∧ n'' ≤ x.2.val ∧ (d x.2).val < n ∧ n ≤ (d x.1).val := by
  rw [mem_invSet]
  obtain ⟨p, q⟩ := x
  have hbt := lt_iff_of_bot hK hd.2 (p := p) (q := q)
  have htp := lt_iff_of_top hJ hd.1 (p := p) (q := q)
  simp only [Fin.lt_iff_val_lt_val] at hbt htp ⊢
  constructor
  · rintro ⟨hpq, hdq⟩
    by_cases hq : q.val < n''
    · have := (hbt (by omega)).1 hdq; omega
    by_cases hp : p.val < n''
    · by_cases hdq' : (d q).val < n
      · by_cases hdp : (d p).val < n
        · have := (htp (by omega)).2 hdq; omega
        · omega
      · by_cases hdp : (d p).val < n
        · omega
        · have := (htp (by omega)).2 hdq; omega
    · have := (hbt (by omega)).1 hdq; omega
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨by omega, by omega⟩

end Crossings

end Categorification.TypeA
