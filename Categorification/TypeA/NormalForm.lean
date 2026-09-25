/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TypeA.Length

/-!
# A normal form for words in adjacent transpositions

We construct canonical reduced words for permutations of `Fin m` and prove that every valid
word can be brought, by braid moves alone, either to the canonical word of the permutation it
represents or to a word containing two equal adjacent letters.

## Canonical words

For `0 ≤ b ≤ t + 1` let `descRun b (t + 1 - b) = [t, t - 1, …, b]` be the descending run from
`t` down to `b` (empty when `b = t + 1`). A *code* of length `n` is a list `[b_{n-1}, …, b_0]`
with `b_t ≤ t + 1` (so the head of the list governs the top run), and its word is
```
codeWord [b_{n-1}, …, b_0] = [0, …, b_0] ++ [1, …, b_1] ++ ⋯ ++ [n - 1, …, b_{n-1}]
```
where `[t, …, b]` denotes the descending run. Codes of length `m - 1` are in bijection with
`Equiv.Perm (Fin m)` via `c ↦ wordProd m (codeWord c)`: surjectivity comes from the normal
form argument below together with minimality of reduced words, and injectivity from evaluating
at the bottom `b_{n-1}` of the top run, which is sent to `n` (`codeWord_injective`).
`canWord m w` is the word of the unique code of `w`.

## Main results

* `TypeA.codeWord_append_singleton` : appending a letter to a code word gives, up to braid moves,
  another code word or a word with a repeated adjacent letter.
* `TypeA.braidEquiv_canWord_or_hasRepeat` (normal form theorem): every valid word `ρ` is
  braid equivalent to `canWord m (wordProd m ρ)` or to a word with a repeated adjacent letter.
* `TypeA.wordProd_canWord`, `TypeA.validWord_canWord`, `TypeA.length_canWord`,
  `TypeA.isReduced_canWord` : `canWord m w` is a reduced word for `w`.

The descending-run manipulations used are: letters below `b - 1` commute past the run
`[t, …, b]`; the letter `b - 1` extends it; the letter `b` produces a repeat; and for
`b ≤ j < t`, `[t, …, b] ++ [j + 1] ≈ j :: [t, …, b]` (commutations and one braid move).
-/

namespace Categorification.TypeA

open Equiv

/-! ## Descending runs -/

/-- The descending run `[b + l - 1, …, b + 1, b]` of length `l` ending at `b`. -/
def descRun (b l : ℕ) : List ℕ := (List.range' b l).reverse

@[simp] theorem descRun_zero (b : ℕ) : descRun b 0 = [] := rfl

@[simp] theorem length_descRun (b l : ℕ) : (descRun b l).length = l := by
  simp [descRun]

theorem mem_descRun {b l x : ℕ} : x ∈ descRun b l ↔ b ≤ x ∧ x < b + l := by
  simp only [descRun, List.mem_reverse, List.mem_range'_1]

theorem descRun_add (b l₁ l₂ : ℕ) : descRun b (l₁ + l₂) = descRun (b + l₁) l₂ ++ descRun b l₁ := by
  have h := List.range'_append (s := b) (m := l₁) (n := l₂) (step := 1)
  rw [one_mul] at h
  simp only [descRun, ← List.reverse_append, h]

theorem descRun_one (b : ℕ) : descRun b 1 = [b] := rfl

theorem descRun_two (b : ℕ) : descRun b 2 = [b + 1, b] := rfl

/-- Peel the bottom letter off a nonempty descending run. -/
theorem descRun_succ (b l : ℕ) : descRun b (l + 1) = descRun (b + 1) l ++ [b] := by
  rw [Nat.add_comm l 1, descRun_add, descRun_one]

/-! ## Codes and code words -/

/-- A code: a list `[b_{n-1}, …, b_0]` of natural numbers with `b_t ≤ t + 1`. The head of
the list is the entry of largest index. -/
def IsCode : List ℕ → Prop
  | [] => True
  | b :: c => b ≤ c.length + 1 ∧ IsCode c

@[simp] theorem isCode_nil : IsCode [] := trivial

@[simp] theorem isCode_cons {b : ℕ} {c : List ℕ} : IsCode (b :: c) ↔ b ≤ c.length + 1 ∧ IsCode c :=
  Iff.rfl

/-- The word of a code: the concatenation of the descending runs `[t, …, b_t]`, for
`t = 0, 1, …, n - 1` in increasing order. -/
def codeWord : List ℕ → List ℕ
  | [] => []
  | b :: c => codeWord c ++ descRun b (c.length + 1 - b)

@[simp] theorem codeWord_nil : codeWord [] = [] := rfl

theorem codeWord_cons (b : ℕ) (c : List ℕ) :
    codeWord (b :: c) = codeWord c ++ descRun b (c.length + 1 - b) := rfl

/-- All letters of the word of a code of length `n` are smaller than `n`. -/
theorem lt_of_mem_codeWord {c : List ℕ} {x : ℕ} (hx : x ∈ codeWord c) : x < c.length := by
  induction c with
  | nil => simp at hx
  | cons b c ih =>
    rw [codeWord_cons, List.mem_append, mem_descRun] at hx
    rcases hx with hx | hx
    · have := ih hx; simp; omega
    · simp; omega

/-- The code of the identity permutation: all runs are empty. -/
def idCode : ℕ → List ℕ
  | 0 => []
  | n + 1 => (n + 1) :: idCode n

@[simp] theorem length_idCode (n : ℕ) : (idCode n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [idCode, ih]

theorem isCode_idCode (n : ℕ) : IsCode (idCode n) := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨by simp, ih⟩

@[simp] theorem codeWord_idCode (n : ℕ) : codeWord (idCode n) = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [idCode, codeWord_cons, ih]

/-! ## Braid moves on code words -/

/-- For `b ≤ j < t`, `[t, …, b] ++ [j + 1] ≈ j :: [t, …, b]`. -/
theorem braidEquiv_descRun_append_middle {b j t : ℕ} (hbj : b ≤ j) (hjt : j < t) :
    BraidEquiv (descRun b (t + 1 - b) ++ [j + 1]) (j :: descRun b (t + 1 - b)) := by
  have hR : descRun b (t + 1 - b) = descRun (j + 2) (t - j - 1) ++ [j + 1, j] ++ descRun b (j - b) := by
    rw [show t + 1 - b = (j - b) + (2 + (t - j - 1)) by omega, descRun_add,
      show b + (j - b) = j by omega, descRun_add, descRun_two, List.append_assoc]
  rw [hR]
  set H := descRun (j + 2) (t - j - 1)
  set L := descRun b (j - b)
  have hL : ∀ x ∈ L, x + 1 < j + 1 ∨ j + 1 + 1 < x := fun x hx => by
    rw [mem_descRun] at hx; omega
  have hH : ∀ x ∈ H, x + 1 < j ∨ j + 1 < x := fun x hx => by
    rw [mem_descRun] at hx; omega
  -- move `j + 1` left past `L`
  have e1 : BraidEquiv (H ++ [j + 1, j] ++ L ++ [j + 1]) (H ++ [j + 1, j, j + 1] ++ L) := by
    have := (braidEquiv_append_singleton_of_distant hL).append_left (H ++ [j + 1, j])
    simpa using this
  -- braid move
  have e2 : BraidEquiv (H ++ [j + 1, j, j + 1] ++ L) (H ++ [j, j + 1, j] ++ L) :=
    braidEquiv_braid_symm H L j
  -- move `j` left past `H`
  have e3 : BraidEquiv (H ++ [j, j + 1, j] ++ L) (j :: (H ++ [j + 1, j] ++ L)) := by
    have := (braidEquiv_append_singleton_of_distant hH).append_right ([j + 1, j] ++ L)
    simpa using this
  exact e1.trans (e2.trans e3)

/-- **Key lemma.** Appending a letter `k < n` to the word of a code of length `n` gives, up to
braid moves, either the word of another code of length `n` or a word with two equal adjacent
letters. -/
theorem codeWord_append_singleton {c : List ℕ} (hc : IsCode c) {k : ℕ} (hk : k < c.length) :
    (∃ c', IsCode c' ∧ c'.length = c.length ∧ BraidEquiv (codeWord c ++ [k]) (codeWord c')) ∨
      ∃ σ, BraidEquiv (codeWord c ++ [k]) σ ∧ HasRepeat σ := by
  induction c generalizing k with
  | nil => simp at hk
  | cons b c ih =>
    rw [isCode_cons] at hc
    simp only [List.length_cons] at hk ⊢
    set t := c.length with ht
    set R := descRun b (t + 1 - b) with hR
    rw [codeWord_cons]
    -- reduction: if `R ++ [k] ≈ j :: R` with `j < t`, conclude by induction
    have reduce : ∀ j, j < t → BraidEquiv (R ++ [k]) (j :: R) →
        (∃ c', IsCode c' ∧ c'.length = t + 1 ∧ BraidEquiv (codeWord c ++ R ++ [k]) (codeWord c'))
          ∨ ∃ σ, BraidEquiv (codeWord c ++ R ++ [k]) σ ∧ HasRepeat σ := by
      intro j hj hRj
      have e : BraidEquiv (codeWord c ++ R ++ [k]) (codeWord c ++ [j] ++ R) := by
        simpa using hRj.append_left (codeWord c)
      rcases ih hc.2 hj with ⟨c₁, hc₁, hl₁, h₁⟩ | ⟨σ, h₁, hσ⟩
      · refine Or.inl ⟨b :: c₁, ⟨by omega, hc₁⟩, by simp [hl₁], ?_⟩
        rw [codeWord_cons, hl₁]
        exact e.trans (h₁.append_right R)
      · exact Or.inr ⟨σ ++ R, e.trans (h₁.append_right R), hσ.append_right R⟩
    rcases lt_trichotomy (k + 1) b with hkb | hkb | hkb
    · -- `k` commutes past the run
      refine reduce k (by omega) (braidEquiv_append_singleton_of_distant fun x hx => ?_)
      rw [hR, mem_descRun] at hx; omega
    · -- `k` extends the run
      refine Or.inl ⟨k :: c, ⟨by omega, hc.2⟩, by simp [ht], ?_⟩
      rw [codeWord_cons, ← ht, show t + 1 - k = (t + 1 - b) + 1 by omega, descRun_succ,
        show k + 1 = b by omega, List.append_assoc]
      exact BraidEquiv.refl _
    · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hkb) with hkb' | hkb'
      · -- `k = j + 1` with `b ≤ j < t`
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        exact reduce j (by omega) (braidEquiv_descRun_append_middle (by omega) (by omega))
      · -- `k = b` gives a repeated letter
        refine Or.inr ⟨_, BraidEquiv.refl _, ?_⟩
        rw [hkb', show c.length + 1 - k = (c.length - k) + 1 by omega, descRun_succ]
        simpa using hasRepeat_append_pair (codeWord c ++ descRun (k + 1) (c.length - k)) [] k

/-- Every word with letters `< n` is braid equivalent to the word of a code of length `n` or to
a word with two equal adjacent letters. -/
theorem exists_codeWord_or_hasRepeat (n : ℕ) {ρ : List ℕ} (hρ : ∀ x ∈ ρ, x < n) :
    (∃ c, IsCode c ∧ c.length = n ∧ BraidEquiv ρ (codeWord c)) ∨
      ∃ σ, BraidEquiv ρ σ ∧ HasRepeat σ := by
  induction ρ using List.reverseRecOn with
  | nil =>
    refine Or.inl ⟨idCode n, isCode_idCode n, length_idCode n, ?_⟩
    rw [codeWord_idCode]
    exact BraidEquiv.refl _
  | append_singleton ρ k ih =>
    have hk : k < n := hρ k (by simp)
    rcases ih fun x hx => hρ x (by simp [hx]) with ⟨c, hc, hl, h⟩ | ⟨σ, h, hσ⟩
    · rcases codeWord_append_singleton hc (k := k) (by omega) with ⟨c', hc', hl', h'⟩ | ⟨σ, h', hσ⟩
      · exact Or.inl ⟨c', hc', by omega, (h.append_right [k]).trans h'⟩
      · exact Or.inr ⟨σ, (h.append_right [k]).trans h', hσ⟩
    · exact Or.inr ⟨σ ++ [k], h.append_right [k], hσ.append_right [k]⟩

/-! ## Injectivity of code words -/

theorem wordProd_apply_of_forall_ne {m : ℕ} {ρ : List ℕ} {i : Fin m}
    (h : ∀ x ∈ ρ, x ≠ i ∧ x + 1 ≠ i) : wordProd m ρ i = i := by
  induction ρ with
  | nil => rfl
  | cons k ρ ih =>
    have hk := h k (by simp)
    rw [wordProd_cons, Perm.mul_apply, ih fun x hx => h x (by simp [hx]),
      sadj_apply_of_ne i (Ne.symm hk.1) (Ne.symm hk.2)]

/-- The run `[b + l - 1, …, b]` sends `b` to `b + l`. -/
theorem wordProd_descRun_apply {m b l : ℕ} (h : b + l < m) :
    wordProd m (descRun b l) ⟨b, by omega⟩ = ⟨b + l, h⟩ := by
  induction l generalizing b with
  | zero => rfl
  | succ l ih =>
    rw [descRun_succ, wordProd_append, wordProd_singleton, Perm.mul_apply,
      sadj_apply_left (by omega), ih (by omega)]
    ext; simp; omega

/-- The word of a code of length `n` sends the bottom of its top run to `n`. -/
theorem wordProd_codeWord_cons_apply {m b : ℕ} {c : List ℕ} (hb : b ≤ c.length + 1)
    (hm : c.length + 1 < m) :
    wordProd m (codeWord (b :: c)) ⟨b, by omega⟩ = ⟨c.length + 1, hm⟩ := by
  rw [codeWord_cons, wordProd_append, Perm.mul_apply,
    wordProd_descRun_apply (show b + (c.length + 1 - b) < m by omega)]
  have e : (⟨b + (c.length + 1 - b), by omega⟩ : Fin m) = ⟨c.length + 1, hm⟩ := by
    ext; simp; omega
  rw [e]
  exact wordProd_apply_of_forall_ne fun x hx => by
    have := lt_of_mem_codeWord hx; simp; omega

/-- Distinct codes of the same length `< m` give distinct permutations of `Fin m`. -/
theorem codeWord_injective {m : ℕ} {c c' : List ℕ} (hc : IsCode c) (hc' : IsCode c')
    (hl : c.length = c'.length) (hm : c.length < m)
    (h : wordProd m (codeWord c) = wordProd m (codeWord c')) : c = c' := by
  induction c generalizing c' with
  | nil => exact (List.length_eq_zero_iff.1 hl.symm).symm
  | cons b c ih =>
    obtain _ | ⟨b', c'⟩ := c'
    · simp at hl
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl hm
    rw [isCode_cons] at hc hc'
    have e1 := wordProd_codeWord_cons_apply hc.1 hm
    have e2 := wordProd_codeWord_cons_apply (m := m) hc'.1 (by omega)
    simp only [hl, h] at e1 e2
    have hb : b = b' := by
      have := (wordProd m (codeWord (b' :: c'))).injective (e1.trans e2.symm)
      simpa using this
    subst hb
    rw [codeWord_cons, codeWord_cons, wordProd_append, wordProd_append, hl] at h
    rw [ih hc.2 hc'.2 hl (by omega) (mul_right_cancel h)]

/-! ## Canonical words -/

/-- Every permutation of `Fin m` is represented by the word of a code of length `m - 1`. -/
theorem exists_code (m : ℕ) (w : Perm (Fin m)) :
    ∃ c, IsCode c ∧ c.length = m - 1 ∧ wordProd m (codeWord c) = w := by
  obtain ⟨ρ, hv, hw, hl⟩ := exists_word_length_eq m w
  rcases exists_codeWord_or_hasRepeat (m - 1) (ρ := ρ) (fun x hx => by have := hv x hx; omega)
    with ⟨c, hc, hl', h⟩ | ⟨σ, h, hσ⟩
  · exact ⟨c, hc, hl', by rw [← h.wordProd_eq hv, hw]⟩
  · exfalso
    have := length_wordProd_add_two_le_of_hasRepeat (h.validWord_iff.1 hv) hσ
    rw [← h.wordProd_eq hv, hw, ← h.length_eq, hl] at this
    omega

/-- The code of a permutation `w` of `Fin m`: the unique code of length `m - 1` whose word
represents `w`. -/
noncomputable def code (m : ℕ) (w : Perm (Fin m)) : List ℕ :=
  (exists_code m w).choose

theorem isCode_code (m : ℕ) (w : Perm (Fin m)) : IsCode (code m w) :=
  (exists_code m w).choose_spec.1

theorem length_code (m : ℕ) (w : Perm (Fin m)) : (code m w).length = m - 1 :=
  (exists_code m w).choose_spec.2.1

/-- The canonical word of a permutation `w` of `Fin m`: the word of its code, i.e. the
concatenation of descending runs `[t, …, b_t]` for `t = 0, …, m - 2`. -/
noncomputable def canWord (m : ℕ) (w : Perm (Fin m)) : List ℕ :=
  codeWord (code m w)

@[simp] theorem wordProd_canWord (m : ℕ) (w : Perm (Fin m)) : wordProd m (canWord m w) = w :=
  (exists_code m w).choose_spec.2.2

theorem validWord_canWord (m : ℕ) (w : Perm (Fin m)) : ValidWord m (canWord m w) := by
  intro x hx
  have := lt_of_mem_codeWord hx
  rw [length_code] at this
  omega

/-- The code of the permutation represented by a code word is that code. -/
theorem code_wordProd_codeWord {m : ℕ} {c : List ℕ} (hc : IsCode c) (hl : c.length = m - 1) :
    code m (wordProd m (codeWord c)) = c := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [List.length_eq_zero_iff.1 hl]
    exact List.length_eq_zero_iff.1 (length_code _ _)
  · exact codeWord_injective (isCode_code _ _) hc (by rw [length_code, hl]) (by
      rw [length_code]; omega) (wordProd_canWord _ _)

theorem canWord_wordProd_codeWord {m : ℕ} {c : List ℕ} (hc : IsCode c) (hl : c.length = m - 1) :
    canWord m (wordProd m (codeWord c)) = codeWord c := by
  rw [canWord, code_wordProd_codeWord hc hl]

/-! ## The normal form theorem -/

/-- **Normal form theorem.** Every valid word is braid equivalent either to the canonical word
of the permutation it represents, or to a word containing two equal adjacent letters. -/
theorem braidEquiv_canWord_or_hasRepeat {m : ℕ} {ρ : List ℕ} (hv : ValidWord m ρ) :
    BraidEquiv ρ (canWord m (wordProd m ρ)) ∨ ∃ σ, BraidEquiv ρ σ ∧ HasRepeat σ := by
  rcases exists_codeWord_or_hasRepeat (m - 1) (ρ := ρ) (fun x hx => by have := hv x hx; omega)
    with ⟨c, hc, hl, h⟩ | h
  · left
    rwa [h.wordProd_eq hv, canWord_wordProd_codeWord hc hl]
  · exact Or.inr h

/-- The canonical word has the length of the permutation it represents. -/
theorem length_canWord (m : ℕ) (w : Perm (Fin m)) : (canWord m w).length = length m w := by
  obtain ⟨ρ, hv, hw, hl⟩ := exists_word_length_eq m w
  rcases braidEquiv_canWord_or_hasRepeat hv with h | ⟨σ, h, hσ⟩
  · rw [← hl, h.length_eq, hw]
  · exfalso
    have := length_wordProd_add_two_le_of_hasRepeat (h.validWord_iff.1 hv) hσ
    rw [← h.wordProd_eq hv, hw, ← h.length_eq, hl] at this
    omega

/-- The canonical word is a reduced word. -/
theorem isReduced_canWord (m : ℕ) (w : Perm (Fin m)) : IsReduced m (canWord m w) :=
  ⟨validWord_canWord m w, by rw [length_canWord, wordProd_canWord]⟩

end Categorification.TypeA
