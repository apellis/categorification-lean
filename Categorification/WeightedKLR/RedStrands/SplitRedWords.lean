/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.SplitRedLoading
import Categorification.WeightedKLR.RedStrands.StendhalPolyRep
import Categorification.TypeA.DoubleCoset

/-!
# Splitting a red strand: words

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §4.3,
Proposition 4.21. A crossing of two strands of a loading becomes, after the red strand
`λ_c` is split into `λ_c`, `λ_{c+1}`, one crossing or two crossings: a black strand crossing
`λ_c` crosses both new red strands. This file expands words accordingly.

## Main definitions

* `wLetters j q` : the letters replacing the crossing `s_j` of a loading whose red strand
  `λ_c` sits at `q`.
* `expandWord c s ρ` : the word `ρ`, acting on the loading `s`, with each letter replaced.

## Main results

* `splitLoading_wordProd` : the expanded word acts on the split loading as `ρ` acts on `s`.
* `wordProd_expandWord_splitPos`, `wordProd_expandWord_newPos` : the expanded word moves the
  old strands as `ρ` does and the new red strand along with `λ_c`.
* `isReduced_expandWord` : expanding a reduced word gives a reduced word.
* `noRedCross_expandWord` : expanding a word that exchanges no two red strands gives such a
  word.
-/

noncomputable section

namespace Categorification.Stendhal.SplitRed

open KLR TypeA Equiv

variable {I : Type} {ℓ : ℕ} (c : Fin ℓ) {ν : Multiset I} [DecidableEq I]

local notation "μ" => stendhalWeight ℓ ν
local notation "μ'" => stendhalWeight (ℓ + 1) ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "m'" => Multiset.card (stendhalWeight (ℓ + 1) ν)

/-- The letters replacing the crossing `s_j` when the red strand `λ_c` sits at `q`. -/
def wLetters (j q : ℕ) : List ℕ :=
  if j + 1 < q then [j] else if j + 1 = q then [j + 1, j] else if j = q then [j, j + 1]
  else [j + 1]

/-- The word `ρ`, acting on `s`, with each crossing replaced by its letters in the split
loading. The rightmost letter acts first. -/
def expandWord (s : Seq μ) : List ℕ → List ℕ
  | [] => []
  | j :: ρ => wLetters j (redPos c (wordProd m ρ • s)) ++ expandWord s ρ

@[simp] theorem expandWord_nil (s : Seq μ) : expandWord c s [] = [] := rfl

theorem expandWord_cons (s : Seq μ) (j : ℕ) (ρ : List ℕ) :
    expandWord c s (j :: ρ) = wLetters j (redPos c (wordProd m ρ • s)) ++ expandWord c s ρ :=
  rfl

omit [DecidableEq I] in
theorem m'_eq : m' = m + 1 := card_split ℓ ν

/-- One crossing of the old loading. -/
theorem splitLoading_sadj (t : Seq μ) {j : ℕ} (hj : j + 1 < m) :
    splitLoading c (sadj m j • t) =
      wordProd m' (wLetters j (redPos c t)) • splitLoading c t := by
  unfold wLetters
  split_ifs with h1 h2 h3
  · simp [splitLoading_sadj_left c t h1]
  · simp [splitLoading_sadj_cross_left c t h2, mul_smul]
  · simp [splitLoading_sadj_cross_right c t h3 hj, mul_smul]
  · simp [splitLoading_sadj_right c t (by omega) hj]

theorem splitLoading_wordProd (s : Seq μ) {ρ : List ℕ} (hρ : ValidWord m ρ) :
    splitLoading c (wordProd m ρ • s) = wordProd m' (expandWord c s ρ) • splitLoading c s := by
  induction ρ with
  | nil => simp
  | cons j ρ ih =>
    rw [validWord_cons] at hρ
    rw [wordProd_cons, mul_smul, splitLoading_sadj c _ hρ.1, ih hρ.2, expandWord_cons,
      wordProd_append, mul_smul]

/-! ### Positions -/

theorem splitPos_eq_of_le (t : Seq μ) {a : ℕ} (ha : a ≤ redPos c t) (h : a < m') :
    (⟨a, h⟩ : Fin m') = splitPos c t ⟨a, by have := (redPos c t).2; omega⟩ := by
  ext; rw [splitPos_val]; simp [ha]

theorem splitPos_eq_of_lt (t : Seq μ) {a : ℕ} (ha : (redPos c t : ℕ) < a) (hm : a < m)
    (h : a + 1 < m') : (⟨a + 1, h⟩ : Fin m') = splitPos c t ⟨a, hm⟩ := by
  ext; rw [splitPos_val]; simp only; split_ifs <;> omega

theorem newPos_eq (t : Seq μ) (h : (redPos c t : ℕ) + 1 < m') :
    (⟨redPos c t + 1, h⟩ : Fin m') = newPos c t := by
  ext; rw [newPos_val]

omit [DecidableEq I] in
/-- The value of a word at a point, computed with `swapNat`. -/
theorem wordProd_val {n : ℕ} {ρ : List ℕ} (hρ : ValidWord n ρ) (y : Fin n) :
    (wordProd n ρ y : ℕ) = ρ.foldr swapNat y := by
  induction ρ with
  | nil => rfl
  | cons k ρ ih =>
    rw [validWord_cons] at hρ
    rw [wordProd_cons, Perm.mul_apply, sadj_val_of_lt hρ.1, ih hρ.2, List.foldr_cons]

omit [DecidableEq I] in
theorem validWord_wLetters {j q n : ℕ} (hj : j + 1 + 1 < n) : ValidWord n (wLetters j q) := by
  unfold wLetters; split_ifs <;> simp <;> omega

omit [DecidableEq I] in
theorem foldr_wLetters_old (j q x : ℕ) :
    (wLetters j q).foldr swapNat (if x ≤ q then x else x + 1) =
      if swapNat j x ≤ swapNat j q then swapNat j x else swapNat j x + 1 := by
  unfold wLetters
  by_cases h1 : j + 1 < q
  · simp only [h1, ↓reduceIte, List.foldr_cons, List.foldr_nil]
    unfold swapNat; split_ifs <;> omega
  by_cases h2 : j + 1 = q
  · subst h2; simp only [h1, ↓reduceIte, List.foldr_cons, List.foldr_nil]
    unfold swapNat; split_ifs <;> omega
  by_cases h3 : j = q
  · subst h3; simp only [h1, h2, ↓reduceIte, List.foldr_cons, List.foldr_nil]
    unfold swapNat; split_ifs <;> omega
  · simp only [h1, h2, h3, ↓reduceIte, List.foldr_cons, List.foldr_nil]
    unfold swapNat; split_ifs <;> omega

omit [DecidableEq I] in
theorem foldr_wLetters_new (j q : ℕ) :
    (wLetters j q).foldr swapNat (q + 1) = swapNat j q + 1 := by
  unfold wLetters swapNat; split_ifs <;> simp <;> split_ifs <;> omega

/-- One crossing moves the old strands as it does in the old loading. -/
theorem wLetters_splitPos (t : Seq μ) {j : ℕ} (hj : j + 1 < m) (a : Fin m) :
    wordProd m' (wLetters j (redPos c t)) (splitPos c t a) =
      splitPos c (sadj m j • t) (sadj m j a) := by
  have hm' := m'_eq (ν := ν) (ℓ := ℓ)
  ext
  rw [wordProd_val (validWord_wLetters (by omega)), splitPos_val, splitPos_val,
    sadj_val_of_lt hj, redPos_sadj_val c t hj, foldr_wLetters_old]

theorem wLetters_newPos (t : Seq μ) {j : ℕ} (hj : j + 1 < m) :
    wordProd m' (wLetters j (redPos c t)) (newPos c t) = newPos c (sadj m j • t) := by
  have hm' := m'_eq (ν := ν) (ℓ := ℓ)
  ext
  rw [wordProd_val (validWord_wLetters (by omega)), newPos_val, newPos_val,
    redPos_sadj_val c t hj, foldr_wLetters_new]

theorem wordProd_expandWord_splitPos (s : Seq μ) {ρ : List ℕ} (hρ : ValidWord m ρ)
    (a : Fin m) :
    wordProd m' (expandWord c s ρ) (splitPos c s a) =
      splitPos c (wordProd m ρ • s) (wordProd m ρ a) := by
  induction ρ with
  | nil => rfl
  | cons j ρ ih =>
    rw [validWord_cons] at hρ
    rw [expandWord_cons, wordProd_append, Perm.mul_apply, ih hρ.2, wLetters_splitPos c _ hρ.1,
      wordProd_cons, mul_smul, Perm.mul_apply]

theorem wordProd_expandWord_newPos (s : Seq μ) {ρ : List ℕ} (hρ : ValidWord m ρ) :
    wordProd m' (expandWord c s ρ) (newPos c s) = newPos c (wordProd m ρ • s) := by
  induction ρ with
  | nil => rfl
  | cons j ρ ih =>
    rw [validWord_cons] at hρ
    rw [expandWord_cons, wordProd_append, Perm.mul_apply, ih hρ.2, wLetters_newPos c _ hρ.1,
      wordProd_cons, mul_smul]

theorem inv_wordProd_expandWord_splitPos (s : Seq μ) {ρ : List ℕ} (hρ : ValidWord m ρ)
    (b : Fin m) :
    (wordProd m' (expandWord c s ρ))⁻¹ (splitPos c (wordProd m ρ • s) b) =
      splitPos c s ((wordProd m ρ)⁻¹ b) := by
  rw [Perm.inv_eq_iff_eq, wordProd_expandWord_splitPos c s hρ]; simp

theorem inv_wordProd_expandWord_newPos (s : Seq μ) {ρ : List ℕ} (hρ : ValidWord m ρ) :
    (wordProd m' (expandWord c s ρ))⁻¹ (newPos c (wordProd m ρ • s)) = newPos c s := by
  rw [Perm.inv_eq_iff_eq, wordProd_expandWord_newPos c s hρ]

/-! ### Reduced words -/

omit [DecidableEq I] in
theorem isReduced_cons_of_lt {n a : ℕ} {γ : List ℕ} (h : IsReduced n γ) (ha : a + 1 < n)
    (hlt : (wordProd n γ)⁻¹ ⟨a, by omega⟩ < (wordProd n γ)⁻¹ ⟨a + 1, ha⟩) :
    IsReduced n (a :: γ) := by
  refine ⟨validWord_cons.2 ⟨ha, h.1⟩, ?_⟩
  rw [wordProd_cons, length_sadj_mul_of_lt ha hlt, ← h.2]; rfl

theorem redPos_eq_inv (s : Seq μ) (v : Perm (Fin m)) : redPos c s = v⁻¹ (redPos c (v • s)) := by
  rw [redPos_smul]; simp

/-- **Expanding a reduced word gives a reduced word.** -/
theorem isReduced_expandWord (s : Seq μ) {ρ : List ℕ} (hρ : IsReduced m ρ) :
    IsReduced m' (expandWord c s ρ) := by
  induction ρ with
  | nil => exact ⟨validWord_nil _, by simp⟩
  | cons j ρ ih =>
    obtain ⟨hj, hρ', hlt⟩ := hρ.cons_inv
    have IH := ih hρ'
    have hv := hρ'.1
    have hm' := m'_eq (ν := ν) (ℓ := ℓ)
    have hS := inv_wordProd_expandWord_splitPos c s hv
    have hN := inv_wordProd_expandWord_newPos c s hv
    have hred := redPos_eq_inv c s (wordProd m ρ)
    rw [expandWord_cons]
    unfold wLetters
    set v := wordProd m ρ
    set E := expandWord c s ρ
    split_ifs with h1 h2 h3
    · apply isReduced_cons_of_lt IH (by omega)
      rw [splitPos_eq_of_le c (v • s) (a := j) (by omega),
        splitPos_eq_of_le c (v • s) (a := j + 1) (by omega), hS, hS, splitPos_lt_splitPos_iff]
      exact hlt
    · have hq : redPos c (v • s) = ⟨j + 1, hj⟩ := Fin.ext h2.symm
      have step : IsReduced m' (j :: E) := by
        apply isReduced_cons_of_lt IH (by omega)
        rw [splitPos_eq_of_le c (v • s) (a := j) (by omega),
          splitPos_eq_of_le c (v • s) (a := j + 1) (by omega), hS, hS,
          splitPos_lt_splitPos_iff]
        exact hlt
      apply isReduced_cons_of_lt step (by omega)
      rw [wordProd_cons, mul_inv_rev, sadj_inv, Perm.mul_apply, Perm.mul_apply,
        sadj_apply_right (by omega), sadj_apply_of_ne _ (by simp only [ne_eq]; omega)
          (by simp only [ne_eq]; omega),
        splitPos_eq_of_le c (v • s) (a := j) (by omega)]
      rw [show (⟨j + 1 + 1, by omega⟩ : Fin m') = newPos c (v • s) from
        (newPos_eq c (v • s) (by omega)).symm.trans (by ext; simp [h2]) |>.symm, hS, hN,
        Fin.lt_def, splitPos_val, newPos_val, hred]
      simp only [hq]
      have := Fin.lt_def.1 hlt
      split_ifs <;> omega
    · have hq : redPos c (v • s) = ⟨j, by omega⟩ := Fin.ext h3.symm
      have step : IsReduced m' ((j + 1) :: E) := by
        apply isReduced_cons_of_lt IH (by omega)
        rw [show (⟨j + 1, by omega⟩ : Fin m') = newPos c (v • s) by ext; simp [newPos_val, h3],
          splitPos_eq_of_lt c (v • s) (a := j + 1) (by omega) hj, hS, hN, Fin.lt_def,
          splitPos_val, newPos_val, hred]
        simp only [hq]
        have := Fin.lt_def.1 hlt
        split_ifs <;> omega
      apply isReduced_cons_of_lt step (by omega)
      rw [wordProd_cons, mul_inv_rev, sadj_inv, Perm.mul_apply, Perm.mul_apply,
        sadj_apply_left (by omega), sadj_apply_of_ne _ (by simp only [ne_eq]; omega)
          (by simp only [ne_eq]; omega),
        splitPos_eq_of_le c (v • s) (a := j) (by omega),
        splitPos_eq_of_lt c (v • s) (a := j + 1) (by omega) hj, hS, hS,
        splitPos_lt_splitPos_iff]
      exact hlt
    · apply isReduced_cons_of_lt IH (by omega)
      rw [splitPos_eq_of_lt c (v • s) (a := j) (by omega) (by omega),
        splitPos_eq_of_lt c (v • s) (a := j + 1) (by omega) hj, hS, hS,
        splitPos_lt_splitPos_iff]
      exact hlt

end Categorification.Stendhal.SplitRed
