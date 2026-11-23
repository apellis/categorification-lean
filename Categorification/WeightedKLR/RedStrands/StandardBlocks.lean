/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.StandardAction
import Categorification.KLR.WindowBlock

/-!
# The blocks of black strands between the red strands

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1, the
map `℘_α` of Proposition 5.3. A root function `α` cuts the black strands into the blocks
`α(0), α(1), …, α(ℓ)` lying between consecutive red strands; `℘_α` places diagrams of
`R_{α(0)} ⊗ R_{α(1)} ⊗ ⋯ ⊗ R_{α(ℓ)}` side by side, with the red strands straight in between.

Here a root function is presented by the black weights `b j` of its blocks: the root function
`blockRoot b` counts, for the red strand `λ_r`, the black strands of the first `r + 1` blocks.
For a sequence `s` with red strands in order and root function `blockRoot b`, the red strand
`λ_r` sits at position `r + |b 0| + ⋯ + |b r|` (`redPos_val`), and the labels of the block
`j` of positions are a sequence of weight `b j` (`map_window`). So the block `j` gives a block
embedding of the KLR algebra of `b j` into the corner of `e_α` (`StendhalAlgebra.blockEmb`).

## Main definitions

* `Stendhal.blockPrefix`, `blockRoot`, `blockStart`: the weight of the first blocks, the root
  function and the first position of a block.
* `Stendhal.redPos`, `Stendhal.countBefore`: the position of a red strand and the number of
  positions before a point with a given label.
* `Stendhal.StendhalAlgebra.blockEmb`: the block embedding of the block `j`.
-/

namespace Categorification.Stendhal

open KLR KLRAlgebra

variable {I : Type*} {ℓ : ℕ}

/-! ### Block weights -/

section Blocks

variable (b : Fin (ℓ + 1) → Multiset I)

/-- The black weight `b 0 + ⋯ + b (n - 1)` of the first `n` blocks. -/
def blockPrefix (n : ℕ) : Multiset I :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin (ℓ + 1) => j.val < n), b j

/-- The root function of the blocks `b`: the number of black `i`-strands left of `λ_r`. -/
def blockRoot [DecidableEq I] (r : Fin ℓ) (i : I) : ℕ := (blockPrefix b (r + 1)).count i

/-- The first position `j + |b 0| + ⋯ + |b (j - 1)|` of the block `j`. -/
def blockStart (j : ℕ) : ℕ := j + Multiset.card (blockPrefix b j)

@[simp] theorem blockPrefix_zero : blockPrefix b 0 = 0 := by
  simp [blockPrefix]

theorem blockPrefix_succ {j : ℕ} (hj : j < ℓ + 1) :
    blockPrefix b (j + 1) = blockPrefix b j + b ⟨j, hj⟩ := by
  have : Finset.univ.filter (fun x : Fin (ℓ + 1) => x.val < j + 1) =
      insert ⟨j, hj⟩ (Finset.univ.filter fun x : Fin (ℓ + 1) => x.val < j) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  rw [blockPrefix, blockPrefix, this, Finset.sum_insert (by simp), add_comm]

theorem blockPrefix_of_le {n : ℕ} (hn : ℓ + 1 ≤ n) : blockPrefix b n = ∑ j, b j := by
  rw [blockPrefix, Finset.filter_true_of_mem fun j _ => by omega]

theorem blockPrefix_mono {n n' : ℕ} (h : n ≤ n') : blockPrefix b n ≤ blockPrefix b n' := by
  rw [blockPrefix, blockPrefix, ← Finset.sum_filter_add_sum_filter_not
    (Finset.univ.filter fun j : Fin (ℓ + 1) => j.val < n') (fun j => j.val < n),
    Finset.filter_filter]
  have : Finset.univ.filter (fun j : Fin (ℓ + 1) => j.val < n' ∧ j.val < n) =
      Finset.univ.filter fun j : Fin (ℓ + 1) => j.val < n := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  rw [this]
  exact le_self_add

theorem blockStart_succ {j : ℕ} (hj : j < ℓ + 1) :
    blockStart b (j + 1) = blockStart b j + Multiset.card (b ⟨j, hj⟩) + 1 := by
  rw [blockStart, blockStart, blockPrefix_succ b hj, Multiset.card_add]
  omega

theorem blockStart_lt_blockStart {j j' : ℕ} (h : j < j') : blockStart b j < blockStart b j' := by
  have := Multiset.card_le_card (blockPrefix_mono b h.le)
  rw [blockStart, blockStart]
  omega

end Blocks

/-! ### Counting labels before a position -/

section Count

variable [DecidableEq I] {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card μ

theorem count_map_univ {α : Type*} [DecidableEq α] {n : ℕ} (f : Fin n → α) (x : α) :
    (Finset.univ.val.map f).count x = ∑ a, if f a = x then 1 else 0 := by
  rw [Multiset.count_map, ← Finset.filter_val, Finset.card_val, Finset.card_filter]
  exact Finset.sum_congr rfl fun a _ => by simp only [eq_comm]

/-- The number of positions before `p` carrying the label `x`. -/
def countBefore (s : Seq μ) (x : I ⊕ Fin ℓ) (p : ℕ) : ℕ :=
  ∑ a : Fin m, if a.val < p ∧ s.lbl a = x then 1 else 0

@[simp] theorem countBefore_zero (s : Seq μ) (x : I ⊕ Fin ℓ) : countBefore s x 0 = 0 := by
  simp [countBefore]

theorem countBefore_succ (s : Seq μ) (x : I ⊕ Fin ℓ) {p : ℕ} (hp : p < m) :
    countBefore s x (p + 1) = countBefore s x p + if s.lbl ⟨p, hp⟩ = x then 1 else 0 := by
  rw [countBefore, countBefore, ← Finset.sum_erase_add _ _ (Finset.mem_univ (⟨p, hp⟩ : Fin m)),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ (⟨p, hp⟩ : Fin m))]
  simp only [lt_add_one, true_and, lt_irrefl, false_and, ite_false, add_zero]
  congr 1
  refine Finset.sum_congr rfl fun a ha => ?_
  have : a.val ≠ p := fun h => (Finset.mem_erase.1 ha).1 (Fin.ext h)
  have h2 : a.val < p + 1 ↔ a.val < p := by omega
  simp only [h2]

theorem countBefore_card (s : Seq μ) (x : I ⊕ Fin ℓ) :
    countBefore s x m = Multiset.count x μ := by
  have h := congrArg (Multiset.count x) s.2
  rw [← h, count_map_univ, countBefore]
  exact Finset.sum_congr rfl fun a _ => by simp [a.2]

/-- Counting the labels of a window of positions, additively. -/
theorem countBefore_add_count_window (s : Seq μ) (x : I ⊕ Fin ℓ) (o : ℕ) :
    ∀ (n : ℕ) (h : o + n ≤ m),
      countBefore s x o + (Finset.univ.val.map fun a : Fin n => s.1 ⟨o + a, by omega⟩).count x =
        countBefore s x (o + n)
  | 0, _ => by simp
  | n + 1, h => by
    have ih := countBefore_add_count_window s x o n (by omega)
    rw [count_map_univ] at ih ⊢
    rw [Fin.sum_univ_castSucc, ← add_assoc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih, show o + (n + 1) = o + n + 1 by omega, countBefore_succ s x (by omega)]

/-- Counting the labels of a window of positions. -/
theorem count_window (s : Seq μ) (x : I ⊕ Fin ℓ) (o n : ℕ) (h : o + n ≤ m) :
    (Finset.univ.val.map fun a : Fin n => s.1 ⟨o + a, by omega⟩).count x =
      countBefore s x (o + n) - countBefore s x o := by
  have := countBefore_add_count_window s x o n h
  omega

end Count


/-! ### Positions of the red strands -/

section RedPositions

variable [DecidableEq I] {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card μ

omit [DecidableEq I] in
theorem card_stendhalWeight : m = Multiset.card ν + ℓ := by
  simp [stendhalWeight]

/-- The position of the red strand `λ_r`. -/
noncomputable def redPos (s : Seq μ) (r : Fin ℓ) : Fin m := (exists_lbl_eq_inr s r).choose

omit [DecidableEq I] in
theorem lbl_redPos (s : Seq μ) (r : Fin ℓ) : s.lbl (redPos s r) = .inr r :=
  (exists_lbl_eq_inr s r).choose_spec

theorem eq_redPos {s : Seq μ} {a : Fin m} {r : Fin ℓ} (h : s.lbl a = .inr r) : a = redPos s r :=
  lbl_eq_inr_unique h (lbl_redPos s r)

omit [DecidableEq I] in
theorem redPos_lt_iff {s : Seq μ} (hs : IsRedOrdered s) {r r' : Fin ℓ} :
    redPos s r' < redPos s r ↔ r' < r := by
  constructor
  · intro h
    exact hs _ _ _ _ h (lbl_redPos s r') (lbl_redPos s r)
  · intro h
    rcases lt_trichotomy (redPos s r') (redPos s r) with h1 | h1 | h1
    · exact h1
    · have := congrArg s.lbl h1
      rw [lbl_redPos, lbl_redPos] at this
      exact absurd (Sum.inr_injective this) h.ne
    · exact absurd (hs _ _ _ _ h1 (lbl_redPos s r) (lbl_redPos s r')) (lt_asymm h)

theorem countBefore_inr_redPos {s : Seq μ} (hs : IsRedOrdered s) (r r' : Fin ℓ) :
    countBefore s (.inr r') (redPos s r) = if r'.val < r.val then 1 else 0 := by
  rw [countBefore, Finset.sum_eq_single (redPos s r')]
  · have h := redPos_lt_iff hs (r := r) (r' := r')
    simp only [Fin.lt_def] at h
    simp only [lbl_redPos, and_true, h]
  · intro a _ ha
    simp only [ite_eq_right_iff]
    rintro ⟨-, h⟩
    exact absurd (eq_redPos h) ha
  · simp

theorem blackCount_eq_countBefore (s : Seq μ) (r : Fin ℓ) (i : I) :
    blackCount s r i = countBefore s (.inl i) (redPos s r) := by
  rw [blackCount, Finset.card_filter, countBefore]
  refine Finset.sum_congr rfl fun a _ => ?_
  have : (s.lbl a = .inl i ∧ ∀ b, s.lbl b = .inr r → a < b) ↔
      (a.val < (redPos s r).val ∧ s.lbl a = .inl i) := by
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2 _ (lbl_redPos s r), h1⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h2, fun b hb => ?_⟩
      rw [eq_redPos hb]
      exact h1
  simp only [this]

theorem count_labels_before (s : Seq μ) (p : ℕ) (x : I ⊕ Fin ℓ) :
    ((Finset.univ.filter fun a : Fin m => a.val < p).val.map s.lbl).count x =
      countBefore s x p := by
  rw [Multiset.count_map, ← Finset.filter_val, Finset.card_val, Finset.filter_filter,
    Finset.card_filter, countBefore]
  exact Finset.sum_congr rfl fun a _ => by simp only [eq_comm]

variable {b : Fin (ℓ + 1) → Multiset I}

/-- The red strand `λ_r` sits at position `r + |b 0| + ⋯ + |b r|`. -/
theorem redPos_val {s : Seq μ} (hs : IsRedOrdered s) (hα : blackCount s = blockRoot b)
    (r : Fin ℓ) : (redPos s r).val = r.val + Multiset.card (blockPrefix b (r.val + 1)) := by
  have hL : (Finset.univ.filter fun a : Fin m => a.val < (redPos s r).val).val.map s.lbl =
      (blockPrefix b (r.val + 1)).map Sum.inl +
        (Finset.univ.filter fun r' : Fin ℓ => r'.val < r.val).val.map Sum.inr := by
    ext x
    rw [count_labels_before, Multiset.count_add]
    rcases x with i | r'
    · rw [← blackCount_eq_countBefore, hα, Multiset.count_map_eq_count' _ _ Sum.inl_injective]
      simp [blockRoot]
    · rw [countBefore_inr_redPos hs, Multiset.count_map_eq_count' _ _ Sum.inr_injective,
        Multiset.count_eq_of_nodup (Finset.nodup _)]
      simp
  have := congrArg Multiset.card hL
  simp only [Multiset.card_map, Finset.card_val, Multiset.card_add,
    Fin.card_filter_val_lt] at this
  have h1 := (redPos s r).2
  have h2 := r.2
  omega

end RedPositions

/-! ### The labels of a block -/

section Window

variable [DecidableEq I] {ν : Multiset I} {b : Fin (ℓ + 1) → Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card μ

/-- The block `j + 1` starts right after the red strand `λ_j`. -/
theorem blockStart_succ_eq_redPos {s : Seq μ} (hs : IsRedOrdered s)
    (hα : blackCount s = blockRoot b) (r : Fin ℓ) :
    blockStart b (r.val + 1) = (redPos s r).val + 1 := by
  rw [redPos_val hs hα, blockStart]
  omega

theorem countBefore_blockStart_inl {s : Seq μ} (hs : IsRedOrdered s)
    (hα : blackCount s = blockRoot b) {j : ℕ} (hj : j ≤ ℓ) (i : I) :
    countBefore s (.inl i) (blockStart b j) = (blockPrefix b j).count i := by
  rcases j with _ | j
  · simp [blockStart]
  · rw [blockStart_succ_eq_redPos hs hα ⟨j, by omega⟩,
      countBefore_succ s _ (redPos s ⟨j, by omega⟩).2, ← blackCount_eq_countBefore, hα]
    simp [lbl_redPos, blockRoot]

theorem countBefore_blockStart_inr {s : Seq μ} (hs : IsRedOrdered s)
    (hα : blackCount s = blockRoot b) {j : ℕ} (hj : j ≤ ℓ) (r : Fin ℓ) :
    countBefore s (.inr r) (blockStart b j) = if r.val < j then 1 else 0 := by
  rcases j with _ | j
  · simp [blockStart]
  · rw [blockStart_succ_eq_redPos hs hα ⟨j, by omega⟩,
      countBefore_succ s _ (redPos s ⟨j, by omega⟩).2, countBefore_inr_redPos hs]
    simp only [Fin.eta, lbl_redPos, Sum.inr.injEq, Fin.ext_iff]
    split_ifs <;> omega

/-- The last position of the block `j`, plus one, is `λ_j` (or the end for `j = ℓ`). -/
theorem blockEnd_eq {s : Seq μ} (hs : IsRedOrdered s) (hα : blackCount s = blockRoot b)
    {j : ℕ} (hj : j < ℓ) :
    blockStart b j + Multiset.card (b ⟨j, by omega⟩) = (redPos s ⟨j, hj⟩).val := by
  have := blockStart_succ b (j := j) (by omega)
  have h2 := blockStart_succ_eq_redPos hs hα ⟨j, hj⟩
  simp only at h2
  omega

omit [DecidableEq I] in
theorem blockEnd_last (hb : blockPrefix b (ℓ + 1) = ν) :
    blockStart b ℓ + Multiset.card (b ⟨ℓ, by omega⟩) = m := by
  have := blockStart_succ b (j := ℓ) (by omega)
  rw [blockStart, hb] at this
  rw [card_stendhalWeight]
  omega

omit [DecidableEq I] in
theorem blockEnd_le (hb : blockPrefix b (ℓ + 1) = ν) {j : ℕ} (hj : j < ℓ + 1) :
    blockStart b j + Multiset.card ((b ⟨j, hj⟩).map (Sum.inl : I → I ⊕ Fin ℓ)) ≤ m := by
  rw [Multiset.card_map, ← blockEnd_last hb]
  rcases (Nat.lt_succ_iff.1 hj).lt_or_eq with h | h
  · have h1 := blockStart_succ b hj
    have h2 := Multiset.card_le_card (blockPrefix_mono b (n := j + 1) (n' := ℓ) (by omega))
    simp only [blockStart] at h1 ⊢
    omega
  · subst h
    rfl

theorem countBefore_blockEnd_inl {s : Seq μ} (hs : IsRedOrdered s)
    (hα : blackCount s = blockRoot b) (hb : blockPrefix b (ℓ + 1) = ν) {j : ℕ} (hj : j < ℓ + 1)
    (i : I) :
    countBefore s (.inl i) (blockStart b j + Multiset.card (b ⟨j, hj⟩)) =
      (blockPrefix b (j + 1)).count i := by
  rcases (Nat.lt_succ_iff.1 hj).lt_or_eq with h | h
  · rw [blockEnd_eq hs hα h, ← blackCount_eq_countBefore, hα]
    rfl
  · subst h
    rw [blockEnd_last hb, countBefore_card, hb]
    simp [stendhalWeight, Multiset.count_map_eq_count' _ _ Sum.inl_injective]

theorem countBefore_blockEnd_inr {s : Seq μ} (hs : IsRedOrdered s)
    (hα : blackCount s = blockRoot b) (hb : blockPrefix b (ℓ + 1) = ν) {j : ℕ} (hj : j < ℓ + 1)
    (r : Fin ℓ) :
    countBefore s (.inr r) (blockStart b j + Multiset.card (b ⟨j, hj⟩)) =
      if r.val < j then 1 else 0 := by
  rcases (Nat.lt_succ_iff.1 hj).lt_or_eq with h | h
  · rw [blockEnd_eq hs hα h, countBefore_inr_redPos hs]
  · subst h
    rw [blockEnd_last hb, countBefore_card, stendhalWeight, Multiset.count_add,
      Multiset.count_map_eq_count' _ _ Sum.inr_injective,
      Multiset.count_eq_of_nodup (Finset.nodup _)]
    simp

/-- The labels of the block `j` of positions form the black weight `b j`. -/
theorem map_window {s : Seq μ} (hs : IsRedOrdered s) (hα : blackCount s = blockRoot b)
    (hb : blockPrefix b (ℓ + 1) = ν) {j : ℕ} (hj : j < ℓ + 1) :
    Finset.univ.val.map (fun a => s.1 (KLRAlgebra.windowPos (blockStart b j)
      (blockEnd_le hb hj) a)) = (b ⟨j, hj⟩).map (Sum.inl : I → I ⊕ Fin ℓ) := by
  ext x
  have hw : Multiset.count x (Finset.univ.val.map (fun a => s.1 (KLRAlgebra.windowPos
      (blockStart b j) (blockEnd_le hb hj) a))) = _ :=
    count_window s x (blockStart b j) _ (blockEnd_le hb hj)
  rw [hw, Multiset.card_map]
  rcases x with i | r
  · rw [countBefore_blockEnd_inl hs hα hb hj, countBefore_blockStart_inl hs hα (by omega),
      blockPrefix_succ b hj, Multiset.count_add, Multiset.count_map_eq_count' _ _
        Sum.inl_injective]
    omega
  · rw [countBefore_blockEnd_inr hs hα hb hj, countBefore_blockStart_inr hs hα (by omega)]
    simp

end Window

/-! ### The block embeddings -/

namespace StendhalAlgebra

variable [DecidableEq I] {ν : Multiset I} {b : Fin (ℓ + 1) → Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card μ

omit [DecidableEq I] in
theorem ne_of_isLeft {t : Seq μ} {a d : Fin m} {r : Fin ℓ} (ha : (t.1 a).isLeft)
    (hd : t.lbl d = .inr r) : a ≠ d := by
  rintro rfl
  rw [show t.1 a = .inr r from hd] at ha
  simp at ha

theorem isLeft_of_mem_rootSet (hb : blockPrefix b (ℓ + 1) = ν) {j : ℕ} (hj : j < ℓ + 1)
    {t : Seq μ} (ht : t ∈ rootSet ν (blockRoot b))
    (a : Fin (Multiset.card ((b ⟨j, hj⟩).map (Sum.inl : I → I ⊕ Fin ℓ)))) :
    (t.1 (KLRAlgebra.windowPos (blockStart b j) (blockEnd_le hb hj) a)).isLeft := by
  obtain ⟨hs, hα⟩ := mem_rootSet.1 ht
  have hm : t.1 (KLRAlgebra.windowPos (blockStart b j) (blockEnd_le hb hj) a) ∈
      (b ⟨j, hj⟩).map (Sum.inl : I → I ⊕ Fin ℓ) := by
    have h := Multiset.mem_map_of_mem
      (fun a => t.1 (KLRAlgebra.windowPos (blockStart b j) (blockEnd_le hb hj) a))
      (Finset.mem_univ_val a)
    rwa [map_window hs hα hb hj] at h
  obtain ⟨i, -, hi⟩ := Multiset.mem_map.1 hm
  rw [← hi]
  rfl

/-- The set of red-ordered sequences of root function `blockRoot b` is stable under the
adjacent transpositions inside a block. -/
theorem sadj_mem_rootSet (hb : blockPrefix b (ℓ + 1) = ν) {j : ℕ} (hj : j < ℓ + 1) {j' : ℕ}
    (hj' : j' + 1 < Multiset.card ((b ⟨j, hj⟩).map (Sum.inl : I → I ⊕ Fin ℓ))) {t : Seq μ}
    (ht : t ∈ rootSet ν (blockRoot b)) :
    TypeA.sadj m (blockStart b j + j') • t ∈ rootSet ν (blockRoot b) := by
  obtain ⟨hs, hα⟩ := mem_rootSet.1 ht
  have hle := blockEnd_le hb hj
  have hn : blockStart b j + j' + 1 < m := by omega
  have h1 := isLeft_of_mem_rootSet hb hj ht ⟨j', by omega⟩
  have h2 := isLeft_of_mem_rootSet hb hj ht ⟨j' + 1, hj'⟩
  refine mem_rootSet.2 ⟨isRedOrdered_sadj hs hn (Or.inl h1), ?_⟩
  rw [← hα]
  funext r i
  rw [blackCount_sadj, blackCount]
  congr 1
  ext c
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine and_congr_right fun _ => forall_congr' fun d => imp_congr_right fun hd => ?_
  have hd1 : d.val ≠ blockStart b j + j' := fun h => ne_of_isLeft h1 hd (Fin.ext h.symm)
  have hd2 : d.val ≠ blockStart b j + j' + 1 := fun h => ne_of_isLeft h2 hd (Fin.ext h.symm)
  rw [Fin.lt_def, Fin.lt_def, KLRAlgebra.sadj_apply_val hn, KLRAlgebra.sadj_apply_val hn]
  split_ifs <;> omega

/-- **The block embedding of the block `j`** (arXiv:1309.3796v3, §5.1, the map `℘_α` of
Proposition 5.3): the KLR algebra of the black weight `b j` acts on the positions of the block
`j` of the red-ordered sequences of root function `blockRoot b`. -/
noncomputable def blockEmb (hb : blockPrefix b (ℓ + 1) = ν) (j : ℕ) (hj : j < ℓ + 1) :
    KLRAlgebra.BlockEmb ((b ⟨j, hj⟩).map (Sum.inl : I → I ⊕ Fin ℓ)) μ
      (rootSet ν (blockRoot b)) :=
  KLRAlgebra.BlockEmb.window _ (blockStart b j) (blockEnd_le hb hj)
    (fun _ ht => map_window (mem_rootSet.1 ht).1 (mem_rootSet.1 ht).2 hb hj)
    (fun j' hj' t => ⟨sadj_mem_rootSet hb hj hj', fun h => by
      rw [← KLRAlgebra.sadj_smul_smul (blockStart b j + j') t]
      exact sadj_mem_rootSet hb hj hj' h⟩)

end StendhalAlgebra

end Categorification.Stendhal
