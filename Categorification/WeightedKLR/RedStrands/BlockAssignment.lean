/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.RedStrands.BlockInsertWord
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.Ring.Nat
import Mathlib.Data.Finset.Card

/-!
# Block assignments and the bottoms of Webster's diagrams `x_φ`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.4,
the set `Φ̃` before Lemma 5.19 and the recursion in the proof of Lemma 5.19.

The red strands of a word cut its black letters into blocks: a letter at position `p` lies in
block `b(p)`, the number of red letters before it. An element of Webster's set `Φ̃` moves every
black strand into a block at most its own, keeps the red strands in place relative to each
other, and keeps the relative order of the black strands ending in the same block. It is
determined by the new blocks `f(p) ≤ b(p)` of the black strands; we call `f` a *block
assignment*, and record it as a function on all positions with `f(p) = b(p)` on red letters
(`assignList`). The bottom word of the diagram is obtained by sorting the positions stably by
the key `2 f(p)` for black letters and `2 f(p) + 1` for red letters (`assignWord`, via a stable
counting sort `countSort`).

Webster proves Lemma 5.19 by removing the rightmost strand. We record the resulting recursion on
words (`phiWords`): a red letter at the end is kept at the end, and a black letter at the end
is moved to the end of any block `k` not to the right of its own (`blockInsertList`). The words
of the bottoms of all block assignments are exactly these words (`map_assignWord_assignList`).

## Main definitions

* `countSort`: stable sorting by a key in `ℕ`.
* `redsBefore`, `assignChoices`, `assignList`, `assignKey`, `assignWord`.
* `phiWords`: the bottom words in the recursion of Lemma 5.19.

## Main results

* `map_assignWord_assignList`: the bottoms of the block assignments are `phiWords`.
-/

namespace Categorification.Stendhal

section CountSort

variable {α : Type*} (key : α → ℕ)

/-- Stable sorting by a key: the elements of key `0`, then those of key `1`, and so on up to
key `N - 1`, each in their original order. -/
def countSort (N : ℕ) (L : List α) : List α :=
  (List.range N).flatMap fun c => L.filter fun a => key a = c

theorem mem_countSort {N : ℕ} {L : List α} {a : α} :
    a ∈ countSort key N L ↔ a ∈ L ∧ key a < N := by
  simp only [countSort, List.mem_flatMap, List.mem_range, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨c, hc, ha, rfl⟩
    exact ⟨ha, hc⟩
  · rintro ⟨ha, hc⟩
    exact ⟨_, hc, ha, rfl⟩

theorem countSort_map {β : Type*} (h : β → α) (N : ℕ) (L : List β) :
    countSort key N (L.map h) = (countSort (key ∘ h) N L).map h := by
  simp only [countSort, List.map_flatMap, List.filter_map]
  rfl

private theorem flatMap_filter_eq_nil {L : List α} {cs : List ℕ}
    (h : ∀ a ∈ L, key a ∉ cs) : (cs.flatMap fun c => L.filter fun a => key a = c) = [] := by
  simp only [List.flatMap_eq_nil_iff, List.filter_eq_nil_iff, decide_eq_true_eq]
  intro c hc a ha hac
  exact h a ha (hac ▸ hc)

/-- The bound in `countSort` can be raised. -/
theorem countSort_of_le {N N' : ℕ} {L : List α} (hN : N ≤ N') (h : ∀ a ∈ L, key a < N) :
    countSort key N L = countSort key N' L := by
  unfold countSort
  rw [show N' = N + (N' - N) by omega, List.range_add, List.flatMap_append,
    show (List.map (fun x => N + x) (List.range (N' - N))) = List.range' N (N' - N) by
      rw [List.range_eq_range', List.map_add_range']; simp]
  rw [flatMap_filter_eq_nil key (cs := List.range' N (N' - N)) fun a ha hc => by
    have := (List.mem_range'_1.1 hc).1
    have := h a ha
    omega, List.append_nil]

/-- Appending an element `x` of key `c`: it lands after all elements of key at most `c`. -/
theorem countSort_append_singleton {N : ℕ} (L : List α) (x : α) (hx : key x < N) :
    countSort key N (L ++ [x]) = countSort key (key x + 1) L ++
      x :: ((List.range' (key x + 1) (N - (key x + 1))).flatMap fun c =>
        L.filter fun a => key a = c) := by
  unfold countSort
  rw [show N = (key x + 1) + (N - (key x + 1)) by omega, List.range_add, List.flatMap_append,
    show (List.map (fun y => (key x + 1) + y) (List.range (N - (key x + 1)))) =
      List.range' (key x + 1) (N - (key x + 1)) by
      rw [List.range_eq_range', List.map_add_range'],
    show key x + 1 + (N - (key x + 1)) - (key x + 1) = N - (key x + 1) by omega]
  have hpost : ((List.range' (key x + 1) (N - (key x + 1))).flatMap fun c =>
      (L ++ [x]).filter fun a => key a = c) =
      ((List.range' (key x + 1) (N - (key x + 1))).flatMap fun c =>
        L.filter fun a => key a = c) := by
    refine List.flatMap_congr fun c hc => ?_
    have hne : key x ≠ c := by have := (List.mem_range'_1.1 hc).1; omega
    simp [List.filter_append, hne]
  rw [hpost, List.range_succ, List.flatMap_append, List.flatMap_append]
  have hpre : ((List.range (key x)).flatMap fun c => (L ++ [x]).filter fun a => key a = c) =
      ((List.range (key x)).flatMap fun c => L.filter fun a => key a = c) := by
    refine List.flatMap_congr fun c hc => ?_
    have hne : key x ≠ c := by have := List.mem_range.1 hc; omega
    simp [List.filter_append, hne]
  rw [hpre]
  simp [List.filter_append]

/-- Elements of `countSort` in its pieces. -/
theorem mem_flatMap_range'_filter {L : List α} {c d : ℕ} {a : α}
    (ha : a ∈ (List.range' c d).flatMap fun c' => L.filter fun a => key a = c') :
    a ∈ L ∧ c ≤ key a ∧ key a < c + d := by
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_range'_1] at ha
  obtain ⟨c', hc', ha, rfl⟩ := ha
  exact ⟨ha, hc'.1, hc'.2⟩

end CountSort

variable {I : Type*} {n : ℕ}

/-- The number of red letters of a word. -/
def redCount (L : List (I ⊕ Fin n)) : ℕ :=
  L.countP fun y => y.isRight

@[simp] theorem redCount_nil : redCount ([] : List (I ⊕ Fin n)) = 0 := rfl

@[simp] theorem redCount_append (L L' : List (I ⊕ Fin n)) :
    redCount (L ++ L') = redCount L + redCount L' := List.countP_append ..

@[simp] theorem redCount_reverse (L : List (I ⊕ Fin n)) : redCount L.reverse = redCount L :=
  List.countP_reverse ..

@[simp] theorem redCount_singleton_inl (i : I) : redCount [(.inl i : I ⊕ Fin n)] = 0 := rfl

@[simp] theorem redCount_singleton_inr (r : Fin n) :
    redCount [(.inr r : I ⊕ Fin n)] = 1 := rfl

/-! ### The recursion of Lemma 5.19 -/

/-- `phiWords` on the reversed word. -/
def phiWordsRev : List (I ⊕ Fin n) → List (List (I ⊕ Fin n))
  | [] => [[]]
  | .inl i :: R => (phiWordsRev R).flatMap fun W =>
      (List.range (redCount R + 1)).map fun k => blockInsertList i k W
  | .inr r :: R => (phiWordsRev R).map (· ++ [.inr r])

/-- **The bottom words of Lemma 5.19** (Webster, arXiv:1309.3796v3, proof of Lemma 5.19): for
a word ending in a red letter, the words for the rest followed by that letter; for a word ending
in a black letter `i`, the words for the rest with `i` inserted at the end of any block. -/
def phiWords (L : List (I ⊕ Fin n)) : List (List (I ⊕ Fin n)) :=
  phiWordsRev L.reverse

@[simp] theorem phiWords_nil : phiWords ([] : List (I ⊕ Fin n)) = [[]] := rfl

theorem phiWords_append_inl (L : List (I ⊕ Fin n)) (i : I) :
    phiWords (L ++ [.inl i]) = (phiWords L).flatMap fun W =>
      (List.range (redCount L + 1)).map fun k => blockInsertList i k W := by
  rw [phiWords, List.reverse_append, List.reverse_singleton, List.singleton_append, phiWordsRev,
    redCount_reverse]
  rfl

theorem phiWords_append_inr (L : List (I ⊕ Fin n)) (r : Fin n) :
    phiWords (L ++ [.inr r]) = (phiWords L).map (· ++ [.inr r]) := by
  rw [phiWords, List.reverse_append, List.reverse_singleton, List.singleton_append, phiWordsRev]
  rfl

/-! ### Block assignments -/

section Assign

variable {m : ℕ}

/-- The number of red letters before position `p`: the block of `p`. -/
def redsBefore (lbl : Fin m → I ⊕ Fin n) (p : Fin m) : ℕ :=
  redCount ((List.ofFn lbl).take p)

theorem redsBefore_castSucc (lbl : Fin (m + 1) → I ⊕ Fin n) (p : Fin m) :
    redsBefore lbl p.castSucc = redsBefore (fun q => lbl q.castSucc) p := by
  unfold redsBefore
  rw [List.ofFn_succ', List.concat_eq_append, Fin.val_castSucc,
    List.take_append_of_le_length (by simp [p.2.le])]

theorem redsBefore_last (lbl : Fin (m + 1) → I ⊕ Fin n) :
    redsBefore lbl (Fin.last m) = redCount (List.ofFn fun q => lbl q.castSucc) := by
  unfold redsBefore
  rw [List.ofFn_succ', List.concat_eq_append, Fin.val_last,
    List.take_append_of_le_length (by simp), List.take_of_length_le (by simp)]

theorem redsBefore_le (lbl : Fin m → I ⊕ Fin n) (p : Fin m) : redsBefore lbl p ≤ p := by
  unfold redsBefore redCount
  refine (List.countP_le_length).trans ?_
  simp

/-- The possible new blocks of position `p`: any block at most `b(p)` for a black letter, and
`b(p)` itself for a red letter. -/
def assignChoices (lbl : Fin m → I ⊕ Fin n) (p : Fin m) : List ℕ :=
  if (lbl p).isRight then [redsBefore lbl p] else List.range (redsBefore lbl p + 1)

/-- The functions `g` with `g p ∈ S p` for all `p`. -/
def assignList : (m : ℕ) → (Fin m → List ℕ) → List (Fin m → ℕ)
  | 0, _ => [fun p => p.elim0]
  | m + 1, S => (assignList m fun p => S p.castSucc).flatMap fun g =>
      (S (Fin.last m)).map fun a => Fin.snoc (α := fun _ => ℕ) g a

theorem mem_assignList : ∀ {m : ℕ} {S : Fin m → List ℕ} {g : Fin m → ℕ},
    g ∈ assignList m S ↔ ∀ p, g p ∈ S p
  | 0, S, g => by
    simp only [assignList, List.mem_singleton, IsEmpty.forall_iff, iff_true]
    exact funext fun p => p.elim0
  | m + 1, S, g => by
    simp only [assignList, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨g', hg', a, ha, rfl⟩
      refine Fin.lastCases ?_ (fun p => ?_)
      · simpa using ha
      · simpa using (mem_assignList.1 hg') p
    · intro h
      refine ⟨Fin.init g, mem_assignList.2 fun p => h p.castSucc, g (Fin.last m), h _, ?_⟩
      exact Fin.snoc_init_self g

/-- **Webster's set `Φ̃`**, as block assignments. -/
abbrev assignments (lbl : Fin m → I ⊕ Fin n) : List (Fin m → ℕ) :=
  assignList m (assignChoices lbl)

/-- The sorting key of a block assignment. -/
def assignKey (lbl : Fin m → I ⊕ Fin n) (g : Fin m → ℕ) (p : Fin m) : ℕ :=
  2 * g p + if (lbl p).isRight then 1 else 0

/-- **The bottom word of `x_φ`**: the letters sorted stably by the key of the block
assignment. -/
def assignWord (lbl : Fin m → I ⊕ Fin n) (g : Fin m → ℕ) : List (I ⊕ Fin n) :=
  (countSort (assignKey lbl g) (2 * m + 2) (List.finRange m)).map lbl

theorem assignKey_lt {lbl : Fin m → I ⊕ Fin n} {g : Fin m → ℕ} (hg : g ∈ assignments lbl)
    (p : Fin m) : assignKey lbl g p < 2 * m + 2 := by
  have h := mem_assignList.1 hg p
  have hb := redsBefore_le lbl p
  have hp := p.2
  unfold assignKey
  unfold assignChoices at h
  split_ifs at h ⊢ with hr
  · rw [List.mem_singleton.1 h]; omega
  · have := List.mem_range.1 h; omega

/-- Red letters of a red-ordered word with all red letters: `λ_r` has `r` red letters before
it. -/
def RedIndexed (lbl : Fin m → I ⊕ Fin n) : Prop :=
  ∀ p (r : Fin n), lbl p = .inr r → r.val = redsBefore lbl p

theorem RedIndexed.init {lbl : Fin (m + 1) → I ⊕ Fin n} (h : RedIndexed lbl) :
    RedIndexed fun q => lbl q.castSucc := fun p r hp => by
  rw [← redsBefore_castSucc]
  exact h _ r hp

theorem exists_redsBefore_eq : ∀ {m : ℕ} (lbl : Fin m → I ⊕ Fin n) {k : ℕ},
    k < redCount (List.ofFn lbl) → ∃ q, (lbl q).isRight ∧ redsBefore lbl q = k
  | 0, _, k, h => by simp at h
  | m + 1, lbl, k, h => by
    rw [List.ofFn_succ', List.concat_eq_append, redCount_append] at h
    by_cases hk : k < redCount (List.ofFn fun q => lbl q.castSucc)
    · obtain ⟨q, hq, hq'⟩ := exists_redsBefore_eq _ hk
      exact ⟨q.castSucc, hq, by rw [redsBefore_castSucc, hq']⟩
    · refine ⟨Fin.last m, ?_, ?_⟩
      · rcases hl : lbl (Fin.last m) with i | r
        · rw [hl] at h; simp at h; omega
        · rfl
      · rw [redsBefore_last]
        rcases hl : lbl (Fin.last m) with i | r
        · rw [hl] at h; simp at h; omega
        · rw [hl] at h; simp at h; omega

/-- A red letter has fewer red letters before it than the whole word. -/
theorem redsBefore_lt_redCount {lbl : Fin m → I ⊕ Fin n} {q : Fin m} (hq : (lbl q).isRight) :
    redsBefore lbl q < redCount (List.ofFn lbl) := by
  unfold redsBefore redCount
  conv_rhs => rw [← List.take_append_drop q (List.ofFn lbl)]
  rw [List.countP_append, List.drop_eq_getElem_cons (by simp), List.countP_cons]
  simp [hq]

theorem redsBefore_le_redCount (lbl : Fin m → I ⊕ Fin n) (q : Fin m) :
    redsBefore lbl q ≤ redCount (List.ofFn lbl) := by
  unfold redsBefore redCount
  conv_rhs => rw [← List.take_append_drop q (List.ofFn lbl)]
  rw [List.countP_append]
  omega

private theorem finRange_succ' : List.finRange (m + 1) =
    (List.finRange m).map Fin.castSucc ++ [Fin.last m] := by
  rw [List.finRange_succ_last]

theorem assignKey_snoc_castSucc (lbl : Fin (m + 1) → I ⊕ Fin n) (g : Fin m → ℕ) (a : ℕ) :
    assignKey lbl (Fin.snoc (α := fun _ => ℕ) g a) ∘ Fin.castSucc =
      assignKey (fun q => lbl q.castSucc) g := by
  funext p
  simp [assignKey]

theorem assignKey_snoc_last (lbl : Fin (m + 1) → I ⊕ Fin n) (g : Fin m → ℕ) (a : ℕ) :
    assignKey lbl (Fin.snoc (α := fun _ => ℕ) g a) (Fin.last m) =
      2 * a + if (lbl (Fin.last m)).isRight then 1 else 0 := by
  simp [assignKey]

/-- Splitting the bottom word at the last strand. -/
theorem assignWord_snoc (lbl : Fin (m + 1) → I ⊕ Fin n) {g : Fin m → ℕ}
    (hg : g ∈ assignments fun q => lbl q.castSucc) (a : ℕ)
    (ha : a ∈ assignChoices lbl (Fin.last m)) :
    assignWord lbl (Fin.snoc (α := fun _ => ℕ) g a) =
      (countSort (assignKey (fun q => lbl q.castSucc) g)
          (assignKey lbl (Fin.snoc (α := fun _ => ℕ) g a) (Fin.last m) + 1)
          (List.finRange m)).map (fun q => lbl q.castSucc) ++
        lbl (Fin.last m) ::
          ((List.range' (assignKey lbl (Fin.snoc (α := fun _ => ℕ) g a) (Fin.last m) + 1)
            (2 * (m + 1) + 2 -
              (assignKey lbl (Fin.snoc (α := fun _ => ℕ) g a) (Fin.last m) + 1))).flatMap
            fun c => (List.finRange m).filter fun q =>
              assignKey (fun q => lbl q.castSucc) g q = c).map (fun q => lbl q.castSucc) := by
  have hlast : assignKey lbl (Fin.snoc (α := fun _ => ℕ) g a) (Fin.last m) < 2 * (m + 1) + 2 :=
    assignKey_lt (mem_assignList.2 fun p => by
      refine Fin.lastCases ?_ (fun p => ?_) p
      · simpa using ha
      · simpa [assignChoices, redsBefore_castSucc] using (mem_assignList.1 hg) p) _
  unfold assignWord
  rw [finRange_succ', countSort_append_singleton _ _ _ hlast, countSort_map,
    assignKey_snoc_castSucc]
  simp only [List.map_append, List.map_cons, List.map_map]
  congr 2
  · rw [List.map_flatMap, List.map_flatMap]
    refine List.flatMap_congr fun c _ => ?_
    rw [List.filter_map, List.map_map]
    congr 2
    funext q
    rw [Function.comp_apply, decide_eq_decide]
    simp [assignKey]

/-- **The bottoms of the block assignments are the words of Lemma 5.19**. -/
theorem map_assignWord_assignList : ∀ {m : ℕ} (lbl : Fin m → I ⊕ Fin n), RedIndexed lbl →
    (assignments lbl).map (assignWord lbl) = phiWords (List.ofFn lbl)
  | 0, lbl, _ => by
    simp [assignments, assignList, assignWord, countSort]
  | m + 1, lbl, hlbl => by
    set lbl' : Fin m → I ⊕ Fin n := fun q => lbl q.castSucc with hlbl'
    have ih := map_assignWord_assignList lbl' hlbl.init
    have hch : (fun p : Fin m => assignChoices lbl p.castSucc) = assignChoices lbl' := by
      funext p
      simp [assignChoices, redsBefore_castSucc, lbl']
    have hR : redsBefore lbl (Fin.last m) = redCount (List.ofFn lbl') := redsBefore_last lbl
    rw [List.ofFn_succ', List.concat_eq_append]
    simp only [assignments, assignList, hch, List.map_flatMap, List.map_map]
    -- the full bottom word of `g`
    have hfull : ∀ g ∈ assignments lbl', ∀ N, 2 * m + 2 ≤ N →
        (countSort (assignKey lbl' g) N (List.finRange m)).map lbl' = assignWord lbl' g :=
      fun g hg N hN => by
        rw [assignWord, ← countSort_of_le _ hN fun p _ => assignKey_lt hg p]
    rcases hx : lbl (Fin.last m) with i | r
    · -- a black letter at the end
      rw [phiWords_append_inl, ← ih, List.flatMap_map]
      refine List.flatMap_congr fun g hg => ?_
      have hchl : assignChoices lbl (Fin.last m) = List.range (redCount (List.ofFn lbl') + 1) := by
        simp [assignChoices, hx, hR]
      rw [hchl]
      refine List.map_congr_left fun k hk => ?_
      have hk' := List.mem_range.1 hk
      simp only [Function.comp_apply]
      rw [assignWord_snoc lbl hg k (by rw [hchl]; exact hk), assignKey_snoc_last, hx]
      simp only [Sum.isRight_inl, Bool.false_eq_true, ite_false, add_zero]
      have hgm := mem_assignList.1 hg
      have hRm : redCount (List.ofFn lbl') ≤ m :=
        (List.countP_le_length).trans (by simp)
      -- the pieces: keys at most `2k` and above `2k`
      set pre := (countSort (assignKey lbl' g) (2 * k + 1) (List.finRange m)).map lbl'
      set post := ((List.range' (2 * k + 1) (2 * (m + 1) + 2 - (2 * k + 1))).flatMap
        fun c => (List.finRange m).filter fun q => assignKey lbl' g q = c).map lbl'
      have hsplit : assignWord lbl' g = pre ++ post := by
        rw [← hfull g hg (2 * (m + 1) + 2) (by omega),
          show 2 * (m + 1) + 2 = (2 * k + 1) + (2 * (m + 1) + 2 - (2 * k + 1)) by omega]
        unfold countSort
        rw [List.range_add, List.flatMap_append, List.map_append,
          show (List.map (fun y => (2 * k + 1) + y) (List.range (2 * (m + 1) + 2 - (2 * k + 1))))
            = List.range' (2 * k + 1) (2 * (m + 1) + 2 - (2 * k + 1)) by
            rw [List.range_eq_range', List.map_add_range']]
        rfl
      have hkey_red : ∀ q, (lbl' q).isRight → assignKey lbl' g q = 2 * redsBefore lbl' q + 1 :=
        fun q hq => by
          have := hgm q
          simp only [assignChoices, hq, ite_true, List.mem_singleton] at this
          simp [assignKey, hq, this]
      have hkey_black : ∀ q, (lbl' q).isRight = false →
          assignKey lbl' g q = 2 * g q ∧ g q ≤ redsBefore lbl' q := fun q hq => by
        have := hgm q
        simp only [assignChoices, hq, Bool.false_eq_true, ite_false, List.mem_range] at this
        refine ⟨?_, by omega⟩
        simp [assignKey, hq]
      have hpre : ∀ y ∈ pre, redAtLeast k y = false := by
        intro y hy
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hy
        have hq' := ((mem_countSort _).1 hq).2
        rcases hl : lbl' q with j | r
        · rfl
        · have hr : r.val = redsBefore lbl' q := hlbl.init q r hl
          have := hkey_red q (by simp [hl])
          simp only [redAtLeast, decide_eq_false_iff_not, not_le]
          omega
      rw [blockInsertList, hsplit, insertBefore_append_of_forall _ _ _ _ hpre]
      congr 1
      rcases Nat.lt_or_ge k (redCount (List.ofFn lbl')) with hlt | hge
      · -- the red strand `λ_k` starts `post`
        obtain ⟨q₀, hq₀, hq₀'⟩ := exists_redsBefore_eq lbl' hlt
        have hfirst : ((List.finRange m).filter fun q => assignKey lbl' g q = 2 * k + 1) ≠ [] := by
          refine List.ne_nil_of_mem (a := q₀) ?_
          simp [hkey_red q₀ hq₀, hq₀']
        obtain ⟨y, ys, hys⟩ := List.exists_cons_of_ne_nil hfirst
        have hy : y ∈ (List.finRange m).filter fun q => assignKey lbl' g q = 2 * k + 1 :=
          hys ▸ List.mem_cons_self
        have hyk := of_decide_eq_true (List.mem_filter.1 hy).2
        have hyr : (lbl' y).isRight := by
          by_contra h
          have := (hkey_black y (by simpa using h)).1
          omega
        have hpost : post = lbl' y :: (ys.map lbl' ++ ((List.range' (2 * k + 2)
            (2 * (m + 1) + 2 - (2 * k + 2))).flatMap fun c => (List.finRange m).filter fun q =>
              assignKey lbl' g q = c).map lbl') := by
          simp only [post]
          rw [show 2 * (m + 1) + 2 - (2 * k + 1) = (2 * (m + 1) + 2 - (2 * k + 2)) + 1 by omega,
            List.range'_succ, List.flatMap_cons, hys]
          simp
        rw [hpost]
        rcases hl : lbl' y with j | r
        · rw [hl] at hyr; simp at hyr
        · have hr : r.val = redsBefore lbl' y := hlbl.init y r hl
          have := hkey_red y hyr
          have hkr : k ≤ r.val := by omega
          simp [insertBefore, redAtLeast, hkr]
      · -- no strand lies above block `k`
        have hpost : post = [] := by
          simp only [post, List.map_eq_nil_iff]
          refine flatMap_filter_eq_nil _ fun q _ hc => ?_
          have hc' := (List.mem_range'_1.1 hc).1
          have hb := redsBefore_le_redCount lbl' q
          by_cases hq : (lbl' q).isRight
          · have := hkey_red q hq
            have := redsBefore_lt_redCount hq
            omega
          · have := hkey_black q (by simpa using hq)
            omega
        rw [hpost]
        rfl
    · -- a red letter at the end
      rw [phiWords_append_inr, ← ih, List.map_map]
      refine (List.flatMap_congr (g := fun g => [assignWord lbl' g ++ [.inr r]])
        fun g hg => ?_).trans ?_
      swap
      · exact List.map_eq_flatMap.symm
      have hchl : assignChoices lbl (Fin.last m) = [redCount (List.ofFn lbl')] := by
        simp [assignChoices, hx, hR]
      rw [hchl]
      simp only [List.map_cons, List.map_nil, Function.comp_apply]
      congr 1
      rw [assignWord_snoc lbl hg _ (by rw [hchl]; exact List.mem_singleton_self _),
        assignKey_snoc_last, hx]
      simp only [Sum.isRight_inr, ite_true]
      have hgm := mem_assignList.1 hg
      have hlt : ∀ q, assignKey lbl' g q < 2 * redCount (List.ofFn lbl') + 1 := fun q => by
        have := hgm q
        have hb := redsBefore_le_redCount lbl' q
        unfold assignChoices at this
        unfold assignKey
        split_ifs at this ⊢ with hq
        · rw [List.mem_singleton.1 this]
          have := redsBefore_lt_redCount hq
          omega
        · have := List.mem_range.1 this
          omega
      have hpost : ((List.range' (2 * redCount (List.ofFn lbl') + 1 + 1)
          (2 * (m + 1) + 2 - (2 * redCount (List.ofFn lbl') + 1 + 1))).flatMap fun c =>
            (List.finRange m).filter fun q => assignKey lbl' g q = c) = [] :=
        flatMap_filter_eq_nil _ fun q _ hc => by
          have := (List.mem_range'_1.1 hc).1
          have := hlt q
          omega
      rw [hpost, List.map_nil]
      rw [countSort_of_le _ (N' := 2 * m + 2 + (2 * redCount (List.ofFn lbl') + 2)) (by omega)
          fun q _ => (hlt q).trans (by omega),
        ← countSort_of_le _ (N := 2 * m + 2) (by omega) fun q _ => assignKey_lt hg q]
      rfl

end Assign

/-! ### The permutation of a block assignment -/

section Perm

variable {m : ℕ} (key : Fin m → ℕ)

/-- Positions ordered by key, then by position. -/
def keyOrd (p : Fin m) : ℕ := key p * m + p

theorem keyOrd_mod (p : Fin m) : keyOrd key p % m = p := by
  rw [keyOrd, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt p.2]

theorem keyOrd_injective : Function.Injective (keyOrd key) := fun p q h =>
  Fin.ext (by rw [← keyOrd_mod key p, h, keyOrd_mod])

theorem keyOrd_lt_of_key_lt {p q : Fin m} (h : key p < key q) : keyOrd key p < keyOrd key q := by
  unfold keyOrd
  have h1 : key p * m + p < (key p + 1) * m := by rw [Nat.succ_mul]; omega
  have h2 : (key p + 1) * m ≤ key q * m := Nat.mul_le_mul_right _ h
  omega

theorem keyOrd_lt_iff {p q : Fin m} :
    keyOrd key p < keyOrd key q ↔ key p < key q ∨ (key p = key q ∧ p < q) := by
  constructor
  · intro h
    rcases lt_trichotomy (key p) (key q) with hk | hk | hk
    · exact .inl hk
    · refine .inr ⟨hk, ?_⟩
      unfold keyOrd at h
      rw [hk] at h
      exact Fin.lt_def.2 (by omega)
    · exact absurd (keyOrd_lt_of_key_lt key hk) (by omega)
  · rintro (h | ⟨h, h'⟩)
    · exact keyOrd_lt_of_key_lt key h
    · unfold keyOrd
      rw [h]
      have := Fin.lt_def.1 h'
      omega

/-- The rank of a position in the order by `keyOrd`. -/
def keyRank (p : Fin m) : Fin m :=
  ⟨(Finset.univ.filter fun q => keyOrd key q < keyOrd key p).card, by
    have : (Finset.univ.filter fun q => keyOrd key q < keyOrd key p) ⊂ Finset.univ :=
      Finset.filter_ssubset.2 ⟨p, Finset.mem_univ _, lt_irrefl _⟩
    simpa using Finset.card_lt_card this⟩

theorem keyRank_lt_keyRank {p q : Fin m} (h : keyOrd key p < keyOrd key q) :
    keyRank key p < keyRank key q := by
  unfold keyRank
  rw [Fin.mk_lt_mk]
  refine Finset.card_lt_card ?_
  refine Finset.ssubset_iff_of_subset (fun a ha => ?_) |>.2 ⟨p, ?_, ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact ha.trans h
  · simpa using h
  · simp

theorem keyRank_lt_iff {p q : Fin m} : keyRank key p < keyRank key q ↔ keyOrd key p < keyOrd key q := by
  refine ⟨fun h => ?_, keyRank_lt_keyRank key⟩
  rcases lt_trichotomy (keyOrd key p) (keyOrd key q) with h' | h' | h'
  · exact h'
  · rw [keyOrd_injective key h'] at h
    exact absurd h (lt_irrefl _)
  · exact absurd (keyRank_lt_keyRank key h') (not_lt.2 h.le)

theorem keyRank_injective : Function.Injective (keyRank key) := by
  intro p q h
  rcases lt_trichotomy (keyOrd key p) (keyOrd key q) with h' | h' | h'
  · exact absurd h (keyRank_lt_keyRank key h').ne
  · exact keyOrd_injective key h'
  · exact absurd h (keyRank_lt_keyRank key h').ne'

/-- **The permutation of a key**: position `p` goes to its rank in the order by key, then by
position. For a block assignment this is Webster's `φ ∈ Φ̃`. -/
noncomputable def keyPerm : Equiv.Perm (Fin m) :=
  Equiv.ofBijective (keyRank key) (Finite.injective_iff_bijective.1 (keyRank_injective key))

@[simp] theorem keyPerm_apply (p : Fin m) : keyPerm key p = keyRank key p := rfl

theorem keyPerm_lt_iff {p q : Fin m} :
    keyPerm key p < keyPerm key q ↔ key p < key q ∨ (key p = key q ∧ p < q) := by
  rw [keyPerm_apply, keyPerm_apply, keyRank_lt_iff, keyOrd_lt_iff]

theorem pairwise_countSort_finRange (N : ℕ) :
    (countSort key N (List.finRange m)).Pairwise fun p q => keyOrd key p < keyOrd key q := by
  unfold countSort
  rw [List.pairwise_flatMap]
  refine ⟨fun c _ => ?_, ?_⟩
  · refine ((List.pairwise_lt_finRange m).filter _).imp_of_mem fun {p q} hp hq hpq => ?_
    have hp' := of_decide_eq_true (List.mem_filter.1 hp).2
    have hq' := of_decide_eq_true (List.mem_filter.1 hq).2
    exact (keyOrd_lt_iff key).2 (.inr ⟨hp'.trans hq'.symm, hpq⟩)
  · refine (List.pairwise_lt_range).imp fun {c c'} hcc' p hp q hq => ?_
    have hp' := of_decide_eq_true (List.mem_filter.1 hp).2
    have hq' := of_decide_eq_true (List.mem_filter.1 hq).2
    exact keyOrd_lt_of_key_lt key (by omega)

/-- The positions in the order of `keyPerm` are the stably sorted positions. -/
theorem ofFn_keyPerm_symm {N : ℕ} (hN : ∀ p, key p < N) :
    List.ofFn (keyPerm key).symm = countSort key N (List.finRange m) := by
  have hR : ∀ p : Fin m, ¬ keyOrd key p < keyOrd key p := fun p => lt_irrefl _
  have h₁ : (List.ofFn (keyPerm key).symm).Pairwise fun p q => keyOrd key p < keyOrd key q := by
    refine List.pairwise_ofFn.2 fun a b hab => ?_
    rw [← keyRank_lt_iff, ← keyPerm_apply, ← keyPerm_apply, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply]
    exact hab
  have h₂ := pairwise_countSort_finRange key N
  have hnd₁ : (List.ofFn (keyPerm key).symm).Nodup := h₁.imp fun h => (ne_of_lt h) ∘ congrArg _
  have hnd₂ : (countSort key N (List.finRange m)).Nodup :=
    h₂.imp fun h => (ne_of_lt h) ∘ congrArg _
  refine List.Perm.eq_of_pairwise (fun a b _ _ hab hba => absurd (hab.trans hba) (hR a)) h₁ h₂
    ((List.perm_ext_iff_of_nodup hnd₁ hnd₂).2 fun a => ?_)
  rw [mem_countSort, List.mem_ofFn]
  exact ⟨fun _ => ⟨List.mem_finRange a, hN a⟩, fun _ => ⟨keyPerm key a, Equiv.symm_apply_apply _ a⟩⟩

/-- The word of the bottom of `x_φ`. -/
theorem ofFn_comp_keyPerm_symm {α : Type*} (lbl : Fin m → α) {N : ℕ} (hN : ∀ p, key p < N) :
    List.ofFn (lbl ∘ (keyPerm key).symm) = (countSort key N (List.finRange m)).map lbl := by
  rw [← ofFn_keyPerm_symm key hN, List.map_ofFn]

end Perm

/-- The word of the bottom of `x_φ` for a block assignment `g`. -/
theorem ofFn_comp_assignPerm_symm {m : ℕ} {lbl : Fin m → I ⊕ Fin n} {g : Fin m → ℕ}
    (hg : g ∈ assignments lbl) :
    List.ofFn (lbl ∘ (keyPerm (assignKey lbl g)).symm) = assignWord lbl g :=
  ofFn_comp_keyPerm_symm _ lbl (assignKey_lt hg)

end Categorification.Stendhal
