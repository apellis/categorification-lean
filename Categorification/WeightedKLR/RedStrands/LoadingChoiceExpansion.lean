/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LoadingWordExpansion

/-!
# The parameter set of a loading as choices of blocks

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
Proposition 5.20 and proof of Lemma 6.11. Expanding the vector of a loading into word tensors
(`loadingMono`), each black strand chooses one of the red strands to its left and its letter is
appended to the word of that red. This module records the words of the expansion through these
choices: `loadingChoices` lists the choices, one entry per strand (a black strand records the
index of the red it joins, a red strand its own index), and `choiceRows` the resulting words.

## Main results

* `loadingMono_map_snd`: the words of `loadingMono` are the `choiceRows` of the
  `loadingChoices`.
* `mem_loadingChoices_iff`: a description of the admissible choices strand by strand.
* `nodup_loadingChoices`.
-/

namespace Categorification.Stendhal.FirstWeight

open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop

variable {I : Type} [DecidableEq I] {C : QuantumGroup.CartanDatum I}
  {Y : Type*} [AddCommGroup Y] {R : C.toLusztig.RootDatum Y} {J : Type*}

/-- Append the letter `i` to the word of the factor `j`. -/
def addLetter {n : ℕ} (i : I) (u : Fin n → List I) (j : ℕ) : Fin n → List I :=
  fun r => u r ++ if r.val = j then [i] else []

omit [DecidableEq I] in
theorem addLetter_lastCases {n : ℕ} (i : I) (a : List I) (u : Fin n → List I) {j : ℕ}
    (hj : j < n) : addLetter i (Fin.lastCases a u : Fin (n + 1) → List I) j =
      Fin.lastCases a (addLetter i u j) := by
  funext r
  refine Fin.lastCases ?_ (fun r => ?_) r
  · simp [addLetter, Fin.lastCases_last, show n ≠ j by omega]
  · simp [addLetter, Fin.lastCases_castSucc]

omit [DecidableEq I] in
theorem addLetter_last {n : ℕ} (i : I) (u : Fin (n + 1) → List I) :
    addLetter i u n = Fin.lastCases (u (Fin.last n) ++ [i]) fun j => u (Fin.castSucc j) := by
  funext r
  refine Fin.lastCases ?_ (fun r => ?_) r
  · simp [addLetter, Fin.lastCases_last]
  · simp [addLetter, Fin.lastCases_castSucc, r.isLt.ne]

/-- The words of `F_i` applied to a word tensor: `i` is appended to one of the factors. -/
theorem wordF_map_snd (i : I) : ∀ {n : ℕ} (wt : Fin n → Dom R) (u : Fin n → List I),
    (wordF i wt u).map Prod.snd = (List.range n).map (addLetter i u)
  | 0, _, _ => rfl
  | n + 1, wt, u => by
    rw [wordF, List.map_append, List.map_map, List.range_succ, List.map_append]
    congr 1
    · have h := wordF_map_snd i (fun j => wt (Fin.castSucc j)) (fun j => u (Fin.castSucc j))
      have hu : u = Fin.lastCases (u (Fin.last n)) fun j => u (Fin.castSucc j) := by
        funext r; refine Fin.lastCases ?_ (fun r => ?_) r <;> simp
      calc ((wordF i (fun j => wt (Fin.castSucc j)) fun j => u (Fin.castSucc j)).map
            ((fun p => Fin.lastCases (u (Fin.last n)) p) ∘ Prod.snd))
          = ((List.range n).map (addLetter i fun j => u (Fin.castSucc j))).map
              (fun p => Fin.lastCases (u (Fin.last n)) p) := by rw [← List.map_map, h]
        _ = (List.range n).map (addLetter i u) := by
          rw [List.map_map]
          refine List.map_congr_left fun j hj => ?_
          rw [List.mem_range] at hj
          conv_rhs => rw [hu]
          rw [Function.comp_apply, addLetter_lastCases i _ _ hj]
    · simp [addLetter_last]

/-- **The choices of a loading, read from its last strand**: one entry per strand; a black
strand records the index of the red it joins (one of the reds before it), a red strand its own
index. -/
def choicesRev : List (I ⊕ J) → ℕ → List (List ℕ)
  | [], 0 => [[]]
  | [], _ + 1 => []
  | .inl _ :: s, n => (choicesRev s n).flatMap fun c => (List.range n).map fun j => j :: c
  | .inr _ :: _, 0 => []
  | .inr _ :: s, n + 1 => (choicesRev s n).map fun c => n :: c

/-- The words of a choice, read from the last strand. -/
def rowsRev : List (I ⊕ J) → List ℕ → (n : ℕ) → Fin n → List I
  | .inl i :: s, j :: c, n => addLetter i (rowsRev s c n) j
  | .inr _ :: s, _ :: c, n + 1 => Fin.lastCases [] (rowsRev s c n)
  | _, _, _ => fun _ => []

theorem monoReverse_map_snd : ∀ (s : List (I ⊕ J)) {n : ℕ} (wt : Fin n → Dom R),
    (monoReverse (C := C) s wt).map Prod.snd = (choicesRev s n).map fun c => rowsRev s c n
  | [], 0, _ => by
    simp only [monoReverse, choicesRev, List.map_cons, List.map_nil, List.cons.injEq, and_true]
    funext r; exact r.elim0
  | [], _ + 1, _ => rfl
  | .inl i :: s, n, wt => by
    rw [monoReverse, monoF, choicesRev, List.map_flatMap, List.map_flatMap]
    have h := monoReverse_map_snd s wt
    trans ((monoReverse (C := C) s wt).map Prod.snd).flatMap fun u =>
      (List.range n).map (addLetter i u)
    · rw [List.flatMap_map]
      refine List.flatMap_congr fun p _ => ?_
      rw [List.map_map, ← wordF_map_snd i wt p.2]
      rfl
    · rw [h, List.flatMap_map]
      refine List.flatMap_congr fun c _ => ?_
      rw [List.map_map]
      rfl
  | .inr _ :: _, 0, _ => rfl
  | .inr _ :: s, n + 1, wt => by
    rw [monoReverse, monoRed, choicesRev, List.map_map, List.map_map]
    have h := monoReverse_map_snd s (fun j => wt (Fin.castSucc j))
    trans (((monoReverse (C := C) s fun j => wt (Fin.castSucc j)).map Prod.snd).map
      fun u => (Fin.lastCases [] u : Fin (n + 1) → List I))
    · rw [List.map_map]; rfl
    · rw [h, List.map_map]; rfl

/-- **The choices of a loading** (Webster, arXiv:1309.3796v2, Proposition 5.20). -/
def loadingChoices (s : List (I ⊕ J)) (n : ℕ) : List (List ℕ) := choicesRev s.reverse n

/-- The words of a choice of a loading. -/
def choiceRows (s : List (I ⊕ J)) (c : List ℕ) (n : ℕ) : Fin n → List I :=
  rowsRev s.reverse c n

/-- **The words of the expansion of a loading are the words of its choices**. -/
theorem loadingMono_map_snd (s : List (I ⊕ J)) {n : ℕ} (wt : Fin n → Dom R) :
    (loadingMono (C := C) wt s).map Prod.snd =
      (loadingChoices s n).map fun c => choiceRows s c n :=
  monoReverse_map_snd s.reverse wt

/-! ### Admissible choices -/

/-- The number of red strands among the first `x` strands of a loading. -/
def redsBefore {m : ℕ} (t : Fin m → I ⊕ J) (x : ℕ) : ℕ :=
  ((List.ofFn t).take x).countP fun a => a.isRight

omit [DecidableEq I] in
theorem redsBefore_castSucc {m : ℕ} (t : Fin (m + 1) → I ⊕ J) {x : ℕ} (hx : x ≤ m) :
    redsBefore t x = redsBefore (fun y => t (Fin.castSucc y)) x := by
  rw [redsBefore, redsBefore, List.ofFn_succ_last, List.take_append_of_le_length (by simpa)]

omit [DecidableEq I] in
theorem redsBefore_last {m : ℕ} (t : Fin (m + 1) → I ⊕ J) :
    redsBefore t m = (List.ofFn fun y => t (Fin.castSucc y)).countP fun a => a.isRight := by
  rw [redsBefore, List.ofFn_succ_last, List.take_left' (by simp)]

omit [DecidableEq I] in
theorem reverse_ofFn_succ {α : Type*} {m : ℕ} (f : Fin (m + 1) → α) :
    (List.ofFn f).reverse = f (Fin.last m) :: (List.ofFn fun y => f (Fin.castSucc y)).reverse := by
  rw [List.ofFn_succ_last, List.reverse_concat]

/-- A choice `ch` of a loading `t` is admissible: a black strand chooses one of the reds before
it, a red strand records the number of reds before it. -/
structure IsAdmissibleChoice {m : ℕ} (t : Fin m → I ⊕ J) (ch : Fin m → ℕ) : Prop where
  black : ∀ x, (t x).isLeft → ch x < redsBefore t x
  red : ∀ x, (t x).isRight → ch x = redsBefore t x

omit [DecidableEq I] in
theorem IsAdmissibleChoice.castSucc {m : ℕ} {t : Fin (m + 1) → I ⊕ J} {ch : Fin (m + 1) → ℕ}
    (h : IsAdmissibleChoice t ch) :
    IsAdmissibleChoice (fun y => t (Fin.castSucc y)) fun y => ch (Fin.castSucc y) where
  black x hx := by
    have := h.black _ hx
    rwa [Fin.val_castSucc, redsBefore_castSucc t (Nat.le_of_lt x.isLt)] at this
  red x hx := by
    have := h.red _ hx
    rwa [Fin.val_castSucc, redsBefore_castSucc t (Nat.le_of_lt x.isLt)] at this

omit [DecidableEq I] in
/-- **Admissible choices are choices of the loading**. -/
theorem mem_loadingChoices_ofFn : ∀ {m : ℕ} (t : Fin m → I ⊕ J) (ch : Fin m → ℕ),
    IsAdmissibleChoice t ch →
      (List.ofFn ch).reverse ∈ loadingChoices (List.ofFn t)
        ((List.ofFn t).countP fun a => a.isRight)
  | 0, _, _, _ => by simp [loadingChoices, choicesRev]
  | m + 1, t, ch, h => by
    have ih := mem_loadingChoices_ofFn _ _ h.castSucc
    rw [loadingChoices] at ih ⊢
    rw [reverse_ofFn_succ t, reverse_ofFn_succ ch]
    have hc : (List.ofFn t).countP (fun a => a.isRight) =
        (List.ofFn fun y => t (Fin.castSucc y)).countP (fun a => a.isRight) +
          if (t (Fin.last m)).isRight then 1 else 0 := by
      rw [List.ofFn_succ_last, List.countP_append]
      cases t (Fin.last m) <;> simp
    rcases ht : t (Fin.last m) with i | r
    · rw [ht] at hc
      simp only [Sum.isRight_inl, Bool.false_eq_true, ↓reduceIte, add_zero] at hc
      rw [hc, choicesRev, List.mem_flatMap]
      refine ⟨_, ih, List.mem_map.2 ⟨ch (Fin.last m), ?_, rfl⟩⟩
      have := h.black (Fin.last m) (by rw [ht]; rfl)
      rw [List.mem_range, ← redsBefore_last]
      exact this
    · rw [ht] at hc
      simp only [Sum.isRight_inr, ↓reduceIte] at hc
      rw [hc, choicesRev]
      have := h.red (Fin.last m) (by rw [ht]; rfl)
      rw [Fin.val_last, redsBefore_last] at this
      rw [this]
      exact List.mem_map.2 ⟨_, ih, rfl⟩

/-- The letter of a strand that chose the red `r`. -/
def choiceLetter (r : ℕ) : (I ⊕ J) × ℕ → Option I
  | (.inl i, j) => if j = r then some i else none
  | (.inr _, _) => none

omit [DecidableEq I] in
/-- **The words of an admissible choice**: the word of the red `r` lists the letters of the
black strands that chose it, in order. -/
theorem choiceRows_ofFn : ∀ {m : ℕ} (t : Fin m → I ⊕ J) (ch : Fin m → ℕ),
    IsAdmissibleChoice t ch → ∀ r : Fin ((List.ofFn t).countP fun a => a.isRight),
      choiceRows (List.ofFn t) (List.ofFn ch).reverse _ r =
        (List.finRange m).filterMap fun x => choiceLetter r.val (t x, ch x)
  | 0, _, _, _, r => by simp at r; exact r.elim0
  | m + 1, t, ch, h, r => by
    have ih := choiceRows_ofFn _ _ h.castSucc
    have hc : (List.ofFn t).countP (fun a => a.isRight) =
        (List.ofFn fun y => t (Fin.castSucc y)).countP (fun a => a.isRight) +
          if (t (Fin.last m)).isRight then 1 else 0 := by
      rw [List.ofFn_succ_last, List.countP_append]
      cases t (Fin.last m) <;> simp
    rw [List.finRange_succ_last, List.filterMap_append, List.filterMap_map]
    simp only [List.filterMap_cons, List.filterMap_nil]
    revert r
    rw [choiceRows, reverse_ofFn_succ t, reverse_ofFn_succ ch]
    rcases ht : t (Fin.last m) with i | q
    · rw [ht] at hc
      simp only [Sum.isRight_inl, Bool.false_eq_true, ↓reduceIte, add_zero] at hc
      rw [hc]
      intro r
      rw [rowsRev, addLetter]
      have := ih r
      rw [choiceRows] at this
      rw [this]
      congr 1
      by_cases h1 : ch (Fin.last m) = (r : ℕ)
      · simp [choiceLetter, h1]
      · simp [choiceLetter, h1, Ne.symm h1]
    · rw [ht] at hc
      simp only [Sum.isRight_inr, ↓reduceIte] at hc
      rw [hc]
      intro r
      rw [rowsRev]
      dsimp only
      refine Fin.lastCases ?_ (fun r => ?_) r
      · rw [Fin.lastCases_last]
        simp only [choiceLetter, Fin.val_last]
        symm
        rw [List.append_nil, List.filterMap_eq_nil_iff]
        intro x _
        simp only [Function.comp_apply]
        rcases hx : t (Fin.castSucc x) with i' | q'
        · have hb := h.black (Fin.castSucc x) (by rw [hx]; rfl)
          rw [Fin.val_castSucc, redsBefore_castSucc t (Nat.le_of_lt x.isLt)] at hb
          have hle : redsBefore (fun y => t (Fin.castSucc y)) x ≤
              (List.ofFn fun y => t (Fin.castSucc y)).countP fun a => a.isRight :=
            (List.take_sublist _ _).countP_le
          simp only [ite_eq_right_iff, reduceCtorEq, imp_false]
          omega
        · rfl
      · rw [Fin.lastCases_castSucc]
        have := ih r
        rw [choiceRows] at this
        rw [this]
        simp [choiceLetter, Function.comp_def]

omit [DecidableEq I] in
/-- The choices of a loading are distinct. -/
theorem nodup_choicesRev : ∀ (s : List (I ⊕ J)) (n : ℕ), (choicesRev s n).Nodup
  | [], 0 => List.nodup_singleton _
  | [], _ + 1 => List.nodup_nil
  | .inl _ :: s, n => by
    rw [choicesRev, List.nodup_flatMap]
    refine ⟨fun c _ => (List.nodup_range).map fun a b h => List.head_eq_of_cons_eq h, ?_⟩
    refine (nodup_choicesRev s n).imp fun {c c'} hcc' => ?_
    rw [Function.onFun, List.disjoint_left]
    intro l hl hl'
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hl
    obtain ⟨b, -, h⟩ := List.mem_map.1 hl'
    exact hcc' (List.tail_eq_of_cons_eq h).symm
  | .inr _ :: _, 0 => List.nodup_nil
  | .inr _ :: s, n + 1 => by
    rw [choicesRev]
    exact (nodup_choicesRev s n).map fun a b h => List.tail_eq_of_cons_eq h

omit [DecidableEq I] in
theorem nodup_loadingChoices (s : List (I ⊕ J)) (n : ℕ) : (loadingChoices s n).Nodup :=
  nodup_choicesRev s.reverse n

omit [DecidableEq I] in
theorem mem_loadingChoices_ofFn_of_eq {m : ℕ} (t : Fin m → I ⊕ J) (ch : Fin m → ℕ)
    (h : IsAdmissibleChoice t ch) {n : ℕ} (hn : ((List.ofFn t).countP fun a => a.isRight) = n) :
    (List.ofFn ch).reverse ∈ loadingChoices (List.ofFn t) n := by
  subst hn
  exact mem_loadingChoices_ofFn t ch h

omit [DecidableEq I] in
theorem choiceRows_ofFn_of_eq {m : ℕ} (t : Fin m → I ⊕ J) (ch : Fin m → ℕ)
    (h : IsAdmissibleChoice t ch) {n : ℕ} (hn : ((List.ofFn t).countP fun a => a.isRight) = n)
    (r : Fin n) : choiceRows (List.ofFn t) (List.ofFn ch).reverse n r =
      (List.finRange m).filterMap fun x => choiceLetter r.val (t x, ch x) := by
  subst hn
  exact choiceRows_ofFn t ch h r

end Categorification.Stendhal.FirstWeight
