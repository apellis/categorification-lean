/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Chord diagrams built from cups and crossings: a normal form

A purely combinatorial companion to M. Khovanov, A. Lauda, *A categorification of quantum
`sl(n)`*, arXiv:0807.3250v1, §3.2.3, proof of Proposition 3.11 ("arbitrary homotopies of colored
dotted diagrams modulo lower order terms", following A. Lauda, arXiv:0803.3652v3, §8): a diagram
of cups and crossings with all its endpoints on top is, up to isotopy and Reidemeister III moves,
either non-minimal (it contains a double crossing or a curl) or the chosen minimal diagram of its
pairing. Nothing here depends on the 2-category `U`.

## Diagrams

A *state* is a list of pairs `(arc id, letter)`, letters in a type `α` with a map
`d : α → α` (the dual letter). A *diagram* is a list of moves (`Move`), applied from the bottom
to the empty state (`step`, `run`):

* `cup g a`: insert `(k, a), (k, d a)` at position `g`, where `k` is a fresh id (a new arc, its
  left leg labelled `a`, its right leg `d a`);
* `cross p`: exchange the entries at positions `p` and `p + 1` (a crossing of two strands).

`Fits n D` says every move of `D` makes sense starting from `n` strands. The final state of a
diagram is a pairing (`Valid`: each position has exactly one partner, `Same`).

## The canonical diagram

For a pairing `s`, `canon s` is defined by recursion on the number of positions plus the number
`cr s` of pairs of interleaved arcs: if `s` has an adjacent arc (positions `r, r + 1` joined),
take the leftmost one and put `canon (rmAt s r) ++ [cup r a]`; otherwise take the first position
`q` which is the left end of an arc followed by the right end of another, and put
`canon (swapAt s q) ++ [cross q]` (the two arcs interleave in `s` but not in `swapAt s q`). So the
cups of `canon s` are created last, above the crossings.

## Moves

`Equiv` is the equivalence on diagrams generated, in context, by `Step`:

* moves at disjoint places commute (`cross`/`cross`, `cross`/`cup`, `cup`/`cup`, with the index
  shifts);
* the braid relation `cross p, cross (p+1), cross p ~ cross (p+1), cross p, cross (p+1)`;
* the pitchfork move `cup g a, cross (g+1) ~ cup (g+1) a, cross g` (a strand passing a cup on
  either side).

A diagram is `Reducible` if it is equivalent to one containing a double crossing
`cross p, cross p` or a curl `cup p a, cross p`.

## Main results

* `canon_cup` (**C1**): the cup of any adjacent arc can be taken last in `canon s`.
* `canon_ilv` (**Ex**): a crossing of any two interleaved arcs at adjacent positions can be
  taken last in `canon s` (the proof uses the pitchfork move when the two arcs meet a third
  endpoint of one of them, and the braid relation when three arcs pairwise interleave).
* `equiv_canon_or_reducible`: **every diagram that fits on the empty state is reducible or
  equivalent to the canonical diagram of its final pairing.**
* `Equiv.fits_letters`: equivalent diagrams fit on the same states and produce the same letters.
* `canon_eq_of_iso`: `canon s` depends only on the letters and the pairing of `s`.
* `run_canon`: `canon s` fits on the empty state and realises the letters and pairing of `s`
  (when the letters at the two ends of each arc are `a` and `d a`).
-/

namespace Categorification.Chord

section ListOps

variable {β : Type*}

/-- The transposition of `p` and `p + 1`. -/
def tau (p i : ℕ) : ℕ := if i = p then p + 1 else if i = p + 1 then p else i

theorem tau_tau (p i : ℕ) : tau p (tau p i) = i := by unfold tau; split_ifs <;> omega

theorem tau_inj {p i j : ℕ} : tau p i = tau p j ↔ i = j :=
  ⟨fun h => by rw [← tau_tau p i, h, tau_tau], fun h => h ▸ rfl⟩

/-- Exchange the entries at positions `p` and `p + 1` (no change if `p + 1` is out of range). -/
def swapAt (s : List β) (p : ℕ) : List β :=
  if h : p + 1 < s.length then (s.set p s[p + 1]).set (p + 1) s[p] else s

/-- Remove the entries at positions `r` and `r + 1`. -/
def rmAt (s : List β) (r : ℕ) : List β := s.take r ++ s.drop (r + 2)

/-- Insert `x, y` at position `g`. -/
def insAt (s : List β) (g : ℕ) (x y : β) : List β := s.take g ++ x :: y :: s.drop g

/-- The position in `s` of the entry at position `i` of `rmAt s r`. -/
def rmIdx (r i : ℕ) : ℕ := if i < r then i else i + 2

@[simp] theorem length_swapAt (s : List β) (p : ℕ) : (swapAt s p).length = s.length := by
  unfold swapAt; split_ifs <;> simp

theorem length_rmAt (s : List β) {r : ℕ} (h : r + 2 ≤ s.length) :
    (rmAt s r).length = s.length - 2 := by simp [rmAt]; omega

theorem length_insAt (s : List β) {g : ℕ} (h : g ≤ s.length) (x y : β) :
    (insAt s g x y).length = s.length + 2 := by simp [insAt]; omega

theorem getElem?_swapAt (s : List β) {p : ℕ} (hp : p + 1 < s.length) (i : ℕ) :
    (swapAt s p)[i]? = s[tau p i]? := by
  have hp' : p < s.length := by omega
  rcases (show i = p ∨ i = p + 1 ∨ (i ≠ p ∧ i ≠ p + 1) by omega) with rfl | rfl | ⟨h1, h2⟩
  · simp [swapAt, hp, tau, hp']
  · simp [swapAt, hp, tau, hp']
  · simp [swapAt, hp, tau, h1, h2, Ne.symm h1, Ne.symm h2]

theorem getElem?_rmAt (s : List β) {r : ℕ} (hr : r + 2 ≤ s.length) (i : ℕ) :
    (rmAt s r)[i]? = s[rmIdx r i]? := by
  simp only [rmAt, rmIdx, List.getElem?_append, List.length_take, List.getElem?_take,
    List.getElem?_drop]
  split_ifs <;> first | rfl | (congr 1; omega)

theorem getElem?_insAt (s : List β) {g : ℕ} (hg : g ≤ s.length) (x y : β) (i : ℕ) :
    (insAt s g x y)[i]? = if i < g then s[i]? else if i = g then some x
      else if i = g + 1 then some y else s[i - 2]? := by
  simp only [insAt, List.getElem?_append, List.length_take, List.getElem?_take]
  rcases (show i < g ∨ i = g ∨ i = g + 1 ∨ g + 1 < i by omega) with h | rfl | rfl | h
  · simp [h]; omega
  · simp [Nat.min_eq_left hg]
  · simp [Nat.min_eq_left hg]
  · simp [Nat.min_eq_left hg, show ¬ i < g by omega, show i ≠ g by omega, show i ≠ g + 1 by omega]
    obtain ⟨m, rfl⟩ : ∃ m, i = g + 2 + m := ⟨i - g - 2, by omega⟩
    rw [show g + 2 + m - g = m + 2 by omega, show g + 2 + m - 2 = g + m by omega]
    simp [List.getElem?_drop]


theorem rmIdx_lt_iff (r : ℕ) {i j : ℕ} : rmIdx r i < rmIdx r j ↔ i < j := by
  unfold rmIdx; split_ifs <;> omega

theorem rmIdx_inj {r i j : ℕ} : rmIdx r i = rmIdx r j ↔ i = j := by
  unfold rmIdx; split_ifs <;> omega

theorem tau_lt_iff (p : ℕ) {i j : ℕ} (h : ¬ (i = p ∧ j = p + 1)) (h' : ¬ (i = p + 1 ∧ j = p)) :
    tau p i < tau p j ↔ i < j := by unfold tau; split_ifs <;> omega

theorem swapAt_swapAt (s : List β) (p : ℕ) : swapAt (swapAt s p) p = s := by
  by_cases hp : p + 1 < s.length
  · apply List.ext_getElem?; intro i
    rw [getElem?_swapAt _ (by simpa using hp), getElem?_swapAt _ hp, tau_tau]
  · simp [swapAt, hp]

theorem swapAt_of_le (s : List β) {p : ℕ} (hp : ¬ p + 1 < s.length) : swapAt s p = s := by
  simp [swapAt, hp]

theorem rmAt_insAt (s : List β) (g : ℕ) (x y : β) (hg : g ≤ s.length) :
    rmAt (insAt s g x y) g = s := by
  apply List.ext_getElem?; intro i
  rw [getElem?_rmAt _ (by rw [length_insAt s hg]; omega), getElem?_insAt s hg]
  unfold rmIdx; split_ifs <;> first | rfl | omega

theorem insAt_rmAt (s : List β) {r : ℕ} (hr : r + 1 < s.length) :
    insAt (rmAt s r) r s[r] s[r + 1] = s := by
  have hl := length_rmAt s (r := r) (by omega)
  apply List.ext_getElem?; intro i
  rw [getElem?_insAt _ (by omega)]
  simp only [getElem?_rmAt s (show r + 2 ≤ s.length by omega), rmIdx]
  rcases (show i < r ∨ i = r ∨ i = r + 1 ∨ r + 1 < i by omega) with h | rfl | rfl | h
  · simp [h]
  · simp
  · simp
  · simp [show ¬ i < r by omega, show i ≠ r by omega, show i ≠ r + 1 by omega,
      show ¬ i - 2 < r by omega, show i - 2 + 2 = i by omega]

end ListOps

/-! ## Pairings -/

section Pairings

variable {α : Type*}

/-- The arc id at position  (if any). -/
def idAt (s : List (ℕ × α)) (i : ℕ) : Option ℕ := (s[i]?).map Prod.fst

/-- Positions  of  carry the same arc id. -/
def Same (s : List (ℕ × α)) (i j : ℕ) : Prop := i ≠ j ∧ idAt s i ≠ none ∧ idAt s i = idAt s j

/--  is a pairing: every position has exactly one partner. -/
def Valid (s : List (ℕ × α)) : Prop := ∀ i < s.length, ∃! j, Same s i j

variable {s : List (ℕ × α)}

theorem idAt_ne_none_iff {i : ℕ} : idAt s i ≠ none ↔ i < s.length := by
  simp [idAt]

theorem Same.symm {i j : ℕ} (h : Same s i j) : Same s j i :=
  ⟨h.1.symm, h.2.2 ▸ h.2.1, h.2.2.symm⟩

theorem same_comm {i j : ℕ} : Same s i j ↔ Same s j i := ⟨Same.symm, Same.symm⟩

theorem Same.lt_left {i j : ℕ} (h : Same s i j) : i < s.length := idAt_ne_none_iff.1 h.2.1

theorem Same.lt_right {i j : ℕ} (h : Same s i j) : j < s.length := h.symm.lt_left

theorem Same.ne {i j : ℕ} (h : Same s i j) : i ≠ j := h.1

theorem Valid.unique (hv : Valid s) {i j j' : ℕ} (h : Same s i j) (h' : Same s i j') : j = j' :=
  (hv i h.lt_left).unique h h'

theorem Valid.exists (hv : Valid s) {i : ℕ} (hi : i < s.length) : ∃ j, Same s i j :=
  (hv i hi).exists

theorem idAt_swapAt {p : ℕ} (hp : p + 1 < s.length) (i : ℕ) :
    idAt (swapAt s p) i = idAt s (tau p i) := by
  simp [idAt, getElem?_swapAt s hp]

theorem same_swapAt {p : ℕ} (hp : p + 1 < s.length) {i j : ℕ} :
    Same (swapAt s p) i j ↔ Same s (tau p i) (tau p j) := by
  simp only [Same, idAt_swapAt hp, ne_eq, tau_inj]

theorem idAt_rmAt {r : ℕ} (hr : r + 2 ≤ s.length) (i : ℕ) :
    idAt (rmAt s r) i = idAt s (rmIdx r i) := by
  simp [idAt, getElem?_rmAt s hr]

theorem same_rmAt {r : ℕ} (hr : r + 2 ≤ s.length) {i j : ℕ} :
    Same (rmAt s r) i j ↔ Same s (rmIdx r i) (rmIdx r j) := by
  simp only [Same, idAt_rmAt hr, ne_eq, rmIdx_inj]

theorem Valid.swapAt (hv : Valid s) {p : ℕ} (hp : p + 1 < s.length) :
    Valid (Chord.swapAt s p) := by
  intro i hi
  have hi' : tau p i < s.length := by simp at hi; unfold tau; split_ifs <;> omega
  obtain ⟨j, hj, hu⟩ := hv (tau p i) hi'
  refine ⟨tau p j, ?_, fun k hk => ?_⟩
  · show Same _ _ _
    rw [same_swapAt hp, tau_tau]; exact hj
  · have hk' : Same (Chord.swapAt s p) i k := hk
    rw [same_swapAt hp] at hk'
    rw [← hu _ hk', tau_tau]

theorem Valid.rmAt (hv : Valid s) {r : ℕ} (hadj : Same s r (r + 1)) :
    Valid (Chord.rmAt s r) := by
  have hr : r + 2 ≤ s.length := hadj.lt_right
  intro i hi
  rw [length_rmAt s hr] at hi
  have hi' : rmIdx r i < s.length := by unfold rmIdx; split_ifs <;> omega
  obtain ⟨j, hj, hu⟩ := hv (rmIdx r i) hi'
  have hjr : j ≠ r ∧ j ≠ r + 1 := by
    constructor
    · rintro rfl
      have := hv.unique hadj hj.symm
      unfold rmIdx at this; split_ifs at this <;> omega
    · rintro rfl
      have := hv.unique hadj.symm hj.symm
      unfold rmIdx at this; split_ifs at this <;> omega
  refine ⟨if j < r then j else j - 2, ?_, fun k hk => ?_⟩
  · show Same _ _ _
    rw [same_rmAt hr]
    have e : rmIdx r (if j < r then j else j - 2) = j := by
      unfold rmIdx; split_ifs <;> omega
    rw [e]; exact hj
  · have hk' : Same (Chord.rmAt s r) i k := hk
    rw [same_rmAt hr] at hk'
    have := hu _ hk'
    unfold rmIdx at this; split_ifs at this ⊢ <;> omega

theorem idAt_insAt {g : ℕ} (hg : g ≤ s.length) (k : ℕ) (a b : α) (i : ℕ) :
    idAt (insAt s g (k, a) (k, b)) i = if i < g then idAt s i else if i = g then some k
      else if i = g + 1 then some k else idAt s (i - 2) := by
  simp only [idAt, getElem?_insAt s hg]
  split_ifs <;> rfl

theorem same_insAt_iff {g : ℕ} (hg : g ≤ s.length) {k : ℕ} (hk : ∀ x ∈ s, x.1 ≠ k) (a b : α)
    {i j : ℕ} : Same (insAt s g (k, a) (k, b)) i j ↔
      ((i = g ∧ j = g + 1) ∨ (i = g + 1 ∧ j = g) ∨
        (i ≠ g ∧ i ≠ g + 1 ∧ j ≠ g ∧ j ≠ g + 1 ∧ Same s (if i < g then i else i - 2)
          (if j < g then j else j - 2))) := by
  have hk' : ∀ i, idAt s i ≠ some k := by
    intro i h
    simp only [idAt, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, rfl⟩ := h
    exact hk x (List.mem_of_getElem? hx) rfl
  simp only [Same, idAt_insAt hg]
  constructor
  · rintro ⟨h1, h2, h3⟩
    split_ifs at h2 h3 <;> first
      | (left; omega) | (right; left; omega)
      | (exfalso; exact hk' _ h3) | (exfalso; exact hk' _ h3.symm)
      | (right; right; refine ⟨by omega, by omega, by omega, by omega, ?_⟩
         split_ifs; first | omega | exact ⟨by omega, h2, h3⟩)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨h1, h2, h3, h4, h5, h6, h7⟩)
    · simp
    · simp
    · refine ⟨fun e => ?_, ?_⟩
      · subst e; split_ifs at h5 <;> omega
      · split_ifs at h6 h7 ⊢ <;> first | omega | exact ⟨h6, h7⟩

theorem Valid.insAt (hv : Valid s) {g : ℕ} (hg : g ≤ s.length) {k : ℕ} (hk : ∀ x ∈ s, x.1 ≠ k)
    (a b : α) : Valid (Chord.insAt s g (k, a) (k, b)) := by
  intro i hi
  rw [length_insAt s hg] at hi
  by_cases h1 : i = g
  · subst h1
    refine ⟨i + 1, (same_insAt_iff hg hk a b).2 (Or.inl ⟨rfl, rfl⟩), fun j hj => ?_⟩
    have hj' : Same _ _ _ := hj
    rw [same_insAt_iff hg hk] at hj'; omega
  by_cases h2 : i = g + 1
  · subst h2
    refine ⟨g, (same_insAt_iff hg hk a b).2 (Or.inr (Or.inl ⟨rfl, rfl⟩)), fun j hj => ?_⟩
    have hj' : Same _ _ _ := hj
    rw [same_insAt_iff hg hk] at hj'; omega
  obtain ⟨j, hj, hu⟩ := hv (if i < g then i else i - 2) (by split_ifs <;> omega)
  have hjl := hj.lt_right
  refine ⟨if j < g then j else j + 2, ?_, fun j' hj' => ?_⟩
  · show Same _ _ _
    rw [same_insAt_iff hg hk]
    right; right
    refine ⟨h1, h2, by split_ifs <;> omega, by split_ifs <;> omega, ?_⟩
    have e : (if (if j < g then j else j + 2) < g then (if j < g then j else j + 2)
        else (if j < g then j else j + 2) - 2) = j := by split_ifs <;> omega
    rw [e]; exact hj
  · have hj'' : Same _ _ _ := hj'
    rw [same_insAt_iff hg hk] at hj''
    rcases hj'' with h | h | ⟨-, -, h3, h4, h5⟩
    · omega
    · omega
    · have := hu _ h5
      split_ifs at this ⊢ <;> omega

end Pairings

/-! ## Crossings -/

section Crossings

open scoped Classical

variable {α : Type*} {s : List (ℕ × α)}

/-- Positions `i < j < k < l` with `i, k` on one arc and `j, l` on another: a crossing. -/
def Cr4 (s : List (ℕ × α)) (i j k l : ℕ) : Prop := i < j ∧ j < k ∧ k < l ∧ Same s i k ∧ Same s j l

/-- The set of crossings, as quadruples of positions. -/
noncomputable def crSet (s : List (ℕ × α)) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  ((Finset.range s.length) ×ˢ (Finset.range s.length) ×ˢ (Finset.range s.length) ×ˢ
    (Finset.range s.length)).filter fun x => Cr4 s x.1 x.2.1 x.2.2.1 x.2.2.2

/-- The crossing number of a pairing: the number of pairs of interleaved arcs. -/
noncomputable def cr (s : List (ℕ × α)) : ℕ := (crSet s).card

theorem mem_crSet {x : ℕ × ℕ × ℕ × ℕ} : x ∈ crSet s ↔ Cr4 s x.1 x.2.1 x.2.2.1 x.2.2.2 := by
  simp only [crSet, Finset.mem_filter, Finset.mem_product, Finset.mem_range, and_iff_right_iff_imp]
  intro h
  exact ⟨h.2.2.2.1.lt_left, h.2.2.2.2.lt_left, h.2.2.2.1.lt_right, h.2.2.2.2.lt_right⟩

/-- The arcs at positions `q` and `q + 1` interleave. -/
def Ilv (s : List (ℕ × α)) (q : ℕ) : Prop :=
  ∃ i j k l, Cr4 s i j k l ∧ ((i = q ∧ j = q + 1) ∨ (j = q ∧ k = q + 1) ∨ (k = q ∧ l = q + 1))

/-- In a pairing, whether the arcs at `q` and `q + 1` (with partners `a` and `b`) interleave. -/
theorem ilv_iff (hv : Valid s) {q a b : ℕ} (ha : Same s q a) (hb : Same s (q + 1) b) :
    Ilv s q ↔ (q + 1 < a ∧ a < b) ∨ (b < q ∧ q + 1 < a) ∨ (a < b ∧ b < q) := by
  constructor
  · rintro ⟨i, j, k, l, ⟨h1, h2, h3, h4, h5⟩, h | h | h⟩ <;> obtain ⟨rfl, rfl⟩ := h
    · have := hv.unique ha h4; have := hv.unique hb h5; omega
    · have := hv.unique ha h5; have := hv.unique hb h4.symm; omega
    · have := hv.unique ha h4.symm; have := hv.unique hb h5.symm; omega
  · rintro (h | h | h)
    · exact ⟨q, q + 1, a, b, ⟨by omega, by omega, by omega, ha, hb⟩, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨b, q, q + 1, a, ⟨by omega, by omega, by omega, hb.symm, ha⟩,
        Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    · exact ⟨a, b, q, q + 1, ⟨by omega, by omega, by omega, ha.symm, hb.symm⟩,
        Or.inr (Or.inr ⟨rfl, rfl⟩)⟩

theorem Ilv.lt (h : Ilv s q) : q + 1 < s.length := by
  obtain ⟨i, j, k, l, ⟨h1, h2, h3, h4, h5⟩, h | h | h⟩ := h <;> obtain ⟨rfl, rfl⟩ := h
  · exact h5.lt_left
  · exact h4.lt_right
  · exact h5.lt_right

theorem Ilv.not_same (hv : Valid s) (h : Ilv s q) : ¬ Same s q (q + 1) := by
  intro hq
  obtain ⟨a, ha⟩ := hv.exists (show q < s.length by have := h.lt; omega)
  obtain ⟨b, hb⟩ := hv.exists h.lt
  have e1 := hv.unique ha hq
  have e2 := hv.unique hb hq.symm
  rw [ilv_iff hv ha hb] at h
  omega

/-- The partners of `q` and `q + 1` after exchanging them. -/
theorem swapAt_partners {p : ℕ} (hp : p + 1 < s.length) {a b : ℕ} (ha : Same s p a)
    (hb : Same s (p + 1) b) (hab : ¬ Same s p (p + 1)) :
    Same (swapAt s p) p b ∧ Same (swapAt s p) (p + 1) a := by
  have ha1 : a ≠ p + 1 := fun e => hab (e ▸ ha)
  have hb1 : b ≠ p := fun e => hab (e ▸ hb).symm
  have ta : tau p a = a := by unfold tau; have := ha.ne; split_ifs <;> omega
  have tb : tau p b = b := by unfold tau; have := hb.ne; split_ifs <;> omega
  have t1 : tau p p = p + 1 := by simp [tau]
  have t2 : tau p (p + 1) = p := by simp [tau]
  rw [same_swapAt hp, same_swapAt hp, ta, tb, t1, t2]
  exact ⟨hb, ha⟩

/-- Exchanging two adjacent endpoints of different arcs toggles their interleaving. -/
theorem ilv_swapAt_iff (hv : Valid s) {p : ℕ} (hp : p + 1 < s.length)
    (hab : ¬ Same s p (p + 1)) : Ilv (swapAt s p) p ↔ ¬ Ilv s p := by
  obtain ⟨a, ha⟩ := hv.exists (show p < s.length by omega)
  obtain ⟨b, hb⟩ := hv.exists hp
  obtain ⟨ha', hb'⟩ := swapAt_partners hp ha hb hab
  have hab' : a ≠ b := fun e => by subst e; have := hv.unique ha.symm hb.symm; omega
  have ha1 : a ≠ p + 1 := fun e => hab (e ▸ ha)
  have hb1 : b ≠ p := fun e => hab (e ▸ hb).symm
  rw [ilv_iff (hv.swapAt hp) ha' hb', ilv_iff hv ha hb]
  have := ha.ne; have := hb.ne
  omega

theorem cr_rmAt_le {r : ℕ} (hr : r + 2 ≤ s.length) : cr (rmAt s r) ≤ cr s := by
  unfold cr
  refine Finset.card_le_card_of_injOn (fun x => (rmIdx r x.1, rmIdx r x.2.1, rmIdx r x.2.2.1,
    rmIdx r x.2.2.2)) (fun x hx => ?_) (fun x _ y _ h => ?_)
  · obtain ⟨h1, h2, h3, h4, h5⟩ := mem_crSet.1 hx
    apply mem_crSet.2
    exact ⟨(rmIdx_lt_iff r).2 h1, (rmIdx_lt_iff r).2 h2, (rmIdx_lt_iff r).2 h3,
      (same_rmAt hr).1 h4, (same_rmAt hr).1 h5⟩
  · simp only [Prod.mk.injEq, rmIdx_inj] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    exact Prod.ext h1 (Prod.ext h2 (Prod.ext h3 h4))

theorem cr_swapAt_lt (hv : Valid s) {p : ℕ} (h : Ilv s p) : cr (swapAt s p) < cr s := by
  have hp := h.lt
  have hn : ¬ Ilv (swapAt s p) p := by
    rw [ilv_swapAt_iff hv hp (h.not_same hv)]; exact not_not.2 h
  unfold cr
  let F : ℕ × ℕ × ℕ × ℕ → ℕ × ℕ × ℕ × ℕ := fun x => (tau p x.1, tau p x.2.1, tau p x.2.2.1,
    tau p x.2.2.2)
  have hF : Function.Injective F := by
    intro x y e
    simp only [F, Prod.mk.injEq, tau_inj] at e
    exact Prod.ext e.1 (Prod.ext e.2.1 (Prod.ext e.2.2.1 e.2.2.2))
  rw [← Finset.card_image_of_injective _ hF]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · obtain ⟨i, j, k, l, hc, hq⟩ := h
    refine ⟨(i, j, k, l), mem_crSet.2 hc, fun hm => ?_⟩
    obtain ⟨x, hx, e⟩ := Finset.mem_image.1 hm
    rw [mem_crSet] at hx
    have ex : x = F (i, j, k, l) := by rw [← e]; simp [F, tau_tau]
    subst ex
    obtain ⟨h1, h2, h3, -, -⟩ := hx
    simp only [F, tau] at h1 h2 h3
    rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      obtain ⟨h1', h2', h3', -, -⟩ := hc <;> split_ifs at h1 h2 h3 <;> omega
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    rw [mem_crSet] at hx ⊢
    obtain ⟨h1, h2, h3, h4, h5⟩ := hx
    have n1 : ¬ (x.1 = p ∧ x.2.1 = p + 1) := fun ⟨e1, e2⟩ =>
      hn ⟨_, _, _, _, ⟨h1, h2, h3, h4, h5⟩, Or.inl ⟨e1, e2⟩⟩
    have n2 : ¬ (x.2.1 = p ∧ x.2.2.1 = p + 1) := fun ⟨e1, e2⟩ =>
      hn ⟨_, _, _, _, ⟨h1, h2, h3, h4, h5⟩, Or.inr (Or.inl ⟨e1, e2⟩)⟩
    have n3 : ¬ (x.2.2.1 = p ∧ x.2.2.2 = p + 1) := fun ⟨e1, e2⟩ =>
      hn ⟨_, _, _, _, ⟨h1, h2, h3, h4, h5⟩, Or.inr (Or.inr ⟨e1, e2⟩)⟩
    exact ⟨(tau_lt_iff p n1 (by omega)).2 h1, (tau_lt_iff p n2 (by omega)).2 h2,
      (tau_lt_iff p n3 (by omega)).2 h3, (same_swapAt hp).1 h4, (same_swapAt hp).1 h5⟩

end Crossings

/-! ## Moves, the equivalence, and the canonical diagram -/

section Moves

variable {α : Type*}

/-- A move: a cup inserting a new arc at gap `g` with left leg labelled `a`, or a crossing of the
strands at positions `p` and `p + 1`. -/
inductive Move (α : Type*)
  | cup (g : ℕ) (a : α)
  | cross (p : ℕ)

/-- The generating relations (each one relating two short diagrams that are equal up to isotopy,
or, for `braid`, up to the Reidemeister III move):

* `xx`: crossings at distant positions commute;
* `xuL`, `xuR`: a crossing and a cup at distant positions commute;
* `uu`: two cups commute;
* `braid`: the braid relation;
* `pitch`: a strand crossing the right leg of a cup equals it crossing the left leg of the cup
  on its other side (a pitchfork move). -/
inductive Step : List (Move α) → List (Move α) → Prop
  | xx {p p' : ℕ} (h : p + 2 ≤ p') : Step [.cross p, .cross p'] [.cross p', .cross p]
  | xuL {p g : ℕ} (a : α) (h : p + 2 ≤ g) : Step [.cross p, .cup g a] [.cup g a, .cross p]
  | xuR {p g : ℕ} (a : α) (h : g ≤ p) : Step [.cross p, .cup g a] [.cup g a, .cross (p + 2)]
  | uu {g g' : ℕ} (a b : α) (h : g' ≤ g) :
      Step [.cup g a, .cup g' b] [.cup g' b, .cup (g + 2) a]
  | braid (p : ℕ) :
      Step [.cross p, .cross (p + 1), .cross p] [.cross (p + 1), .cross p, .cross (p + 1)]
  | pitch (g : ℕ) (a : α) : Step [.cup g a, .cross (g + 1)] [.cup (g + 1) a, .cross g]

/-- One generating relation applied in context. -/
def Rw (X Y : List (Move α)) : Prop :=
  ∃ A B L R, Step L R ∧ X = A ++ L ++ B ∧ Y = A ++ R ++ B

/-- The equivalence of diagrams generated by the moves `Step` in context. -/
def Equiv : List (Move α) → List (Move α) → Prop := Relation.EqvGen Rw

namespace Equiv

@[refl] theorem refl (X : List (Move α)) : Equiv X X := Relation.EqvGen.refl X

theorem symm {X Y : List (Move α)} (h : Equiv X Y) : Equiv Y X := Relation.EqvGen.symm _ _ h

theorem trans {X Y Z : List (Move α)} (h : Equiv X Y) (h' : Equiv Y Z) : Equiv X Z :=
  Relation.EqvGen.trans _ _ _ h h'

theorem of_step {L R : List (Move α)} (h : Step L R) : Equiv L R :=
  Relation.EqvGen.rel _ _ ⟨[], [], L, R, h, by simp, by simp⟩

theorem append_right {X Y : List (Move α)} (h : Equiv X Y) (Z : List (Move α)) :
    Equiv (X ++ Z) (Y ++ Z) := by
  induction h with
  | rel X Y h =>
    obtain ⟨A, B, L, R, h, rfl, rfl⟩ := h
    exact Relation.EqvGen.rel _ _ ⟨A, B ++ Z, L, R, h, by simp, by simp⟩
  | refl => exact refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

theorem append_left {X Y : List (Move α)} (h : Equiv X Y) (Z : List (Move α)) :
    Equiv (Z ++ X) (Z ++ Y) := by
  induction h with
  | rel X Y h =>
    obtain ⟨A, B, L, R, h, rfl, rfl⟩ := h
    exact Relation.EqvGen.rel _ _ ⟨Z ++ A, B, L, R, h, by simp, by simp⟩
  | refl => exact refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

/-- A move in context. -/
theorem step_mid {L R : List (Move α)} (h : Step L R) (A B : List (Move α)) :
    Equiv (A ++ L ++ B) (A ++ R ++ B) :=
  ((of_step h).append_left A).append_right B

end Equiv

/-- A diagram is *reducible* if it is equivalent to one containing a double crossing
`cross p, cross p` or a curl `cup p a, cross p`. -/
def Reducible (D : List (Move α)) : Prop :=
  ∃ A B : List (Move α), ∃ p : ℕ, (Equiv D (A ++ [.cross p, .cross p] ++ B)) ∨
    ∃ a : α, Equiv D (A ++ [.cup p a, .cross p] ++ B)

theorem Reducible.of_equiv {D D' : List (Move α)} (h : Reducible D') (e : Equiv D D') :
    Reducible D := by
  obtain ⟨A, B, p, h⟩ := h
  refine ⟨A, B, p, ?_⟩
  rcases h with h | ⟨a, h⟩
  · exact Or.inl (e.trans h)
  · exact Or.inr ⟨a, e.trans h⟩

theorem Reducible.append {D : List (Move α)} (h : Reducible D) (Z : List (Move α)) :
    Reducible (D ++ Z) := by
  obtain ⟨A, B, p, h⟩ := h
  refine ⟨A, B ++ Z, p, ?_⟩
  rcases h with h | ⟨a, h⟩
  · exact Or.inl (by simpa using h.append_right Z)
  · exact Or.inr ⟨a, by simpa using h.append_right Z⟩

/-- Position `q` is the left end of its arc. -/
def Opn (s : List (ℕ × α)) (q : ℕ) : Prop := ∃ j, q < j ∧ Same s q j

/-- Position `q` is the right end of its arc. -/
def Cls (s : List (ℕ × α)) (q : ℕ) : Prop := ∃ j, j < q ∧ Same s q j

theorem ilv_of_opn_cls {s : List (ℕ × α)} (hv : Valid s) {q : ℕ} (hn : ¬ Same s q (q + 1))
    (ho : Opn s q) (hc : Cls s (q + 1)) : Ilv s q := by
  obtain ⟨a, hqa, ha⟩ := ho
  obtain ⟨b, hbq, hb⟩ := hc
  have h1 : a ≠ q + 1 := fun e => hn (e ▸ ha)
  have h2 : b ≠ q := fun e => hn (e ▸ hb).symm
  rw [ilv_iff hv ha hb]; omega

open scoped Classical in
/-- The canonical diagram of a pairing: remove the leftmost adjacent arc (a cup, created last),
or else uncross the first pair of adjacent endpoints "left end, right end". -/
noncomputable def canon (s : List (ℕ × α)) : List (Move α) :=
  if hv : Valid s then
    if h : ∃ r, Same s r (r + 1) then
      canon (rmAt s (Nat.find h)) ++
        [.cup (Nat.find h) (s[Nat.find h]'((Nat.find_spec h).lt_left)).2]
    else if h' : ∃ q, Opn s q ∧ Cls s (q + 1) then
      canon (swapAt s (Nat.find h')) ++ [.cross (Nat.find h')]
    else []
  else []
termination_by s.length + cr s
decreasing_by
  · have h1 := (Nat.find_spec h).lt_right
    have := cr_rmAt_le (s := s) (r := Nat.find h) (by omega)
    rw [length_rmAt s (by omega)]; omega
  · have := cr_swapAt_lt hv (ilv_of_opn_cls hv (fun hs => h ⟨_, hs⟩) (Nat.find_spec h').1
      (Nat.find_spec h').2)
    rw [length_swapAt]; omega

theorem canon_adj {s : List (ℕ × α)} (hv : Valid s) {r : ℕ} (hr : Same s r (r + 1))
    (hmin : ∀ r' < r, ¬ Same s r' (r' + 1)) :
    canon s = canon (rmAt s r) ++ [.cup r (s[r]'hr.lt_left).2] := by
  classical
  have h : ∃ r, Same s r (r + 1) := ⟨r, hr⟩
  have e : Nat.find h = r := le_antisymm (Nat.find_min' h hr)
    (not_lt.1 fun hl => hmin _ hl (Nat.find_spec h))
  rw [canon, dite_eq_left hv, dite_eq_left h]
  subst e
  rfl

theorem canon_cross {s : List (ℕ × α)} (hv : Valid s) (hno : ∀ r, ¬ Same s r (r + 1))
    (hne : s ≠ []) : ∃ q, Opn s q ∧ Cls s (q + 1) ∧ canon s = canon (swapAt s q) ++ [.cross q] ∧
      ∀ q' < q, ¬ (Opn s q' ∧ Cls s (q' + 1)) := by
  classical
  have h : ¬ ∃ r, Same s r (r + 1) := fun ⟨r, hr⟩ => hno r hr
  have h' : ∃ q, Opn s q ∧ Cls s (q + 1) := by
    -- the first right end
    have hex : ∃ i, Cls s i := by
      obtain ⟨j, hj⟩ := hv.exists (show 0 < s.length from List.length_pos_of_ne_nil hne)
      exact ⟨j, 0, Nat.pos_of_ne_zero hj.ne.symm, hj.symm⟩
    have hi := Nat.find_spec hex
    have hpos : Nat.find hex ≠ 0 := by
      intro e; obtain ⟨j, hj, -⟩ := hi; omega
    refine ⟨Nat.find hex - 1, ?_, by rw [Nat.sub_add_cancel (by omega)]; exact hi⟩
    obtain ⟨j, hj⟩ := hv.exists (show Nat.find hex - 1 < s.length by
      obtain ⟨_, _, hc⟩ := hi; have := hc.lt_left; omega)
    refine ⟨j, ?_, hj⟩
    by_contra hlt
    have hj' : j < Nat.find hex - 1 := lt_of_le_of_ne (not_lt.1 hlt) hj.ne.symm
    exact Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega) ⟨j, hj', hj⟩
  refine ⟨Nat.find h', (Nat.find_spec h').1, (Nat.find_spec h').2, ?_,
    fun q' hq' => Nat.find_min h' hq'⟩
  rw [canon, dite_eq_left hv, dite_eq_right h, dite_eq_left h']

theorem canon_nil : canon ([] : List (ℕ × α)) = [] := by
  classical
  have hv : Valid ([] : List (ℕ × α)) := fun i hi => by simp at hi
  rw [canon, dite_eq_left hv, dite_eq_right (fun ⟨r, hr⟩ => by have := hr.lt_left; simp at this),
    dite_eq_right (fun ⟨q, ⟨j, _, hj⟩, _⟩ => by have := hj.lt_left; simp at this)]

end Moves

/-! ## Taking a cup last -/

section CupLast

variable {α : Type*}

theorem getElem_eq_of_getElem? {β : Type*} {l l' : List β} {i j : ℕ} (hi : i < l.length)
    (hj : j < l'.length) (h : l[i]? = l'[j]?) : l[i] = l'[j] := by
  rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj] at h
  exact Option.some.inj h

theorem rmAt_rmAt {β : Type*} (s : List β) {r₀ m : ℕ} (h : r₀ ≤ m) (hl : m + 4 ≤ s.length) :
    rmAt (rmAt s (m + 2)) r₀ = rmAt (rmAt s r₀) m := by
  apply List.ext_getElem?; intro i
  rw [getElem?_rmAt _ (by rw [length_rmAt _ (by omega)]; omega), getElem?_rmAt _ (by omega),
    getElem?_rmAt _ (by rw [length_rmAt _ (by omega)]; omega), getElem?_rmAt _ (by omega)]
  congr 1; unfold rmIdx; split_ifs <;> omega

/-- **C1.** In a pairing, the cup of any adjacent arc can be taken as the last move of the
canonical diagram. -/
theorem canon_cup {s : List (ℕ × α)} (hv : Valid s) {r : ℕ} (hr : Same s r (r + 1)) :
    Equiv (canon s) (canon (rmAt s r) ++ [.cup r (s[r]'hr.lt_left).2]) := by
  induction' hn : s.length using Nat.strong_induction_on with n ih generalizing s r
  classical
  have h : ∃ r, Same s r (r + 1) := ⟨r, hr⟩
  obtain ⟨r₀, hr₀, hmin, hle⟩ : ∃ r₀, Same s r₀ (r₀ + 1) ∧ (∀ r' < r₀, ¬ Same s r' (r' + 1)) ∧
      r₀ ≤ r := ⟨Nat.find h, Nat.find_spec h, fun _ => Nat.find_min h, Nat.find_min' h hr⟩
  rw [canon_adj hv hr₀ hmin]
  rcases hle.eq_or_lt with e | hlt
  · subst e; exact Equiv.refl _
  have h2 : r₀ + 2 ≤ r := by
    by_contra hc
    have e : r = r₀ + 1 := by omega
    subst e
    have := hv.unique hr₀.symm hr
    omega
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 2 := ⟨r - 2, by omega⟩
  have hl : m + 4 ≤ s.length := hr.lt_right
  have hr' : Same (rmAt s r₀) m (m + 1) := by
    rw [same_rmAt (by omega)]; simp only [rmIdx]
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]; exact hr
  have hr₀' : Same (rmAt s (m + 2)) r₀ (r₀ + 1) := by
    rw [same_rmAt (by omega)]; simp only [rmIdx]
    rw [ite_eq_left (by omega), ite_eq_left (by omega)]; exact hr₀
  have ih1 := ih _ (by rw [← hn, length_rmAt s (by omega)]; omega) (hv.rmAt hr₀) hr' rfl
  have ih2 := ih _ (by rw [← hn, length_rmAt s (by omega)]; omega) (hv.rmAt hr) hr₀' rfl
  have ea' : (rmAt s r₀)[m]? = s[m + 2]? := by
    rw [getElem?_rmAt s (by omega)]; simp only [rmIdx]; rw [ite_eq_right (by omega)]
  have eb' : (rmAt s (m + 2))[r₀]? = s[r₀]? := by
    rw [getElem?_rmAt s (by omega)]; simp only [rmIdx]; rw [ite_eq_left (by omega)]
  have ea : ((rmAt s r₀)[m]'hr'.lt_left).2 = (s[m + 2]'hr.lt_left).2 := by
    rw [getElem_eq_of_getElem? hr'.lt_left hr.lt_left ea']
  have eb : ((rmAt s (m + 2))[r₀]'hr₀'.lt_left).2 = (s[r₀]'hr₀.lt_left).2 := by
    rw [getElem_eq_of_getElem? hr₀'.lt_left hr₀.lt_left eb']
  rw [ea] at ih1
  rw [eb, rmAt_rmAt s (by omega) hl] at ih2
  refine (ih1.append_right _).trans (Equiv.trans ?_ (ih2.symm.append_right _))
  have := Equiv.step_mid (Step.uu (s[m + 2]'hr.lt_left).2 (s[r₀]'hr₀.lt_left).2 (g := m)
    (g' := r₀) (by omega)) (canon (rmAt (rmAt s r₀) m)) []
  simpa using this

end CupLast

/-! ## Taking a crossing last -/

section CrossLast

variable {α : Type*}

theorem tau_left (p : ℕ) : tau p p = p + 1 := by simp [tau]

theorem tau_right (p : ℕ) : tau p (p + 1) = p := by simp [tau]

theorem tau_of_ne {p i : ℕ} (h1 : i ≠ p) (h2 : i ≠ p + 1) : tau p i = i := by simp [tau, h1, h2]

theorem swapAt_comm {β : Type*} (s : List β) {p p' : ℕ} (h : p + 2 ≤ p') (hl : p' + 1 < s.length) :
    swapAt (swapAt s p) p' = swapAt (swapAt s p') p := by
  apply List.ext_getElem?; intro i
  rw [getElem?_swapAt _ (by simp; omega), getElem?_swapAt _ (by omega),
    getElem?_swapAt _ (by simp; omega), getElem?_swapAt _ (by omega)]
  congr 1; unfold tau; split_ifs <;> omega

theorem tau_braid (p i : ℕ) : tau p (tau (p + 1) (tau p i)) = tau (p + 1) (tau p (tau (p + 1) i)) := by
  rcases (show i = p ∨ i = p + 1 ∨ i = p + 1 + 1 ∨ (i ≠ p ∧ i ≠ p + 1 ∧ i ≠ p + 1 + 1) by omega) with
    rfl | rfl | rfl | ⟨h1, h2, h3⟩
  · simp (disch := omega) only [tau_left, tau_of_ne]
  · simp (disch := omega) only [tau_left, tau_right, tau_of_ne]
  · simp (disch := omega) only [tau_right, tau_of_ne]
  · simp (disch := omega) only [tau_of_ne]

theorem swapAt_braid {β : Type*} (s : List β) {p : ℕ} (hl : p + 2 < s.length) :
    swapAt (swapAt (swapAt s p) (p + 1)) p = swapAt (swapAt (swapAt s (p + 1)) p) (p + 1) := by
  apply List.ext_getElem?; intro i
  rw [getElem?_swapAt _ (by simp; omega), getElem?_swapAt _ (by simp; omega),
    getElem?_swapAt _ (by omega), getElem?_swapAt _ (by simp; omega),
    getElem?_swapAt _ (by simp; omega), getElem?_swapAt _ (by omega)]
  rw [tau_braid]

theorem rmAt_swapAt {β : Type*} (s : List β) {q q' r : ℕ}
    (h : (q + 2 ≤ r ∧ q' = q) ∨ (r + 2 ≤ q ∧ q' + 2 = q))
    (hq : q + 1 < s.length) (hr : r + 2 ≤ s.length) :
    rmAt (swapAt s q) r = swapAt (rmAt s r) q' := by
  apply List.ext_getElem?; intro i
  rw [getElem?_rmAt _ (by simp; omega), getElem?_swapAt _ hq,
    getElem?_swapAt _ (by rw [length_rmAt _ hr]; omega), getElem?_rmAt _ hr]
  congr 1; unfold tau rmIdx; split_ifs <;> omega

theorem rmAt_swapAt_pitch {β : Type*} (s : List β) {q : ℕ} (hl : q + 2 < s.length) :
    rmAt (swapAt s q) (q + 1) = rmAt (swapAt s (q + 1)) q := by
  apply List.ext_getElem?; intro i
  rw [getElem?_rmAt _ (by simp; omega), getElem?_swapAt _ (by omega),
    getElem?_rmAt _ (by simp; omega), getElem?_swapAt _ (by omega)]
  congr 1; unfold tau rmIdx; split_ifs <;> omega

theorem swapAt_getElem? {β : Type*} (s : List β) {p i : ℕ} (hp : p + 1 < s.length) (h1 : i ≠ p)
    (h2 : i ≠ p + 1) : (swapAt s p)[i]? = s[i]? := by
  rw [getElem?_swapAt s hp, tau_of_ne h1 h2]

/-- A partner in a swapped state. -/
theorem same_swapAt_of {s : List (ℕ × α)} {p x y : ℕ} (hp : p + 1 < s.length)
    (h : Same s (tau p x) y) : Same (swapAt s p) x (tau p y) := by
  rw [same_swapAt hp, tau_tau]; exact h

theorem Valid.eq_of_same {s : List (ℕ × α)} (hv : Valid s) {x y x' y' : ℕ} (h : Same s x y)
    (h' : Same s x' y') (e : x = x') : y = y' := by
  subst e; exact hv.unique h h'

/-- The induction hypothesis of `canon_ilv`. -/
def ExHyp (n : ℕ) : Prop :=
  ∀ t : List (ℕ × α), t.length + cr t < n → Valid t → ∀ q, Ilv t q →
    Equiv (canon t) (canon (swapAt t q) ++ [.cross q])

theorem ExHyp.apply {n : ℕ} (ih : ExHyp (α := α) n) {t : List (ℕ × α)} (hv : Valid t) {q : ℕ}
    (h : Ilv t q) (hn : t.length + cr t < n) :
    Equiv (canon t) (canon (swapAt t q) ++ [.cross q]) := ih t hn hv q h

end CrossLast

section CrossLastCases

variable {α : Type*}

/-- `canon_ilv`, the case of a pairing with an adjacent arc. -/
theorem ex_adj {t : List (ℕ × α)} (hv : Valid t) {q r : ℕ} (h : Ilv t q)
    (hr : Same t r (r + 1)) (ih : ExHyp (α := α) (t.length + cr t)) :
    Equiv (canon t) (canon (swapAt t q) ++ [.cross q]) := by
  have hq := h.lt
  obtain ⟨a, ha⟩ := hv.exists (show q < t.length by omega)
  obtain ⟨b, hb⟩ := hv.exists hq
  have hilv := (ilv_iff hv ha hb).1 h
  have hl2 : r + 2 ≤ t.length := hr.lt_right
  have u1 : q = r → a = r + 1 := fun e => hv.eq_of_same ha hr e
  have u2 : q = r + 1 → a = r := fun e => hv.eq_of_same ha hr.symm e
  have u3 : q + 1 = r → b = r + 1 := fun e => hv.eq_of_same hb hr e
  have u4 : q + 1 = r + 1 → b = r := fun e => hv.eq_of_same hb hr.symm e
  have u5 : a = r → q = r + 1 := fun e => hv.eq_of_same ha.symm hr e
  have u6 : a = r + 1 → q = r := fun e => hv.eq_of_same ha.symm hr.symm e
  have u7 : b = r → q + 1 = r + 1 := fun e => hv.eq_of_same hb.symm hr e
  have u8 : b = r + 1 → q + 1 = r := fun e => hv.eq_of_same hb.symm hr.symm e
  have hqa := ha.ne
  have hqb := hb.ne
  obtain ⟨q', hq'⟩ : ∃ q', (q + 2 ≤ r ∧ q' = q) ∨ (r + 2 ≤ q ∧ q' + 2 = q) := by
    by_cases hc : q + 2 ≤ r
    · exact ⟨q, Or.inl ⟨hc, rfl⟩⟩
    · exact ⟨q - 2, Or.inr ⟨by omega, by omega⟩⟩
  have ht0 := hv.rmAt hr
  have ra : rmIdx r (if a < r then a else a - 2) = a := by unfold rmIdx; split_ifs <;> omega
  have rb : rmIdx r (if b < r then b else b - 2) = b := by unfold rmIdx; split_ifs <;> omega
  have rq : rmIdx r q' = q := by unfold rmIdx; split_ifs <;> omega
  have rq1 : rmIdx r (q' + 1) = q + 1 := by unfold rmIdx; split_ifs <;> omega
  have ha0 : Same (rmAt t r) q' (if a < r then a else a - 2) := by
    rw [same_rmAt hl2, ra, rq]; exact ha
  have hb0 : Same (rmAt t r) (q' + 1) (if b < r then b else b - 2) := by
    rw [same_rmAt hl2, rb, rq1]; exact hb
  have hilv0 : Ilv (rmAt t r) q' := by
    rw [ilv_iff ht0 ha0 hb0]; split_ifs <;> omega
  have e1 := ih.apply ht0 hilv0 (by
    rw [length_rmAt t hl2]; have := cr_rmAt_le (s := t) hl2; omega)
  have c1 := canon_cup hv hr
  have hr' : Same (swapAt t q) r (r + 1) := by
    rw [same_swapAt hq, tau_of_ne (by omega) (by omega), tau_of_ne (by omega) (by omega)]
    exact hr
  have c2 := canon_cup (hv.swapAt hq) hr'
  rw [rmAt_swapAt t hq' hq hl2] at c2
  have ex : ((swapAt t q)[r]'hr'.lt_left).2 = (t[r]'hr.lt_left).2 := by
    rw [getElem_eq_of_getElem? hr'.lt_left hr.lt_left
      (swapAt_getElem? t hq (by omega) (by omega))]
  rw [ex] at c2
  refine c1.trans ((e1.append_right _).trans (Equiv.trans ?_ (c2.symm.append_right _)))
  rcases hq' with ⟨hc, rfl⟩ | ⟨hc, rfl⟩
  · simpa using Equiv.step_mid (Step.xuL (t[r]'hr.lt_left).2 hc) (canon (swapAt (rmAt t r) q')) []
  · simpa using Equiv.step_mid (Step.xuR (t[r]'hr.lt_left).2 (show r ≤ q' by omega))
      (canon (swapAt (rmAt t r) q')) []

theorem tau_cases (p i : ℕ) : (i = p ∧ tau p i = p + 1) ∨ (i = p + 1 ∧ tau p i = p) ∨
    (i ≠ p ∧ i ≠ p + 1 ∧ tau p i = i) := by
  unfold tau; split_ifs <;> omega

/-- Exchanging two adjacent endpoints away from `q, q + 1` does not change whether the arcs at
`q, q + 1` interleave, unless these are the two arcs exchanged. -/
theorem ilv_swapAt_of_ne {t : List (ℕ × α)} (hv : Valid t) {p q a b : ℕ}
    (hp : p + 1 < t.length) (far : q + 2 ≤ p ∨ p + 2 ≤ q) (ha : Same t q a)
    (hb : Same t (q + 1) b) (hpair : ¬ (a = p ∧ b = p + 1) ∧ ¬ (a = p + 1 ∧ b = p)) :
    Ilv (swapAt t p) q ↔ Ilv t q := by
  have ha' : Same (swapAt t p) q (tau p a) :=
    same_swapAt_of hp (by rw [tau_of_ne (by omega) (by omega)]; exact ha)
  have hb' : Same (swapAt t p) (q + 1) (tau p b) :=
    same_swapAt_of hp (by rw [tau_of_ne (by omega) (by omega)]; exact hb)
  have hab : a ≠ b := fun e => by subst e; have := hv.unique ha.symm hb.symm; omega
  have := ha.ne; have := hb.ne
  rw [ilv_iff (hv.swapAt hp) ha' hb', ilv_iff hv ha hb]
  rcases tau_cases p a with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h1', h2⟩ <;>
    rcases tau_cases p b with ⟨h4, h5⟩ | ⟨h4, h5⟩ | ⟨h4, h4', h5⟩ <;>
    rw [h2, h5] <;> constructor <;> intro <;> omega

/-- `canon_ilv`, the case of crossings at distant positions. -/
theorem ex_far {t : List (ℕ × α)} (hv : Valid t) {q q₀ : ℕ} (h : Ilv t q)
    (hno : ∀ r, ¬ Same t r (r + 1)) (ho : Opn t q₀) (hc : Cls t (q₀ + 1))
    (hcanon : canon t = canon (swapAt t q₀) ++ [.cross q₀])
    (far : q + 2 ≤ q₀ ∨ q₀ + 2 ≤ q) (ih : ExHyp (α := α) (t.length + cr t)) :
    Equiv (canon t) (canon (swapAt t q) ++ [.cross q]) := by
  have hq := h.lt
  obtain ⟨a₀, hqa₀, ha₀⟩ := ho
  obtain ⟨b₀, hb₀q, hb₀⟩ := hc
  have hq₀ : q₀ + 1 < t.length := hb₀.lt_left
  have n1 : a₀ ≠ q₀ + 1 := fun e => hno q₀ (e ▸ ha₀)
  have n2 : b₀ ≠ q₀ := fun e => hno q₀ (e ▸ hb₀).symm
  have hilv₀ : Ilv t q₀ := by rw [ilv_iff hv ha₀ hb₀]; omega
  obtain ⟨a, ha⟩ := hv.exists (show q < t.length by omega)
  obtain ⟨b, hb⟩ := hv.exists hq
  have u1 : a = q₀ → q = a₀ := fun e => hv.eq_of_same ha.symm ha₀ e
  have u2 : a = q₀ + 1 → q = b₀ := fun e => hv.eq_of_same ha.symm hb₀ e
  have u3 : b = q₀ → q + 1 = a₀ := fun e => hv.eq_of_same hb.symm ha₀ e
  have u4 : b = q₀ + 1 → q + 1 = b₀ := fun e => hv.eq_of_same hb.symm hb₀ e
  have u5 : a₀ = q → q₀ = a := fun e => hv.eq_of_same ha₀.symm ha e
  have u6 : a₀ = q + 1 → q₀ = b := fun e => hv.eq_of_same ha₀.symm hb e
  have u7 : b₀ = q → q₀ + 1 = a := fun e => hv.eq_of_same hb₀.symm ha e
  have u8 : b₀ = q + 1 → q₀ + 1 = b := fun e => hv.eq_of_same hb₀.symm hb e
  have hilv1 : Ilv (swapAt t q₀) q :=
    (ilv_swapAt_of_ne hv hq₀ far ha hb ⟨by omega, by omega⟩).2 h
  have e1 := ih.apply (hv.swapAt hq₀) hilv1
    (by rw [length_swapAt]; have := cr_swapAt_lt hv hilv₀; omega)
  have hilv2 : Ilv (swapAt t q) q₀ :=
    (ilv_swapAt_of_ne hv hq (by omega) ha₀ hb₀ ⟨by omega, by omega⟩).2 hilv₀
  have e2 := ih.apply (hv.swapAt hq) hilv2
    (by rw [length_swapAt]; have := cr_swapAt_lt hv h; omega)
  have ecomm : swapAt (swapAt t q₀) q = swapAt (swapAt t q) q₀ := by
    rcases far with hf | hf
    · exact (swapAt_comm t hf hq₀).symm
    · exact swapAt_comm t hf hq
  rw [ecomm] at e1
  rw [hcanon]
  refine (e1.append_right _).trans (Equiv.trans ?_ (e2.symm.append_right _))
  rcases far with hf | hf
  · simpa using Equiv.step_mid (Step.xx (α := α) hf) (canon (swapAt (swapAt t q) q₀)) []
  · simpa using (Equiv.step_mid (Step.xx (α := α) hf) (canon (swapAt (swapAt t q) q₀)) []).symm

/-- `canon_ilv`, the case `q = q₀ + 1`. Either the arc at `q₀` ends at `q₀ + 2` (a pitchfork
move) or the three arcs at `q₀, q₀ + 1, q₀ + 2` pairwise interleave (a braid move). -/
theorem ex_right {t : List (ℕ × α)} (hv : Valid t) {q₀ : ℕ} (h : Ilv t (q₀ + 1))
    (hno : ∀ r, ¬ Same t r (r + 1)) (ho : Opn t q₀) (hc : Cls t (q₀ + 1))
    (hcanon : canon t = canon (swapAt t q₀) ++ [.cross q₀])
    (ih : ExHyp (α := α) (t.length + cr t)) :
    Equiv (canon t) (canon (swapAt t (q₀ + 1)) ++ [.cross (q₀ + 1)]) := by
  have hq := h.lt
  obtain ⟨a₀, hqa₀, ha₀⟩ := ho
  obtain ⟨b₀, hb₀q, hb₀⟩ := hc
  have hq₀ : q₀ + 1 < t.length := hb₀.lt_left
  have n1 : a₀ ≠ q₀ + 1 := fun e => hno q₀ (e ▸ ha₀)
  have n2 : b₀ ≠ q₀ := fun e => hno q₀ (e ▸ hb₀).symm
  have hilv₀ : Ilv t q₀ := by rw [ilv_iff hv ha₀ hb₀]; omega
  obtain ⟨c, hc⟩ := hv.exists hq
  have hcb := (ilv_iff hv hb₀ hc).1 h
  have hc1 : c ≠ q₀ + 1 := by omega
  have u1 : c = q₀ → a₀ = q₀ + 1 + 1 := fun e => hv.eq_of_same ha₀ hc.symm e.symm
  have u2 : a₀ = q₀ + 1 + 1 → c = q₀ := fun e => hv.eq_of_same hc ha₀.symm e.symm
  rw [hcanon]
  rcases (show c = q₀ ∨ c < q₀ by omega) with hcq | hcq
  · -- the pitchfork configuration
    have ea := u1 hcq
    subst ea
    have hs1 : Same (swapAt t q₀) (q₀ + 1) (q₀ + 1 + 1) := by
      have := same_swapAt_of (x := q₀ + 1) hq₀ (by rw [tau_right]; exact ha₀)
      rwa [tau_of_ne (by omega) (by omega)] at this
    have hs2 : Same (swapAt t (q₀ + 1)) q₀ (q₀ + 1) := by
      have := same_swapAt_of (x := q₀) hq (by rw [tau_of_ne (by omega) (by omega)]; exact ha₀)
      rwa [tau_right] at this
    have c1 := canon_cup (hv.swapAt hq₀) hs1
    have c2 := canon_cup (hv.swapAt hq) hs2
    have x1 : ((swapAt t q₀)[q₀ + 1]'hs1.lt_left).2 = (t[q₀]'(by omega)).2 := by
      rw [getElem_eq_of_getElem? (l := swapAt t q₀) (l' := t) (i := q₀ + 1) (j := q₀) hs1.lt_left (by omega)
        (by rw [getElem?_swapAt t hq₀, tau_right])]
    have x2 : ((swapAt t (q₀ + 1))[q₀]'hs2.lt_left).2 = (t[q₀]'(by omega)).2 := by
      rw [getElem_eq_of_getElem? (l := swapAt t (q₀ + 1)) (l' := t) (i := q₀) (j := q₀) hs2.lt_left (by omega)
        (by rw [getElem?_swapAt t hq, tau_of_ne (by omega) (by omega)])]
    rw [x1, rmAt_swapAt_pitch t hq] at c1
    rw [x2] at c2
    refine (c1.append_right _).trans (Equiv.trans ?_ (c2.symm.append_right _))
    have := (Equiv.step_mid (Step.pitch q₀ (t[q₀]'(by omega)).2)
      (canon (rmAt (swapAt t (q₀ + 1)) q₀)) []).symm
    simpa using this
  · -- the triangle configuration
    have ha₀' : q₀ + 1 + 1 < a₀ := by
      rcases (show a₀ = q₀ + 1 + 1 ∨ q₀ + 1 + 1 < a₀ by omega) with e | e
      · have := u2 e; omega
      · exact e
    set t₁ := swapAt t q₀ with ht₁
    set t₂ := swapAt t₁ (q₀ + 1) with ht₂
    set u := swapAt t (q₀ + 1) with hu
    set u₁ := swapAt u q₀ with hu₁
    have hv₁ : Valid t₁ := hv.swapAt hq₀
    have hq₁ : q₀ + 1 + 1 < t₁.length := by rw [ht₁, length_swapAt]; exact hq
    have hv₂ : Valid t₂ := hv₁.swapAt hq₁
    have hvu : Valid u := hv.swapAt hq
    have hqu : q₀ + 1 < u.length := by rw [hu, length_swapAt]; omega
    have hvu₁ : Valid u₁ := hvu.swapAt hqu
    -- partners in `t₁`
    have p1 : Same t₁ (q₀ + 1) a₀ := by
      have := same_swapAt_of (x := q₀ + 1) hq₀ (by rw [tau_right]; exact ha₀)
      rwa [tau_of_ne (by omega) (by omega)] at this
    have p2 : Same t₁ (q₀ + 1 + 1) c := by
      have := same_swapAt_of (x := q₀ + 1 + 1) hq₀
        (by rw [tau_of_ne (by omega) (by omega)]; exact hc)
      rwa [tau_of_ne (by omega) (by omega)] at this
    have p3 : Same t₁ q₀ b₀ := by
      have := same_swapAt_of (x := q₀) hq₀ (by rw [tau_left]; exact hb₀)
      rwa [tau_of_ne (by omega) (by omega)] at this
    have i1 : Ilv t₁ (q₀ + 1) := by rw [ilv_iff hv₁ p1 p2]; omega
    -- partners in `t₂`
    have p4 : Same t₂ q₀ b₀ := by
      have := same_swapAt_of (x := q₀) hq₁ (by rw [tau_of_ne (by omega) (by omega)]; exact p3)
      rwa [tau_of_ne (by omega) (by omega)] at this
    have p5 : Same t₂ (q₀ + 1) c := by
      have := same_swapAt_of (x := q₀ + 1) hq₁ (by rw [tau_left]; exact p2)
      rwa [tau_of_ne (by omega) (by omega)] at this
    have i2 : Ilv t₂ q₀ := by rw [ilv_iff hv₂ p4 p5]; omega
    -- partners in `u`
    have p6 : Same u q₀ a₀ := by
      have := same_swapAt_of (x := q₀) hq (by rw [tau_of_ne (by omega) (by omega)]; exact ha₀)
      rwa [tau_of_ne (by omega) (by omega)] at this
    have p7 : Same u (q₀ + 1) c := by
      have := same_swapAt_of (x := q₀ + 1) hq (by rw [tau_left]; exact hc)
      rwa [tau_of_ne (by omega) (by omega)] at this
    have p8 : Same u (q₀ + 1 + 1) b₀ := by
      have := same_swapAt_of (x := q₀ + 1 + 1) hq (by rw [tau_right]; exact hb₀)
      rwa [tau_of_ne (by omega) (by omega)] at this
    have i3 : Ilv u q₀ := by rw [ilv_iff hvu p6 p7]; omega
    -- partners in `u₁`
    have p9 : Same u₁ (q₀ + 1) a₀ := by
      have := same_swapAt_of (x := q₀ + 1) hqu (by rw [tau_right]; exact p6)
      rwa [tau_of_ne (by omega) (by omega)] at this
    have p10 : Same u₁ (q₀ + 1 + 1) b₀ := by
      have := same_swapAt_of (x := q₀ + 1 + 1) hqu
        (by rw [tau_of_ne (by omega) (by omega)]; exact p8)
      rwa [tau_of_ne (by omega) (by omega)] at this
    have i4 : Ilv u₁ (q₀ + 1) := by rw [ilv_iff hvu₁ p9 p10]; omega
    have m1 : cr t₁ < cr t := cr_swapAt_lt hv hilv₀
    have m2 : cr t₂ < cr t₁ := cr_swapAt_lt hv₁ i1
    have m3 : cr u < cr t := cr_swapAt_lt hv h
    have m4 : cr u₁ < cr u := cr_swapAt_lt hvu i3
    have l1 : t₁.length = t.length := by simp [ht₁]
    have e1 := ih.apply hv₁ i1 (by omega)
    have l2 : t₂.length = t.length := by simp [ht₂, ht₁]
    have e2 := ih.apply hv₂ i2 (by omega)
    have l3 : u.length = t.length := by simp [hu]
    have e3 := ih.apply hvu i3 (by omega)
    have l4 : u₁.length = t.length := by simp [hu₁, hu]
    have e4 := ih.apply hvu₁ i4 (by omega)
    have eb : swapAt t₂ q₀ = swapAt u₁ (q₀ + 1) := swapAt_braid t (by omega)
    rw [eb] at e2
    have s1 := e1.append_right [Move.cross q₀]
    have s2 := e2.append_right [Move.cross (q₀ + 1), Move.cross q₀]
    have s3 := Equiv.step_mid (Step.braid (α := α) q₀) (canon (swapAt u₁ (q₀ + 1))) []
    have s4 := e4.symm.append_right [Move.cross q₀, Move.cross (q₀ + 1)]
    have s5 := e3.symm.append_right [Move.cross (q₀ + 1)]
    simp only [List.append_assoc, List.cons_append, List.nil_append,
      List.append_nil] at s1 s2 s3 s4 s5 ⊢
    exact s1.trans (s2.trans (s3.trans (s4.trans s5)))

/-- `canon_ilv`, the case `q + 1 = q₀`: a pitchfork move or a braid move, mirror to
`ex_right`. -/
theorem ex_left {t : List (ℕ × α)} (hv : Valid t) {P : ℕ} (h : Ilv t P)
    (hno : ∀ r, ¬ Same t r (r + 1)) (ho : Opn t (P + 1)) (hc : Cls t (P + 1 + 1))
    (hcanon : canon t = canon (swapAt t (P + 1)) ++ [.cross (P + 1)])
    (ih : ExHyp (α := α) (t.length + cr t)) :
    Equiv (canon t) (canon (swapAt t P) ++ [.cross P]) := by
  have hP := h.lt
  obtain ⟨a₀, hqa₀, ha₀⟩ := ho
  obtain ⟨b₀, hb₀q, hb₀⟩ := hc
  have hq₀ : P + 1 + 1 < t.length := hb₀.lt_left
  have n1 : a₀ ≠ P + 1 + 1 := fun e => hno (P + 1) (e ▸ ha₀)
  have n2 : b₀ ≠ P + 1 := fun e => hno (P + 1) (e ▸ hb₀).symm
  have hilv₀ : Ilv t (P + 1) := by rw [ilv_iff hv ha₀ hb₀]; omega
  obtain ⟨d, hd⟩ := hv.exists (show P < t.length by omega)
  have hda := (ilv_iff hv hd ha₀).1 h
  have u1 : d = P + 1 + 1 → b₀ = P := fun e => hv.eq_of_same hb₀ hd.symm e.symm
  have u2 : b₀ = P → d = P + 1 + 1 := fun e => hv.eq_of_same hd hb₀.symm e.symm
  rw [hcanon]
  rcases (show d = P + 1 + 1 ∨ P + 1 + 1 < d by omega) with hdq | hdq
  · -- the pitchfork configuration
    have eb := u1 hdq
    subst hdq; subst b₀
    have hs1 : Same (swapAt t (P + 1)) P (P + 1) := by
      have := same_swapAt_of (x := P) hq₀ (by rw [tau_of_ne (by omega) (by omega)]; exact hd)
      rwa [tau_right] at this
    have hs2 : Same (swapAt t P) (P + 1) (P + 1 + 1) := by
      have := same_swapAt_of (x := P + 1) hP (by rw [tau_right]; exact hd)
      rwa [tau_of_ne (by omega) (by omega)] at this
    have c1 := canon_cup (hv.swapAt hq₀) hs1
    have c2 := canon_cup (hv.swapAt hP) hs2
    have x1 : ((swapAt t (P + 1))[P]'hs1.lt_left).2 = (t[P]'(by omega)).2 := by
      rw [getElem_eq_of_getElem? (l := swapAt t (P + 1)) (l' := t) (i := P) (j := P) hs1.lt_left
        (by omega) (by rw [getElem?_swapAt t hq₀, tau_of_ne (by omega) (by omega)])]
    have x2 : ((swapAt t P)[P + 1]'hs2.lt_left).2 = (t[P]'(by omega)).2 := by
      rw [getElem_eq_of_getElem? (l := swapAt t P) (l' := t) (i := P + 1) (j := P) hs2.lt_left
        (by omega) (by rw [getElem?_swapAt t hP, tau_right])]
    rw [x1] at c1
    rw [x2, rmAt_swapAt_pitch t hq₀] at c2
    refine (c1.append_right _).trans (Equiv.trans ?_ (c2.symm.append_right _))
    have := Equiv.step_mid (Step.pitch P (t[P]'(by omega)).2) (canon (rmAt (swapAt t (P + 1)) P)) []
    simpa using this
  · -- the triangle configuration
    have hb₀' : b₀ < P := by
      rcases (show b₀ = P ∨ b₀ < P by omega) with e | e
      · have := u2 e; omega
      · exact e
    set t₁ := swapAt t (P + 1) with ht₁
    set t₂ := swapAt t₁ P with ht₂
    set u := swapAt t P with hu
    set u₁ := swapAt u (P + 1) with hu₁
    have hv₁ : Valid t₁ := hv.swapAt hq₀
    have hq₁ : P + 1 < t₁.length := by rw [ht₁, length_swapAt]; exact hP
    have hv₂ : Valid t₂ := hv₁.swapAt hq₁
    have hvu : Valid u := hv.swapAt hP
    have hqu : P + 1 + 1 < u.length := by rw [hu, length_swapAt]; omega
    have hvu₁ : Valid u₁ := hvu.swapAt hqu
    -- partners in `t₁`
    have p1 : Same t₁ P d := by
      have := same_swapAt_of (x := P) hq₀ (by rw [tau_of_ne (by omega) (by omega)]; exact hd)
      rwa [tau_of_ne (by omega) (by omega)] at this
    have p2 : Same t₁ (P + 1) b₀ := by
      have := same_swapAt_of (x := P + 1) hq₀ (by rw [tau_left]; exact hb₀)
      rwa [tau_of_ne (by omega) (by omega)] at this
    have p3 : Same t₁ (P + 1 + 1) a₀ := by
      have := same_swapAt_of (x := P + 1 + 1) hq₀ (by rw [tau_right]; exact ha₀)
      rwa [tau_of_ne (by omega) (by omega)] at this
    have i1 : Ilv t₁ P := by rw [ilv_iff hv₁ p1 p2]; omega
    -- partners in `t₂`
    have p4 : Same t₂ (P + 1) d := by
      have := same_swapAt_of (x := P + 1) hq₁ (by rw [tau_right]; exact p1)
      rwa [tau_of_ne (by omega) (by omega)] at this
    have p5 : Same t₂ (P + 1 + 1) a₀ := by
      have := same_swapAt_of (x := P + 1 + 1) hq₁
        (by rw [tau_of_ne (by omega) (by omega)]; exact p3)
      rwa [tau_of_ne (by omega) (by omega)] at this
    have i2 : Ilv t₂ (P + 1) := by rw [ilv_iff hv₂ p4 p5]; omega
    -- partners in `u`
    have p6 : Same u (P + 1) d := by
      have := same_swapAt_of (x := P + 1) hP (by rw [tau_right]; exact hd)
      rwa [tau_of_ne (by omega) (by omega)] at this
    have p7 : Same u (P + 1 + 1) b₀ := by
      have := same_swapAt_of (x := P + 1 + 1) hP (by rw [tau_of_ne (by omega) (by omega)]; exact hb₀)
      rwa [tau_of_ne (by omega) (by omega)] at this
    have p8 : Same u P a₀ := by
      have := same_swapAt_of (x := P) hP (by rw [tau_left]; exact ha₀)
      rwa [tau_of_ne (by omega) (by omega)] at this
    have i3 : Ilv u (P + 1) := by rw [ilv_iff hvu p6 p7]; omega
    -- partners in `u₁`
    have p9 : Same u₁ P a₀ := by
      have := same_swapAt_of (x := P) hqu (by rw [tau_of_ne (by omega) (by omega)]; exact p8)
      rwa [tau_of_ne (by omega) (by omega)] at this
    have p10 : Same u₁ (P + 1) b₀ := by
      have := same_swapAt_of (x := P + 1) hqu (by rw [tau_left]; exact p7)
      rwa [tau_of_ne (by omega) (by omega)] at this
    have i4 : Ilv u₁ P := by rw [ilv_iff hvu₁ p9 p10]; omega
    have m1 : cr t₁ < cr t := cr_swapAt_lt hv hilv₀
    have m2 : cr t₂ < cr t₁ := cr_swapAt_lt hv₁ i1
    have m3 : cr u < cr t := cr_swapAt_lt hv h
    have m4 : cr u₁ < cr u := cr_swapAt_lt hvu i3
    have l1 : t₁.length = t.length := by simp [ht₁]
    have l2 : t₂.length = t.length := by simp [ht₂, ht₁]
    have l3 : u.length = t.length := by simp [hu]
    have l4 : u₁.length = t.length := by simp [hu₁, hu]
    have e1 := ih.apply hv₁ i1 (by omega)
    have e2 := ih.apply hv₂ i2 (by omega)
    have e3 := ih.apply hvu i3 (by omega)
    have e4 := ih.apply hvu₁ i4 (by omega)
    have eb : swapAt u₁ P = swapAt t₂ (P + 1) := swapAt_braid t (by omega)
    rw [← eb] at e2
    have s1 := e1.append_right [Move.cross (P + 1)]
    have s2 := e2.append_right [Move.cross P, Move.cross (P + 1)]
    have s3 := (Equiv.step_mid (Step.braid (α := α) P) (canon (swapAt u₁ P)) []).symm
    have s4 := e4.symm.append_right [Move.cross (P + 1), Move.cross P]
    have s5 := e3.symm.append_right [Move.cross P]
    simp only [List.append_assoc, List.cons_append, List.nil_append,
      List.append_nil] at s1 s2 s3 s4 s5 ⊢
    exact s1.trans (s2.trans (s3.trans (s4.trans s5)))

/-- **Ex.** In a pairing, if the arcs at `q` and `q + 1` interleave, the crossing at `q` can be
taken as the last move of the canonical diagram. -/
theorem canon_ilv {t : List (ℕ × α)} (hv : Valid t) {q : ℕ} (h : Ilv t q) :
    Equiv (canon t) (canon (swapAt t q) ++ [.cross q]) := by
  suffices H : ∀ n, ExHyp (α := α) n from H _ t (Nat.lt_succ_self _) hv q h
  intro n
  induction n with
  | zero => intro t ht; omega
  | succ n ih =>
    intro t ht hv q h
    have ih' : ExHyp (α := α) (t.length + cr t) := fun t' ht' => ih t' (by omega)
    by_cases hadj : ∃ r, Same t r (r + 1)
    · obtain ⟨r, hr⟩ := hadj
      exact ex_adj hv h hr ih'
    · have hno : ∀ r, ¬ Same t r (r + 1) := fun r hr => hadj ⟨r, hr⟩
      have hne : t ≠ [] := by
        rintro rfl; have := h.lt; simp at this
      obtain ⟨q₀, ho, hc, hcanon, -⟩ := canon_cross hv hno hne
      rcases (show q = q₀ ∨ q = q₀ + 1 ∨ q + 1 = q₀ ∨ q + 2 ≤ q₀ ∨ q₀ + 2 ≤ q by omega) with
        e | e | e | e | e
      · subst e; rw [hcanon]
      · subst e; exact ex_right hv h hno ho hc hcanon ih'
      · subst e; exact ex_left hv h hno ho hc hcanon ih'
      · exact ex_far hv h hno ho hc hcanon (Or.inl e) ih'
      · exact ex_far hv h hno ho hc hcanon (Or.inr e) ih'

end CrossLastCases

/-! ## Diagrams and the normal form theorem -/

section Run

variable {α : Type*} (d : α → α)

/-- Whether a move can be applied to a state with `n` strands. -/
def Move.Ok (n : ℕ) : Move α → Prop
  | .cup g _ => g ≤ n
  | .cross p => p + 1 < n

/-- The number of strands after a move. -/
def Move.len (n : ℕ) : Move α → ℕ
  | .cup _ _ => n + 2
  | .cross _ => n

/-- A diagram fits on `n` strands: every move can be applied. -/
def Fits : ℕ → List (Move α) → Prop
  | _, [] => True
  | n, m :: D => m.Ok n ∧ Fits (m.len n) D

/-- The effect of a move on a state; a cup gets the fresh id `s.length`. -/
def step (s : List (ℕ × α)) : Move α → List (ℕ × α)
  | .cup g a => insAt s g (s.length, a) (s.length, d a)
  | .cross p => swapAt s p

/-- The final state of a diagram (read from the bottom). -/
def run (D : List (Move α)) : List (ℕ × α) := D.foldl (step d) []

variable {d}

theorem length_step (s : List (ℕ × α)) (m : Move α) : (step d s m).length = m.len s.length := by
  cases m with
  | cup g a => simp [step, Move.len, insAt]; omega
  | cross p => simp [step, Move.len]

theorem fits_append : ∀ (n : ℕ) (D E : List (Move α)),
    Fits n (D ++ E) ↔ Fits n D ∧ Fits (D.foldl Move.len n) E
  | n, [], E => by simp [Fits]
  | n, m :: D, E => by
    simp only [List.cons_append, Fits, List.foldl_cons, fits_append _ D E, and_assoc]

theorem length_foldl_step : ∀ (s : List (ℕ × α)) (D : List (Move α)),
    (D.foldl (step d) s).length = D.foldl Move.len s.length
  | s, [] => rfl
  | s, m :: D => by
    simp only [List.foldl_cons, length_foldl_step _ D, length_step]

theorem run_append (D E : List (Move α)) : run d (D ++ E) = E.foldl (step d) (run d D) := by
  simp [run, List.foldl_append]

theorem fits_snoc {D : List (Move α)} {m : Move α} :
    Fits 0 (D ++ [m]) ↔ Fits 0 D ∧ m.Ok (run d D).length := by
  rw [fits_append]
  simp only [Fits, and_true]
  rw [show D.foldl Move.len 0 = (run d D).length by rw [run, length_foldl_step]; rfl]

theorem mem_swapAt {β : Type*} {s : List β} {p : ℕ} {x : β} (h : x ∈ swapAt s p) : x ∈ s := by
  by_cases hp : p + 1 < s.length
  · rw [List.mem_iff_getElem?] at h ⊢
    obtain ⟨i, hi⟩ := h
    exact ⟨tau p i, by rwa [getElem?_swapAt s hp] at hi⟩
  · rwa [swapAt_of_le s hp] at h

/-- The invariant of states reached by diagrams: a pairing with ids below the length. -/
def Inv (s : List (ℕ × α)) : Prop := Valid s ∧ ∀ x ∈ s, x.1 < s.length

theorem Inv.step {s : List (ℕ × α)} (hs : Inv s) {m : Move α} (hm : m.Ok s.length) :
    Inv (step d s m) := by
  cases m with
  | cup g a =>
    simp only [Move.Ok] at hm
    refine ⟨hs.1.insAt hm (fun x hx => (hs.2 x hx).ne) _ _, fun x hx => ?_⟩
    rw [length_step]; show x.1 < s.length + 2
    simp only [Chord.step, insAt, List.mem_append, List.mem_cons] at hx
    rcases hx with hx | rfl | rfl | hx
    · have := hs.2 x (List.mem_of_mem_take hx); omega
    · simp
    · simp
    · have := hs.2 x (List.mem_of_mem_drop hx); omega
  | cross p =>
    simp only [Move.Ok] at hm
    refine ⟨hs.1.swapAt hm, fun x hx => ?_⟩
    rw [length_step]; show x.1 < s.length
    have hx' : x ∈ swapAt s p := hx
    exact hs.2 x (mem_swapAt hx')

theorem inv_run : ∀ {D : List (Move α)}, Fits 0 D → Inv (run d D) := by
  intro D
  induction D using List.reverseRecOn with
  | nil => intro _; exact ⟨fun i hi => by simp [run] at hi, by simp [run]⟩
  | append_singleton D m ih =>
    intro h
    rw [fits_snoc (d := d)] at h
    rw [run_append]
    exact (ih h.1).step h.2

/-- **The normal form theorem.** Every diagram of cups and crossings is either reducible
(equivalent to a diagram containing a double crossing or a curl) or equivalent to the canonical
diagram of its final pairing. -/
theorem equiv_canon_or_reducible : ∀ {D : List (Move α)}, Fits 0 D →
    Reducible D ∨ Equiv D (canon (run d D)) := by
  intro D
  induction D using List.reverseRecOn with
  | nil => intro _; right; rw [run, List.foldl_nil, canon_nil]
  | append_singleton D m ih =>
    intro h
    have hi := inv_run (d := d) ((fits_snoc (d := d)).1 h).1
    have hm := ((fits_snoc (d := d)).1 h).2
    rcases ih ((fits_snoc (d := d)).1 h).1 with hr | he
    · exact Or.inl (hr.append _)
    have he' := he.append_right [m]
    rw [run_append, List.foldl_cons, List.foldl_nil]
    set s := run d D
    cases m with
    | cup g a =>
      simp only [Move.Ok] at hm
      right
      have hk : ∀ x ∈ s, x.1 ≠ s.length := fun x hx => (hi.2 x hx).ne
      have hs : Same (step d s (.cup g a)) g (g + 1) :=
        (same_insAt_iff hm hk a (d a)).2 (Or.inl ⟨rfl, rfl⟩)
      have c := canon_cup ((hi.step (d := d) (m := .cup g a) hm).1) hs
      have e1 : rmAt (step d s (.cup g a)) g = s := rmAt_insAt s g _ _ hm
      have e2 : ((step d s (.cup g a))[g]'hs.lt_left).2 = a := by
        have : (step d s (.cup g a))[g]? = some (s.length, a) := by
          rw [step, getElem?_insAt s hm]; simp
        rw [List.getElem?_eq_getElem hs.lt_left] at this
        rw [Option.some.inj this]
      rw [e1, e2] at c
      exact he'.trans c.symm
    | cross p =>
      simp only [Move.Ok] at hm
      by_cases hsame : Same s p (p + 1)
      · left
        have c := canon_cup hi.1 hsame
        exact ⟨canon (rmAt s p), [], p, Or.inr ⟨_, by simpa using he'.trans (c.append_right _)⟩⟩
      by_cases hilv : Ilv s p
      · left
        have c := canon_ilv hi.1 hilv
        exact ⟨canon (swapAt s p), [], p, Or.inl (by simpa using he'.trans (c.append_right _))⟩
      · right
        have hilv' : Ilv (swapAt s p) p := (ilv_swapAt_iff hi.1 hm hsame).2 hilv
        have c := canon_ilv (hi.1.swapAt hm) hilv'
        rw [swapAt_swapAt] at c
        exact he'.trans c.symm

end Run

/-! ## Relabelling ids, letters, and the canonical diagram realises its pairing -/

section Iso

variable {α : Type*}

/-- Two states with the same letters and the same pairing (they differ by a relabelling of the
arc ids). -/
def Iso (s s' : List (ℕ × α)) : Prop :=
  s.map Prod.snd = s'.map Prod.snd ∧ ∀ i j, Same s i j ↔ Same s' i j

theorem Iso.length_eq {s s' : List (ℕ × α)} (h : Iso s s') : s.length = s'.length := by
  simpa using congrArg List.length h.1

theorem Iso.symm {s s' : List (ℕ × α)} (h : Iso s s') : Iso s' s :=
  ⟨h.1.symm, fun i j => (h.2 i j).symm⟩

theorem Iso.valid {s s' : List (ℕ × α)} (h : Iso s s') (hv : Valid s) : Valid s' := by
  intro i hi
  obtain ⟨j, hj, hu⟩ := hv i (by rw [h.length_eq]; exact hi)
  exact ⟨j, (h.2 i j).1 hj, fun k hk => hu k ((h.2 i k).2 hk)⟩

theorem Iso.snd_getElem {s s' : List (ℕ × α)} (h : Iso s s') {i : ℕ} (hi : i < s.length)
    (hi' : i < s'.length) : (s[i]).2 = (s'[i]).2 := by
  have := congrArg (fun l => l[i]?) h.1
  simp only [List.getElem?_map, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi'] at this
  simpa using this

theorem Iso.swapAt {s s' : List (ℕ × α)} (h : Iso s s') (p : ℕ) :
    Iso (Chord.swapAt s p) (Chord.swapAt s' p) := by
  by_cases hp : p + 1 < s.length
  · have hp' : p + 1 < s'.length := h.length_eq ▸ hp
    refine ⟨?_, fun i j => by rw [same_swapAt hp, same_swapAt hp', h.2]⟩
    apply List.ext_getElem?; intro i
    have := congrArg (fun l => l[tau p i]?) h.1
    simp only [List.getElem?_map] at this ⊢
    rw [getElem?_swapAt s hp, getElem?_swapAt s' hp']; exact this
  · rw [swapAt_of_le s hp, swapAt_of_le s' (h.length_eq ▸ hp)]; exact h

theorem Iso.rmAt {s s' : List (ℕ × α)} (h : Iso s s') {r : ℕ} (hr : r + 2 ≤ s.length) :
    Iso (Chord.rmAt s r) (Chord.rmAt s' r) := by
  have hr' : r + 2 ≤ s'.length := h.length_eq ▸ hr
  refine ⟨?_, fun i j => by rw [same_rmAt hr, same_rmAt hr', h.2]⟩
  apply List.ext_getElem?; intro i
  have := congrArg (fun l => l[rmIdx r i]?) h.1
  simp only [List.getElem?_map] at this ⊢
  rw [getElem?_rmAt s hr, getElem?_rmAt s' hr']; exact this

theorem opn_iff {s s' : List (ℕ × α)} (h : Iso s s') (q : ℕ) : Opn s q ↔ Opn s' q := by
  simp only [Opn, h.2]

theorem cls_iff {s s' : List (ℕ × α)} (h : Iso s s') (q : ℕ) : Cls s q ↔ Cls s' q := by
  simp only [Cls, h.2]

theorem cr_le_of_iso {s s' : List (ℕ × α)} (h : Iso s s') : cr s ≤ cr s' := by
  unfold cr
  refine Finset.card_le_card fun x hx => ?_
  rw [mem_crSet] at hx ⊢
  obtain ⟨h1, h2, h3, h4, h5⟩ := hx
  exact ⟨h1, h2, h3, (h.2 _ _).1 h4, (h.2 _ _).1 h5⟩

/-- The canonical diagram depends only on the letters and the pairing. -/
theorem canon_congr : ∀ (n : ℕ) {s s' : List (ℕ × α)}, s.length + cr s < n → Iso s s' →
    canon s = canon s' := by
  intro n
  induction n with
  | zero => intro s s' h; omega
  | succ n ih =>
    intro s s' hn h
    by_cases hv : Valid s
    swap
    · have hv' : ¬ Valid s' := fun hv' => hv (h.symm.valid hv')
      rw [canon, dite_eq_right hv, canon, dite_eq_right hv']
    have hv' := h.valid hv
    by_cases hadj : ∃ r, Same s r (r + 1)
    · classical
      obtain ⟨r, hr, hmin⟩ : ∃ r, Same s r (r + 1) ∧ ∀ r' < r, ¬ Same s r' (r' + 1) :=
        ⟨Nat.find hadj, Nat.find_spec hadj, fun _ => Nat.find_min hadj⟩
      have hr' : Same s' r (r + 1) := (h.2 _ _).1 hr
      have hmin' : ∀ r' < r, ¬ Same s' r' (r' + 1) := fun r' hr'' hs => hmin r' hr'' ((h.2 _ _).2 hs)
      rw [canon_adj hv hr hmin, canon_adj hv' hr' hmin', h.snd_getElem hr.lt_left hr'.lt_left]
      have hl : r + 2 ≤ s.length := hr.lt_right
      rw [ih (by rw [length_rmAt s hl]; have := cr_rmAt_le hl; omega) (h.rmAt hl)]
    · have hno : ∀ r, ¬ Same s r (r + 1) := fun r hr => hadj ⟨r, hr⟩
      have hno' : ∀ r, ¬ Same s' r (r + 1) := fun r hr => hno r ((h.2 _ _).2 hr)
      by_cases hne : s = []
      · have hne' : s' = [] := List.eq_nil_of_length_eq_zero (by rw [← h.length_eq, hne]; rfl)
        rw [hne, hne']
      have hne' : s' ≠ [] := fun e => hne (List.eq_nil_of_length_eq_zero
        (by rw [h.length_eq, e]; rfl))
      obtain ⟨q, ho, hc, hq, hmin⟩ := canon_cross hv hno hne
      obtain ⟨q', ho', hc', hq', hmin'⟩ := canon_cross hv' hno' hne'
      have e : q = q' := by
        rcases lt_trichotomy q q' with l | l | l
        · exact (hmin' q l ⟨(opn_iff h q).1 ho, (cls_iff h _).1 hc⟩).elim
        · exact l
        · exact (hmin q' l ⟨(opn_iff h q').2 ho', (cls_iff h _).2 hc'⟩).elim
      subst e
      have hilv := ilv_of_opn_cls hv (hno q) ho hc
      rw [hq, hq', ih (by rw [length_swapAt]; have := cr_swapAt_lt hv hilv; omega) (h.swapAt q)]

/-- The canonical diagram depends only on the letters and the pairing. -/
theorem canon_eq_of_iso {s s' : List (ℕ × α)} (h : Iso s s') : canon s = canon s' :=
  canon_congr _ (Nat.lt_succ_self _) h

end Iso

section Letters

variable {α : Type*} {d : α → α}

/-- The effect of a move on the list of letters. -/
def lstep (d : α → α) (l : List α) : Move α → List α
  | .cup g a => insAt l g a (d a)
  | .cross p => swapAt l p

theorem map_insAt {β γ : Type*} (f : β → γ) (s : List β) (g : ℕ) (x y : β) :
    (insAt s g x y).map f = insAt (s.map f) g (f x) (f y) := by
  simp [insAt, List.map_take, List.map_drop]

theorem map_swapAt {β γ : Type*} (f : β → γ) (s : List β) (p : ℕ) :
    (swapAt s p).map f = swapAt (s.map f) p := by
  by_cases hp : p + 1 < s.length
  · apply List.ext_getElem?; intro i
    rw [List.getElem?_map, getElem?_swapAt s hp, getElem?_swapAt _ (by simpa using hp),
      List.getElem?_map]
  · rw [swapAt_of_le s hp, swapAt_of_le _ (by simpa using hp)]

theorem map_rmAt {β γ : Type*} (f : β → γ) (s : List β) (r : ℕ) :
    (rmAt s r).map f = rmAt (s.map f) r := by
  simp [rmAt, List.map_take, List.map_drop]

theorem snd_step (s : List (ℕ × α)) (m : Move α) :
    (step d s m).map Prod.snd = lstep d (s.map Prod.snd) m := by
  cases m with
  | cup g a => simp only [step, lstep, map_insAt]
  | cross p => simp only [step, lstep, map_swapAt]

theorem snd_foldl_step : ∀ (s : List (ℕ × α)) (D : List (Move α)),
    (D.foldl (step d) s).map Prod.snd = D.foldl (lstep d) (s.map Prod.snd)
  | s, [] => rfl
  | s, m :: D => by simp only [List.foldl_cons, snd_foldl_step _ D, snd_step]

/-- The letters of the final state of a diagram. -/
theorem snd_run (D : List (Move α)) : (run d D).map Prod.snd = D.foldl (lstep d) [] := by
  rw [run, snd_foldl_step]; rfl

theorem length_lstep (l : List α) (m : Move α) : (lstep d l m).length = m.len l.length := by
  cases m with
  | cup g a => simp [lstep, Move.len, insAt]; omega
  | cross p => simp [lstep, Move.len]

theorem insAt_insAt {β : Type*} (l : List β) {g g' : ℕ} (h : g' ≤ g) (hg : g ≤ l.length)
    (x y u v : β) : insAt (insAt l g x y) g' u v = insAt (insAt l g' u v) (g + 2) x y := by
  apply List.ext_getElem?; intro i
  have h1 : g' ≤ (insAt l g x y).length := by rw [length_insAt l hg]; omega
  have h2 : g + 2 ≤ (insAt l g' u v).length := by rw [length_insAt l (by omega)]; omega
  simp only [getElem?_insAt _ h1, getElem?_insAt _ h2, getElem?_insAt l hg,
    getElem?_insAt l (show g' ≤ l.length by omega)]
  rcases (show i < g' ∨ i = g' ∨ i = g' + 1 ∨ (g' + 1 < i ∧ i < g + 2) ∨ i = g + 2 ∨ i = g + 3 ∨
    g + 3 < i by omega) with hi | hi | hi | hi | hi | hi | hi <;>
  · simp (disch := omega) only [ite_eq_left, ite_eq_right]

theorem insAt_swapAt_lt {β : Type*} (l : List β) {p g : ℕ} (h : p + 2 ≤ g) (hg : g ≤ l.length)
    (x y : β) : insAt (swapAt l p) g x y = swapAt (insAt l g x y) p := by
  have hp : p + 1 < l.length := by omega
  have hg' : g ≤ (swapAt l p).length := by simpa using hg
  have hp' : p + 1 < (insAt l g x y).length := by rw [length_insAt l hg]; omega
  apply List.ext_getElem?; intro i
  simp only [getElem?_insAt _ hg', getElem?_swapAt _ hp', getElem?_insAt l hg,
    getElem?_swapAt l hp]
  rcases (show i < p ∨ i = p ∨ i = p + 1 ∨ (p + 1 < i ∧ i < g) ∨ i = g ∨ i = g + 1 ∨ g + 1 < i
    by omega) with hi | rfl | rfl | hi | rfl | rfl | hi <;>
  · simp (disch := omega) only [ite_eq_left, ite_eq_right, tau_left, tau_right, tau_of_ne, ↓reduceIte]

theorem insAt_swapAt_ge {β : Type*} (l : List β) {p g : ℕ} (h : g ≤ p) (hp : p + 1 < l.length)
    (x y : β) : insAt (swapAt l p) g x y = swapAt (insAt l g x y) (p + 2) := by
  have hg : g ≤ l.length := by omega
  have hg' : g ≤ (swapAt l p).length := by simpa using hg
  have hp' : p + 2 + 1 < (insAt l g x y).length := by rw [length_insAt l hg]; omega
  apply List.ext_getElem?; intro i
  simp only [getElem?_insAt _ hg', getElem?_swapAt _ hp', getElem?_insAt l hg,
    getElem?_swapAt l hp]
  rcases (show i < g ∨ i = g ∨ i = g + 1 ∨ (g + 1 < i ∧ i < p + 2) ∨ i = p + 2 ∨ i = p + 2 + 1 ∨
    p + 2 + 1 < i by omega) with hi | rfl | rfl | hi | rfl | rfl | hi <;>
  · simp (disch := omega) only [ite_eq_left, ite_eq_right, tau_left, tau_right, tau_of_ne, ↓reduceIte]
    try (congr 1; unfold tau; split_ifs <;> omega)

theorem insAt_pitch {β : Type*} (l : List β) {g : ℕ} (hg : g < l.length) (x y : β) :
    swapAt (insAt l g x y) (g + 1) = swapAt (insAt l (g + 1) x y) g := by
  have h1 : g + 1 + 1 < (insAt l g x y).length := by rw [length_insAt l (by omega)]; omega
  have h2 : g + 1 < (insAt l (g + 1) x y).length := by rw [length_insAt l (by omega)]; omega
  apply List.ext_getElem?; intro i
  simp only [getElem?_swapAt _ h1, getElem?_swapAt _ h2, getElem?_insAt l (show g ≤ l.length by omega),
    getElem?_insAt l (show g + 1 ≤ l.length by omega)]
  rcases (show i < g ∨ i = g ∨ i = g + 1 ∨ i = g + 1 + 1 ∨ g + 1 + 1 < i by omega) with
    hi | rfl | rfl | rfl | hi <;>
  · simp (disch := omega) only [ite_eq_left, ite_eq_right, tau_left, tau_right, tau_of_ne, ↓reduceIte,
      show ∀ n : ℕ, n + 1 + 1 - 2 = n from fun n => by omega]

/-- Each generating move preserves whether a diagram fits and the letters it produces. -/
theorem Step.fits_letters {L R : List (Move α)} (h : Step L R) (l : List α) :
    (Fits l.length L ↔ Fits l.length R) ∧
      (Fits l.length L → L.foldl (lstep d) l = R.foldl (lstep d) l) := by
  cases h with
  | xx h =>
    refine ⟨by simp only [Fits, Move.Ok, Move.len, and_true]; constructor <;> intro <;> omega,
      fun hf => ?_⟩
    simp only [Fits, Move.Ok, Move.len] at hf
    simp only [List.foldl_cons, List.foldl_nil, lstep]
    exact swapAt_comm l h (by omega)
  | xuL a h =>
    refine ⟨by simp only [Fits, Move.Ok, Move.len, and_true]; constructor <;> intro <;> omega,
      fun hf => ?_⟩
    simp only [Fits, Move.Ok, Move.len] at hf
    simp only [List.foldl_cons, List.foldl_nil, lstep]
    rw [insAt_swapAt_lt l h (by simpa using hf.2.1)]
  | xuR a h =>
    refine ⟨by simp only [Fits, Move.Ok, Move.len, and_true]; constructor <;> intro <;> omega,
      fun hf => ?_⟩
    simp only [Fits, Move.Ok, Move.len] at hf
    simp only [List.foldl_cons, List.foldl_nil, lstep]
    rw [insAt_swapAt_ge l h hf.1]
  | uu a b h =>
    refine ⟨by simp only [Fits, Move.Ok, Move.len, and_true]; constructor <;> intro <;> omega,
      fun hf => ?_⟩
    simp only [Fits, Move.Ok, Move.len] at hf
    simp only [List.foldl_cons, List.foldl_nil, lstep]
    exact insAt_insAt l h hf.1 _ _ _ _
  | braid p =>
    refine ⟨by simp only [Fits, Move.Ok, Move.len, and_true]; constructor <;> intro <;> omega,
      fun hf => ?_⟩
    simp only [Fits, Move.Ok, Move.len] at hf
    simp only [List.foldl_cons, List.foldl_nil, lstep]
    exact swapAt_braid l (by omega)
  | pitch g a =>
    refine ⟨by simp only [Fits, Move.Ok, Move.len, and_true]; constructor <;> intro <;> omega,
      fun hf => ?_⟩
    simp only [Fits, Move.Ok, Move.len] at hf
    simp only [List.foldl_cons, List.foldl_nil, lstep]
    exact insAt_pitch l (by omega) _ _

theorem foldl_lstep_len : ∀ (l : List α) (D : List (Move α)),
    (D.foldl (lstep d) l).length = D.foldl Move.len l.length
  | l, [] => rfl
  | l, m :: D => by simp only [List.foldl_cons, foldl_lstep_len _ D, length_lstep]

/-- A move in context preserves whether a diagram fits and the letters it produces. -/
theorem Rw.fits_letters {X Y : List (Move α)} (h : Rw X Y) (l : List α) :
    (Fits l.length X ↔ Fits l.length Y) ∧
      (Fits l.length X → X.foldl (lstep d) l = Y.foldl (lstep d) l) := by
  obtain ⟨A, B, L, R, hs, rfl, rfl⟩ := h
  have hA := foldl_lstep_len (d := d) l A
  obtain ⟨h1, h2⟩ := hs.fits_letters (d := d) (A.foldl (lstep d) l)
  rw [hA] at h1 h2
  have hLR : ∀ hf : Fits (A.foldl Move.len l.length) L, L.foldl Move.len (A.foldl Move.len l.length) =
      R.foldl Move.len (A.foldl Move.len l.length) := fun hf => by
    rw [← hA, ← foldl_lstep_len (d := d), ← foldl_lstep_len (d := d), h2 (hA ▸ hf)]
  simp only [fits_append, List.foldl_append]
  constructor
  · constructor
    · rintro ⟨⟨hA', hL⟩, hB⟩
      exact ⟨⟨hA', h1.1 hL⟩, by rwa [← hLR hL]⟩
    · rintro ⟨⟨hA', hR⟩, hB⟩
      exact ⟨⟨hA', h1.2 hR⟩, by rwa [hLR (h1.2 hR)]⟩
  · rintro ⟨⟨-, hL⟩, -⟩
    rw [h2 (hA ▸ hL)]

/-- Equivalent diagrams fit on the same number of strands and produce the same letters. -/
theorem Equiv.fits_letters {X Y : List (Move α)} (h : Equiv X Y) (l : List α) :
    (Fits l.length X ↔ Fits l.length Y) ∧
      (Fits l.length X → X.foldl (lstep d) l = Y.foldl (lstep d) l) := by
  induction h with
  | rel X Y h => exact h.fits_letters l
  | refl => exact ⟨Iff.rfl, fun _ => rfl⟩
  | symm X Y _ ih => exact ⟨ih.1.symm, fun hf => (ih.2 (ih.1.2 hf)).symm⟩
  | trans X Y Z _ _ ih ih' =>
    exact ⟨ih.1.trans ih'.1, fun hf => (ih.2 hf).trans (ih'.2 (ih.1.1 hf))⟩

end Letters

section RunCanon

variable {α : Type*} {d : α → α}

/-- The letters at the two ends of each arc are `a` (at one end) and `d a` (at the other). -/
def Lettered (d : α → α) (s : List (ℕ × α)) : Prop :=
  ∀ i j, Same s i j → i < j → (s[j]?).map Prod.snd = (s[i]?).map (d ∘ Prod.snd)

theorem Lettered.swapAt {s : List (ℕ × α)} (h : Lettered d s) {p : ℕ}
    (hp : p + 1 < s.length) (hn : ¬ Same s p (p + 1)) : Lettered d (Chord.swapAt s p) := by
  intro i j hij hlt
  rw [same_swapAt hp] at hij
  rw [getElem?_swapAt s hp, getElem?_swapAt s hp]
  have : tau p i < tau p j := by
    rw [tau_lt_iff p]
    · exact hlt
    · rintro ⟨rfl, rfl⟩; exact hn (by simpa [tau] using hij.symm)
    · rintro ⟨rfl, rfl⟩; omega
  exact h _ _ hij this

theorem Lettered.rmAt {s : List (ℕ × α)} (h : Lettered d s) {r : ℕ} (hr : r + 2 ≤ s.length) :
    Lettered d (Chord.rmAt s r) := by
  intro i j hij hlt
  rw [same_rmAt hr] at hij
  rw [getElem?_rmAt s hr, getElem?_rmAt s hr]
  exact h _ _ hij ((rmIdx_lt_iff r).2 hlt)

theorem Iso.insAt {u t : List (ℕ × α)} (h : Iso u t) {g : ℕ} (hg : g ≤ u.length) {k k' : ℕ}
    (hk : ∀ x ∈ u, x.1 ≠ k) (hk' : ∀ x ∈ t, x.1 ≠ k') (a b : α) :
    Iso (Chord.insAt u g (k, a) (k, b)) (Chord.insAt t g (k', a) (k', b)) := by
  have hg' : g ≤ t.length := h.length_eq ▸ hg
  refine ⟨by rw [map_insAt, map_insAt, h.1], fun i j => ?_⟩
  rw [same_insAt_iff hg hk, same_insAt_iff hg' hk', h.2]

theorem ne_id_of_mem_rmAt {s : List (ℕ × α)} (hv : Valid s) {r : ℕ} (hr : Same s r (r + 1))
    {x : ℕ × α} (hx : x ∈ Chord.rmAt s r) : x.1 ≠ (s[r]'hr.lt_left).1 := by
  have hl : r + 2 ≤ s.length := hr.lt_right
  rw [List.mem_iff_getElem?] at hx
  obtain ⟨i, hi⟩ := hx
  rw [getElem?_rmAt s hl] at hi
  intro e
  have hs : Same s (rmIdx r i) r := by
    refine ⟨by unfold rmIdx; split_ifs <;> omega, by simp [idAt, hi], ?_⟩
    simp [idAt, hi, List.getElem?_eq_getElem hr.lt_left, e]
  have := hv.unique hs.symm hr
  unfold rmIdx at this; split_ifs at this <;> omega

/-- **The canonical diagram realises its pairing**: it fits, and its final state has the letters
and the pairing of `s`. -/
theorem run_canon : ∀ (n : ℕ) {s : List (ℕ × α)}, s.length + cr s < n → Valid s →
    Lettered d s → Fits 0 (canon s) ∧ Iso (run d (canon s)) s := by
  intro n
  induction n with
  | zero => intro s h; omega
  | succ n ih =>
    intro s hn hv hl
    by_cases hadj : ∃ r, Same s r (r + 1)
    · classical
      obtain ⟨r, hr, hmin⟩ : ∃ r, Same s r (r + 1) ∧ ∀ r' < r, ¬ Same s r' (r' + 1) :=
        ⟨Nat.find hadj, Nat.find_spec hadj, fun _ => Nat.find_min hadj⟩
      have hl2 : r + 2 ≤ s.length := hr.lt_right
      obtain ⟨hf, hiso⟩ := ih (s := rmAt s r)
        (by rw [length_rmAt s hl2]; have := cr_rmAt_le hl2; omega) (hv.rmAt hr) (hl.rmAt hl2)
      have hinv := inv_run (d := d) hf
      have hlen : (run d (canon (rmAt s r))).length = s.length - 2 := by
        rw [hiso.length_eq, length_rmAt s hl2]
      rw [canon_adj hv hr hmin]
      refine ⟨(fits_snoc (d := d)).2 ⟨hf, by simp only [Move.Ok]; omega⟩, ?_⟩
      rw [run_append, List.foldl_cons, List.foldl_nil]
      have e1 := insAt_rmAt s (show r + 1 < s.length by omega)
      have eid : (s[r + 1]'(by omega)).1 = (s[r]'(by omega)).1 := by
        have := hr.2.2
        simp only [idAt, List.getElem?_eq_getElem (show r < s.length by omega),
          List.getElem?_eq_getElem (show r + 1 < s.length by omega)] at this
        simpa using this.symm
      have elt : (s[r + 1]'(by omega)).2 = d (s[r]'(by omega)).2 := by
        have := hl r (r + 1) hr (by omega)
        simp only [List.getElem?_eq_getElem (show r < s.length by omega),
          List.getElem?_eq_getElem (show r + 1 < s.length by omega)] at this
        simpa using this
      have e2 : s[r + 1]'(by omega) = ((s[r]'(by omega)).1, d (s[r]'(by omega)).2) :=
        Prod.ext eid elt
      conv_rhs => rw [← e1, e2]
      exact hiso.insAt (by omega) (fun x hx => (hinv.2 x hx).ne)
        (fun x hx => ne_id_of_mem_rmAt hv hr hx) _ _
    · have hno : ∀ r, ¬ Same s r (r + 1) := fun r hr => hadj ⟨r, hr⟩
      by_cases hne : s = []
      · subst hne
        rw [canon_nil]
        exact ⟨trivial, ⟨rfl, fun i j => Iff.rfl⟩⟩
      obtain ⟨q, ho, hc, hq, -⟩ := canon_cross hv hno hne
      have hilv := ilv_of_opn_cls hv (hno q) ho hc
      have hql := hilv.lt
      obtain ⟨hf, hiso⟩ := ih (s := swapAt s q)
        (by rw [length_swapAt]; have := cr_swapAt_lt hv hilv; omega) (hv.swapAt hql)
        (hl.swapAt hql (hno q))
      rw [hq]
      refine ⟨(fits_snoc (d := d)).2 ⟨hf, by simp only [Move.Ok]; rw [hiso.length_eq]; simpa⟩, ?_⟩
      rw [run_append, List.foldl_cons, List.foldl_nil]
      have := hiso.swapAt q
      rwa [swapAt_swapAt] at this

end RunCanon

end Categorification.Chord
