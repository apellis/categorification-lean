/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.QuantumGroup.UDotWords

/-!
# Pairings of signed sequences and their degrees (combinatorics)

Khovanov–Lauda III, arXiv:0807.3250v1, §2.2 ("Geometric interpretation of the bilinear form",
TeX label `subsec_geometric`, pp. 14–17 of the arXiv PDF).

## Boundary words, matchings

We place `n` endpoints on the **upper** boundary `ℝ × {1}` of the strip `ℝ × [0, 1]`, labelled
by a signed sequence `L : Fin n → Bool × I` (`true = +`). A strand ending at an upper endpoint
labelled `+i` is oriented upwards there (the endpoint is a *sink*), one ending at `-i` is oriented
downwards (a *source*). A pairing of these endpoints (KL III: "complete matchings of the points
such that the two points in each matching pair share the same label and their orientations are
compatible") is an involution `σ` of `Fin n` exchanging endpoints of the same colour and opposite
sign (`UDot.IsMatching`); `UDot.matchings L` is the finite set of these.

Two-sided `(𝐢, 𝐣)`-pairings (lower sequence `𝐢`, upper sequence `𝐣`) are pairings of the single
upper word `ρW(𝐢) 𝐣` obtained by bending the lower endpoints up around the left side of the strip;
see `Categorification.QuantumGroup.UDotFormFormula`.

## The degree of a minimal diagram

For a pairing `σ` of an upper word we use the following **minimal diagram** `D_σ`: the strand
joining `a < c` is a cup hanging from the upper boundary, descending slowly from `a` to a
minimum just to the left of `c` (at depth `N^c` for a large constant `N`) and rising steeply to
`c`. Two cups meet iff their endpoints interleave, and then exactly once, on the descending parts
of both; nested and disjoint cups do not meet. So `D_σ` is a minimal diagram (no self-intersections,
two strands meet at most once).

The degree `deg(D_σ, λ)` (KL III, table after (2.12), and eq. (2.13): `c_{±i,λ} =
(i·i)/2 (1 ± ⟨i, λ⟩)`) is the sum of

* for every cup `(a, c)`, `a < c`, of colour `i`: its unique local minimum, lying to the left of
  the region adjacent to the upper boundary just right of `c`; that region has weight
  `λ + Σ_{r > c} ε_r (i_r)_X` (`UDot.wR`). The cup is oriented to the right iff the endpoint `a`
  is a source (sign `-`), and a right-oriented cup has degree `c_{+i,·}`, a left-oriented one
  `c_{-i,·}`. Hence the contribution `(i·i)/2 (1 - ε_a ⟨i, wR c⟩)` (`UDot.cupDeg`);
* for every crossing, i.e. every pair of interleaved cups `(a, σ a)`, `(b, σ b)` with
  `a < b < σ a < σ b`: the descending part of the cup `(a, σ a)` is traversed downwards iff `a` is
  a source; the crossing has degree `-i·j` if both strands go down or both go up (`ε_a = ε_b`), and
  degree `0` otherwise (KL III: balanced crossings) (`UDot.crossDeg`).

The total is `UDot.mdeg`. (KL III prove that `deg(D, λ)` only depends on the pairing, not on the
minimal diagram; we only use the specific diagrams `D_σ`.)

## Main results

* `UDot.mdeg_eq_alt` — the reformulation `deg = Σ_{cups} (i·i)/2 (1 - ε_a ⟨i, λ⟩)
  + Σ_{interleaved pairs, ε_a ≠ ε_b} (-a·b) + Σ_{nested pairs} ε_a ε_b (a·b)`, in which only the
  relative position of pairs of cups enters (`UDot.arcDeg`, `UDot.pairDeg`);
* `UDot.isMatching_swap`, `UDot.mdeg_swap` — exchanging two adjacent endpoints `(+i)(-j)` which are
  not joined to each other is a degree-preserving bijection on pairings (KL III, proofs of the
  second and third lemmas after Lemma 2.8);
* `UDot.mdeg_removeArc` — removing a cup joining two adjacent endpoints `p, p + 1` changes the
  degree by the degree of that cup (KL III, class (3) in the proof of the third lemma).
-/

noncomputable section

namespace Categorification.QuantumGroup

namespace UDot

open Finset Equiv
open scoped Classical

variable {I : Type*} (C : CartanDatum I) {n : ℕ}

/-! ### Matchings -/

/-- `σ` is an `(∅, L)`-pairing: an involution of the endpoints exchanging endpoints of the same
colour and opposite sign. -/
def IsMatching (L : Fin n → Bool × I) (σ : Perm (Fin n)) : Prop :=
  ∀ p, σ (σ p) = p ∧ (L (σ p)).2 = (L p).2 ∧ (L (σ p)).1 = !(L p).1

/-- The finite set of pairings of the upper word `L` (KL III's `p'(∅, L)`). -/
def matchings (L : Fin n → Bool × I) : Finset (Perm (Fin n)) := univ.filter (IsMatching L)

theorem mem_matchings {L : Fin n → Bool × I} {σ : Perm (Fin n)} :
    σ ∈ matchings L ↔ IsMatching L σ := by
  simp [matchings]

variable {L : Fin n → Bool × I} {σ : Perm (Fin n)}

theorem IsMatching.invol (h : IsMatching L σ) (p : Fin n) : σ (σ p) = p := (h p).1

theorem IsMatching.col (h : IsMatching L σ) (p : Fin n) : (L (σ p)).2 = (L p).2 := (h p).2.1

theorem IsMatching.sign (h : IsMatching L σ) (p : Fin n) : (L (σ p)).1 = !(L p).1 := (h p).2.2

theorem IsMatching.ne (h : IsMatching L σ) (p : Fin n) : σ p ≠ p := by
  intro e
  have := h.sign p
  rw [e] at this
  cases (L p).1 <;> simp at this

theorem IsMatching.sgn_eq (h : IsMatching L σ) (p : Fin n) :
    sgn (L (σ p)).1 = -sgn (L p).1 := by
  rw [h.sign, sgn_not]

theorem IsMatching.lt_or_gt (h : IsMatching L σ) (p : Fin n) : p < σ p ∨ σ p < p := by
  rcases lt_trichotomy p (σ p) with h1 | h1 | h1
  · exact Or.inl h1
  · exact absurd h1.symm (h.ne p)
  · exact Or.inr h1

/-- A sum over a set of endpoints of a function which is odd under `σ` only sees the endpoints
whose partner lies outside the set. -/
theorem IsMatching.sum_cancel (h : IsMatching L σ) (S : Finset (Fin n)) (g : Fin n → ℤ)
    (hg : ∀ r, g (σ r) = -g r) :
    ∑ r ∈ S, g r = ∑ r ∈ S.filter (fun r => σ r ∉ S), g r := by
  rw [← Finset.sum_filter_add_sum_filter_not S (fun r => σ r ∈ S)]
  have h0 : ∑ r ∈ S.filter (fun r => σ r ∈ S), g r = 0 := by
    refine Finset.sum_involution (fun r _ => σ r) (fun r _ => by rw [hg]; ring)
      (fun r _ _ => h.ne r) (fun r hr => ?_) (fun r _ => h.invol r)
    rw [Finset.mem_filter] at hr ⊢
    exact ⟨hr.2, by rw [h.invol]; exact hr.1⟩
  rw [h0, zero_add]

/-! ### Degrees -/

/-- `⟨i, μ⟩` for the weight `μ = λ + Σ_{r > c} ε_r (i_r)_X` of the region adjacent to the upper
boundary immediately to the right of the endpoint `c` (`ℓ i = ⟨i, λ⟩`, `λ` the weight of the
rightmost region). -/
def wR (ℓ : I → ℤ) (L : Fin n → Bool × I) (c : Fin n) (i : I) : ℤ :=
  ℓ i + ∑ r ∈ univ.filter (c < ·), sgn (L r).1 * A C i (L r).2

/-- The degree of the minimum of the cup `(a, c)` (`a < c`): `c_{-ε_a i, μ}` with `μ = wR c`. -/
def cupDeg (ℓ : I → ℤ) (L : Fin n → Bool × I) (a c : Fin n) : ℤ :=
  di C (L a).2 * (1 - sgn (L a).1 * wR C ℓ L c (L a).2)

/-- The degree of the crossing of the interleaved cups starting at `a < b`: `-i·j` if they are
traversed in the same vertical direction there, `0` (balanced) otherwise. -/
def crossDeg (L : Fin n → Bool × I) (a b : Fin n) : ℤ :=
  if (L a).1 = (L b).1 then -C.dot (L a).2 (L b).2 else 0

/-- **The degree `deg(D_σ, λ)` of the minimal diagram `D_σ` of the pairing `σ`** (KL III §2.2):
the sum of the degrees of the minima of the cups and of the crossings. -/
def mdeg (ℓ : I → ℤ) (L : Fin n → Bool × I) (σ : Perm (Fin n)) : ℤ :=
  (∑ a, if a < σ a then cupDeg C ℓ L a (σ a) else 0) +
    ∑ a, ∑ b, if a < b ∧ b < σ a ∧ σ a < σ b then crossDeg C L a b else 0

/-- The part `(i·i)/2 (1 - ε_a ⟨i, λ⟩)` of the degree of the cup starting at `a`. -/
def arcDeg (ℓ : I → ℤ) (L : Fin n → Bool × I) (a : Fin n) : ℤ :=
  di C (L a).2 * (1 - sgn (L a).1 * ℓ (L a).2)

/-- The interaction of the cups starting at `a` and `b`: `-a·b` if they interleave
(`a < b < σ a < σ b`) with `ε_a ≠ ε_b`, and `ε_a ε_b (a·b)` if the cup at `a` is nested in the
cup at `b` (`b < a < σ a < σ b`). -/
def pairDeg (L : Fin n → Bool × I) (σ : Perm (Fin n)) (a b : Fin n) : ℤ :=
  (if a < b ∧ b < σ a ∧ σ a < σ b then
      (if (L a).1 = (L b).1 then 0 else -C.dot (L a).2 (L b).2) else 0) +
    if b < a ∧ a < σ a ∧ σ a < σ b then
      sgn (L a).1 * sgn (L b).1 * C.dot (L a).2 (L b).2 else 0

/-- `di i · ⟨i, j_X⟩ = i·j` inside the sums. -/
theorem cupDeg_eq (ℓ : I → ℤ) (a c : Fin n) :
    cupDeg C ℓ L a c = arcDeg C ℓ L a -
      ∑ r ∈ univ.filter (c < ·), sgn (L a).1 * sgn (L r).1 * C.dot (L a).2 (L r).2 := by
  rw [cupDeg, arcDeg, wR]
  have : ∑ r ∈ univ.filter (c < ·), sgn (L a).1 * sgn (L r).1 * C.dot (L a).2 (L r).2 =
      di C (L a).2 * (sgn (L a).1 * ∑ r ∈ univ.filter (c < ·), sgn (L r).1 * A C (L a).2 (L r).2) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← di_mul_A]; ring
  rw [this]; ring

theorem mdeg_row_eq (h : IsMatching L σ) (ℓ : I → ℤ) (a : Fin n) :
    ((if a < σ a then cupDeg C ℓ L a (σ a) else 0) +
      ∑ b, if a < b ∧ b < σ a ∧ σ a < σ b then crossDeg C L a b else 0) =
      (if a < σ a then arcDeg C ℓ L a else 0) + ∑ b, pairDeg C L σ a b := by
  by_cases ha : a < σ a
  · rw [if_pos ha, if_pos ha, cupDeg_eq]
    set c := σ a with hc
    set g : Fin n → ℤ := fun r => sgn (L a).1 * sgn (L r).1 * C.dot (L a).2 (L r).2 with hg
    have hgσ : ∀ r, g (σ r) = -g r := fun r => by
      simp only [hg, h.sgn_eq, h.col]; ring
    have h1 : ∑ r ∈ univ.filter (c < ·), g r =
        -∑ b, if b < c ∧ c < σ b then g b else 0 := by
      rw [h.sum_cancel _ g hgσ, Finset.sum_filter, Finset.sum_filter]
      rw [← Equiv.sum_comp σ, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, h.invol, hgσ]
      by_cases h1 : c < σ b
      · by_cases h2 : c < b
        · have h3 : ¬ b < c := not_lt.2 h2.le
          simp [h1, h2, h3]
        · have h3 : b < c := by
            rcases lt_or_eq_of_le (not_lt.1 h2) with h3 | h3
            · exact h3
            · exfalso; rw [h3, hc, h.invol] at h1; exact absurd (h1.trans ha) (lt_irrefl _)
          simp [h1, h2, h3]
      · simp [h1]
    change arcDeg C ℓ L a - ∑ r ∈ univ.filter (c < ·), g r + _ = _
    rw [h1, sub_neg_eq_add, add_assoc, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    clear_value c
    simp only [pairDeg, crossDeg, hg, ← hc]
    by_cases hbc : b < c ∧ c < σ b
    · rcases lt_trichotomy a b with hab | hab | hab
      · have hn : ¬ (b < a ∧ a < c ∧ c < σ b) := fun h' => absurd (h'.1.trans hab) (lt_irrefl _)
        have hp : a < b ∧ b < c ∧ c < σ b := ⟨hab, hbc⟩
        have hba : ¬ b < a := not_lt.2 hab.le
        simp only [hbc, hp, hn, hba, and_self, if_true, if_false, add_zero, false_and]
        cases (L a).1 <;> cases (L b).1 <;> simp
      · exfalso; rw [← hab, ← hc] at hbc; exact lt_irrefl _ hbc.2
      · have hn : ¬ (a < b ∧ b < c ∧ c < σ b) := fun h' => absurd (h'.1.trans hab) (lt_irrefl _)
        have hp : b < a ∧ a < c ∧ c < σ b := ⟨hab, ha, hbc.2⟩
        have hab' : ¬ a < b := not_lt.2 hab.le
        simp only [hbc, hp, hn, hab', ha, and_self, if_true, if_false, zero_add, add_zero, false_and]
    · have hn1 : ¬ (a < b ∧ b < c ∧ c < σ b) := fun h' => hbc ⟨h'.2.1, h'.2.2⟩
      have hn2 : ¬ (b < a ∧ a < c ∧ c < σ b) := fun h' => hbc ⟨h'.1.trans h'.2.1, h'.2.2⟩
      simp only [hbc, hn1, hn2, if_false, add_zero, and_false, zero_add]
  · rw [if_neg ha, if_neg ha]
    simp only [zero_add]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hn1 : ¬ (a < b ∧ b < σ a ∧ σ a < σ b) := fun h' => ha (h'.1.trans h'.2.1)
    have hn2 : ¬ (b < a ∧ a < σ a ∧ σ a < σ b) := fun h' => ha h'.2.1
    simp [pairDeg, hn1, hn2]

/-- **The reformulated degree** (see the module docstring). -/
theorem mdeg_eq_alt (h : IsMatching L σ) (ℓ : I → ℤ) :
    mdeg C ℓ L σ = (∑ a, if a < σ a then arcDeg C ℓ L a else 0) + ∑ a, ∑ b, pairDeg C L σ a b := by
  rw [mdeg, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => mdeg_row_eq C h ℓ a

/-! ### Exchanging two adjacent endpoints -/

/-- The product `∏_{cups (a, σ a)} w(colour of a)`. -/
def arcProd {M : Type*} [CommMonoid M] (w : I → M) (L : Fin n → Bool × I) (σ : Perm (Fin n)) : M :=
  ∏ a, if a < σ a then w (L a).2 else 1

/-- Conjugating a pairing by an involution `τ` of the endpoints gives a pairing of `L ∘ τ`. -/
theorem IsMatching.conj (h : IsMatching L σ) (τ : Perm (Fin n)) (hτ : ∀ x, τ (τ x) = x) :
    IsMatching (L ∘ τ) (τ * σ * τ) := by
  intro x
  simp only [Perm.mul_apply, Function.comp_apply, hτ]
  exact ⟨by rw [h.invol, hτ], h.col _, h.sign _⟩

section Swap

variable {p p' : Fin n}

theorem swap_lt_iff (hp' : p'.val = p.val + 1) {x y : Fin n} (h : ¬ (x = p ∧ y = p'))
    (h' : ¬ (x = p' ∧ y = p)) : swap p p' x < swap p p' y ↔ x < y := by
  rw [Fin.lt_iff_val_lt_val, Fin.lt_iff_val_lt_val, swap_apply_def, swap_apply_def]
  by_cases hx : x = p <;> by_cases hy : y = p <;> by_cases hx' : x = p' <;> by_cases hy' : y = p' <;>
    simp_all [Fin.ext_iff] <;> omega

/-- The value of `pairDeg` as a function of the positions (as natural numbers), signs and the
value of `·` on the colours. -/
def PDn (x y x' y' : ℕ) (sa sb : Bool) (d : ℤ) : ℤ :=
  (if x < y ∧ y < x' ∧ x' < y' then (if sa = sb then 0 else -d) else 0) +
    if y < x ∧ x < x' ∧ x' < y' then sgn sa * sgn sb * d else 0

theorem pairDeg_eq_PDn (L : Fin n → Bool × I) (σ : Perm (Fin n)) (a b : Fin n) :
    pairDeg C L σ a b = PDn a.val b.val (σ a).val (σ b).val (L a).1 (L b).1
      (C.dot (L a).2 (L b).2) := by
  simp only [pairDeg, PDn, Fin.lt_iff_val_lt_val]

/-- The core case analysis: exchanging the adjacent endpoints `P, P + 1` of two different cups
`{P, e}` (with `+` at `P`) and `{P + 1, f}` (with `-` at `P + 1`) preserves the symmetrised
interaction of the two cups. -/
theorem PDn_swap_core (P e f : ℕ) (d : ℤ) :
    (PDn (P + 1) P e f true false d + PDn P (P + 1) f e false true d =
      PDn P (P + 1) e f true false d + PDn (P + 1) P f e false true d) ∧
    (PDn (P + 1) f e P true true d + PDn f (P + 1) P e true true d =
      PDn P f e (P + 1) true true d + PDn f P (P + 1) e true true d) ∧
    (PDn e P (P + 1) f false false d + PDn P e f (P + 1) false false d =
      PDn e (P + 1) P f false false d + PDn (P + 1) e f P false false d) ∧
    (PDn e f (P + 1) P false true d + PDn f e P (P + 1) true false d =
      PDn e f P (P + 1) false true d + PDn f e (P + 1) P true false d) := by
  simp only [PDn, sgn_true, sgn_false]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> split_ifs <;> first | omega | simp_all

variable (hp' : p'.val = p.val + 1) (hsp : (L p).1 = true) (hsp' : (L p').1 = false)
  (hne : σ p ≠ p')

include hp' hsp hsp' hne in
/-- The symmetrised interaction of the cups at `a` and `b` in the bad case (the cup of `a` contains
`p`, that of `b` contains `p + 1`). -/
theorem pair_swap_bad (h : IsMatching L σ) {a b : Fin n} (ha : a = p ∨ σ a = p)
    (hb : b = p' ∨ σ b = p') :
    PDn (swap p p' a).val (swap p p' b).val (swap p p' (σ a)).val (swap p p' (σ b)).val
        (L a).1 (L b).1 (C.dot (L a).2 (L b).2) +
      PDn (swap p p' b).val (swap p p' a).val (swap p p' (σ b)).val (swap p p' (σ a)).val
        (L b).1 (L a).1 (C.dot (L b).2 (L a).2) =
    PDn a.val b.val (σ a).val (σ b).val (L a).1 (L b).1 (C.dot (L a).2 (L b).2) +
      PDn b.val a.val (σ b).val (σ a).val (L b).1 (L a).1 (C.dot (L b).2 (L a).2) := by
  have hσp : σ p ≠ p := h.ne p
  have hσ'p' : σ p' ≠ p' := h.ne p'
  have hσ'p : σ p' ≠ p := fun e => hne (by rw [← e, h.invol])
  have t1 : swap p p' p = p' := swap_apply_left _ _
  have t2 : swap p p' p' = p := swap_apply_right _ _
  have t3 : swap p p' (σ p) = σ p := swap_apply_of_ne_of_ne hσp hne
  have t4 : swap p p' (σ p') = σ p' := swap_apply_of_ne_of_ne hσ'p hσ'p'
  have s1 : (L (σ p)).1 = false := by rw [h.sign, hsp]; rfl
  have s2 : (L (σ p')).1 = true := by rw [h.sign, hsp']; rfl
  have c1 : (L (σ p)).2 = (L p).2 := h.col p
  have c2 : (L (σ p')).2 = (L p').2 := h.col p'
  have hd : C.dot (L p').2 (L p).2 = C.dot (L p).2 (L p').2 := C.symm _ _
  have core := PDn_swap_core p.val (σ p).val (σ p').val (C.dot (L p).2 (L p').2)
  rw [← hp'] at core
  have ha' : a = p ∨ a = σ p := ha.imp id fun e => by rw [← e, h.invol]
  have hb' : b = p' ∨ b = σ p' := hb.imp id fun e => by rw [← e, h.invol]
  rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl <;>
    simp only [h.invol, t1, t2, t3, t4, hsp, hsp', s1, s2, c1, c2, hd]
  · exact core.1
  · exact core.2.1
  · exact core.2.2.1
  · exact core.2.2.2

include hp' hsp hsp' hne in
theorem pair_swap_pt (h : IsMatching L σ) (a b : Fin n) :
    PDn (swap p p' a).val (swap p p' b).val (swap p p' (σ a)).val (swap p p' (σ b)).val
        (L a).1 (L b).1 (C.dot (L a).2 (L b).2) +
      PDn (swap p p' b).val (swap p p' a).val (swap p p' (σ b)).val (swap p p' (σ a)).val
        (L b).1 (L a).1 (C.dot (L b).2 (L a).2) =
    PDn a.val b.val (σ a).val (σ b).val (L a).1 (L b).1 (C.dot (L a).2 (L b).2) +
      PDn b.val a.val (σ b).val (σ a).val (L b).1 (L a).1 (C.dot (L b).2 (L a).2) := by
  by_cases bad1 : (a = p ∨ σ a = p) ∧ (b = p' ∨ σ b = p')
  · exact pair_swap_bad C hp' hsp hsp' hne h bad1.1 bad1.2
  by_cases bad2 : (b = p ∨ σ b = p) ∧ (a = p' ∨ σ a = p')
  · rw [add_comm, add_comm (PDn a.val _ _ _ _ _ _)]
    exact pair_swap_bad C hp' hsp hsp' hne h bad2.1 bad2.2
  -- no pair of the four endpoints is `{p, p + 1}`: the swap preserves all comparisons
  have arc : ∀ x, ¬ (x = p ∧ σ x = p') ∧ ¬ (x = p' ∧ σ x = p) := fun x =>
    ⟨fun ⟨e1, e2⟩ => hne (e1 ▸ e2), fun ⟨e1, e2⟩ => hne (by rw [← e2, h.invol, e1])⟩
  have arc' : ∀ x, ¬ (σ x = p ∧ x = p') ∧ ¬ (σ x = p' ∧ x = p) := fun x =>
    ⟨fun ⟨e1, e2⟩ => (arc x).2 ⟨e2, e1⟩, fun ⟨e1, e2⟩ => (arc x).1 ⟨e2, e1⟩⟩
  have key : ∀ x y : Fin n, ¬ (x = p ∧ y = p') → ¬ (x = p' ∧ y = p) →
      ((swap p p' x).val < (swap p p' y).val ↔ x.val < y.val) := fun x y h1 h2 => by
    rw [← Fin.lt_iff_val_lt_val, ← Fin.lt_iff_val_lt_val]; exact swap_lt_iff hp' h1 h2
  have k1 := key a b (fun e => bad1 ⟨Or.inl e.1, Or.inl e.2⟩) (fun e => bad2 ⟨Or.inl e.2, Or.inl e.1⟩)
  have k2 := key b a (fun e => bad2 ⟨Or.inl e.1, Or.inl e.2⟩) (fun e => bad1 ⟨Or.inl e.2, Or.inl e.1⟩)
  have k3 := key b (σ a) (fun e => bad2 ⟨Or.inl e.1, Or.inr e.2⟩) (fun e => bad1 ⟨Or.inr e.2, Or.inl e.1⟩)
  have k4 := key (σ a) b (fun e => bad1 ⟨Or.inr e.1, Or.inl e.2⟩) (fun e => bad2 ⟨Or.inl e.2, Or.inr e.1⟩)
  have k5 := key (σ a) (σ b) (fun e => bad1 ⟨Or.inr e.1, Or.inr e.2⟩)
    (fun e => bad2 ⟨Or.inr e.2, Or.inr e.1⟩)
  have k6 := key (σ b) (σ a) (fun e => bad2 ⟨Or.inr e.1, Or.inr e.2⟩)
    (fun e => bad1 ⟨Or.inr e.2, Or.inr e.1⟩)
  have k7 := key a (σ a) (arc a).1 (arc a).2
  have k8 := key (σ a) a (arc' a).1 (arc' a).2
  have k9 := key b (σ b) (arc b).1 (arc b).2
  have k10 := key (σ b) b (arc' b).1 (arc' b).2
  have k11 := key a (σ b) (fun e => bad1 ⟨Or.inl e.1, Or.inr e.2⟩) (fun e => bad2 ⟨Or.inr e.2, Or.inl e.1⟩)
  have k12 := key (σ b) a (fun e => bad2 ⟨Or.inr e.1, Or.inl e.2⟩) (fun e => bad1 ⟨Or.inl e.2, Or.inr e.1⟩)
  simp only [PDn, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12]

include hp' hsp hsp' hne in
/-- **Exchanging adjacent endpoints `(+i)(-j)` not joined to each other preserves the degree**
(KL III §2.2, proofs of the second and third lemmas following Lemma 2.8: "the bijection …
preserves the degree of a diagram, since the degree of a balanced crossing is zero"). -/
theorem mdeg_swap (h : IsMatching L σ) (ℓ : I → ℤ) :
    mdeg C ℓ (L ∘ swap p p') (swap p p' * σ * swap p p') = mdeg C ℓ L σ := by
  set τ := swap p p' with hτdef
  have hτ : ∀ x, τ (τ x) = x := swap_apply_self _ _
  have h' := h.conj τ hτ
  rw [mdeg_eq_alt C h' ℓ, mdeg_eq_alt C h ℓ]
  have hσ' : ∀ x, (τ * σ * τ) (τ x) = τ (σ x) := fun x => by simp [hτ]
  have hL' : ∀ x, (L ∘ τ) (τ x) = L x := fun x => by simp [hτ]
  have harc : ∀ a, τ a < τ (σ a) ↔ a < σ a := fun a =>
    swap_lt_iff hp' (fun ⟨e1, e2⟩ => hne (e1 ▸ e2))
      (fun ⟨e1, e2⟩ => hne (by rw [← e2, h.invol, e1]))
  congr 1
  · rw [← Equiv.sum_comp τ]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [hσ', harc, arcDeg, hL']
  · have e1 : ∑ a, ∑ b, pairDeg C (L ∘ τ) (τ * σ * τ) a b =
        ∑ a, ∑ b, PDn (τ a).val (τ b).val (τ (σ a)).val (τ (σ b)).val (L a).1 (L b).1
          (C.dot (L a).2 (L b).2) := by
      rw [← Equiv.sum_comp τ]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Equiv.sum_comp τ]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [pairDeg_eq_PDn, hσ', hσ', hL', hL']
    have e2 : ∑ a, ∑ b, pairDeg C L σ a b =
        ∑ a, ∑ b, PDn a.val b.val (σ a).val (σ b).val (L a).1 (L b).1 (C.dot (L a).2 (L b).2) :=
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => pairDeg_eq_PDn C L σ a b
    rw [e1, e2]
    -- symmetrise
    have sym : ∀ F : Fin n → Fin n → ℤ, 2 * ∑ a, ∑ b, F a b = ∑ a, ∑ b, (F a b + F b a) :=
      fun F => by
        rw [two_mul]
        conv_lhs => arg 2; rw [Finset.sum_comm]
        simp only [Finset.sum_add_distrib]
    have := sym (fun a b => PDn (τ a).val (τ b).val (τ (σ a)).val (τ (σ b)).val (L a).1 (L b).1
      (C.dot (L a).2 (L b).2))
    rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      pair_swap_pt C hp' hsp hsp' hne h a b, ← sym] at this
    exact (mul_right_injective₀ two_ne_zero this).symm ▸ rfl

include hp' hne in
theorem arcProd_swap (h : IsMatching L σ) {M : Type*} [CommMonoid M] (w : I → M) :
    arcProd w (L ∘ swap p p') (swap p p' * σ * swap p p') = arcProd w L σ := by
  have hτ : ∀ x, swap p p' (swap p p' x) = x := swap_apply_self _ _
  unfold arcProd
  rw [← Equiv.prod_comp (swap p p')]
  refine Finset.prod_congr rfl fun a _ => ?_
  have harc : swap p p' a < swap p p' (σ a) ↔ a < σ a :=
    swap_lt_iff hp' (fun ⟨e1, e2⟩ => hne (e1 ▸ e2))
      (fun ⟨e1, e2⟩ => hne (by rw [← e2, h.invol, e1]))
  simp [hτ, harc]

end Swap

/-! ### Removing a cup joining two adjacent endpoints -/

section Remove

variable {m : ℕ} (p : ℕ) (hp : p ≤ m)

/-- The endpoint `p` of `Fin (m + 2)`. -/
def rmP0 : Fin (m + 2) := ⟨p, by omega⟩

/-- The endpoint `p + 1` of `Fin (m + 2)`. -/
def rmP1 : Fin (m + 2) := ⟨p + 1, by omega⟩

/-- The order-preserving embedding `Fin m → Fin (m + 2)` missing `p` and `p + 1`. -/
def rmEmb (x : Fin m) : Fin (m + 2) :=
  ⟨if x.val < p then x.val else x.val + 2, by split_ifs <;> omega⟩

/-- A left inverse of `rmEmb` (for `m > 0`). -/
def rmUnemb (hm : 0 < m) (y : Fin (m + 2)) : Fin m :=
  ⟨if y.val < p then y.val else y.val - 2, by split_ifs <;> omega⟩

theorem rmEmb_val (x : Fin m) : (rmEmb p x).val = if x.val < p then x.val else x.val + 2 := rfl

theorem rmEmb_lt_iff (x y : Fin m) : rmEmb p x < rmEmb p y ↔ x < y := by
  simp only [Fin.lt_iff_val_lt_val, rmEmb_val]
  split_ifs <;> omega

theorem rmEmb_injective : Function.Injective (rmEmb p (m := m)) := fun x y h => by
  have := congrArg Fin.val h
  simp only [rmEmb_val] at this
  ext; split_ifs at this <;> omega

theorem rmEmb_ne_P0 (x : Fin m) : rmEmb p x ≠ rmP0 p hp := fun h => by
  have := congrArg Fin.val h; simp only [rmEmb_val, rmP0] at this; split_ifs at this <;> omega

theorem rmEmb_ne_P1 (x : Fin m) : rmEmb p x ≠ rmP1 p hp := fun h => by
  have := congrArg Fin.val h; simp only [rmEmb_val, rmP1] at this; split_ifs at this <;> omega

theorem rmUnemb_emb (hm : 0 < m) (x : Fin m) : rmUnemb p hp hm (rmEmb p x) = x := by
  ext; simp only [rmUnemb, rmEmb_val]; split_ifs <;> omega

theorem rmEmb_unemb (hm : 0 < m) {y : Fin (m + 2)} (h0 : y ≠ rmP0 p hp) (h1 : y ≠ rmP1 p hp) :
    rmEmb p (rmUnemb p hp hm y) = y := by
  have h0' : y.val ≠ p := fun e => h0 (Fin.ext e)
  have h1' : y.val ≠ p + 1 := fun e => h1 (Fin.ext e)
  ext; simp only [rmUnemb, rmEmb_val]; split_ifs <;> omega

theorem rmP0_lt_P1 : rmP0 p hp < rmP1 p hp := by
  simp [Fin.lt_iff_val_lt_val, rmP0, rmP1]

theorem rmP0_ne_P1 : rmP0 p hp ≠ rmP1 p hp := (rmP0_lt_P1 p hp).ne

theorem exists_emb {y : Fin (m + 2)} (h0 : y ≠ rmP0 p hp) (h1 : y ≠ rmP1 p hp) :
    ∃ x, rmEmb p x = y := by
  have hm : 0 < m := by
    have h0' : y.val ≠ p := fun e => h0 (Fin.ext e)
    have h1' : y.val ≠ p + 1 := fun e => h1 (Fin.ext e)
    have := y.isLt; omega
  exact ⟨rmUnemb p hp hm y, rmEmb_unemb p hp hm h0 h1⟩

/-- `∑_{y : Fin (m + 2)} f y = f p + f (p + 1) + ∑_{x : Fin m} f (emb x)`. -/
theorem sum_rm {R : Type*} [AddCommMonoid R] (f : Fin (m + 2) → R) :
    ∑ y, f y = f (rmP0 p hp) + f (rmP1 p hp) + ∑ x, f (rmEmb p x) := by
  have huniv : (univ : Finset (Fin (m + 2))) =
      insert (rmP0 p hp) (insert (rmP1 p hp) (univ.map ⟨rmEmb p, rmEmb_injective p⟩)) := by
    ext y
    simp only [mem_univ, mem_insert, mem_map, Function.Embedding.coeFn_mk, true_and, true_iff]
    by_cases h0 : y = rmP0 p hp
    · exact Or.inl h0
    by_cases h1 : y = rmP1 p hp
    · exact Or.inr (Or.inl h1)
    exact Or.inr (Or.inr (exists_emb p hp h0 h1))
  rw [huniv, sum_insert, sum_insert, sum_map, add_assoc]
  · rfl
  · simp only [mem_map, Function.Embedding.coeFn_mk, not_exists, not_and]
    exact fun x _ => rmEmb_ne_P1 p hp x
  · simp only [mem_insert, mem_map, Function.Embedding.coeFn_mk, not_or, not_exists, not_and]
    exact ⟨rmP0_ne_P1 p hp, fun x _ => rmEmb_ne_P0 p hp x⟩

theorem prod_rm {M : Type*} [CommMonoid M] (f : Fin (m + 2) → M) :
    ∏ y, f y = f (rmP0 p hp) * f (rmP1 p hp) * ∏ x, f (rmEmb p x) := by
  have := sum_rm p hp (R := Additive M) (fun y => Additive.ofMul (f y))
  simpa [← ofMul_prod] using this

end Remove

section RemoveArc

variable {m : ℕ} {p : ℕ} (hp : p ≤ m) {L : Fin (m + 2) → Bool × I}

/-- The restriction of a pairing `σ` with `σ p = p + 1` to the other endpoints. -/
def rmRes (σ : Perm (Fin (m + 2))) (hσ : IsMatching L σ) (h01 : σ (rmP0 p hp) = rmP1 p hp) :
    Perm (Fin m) :=
  Function.Involutive.toPerm (fun x => rmUnemb p hp x.pos (σ (rmEmb p x))) (fun x => by
    have hne : ∀ x : Fin m, σ (rmEmb p x) ≠ rmP0 p hp ∧ σ (rmEmb p x) ≠ rmP1 p hp := fun x =>
      ⟨fun e => rmEmb_ne_P1 p hp x (by rw [← hσ.invol (rmEmb p x), e, h01]),
       fun e => rmEmb_ne_P0 p hp x (by rw [← hσ.invol (rmEmb p x), e, ← h01, hσ.invol])⟩
    simp only
    rw [rmEmb_unemb p hp _ (hne x).1 (hne x).2, hσ.invol, rmUnemb_emb])

theorem rmEmb_rmRes (σ : Perm (Fin (m + 2))) (hσ : IsMatching L σ)
    (h01 : σ (rmP0 p hp) = rmP1 p hp) (x : Fin m) :
    rmEmb p (rmRes hp σ hσ h01 x) = σ (rmEmb p x) := by
  have hne : σ (rmEmb p x) ≠ rmP0 p hp ∧ σ (rmEmb p x) ≠ rmP1 p hp :=
    ⟨fun e => rmEmb_ne_P1 p hp x (by rw [← hσ.invol (rmEmb p x), e, h01]),
     fun e => rmEmb_ne_P0 p hp x (by rw [← hσ.invol (rmEmb p x), e, ← h01, hσ.invol])⟩
  show rmEmb p (rmUnemb p hp x.pos (σ (rmEmb p x))) = _
  exact rmEmb_unemb p hp x.pos hne.1 hne.2

/-- The extension of an involution of `Fin m` by the cup `(p, p + 1)`. -/
def rmExtFun (τ : Perm (Fin m)) (y : Fin (m + 2)) : Fin (m + 2) :=
  if y = rmP0 p hp then rmP1 p hp else if y = rmP1 p hp then rmP0 p hp else
    if hm : 0 < m then rmEmb p (τ (rmUnemb p hp hm y)) else y

theorem rmExtFun_emb (τ : Perm (Fin m)) (x : Fin m) :
    rmExtFun hp τ (rmEmb p x) = rmEmb p (τ x) := by
  rw [rmExtFun, if_neg (rmEmb_ne_P0 p hp x), if_neg (rmEmb_ne_P1 p hp x), dif_pos x.pos,
    rmUnemb_emb]

theorem rmExtFun_P0 (τ : Perm (Fin m)) : rmExtFun hp τ (rmP0 p hp) = rmP1 p hp := by
  rw [rmExtFun, if_pos rfl]

theorem rmExtFun_P1 (τ : Perm (Fin m)) : rmExtFun hp τ (rmP1 p hp) = rmP0 p hp := by
  rw [rmExtFun, if_neg (rmP0_ne_P1 p hp).symm, if_pos rfl]

/-- The value of `rmExtFun` on any endpoint, by cases. -/
theorem rmExtFun_cases (τ : Perm (Fin m)) (y : Fin (m + 2)) :
    (y = rmP0 p hp ∧ rmExtFun hp τ y = rmP1 p hp) ∨ (y = rmP1 p hp ∧ rmExtFun hp τ y = rmP0 p hp) ∨
      ∃ x, y = rmEmb p x ∧ rmExtFun hp τ y = rmEmb p (τ x) := by
  by_cases h0 : y = rmP0 p hp
  · exact Or.inl ⟨h0, h0 ▸ rmExtFun_P0 hp τ⟩
  by_cases h1 : y = rmP1 p hp
  · exact Or.inr (Or.inl ⟨h1, h1 ▸ rmExtFun_P1 hp τ⟩)
  obtain ⟨x, rfl⟩ := exists_emb p hp h0 h1
  exact Or.inr (Or.inr ⟨x, rfl, rmExtFun_emb hp τ x⟩)

theorem rmExtFun_invol (τ : Perm (Fin m)) (hτ : ∀ x, τ (τ x) = x) (y : Fin (m + 2)) :
    rmExtFun hp τ (rmExtFun hp τ y) = y := by
  rcases rmExtFun_cases hp τ y with ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨x, rfl, e⟩
  · rw [e, rmExtFun_P1]
  · rw [e, rmExtFun_P0]
  · rw [e, rmExtFun_emb, hτ]

/-- The extension, as a permutation (for `τ` an involution). -/
def rmExt (τ : Perm (Fin m)) (hτ : ∀ x, τ (τ x) = x) : Perm (Fin (m + 2)) :=
  Function.Involutive.toPerm (rmExtFun hp τ) (rmExtFun_invol hp τ hτ)

theorem rmExt_apply (τ : Perm (Fin m)) (hτ : ∀ x, τ (τ x) = x) (y : Fin (m + 2)) :
    rmExt hp τ hτ y = rmExtFun hp τ y := rfl

variable (hc : (L (rmP1 p hp)).2 = (L (rmP0 p hp)).2) (hs : (L (rmP1 p hp)).1 = !(L (rmP0 p hp)).1)

theorem isMatching_rmRes (σ : Perm (Fin (m + 2))) (hσ : IsMatching L σ)
    (h01 : σ (rmP0 p hp) = rmP1 p hp) : IsMatching (L ∘ rmEmb p) (rmRes hp σ hσ h01) := by
  intro x
  have e := rmEmb_rmRes hp σ hσ h01
  refine ⟨?_, ?_, ?_⟩
  · exact rmEmb_injective p (by rw [e, e, hσ.invol])
  · simp only [Function.comp_apply, e, hσ.col]
  · simp only [Function.comp_apply, e, hσ.sign]

include hc hs in
theorem isMatching_rmExt (τ : Perm (Fin m)) (hτ : IsMatching (L ∘ rmEmb p) τ) :
    IsMatching L (rmExt hp τ hτ.invol) := by
  intro y
  refine ⟨rmExtFun_invol hp τ hτ.invol y, ?_⟩
  rcases rmExtFun_cases hp τ y with ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨x, rfl, e⟩ <;> rw [rmExt_apply, e]
  · exact ⟨hc, hs⟩
  · refine ⟨hc.symm, ?_⟩; rw [hs]; simp
  · exact ⟨hτ.col x, hτ.sign x⟩

theorem rmExt_rmRes (σ : Perm (Fin (m + 2))) (hσ : IsMatching L σ)
    (h01 : σ (rmP0 p hp) = rmP1 p hp) (hτ : ∀ x, rmRes hp σ hσ h01 (rmRes hp σ hσ h01 x) = x) :
    rmExt hp (rmRes hp σ hσ h01) hτ = σ := by
  ext1 y
  rw [rmExt_apply]
  rcases rmExtFun_cases hp (rmRes hp σ hσ h01) y with ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨x, rfl, e⟩ <;> rw [e]
  · exact h01.symm
  · rw [← h01, hσ.invol]
  · rw [rmEmb_rmRes]

theorem rmRes_rmExt (τ : Perm (Fin m)) (hτ : ∀ x, τ (τ x) = x)
    (hσ : IsMatching L (rmExt hp τ hτ)) (h01 : rmExt hp τ hτ (rmP0 p hp) = rmP1 p hp) :
    rmRes hp (rmExt hp τ hτ) hσ h01 = τ := by
  ext1 x
  exact rmEmb_injective p (by rw [rmEmb_rmRes, rmExt_apply, rmExtFun_emb])

include hc hs in
/-- The weight of the removed cup does not change the region weights of the other cups. -/
theorem wR_rmEmb (ℓ : I → ℤ) (c : Fin m) (i : I) :
    wR C ℓ L (rmEmb p c) i = wR C ℓ (L ∘ rmEmb p) c i := by
  simp only [wR, Finset.sum_filter]
  rw [sum_rm p hp]
  congr 1
  have h01 : (rmEmb p c < rmP0 p hp ↔ rmEmb p c < rmP1 p hp) := by
    simp only [Fin.lt_iff_val_lt_val, rmEmb_val, rmP0, rmP1]; split_ifs <;> omega
  have hcancel : (if rmEmb p c < rmP0 p hp then sgn (L (rmP0 p hp)).1 * A C i (L (rmP0 p hp)).2
      else 0) + (if rmEmb p c < rmP1 p hp then sgn (L (rmP1 p hp)).1 * A C i (L (rmP1 p hp)).2
      else 0) = 0 := by
    simp only [← h01, hs, hc, sgn_not]; split_ifs <;> ring
  rw [hcancel, zero_add]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [rmEmb_lt_iff, Function.comp_apply]

include hc hs in
/-- **Removing the cup `(p, p + 1)`**: `deg(D_σ) = deg(D_{σ|}) + deg(cup (p, p + 1))`. -/
theorem mdeg_rmRes (ℓ : I → ℤ) (σ : Perm (Fin (m + 2))) (hσ : IsMatching L σ)
    (h01 : σ (rmP0 p hp) = rmP1 p hp) :
    mdeg C ℓ L σ = mdeg C ℓ (L ∘ rmEmb p) (rmRes hp σ hσ h01) +
      cupDeg C ℓ L (rmP0 p hp) (rmP1 p hp) := by
  have e := rmEmb_rmRes hp σ hσ h01
  have h10 : σ (rmP1 p hp) = rmP0 p hp := by rw [← h01, hσ.invol]
  have hlt := rmP0_lt_P1 p hp
  have v0 : (rmP0 p hp).val = p := rfl
  have v1 : (rmP1 p hp).val = p + 1 := rfl
  unfold mdeg
  rw [sum_rm p hp, sum_rm p hp]
  simp only [h01, h10, if_pos hlt, if_neg (not_lt.2 hlt.le)]
  -- the rows of `p` and `p + 1` in the crossing sum vanish
  have r0 : ∑ b, (if rmP0 p hp < b ∧ b < rmP1 p hp ∧ rmP1 p hp < σ b then
      crossDeg C L (rmP0 p hp) b else 0) = 0 :=
    Finset.sum_eq_zero fun b _ => if_neg fun h => by
      rw [Fin.lt_iff_val_lt_val, Fin.lt_iff_val_lt_val] at h; omega
  have r1 : ∑ b, (if rmP1 p hp < b ∧ b < rmP0 p hp ∧ rmP0 p hp < σ b then
      crossDeg C L (rmP1 p hp) b else 0) = 0 :=
    Finset.sum_eq_zero fun b _ => if_neg fun h => by
      rw [Fin.lt_iff_val_lt_val, Fin.lt_iff_val_lt_val] at h; omega
  rw [r0, r1]
  have rows : ∀ x : Fin m, (∑ b, if rmEmb p x < b ∧ b < σ (rmEmb p x) ∧ σ (rmEmb p x) < σ b then
      crossDeg C L (rmEmb p x) b else 0) =
      ∑ y, if x < y ∧ y < rmRes hp σ hσ h01 x ∧ rmRes hp σ hσ h01 x < rmRes hp σ hσ h01 y then
        crossDeg C (L ∘ rmEmb p) x y else 0 := fun x => by
    rw [sum_rm p hp, h01, h10, ← e]
    have z0 : ¬ (rmEmb p x < rmP0 p hp ∧ rmP0 p hp < rmEmb p (rmRes hp σ hσ h01 x) ∧
        rmEmb p (rmRes hp σ hσ h01 x) < rmP1 p hp) := fun h => by
      simp only [Fin.lt_iff_val_lt_val] at h; omega
    have z1 : ¬ (rmEmb p x < rmP1 p hp ∧ rmP1 p hp < rmEmb p (rmRes hp σ hσ h01 x) ∧
        rmEmb p (rmRes hp σ hσ h01 x) < rmP0 p hp) := fun h => by
      simp only [Fin.lt_iff_val_lt_val] at h; omega
    rw [if_neg z0, if_neg z1, zero_add, zero_add]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [← e, rmEmb_lt_iff]
    rfl
  simp only [rows, add_zero, zero_add]
  have cups : ∀ x : Fin m, (if rmEmb p x < σ (rmEmb p x) then
      cupDeg C ℓ L (rmEmb p x) (σ (rmEmb p x)) else 0) =
      if x < rmRes hp σ hσ h01 x then cupDeg C ℓ (L ∘ rmEmb p) x (rmRes hp σ hσ h01 x) else 0 :=
    fun x => by
      simp only [← e, rmEmb_lt_iff, cupDeg, wR_rmEmb C hp hc hs]
      rfl
  simp only [cups]
  ring

theorem arcProd_rmRes {M : Type*} [CommMonoid M] (w : I → M) (σ : Perm (Fin (m + 2)))
    (hσ : IsMatching L σ) (h01 : σ (rmP0 p hp) = rmP1 p hp) :
    arcProd w L σ = w (L (rmP0 p hp)).2 * arcProd w (L ∘ rmEmb p) (rmRes hp σ hσ h01) := by
  have e := rmEmb_rmRes hp σ hσ h01
  have h10 : σ (rmP1 p hp) = rmP0 p hp := by rw [← h01, hσ.invol]
  have hlt := rmP0_lt_P1 p hp
  unfold arcProd
  rw [prod_rm p hp, h01, h10, if_pos hlt, if_neg (not_lt.2 hlt.le), mul_one]
  congr 1
  refine Finset.prod_congr rfl fun x _ => ?_
  simp only [← e, rmEmb_lt_iff]; rfl

include hc hs in
/-- **The pairings in which `p` and `p + 1` are joined** correspond to the pairings of the word
with these two endpoints removed (KL III §2.2, class (3) in the proof of the third lemma after
Lemma 2.8). -/
theorem sum_rm_matchings {M R : Type*} [CommMonoid M] [AddCommMonoid R] (G : ℤ → M → R)
    (ℓ : I → ℤ) (w : I → M) :
    ∑ σ ∈ (matchings L).filter (fun σ => σ (rmP0 p hp) = rmP1 p hp),
        G (mdeg C ℓ L σ) (arcProd w L σ) =
      ∑ τ ∈ matchings (L ∘ rmEmb p), G (mdeg C ℓ (L ∘ rmEmb p) τ +
        cupDeg C ℓ L (rmP0 p hp) (rmP1 p hp)) (w (L (rmP0 p hp)).2 * arcProd w (L ∘ rmEmb p) τ) := by
  refine Finset.sum_bij'
    (fun σ hσ => rmRes hp σ (mem_matchings.1 (mem_filter.1 hσ).1) (mem_filter.1 hσ).2)
    (fun τ hτ => rmExt hp τ (mem_matchings.1 hτ).invol) (fun σ hσ => ?_) (fun τ hτ => ?_)
    (fun σ hσ => ?_) (fun τ hτ => ?_) (fun σ hσ => ?_)
  · exact mem_matchings.2 (isMatching_rmRes hp σ _ _)
  · refine mem_filter.2 ⟨mem_matchings.2 (isMatching_rmExt hp hc hs τ (mem_matchings.1 hτ)), ?_⟩
    rw [rmExt_apply, rmExtFun_P0]
  · exact rmExt_rmRes hp σ _ _ _
  · exact rmRes_rmExt hp τ _ _ _
  · dsimp only
    rw [mdeg_rmRes C hp hc hs, arcProd_rmRes hp]

end RemoveArc

/-! ### Words of the form `(-c)(+b)` -/

section Block

variable {m₁ m₂ : ℕ}

/-- The word `(-c₁, …, -c_{m₁}, +b₁, …, +b_{m₂})`. -/
def blockWord (cc : Fin m₁ → I) (bb : Fin m₂ → I) : Fin (m₁ + m₂) → Bool × I :=
  Fin.append (fun k => (false, cc k)) (fun x => (true, bb x))

@[simp] theorem blockWord_left (cc : Fin m₁ → I) (bb : Fin m₂ → I) (k : Fin m₁) :
    blockWord cc bb (Fin.castAdd m₂ k) = (false, cc k) := Fin.append_left _ _ _

@[simp] theorem blockWord_right (cc : Fin m₁ → I) (bb : Fin m₂ → I) (x : Fin m₂) :
    blockWord cc bb (Fin.natAdd m₁ x) = (true, bb x) := Fin.append_right _ _ _

theorem castAdd_lt_natAdd (k : Fin m₁) (x : Fin m₂) : Fin.castAdd m₂ k < Fin.natAdd m₁ x := by
  simp only [Fin.lt_iff_val_lt_val, Fin.coe_castAdd, Fin.coe_natAdd]; omega

/-- A pairing of `(-c)(+b)` joins each `-` to a `+`; so there are none unless `|c| = |b|`. -/
theorem card_eq_of_isMatching {cc : Fin m₁ → I} {bb : Fin m₂ → I} {σ : Perm (Fin (m₁ + m₂))}
    (h : IsMatching (blockWord cc bb) σ) : m₁ = m₂ := by
  have left : ∀ k : Fin m₁, m₁ ≤ (σ (Fin.castAdd m₂ k)).val := fun k => by
    by_contra hk
    have := h.sign (Fin.castAdd m₂ k)
    have e : σ (Fin.castAdd m₂ k) = Fin.castAdd m₂ ⟨_, not_le.1 hk⟩ := Fin.ext rfl
    rw [e, blockWord_left, blockWord_left] at this
    simp at this
  have right : ∀ x : Fin m₂, (σ (Fin.natAdd m₁ x)).val < m₁ := fun x => by
    by_contra hx
    have := h.sign (Fin.natAdd m₁ x)
    have hlt := (σ (Fin.natAdd m₁ x)).isLt
    have e : σ (Fin.natAdd m₁ x) = Fin.natAdd m₁ ⟨(σ (Fin.natAdd m₁ x)).val - m₁, by omega⟩ :=
      Fin.ext (by simp only [Fin.coe_natAdd]; omega)
    rw [e, blockWord_right, blockWord_right] at this
    simp at this
  have h1 : m₁ ≤ m₂ := by
    have := Fintype.card_le_of_injective
      (fun k : Fin m₁ => (⟨(σ (Fin.castAdd m₂ k)).val - m₁,
        by have := (σ (Fin.castAdd m₂ k)).isLt; have := left k; omega⟩ : Fin m₂))
        (fun k k' e => by
        have e' := congrArg Fin.val e
        simp only at e'
        have := left k; have := left k'
        exact Fin.castAdd_inj.1 (σ.injective (Fin.ext (by omega))))
    simpa using this
  have h2 : m₂ ≤ m₁ := by
    have := Fintype.card_le_of_injective
      (fun x : Fin m₂ => (⟨(σ (Fin.natAdd m₁ x)).val, right x⟩ : Fin m₁)) (fun x x' e => by
        have e' := congrArg Fin.val e
        exact (Fin.natAdd_inj m₁).1 (σ.injective (Fin.ext e')))
    simpa using this
  omega

variable {m : ℕ}

/-- The pairing of `(-c)(+b)` given by a permutation `w` (the `+b_x` is joined to
`-c_{m - 1 - w x}`, i.e. to the entry `w x` of the reversed sequence `c^{rev}`). -/
def blockFun (w : Perm (Fin m)) : Fin (m + m) → Fin (m + m) :=
  Fin.addCases (fun k => Fin.natAdd m (w.symm (Fin.rev k))) (fun x => Fin.castAdd m (Fin.rev (w x)))

@[simp] theorem blockFun_left (w : Perm (Fin m)) (k : Fin m) :
    blockFun w (Fin.castAdd m k) = Fin.natAdd m (w.symm (Fin.rev k)) := Fin.addCases_left _

@[simp] theorem blockFun_right (w : Perm (Fin m)) (x : Fin m) :
    blockFun w (Fin.natAdd m x) = Fin.castAdd m (Fin.rev (w x)) := Fin.addCases_right _

theorem blockFun_invol (w : Perm (Fin m)) (z : Fin (m + m)) : blockFun w (blockFun w z) = z := by
  refine Fin.addCases (fun k => ?_) (fun x => ?_) z
  · rw [blockFun_left, blockFun_right, Equiv.apply_symm_apply, Fin.rev_rev]
  · rw [blockFun_right, blockFun_left, Fin.rev_rev, Equiv.symm_apply_apply]

/-- The pairing `σ_w`. -/
def blockPerm (w : Perm (Fin m)) : Perm (Fin (m + m)) :=
  Function.Involutive.toPerm (blockFun w) (blockFun_invol w)

@[simp] theorem blockPerm_left (w : Perm (Fin m)) (k : Fin m) :
    blockPerm w (Fin.castAdd m k) = Fin.natAdd m (w.symm (Fin.rev k)) := blockFun_left w k

@[simp] theorem blockPerm_right (w : Perm (Fin m)) (x : Fin m) :
    blockPerm w (Fin.natAdd m x) = Fin.castAdd m (Fin.rev (w x)) := blockFun_right w x

variable {cc bb : Fin m → I}

theorem isMatching_blockPerm {w : Perm (Fin m)} (hw : ∀ x, cc (Fin.rev (w x)) = bb x) :
    IsMatching (blockWord cc bb) (blockPerm w) := by
  intro z
  refine ⟨blockFun_invol w z, ?_⟩
  refine Fin.addCases (fun k => ?_) (fun x => ?_) z
  · rw [blockPerm_left, blockWord_right, blockWord_left, ← hw, Equiv.apply_symm_apply,
      Fin.rev_rev]
    exact ⟨rfl, rfl⟩
  · rw [blockPerm_right, blockWord_right, blockWord_left, hw]
    exact ⟨rfl, rfl⟩

theorem blockPerm_injective : Function.Injective (blockPerm (m := m)) := fun w w' h => by
  ext x
  have := congrArg (fun σ : Perm (Fin (m + m)) => σ (Fin.natAdd m x)) h
  simp only [blockPerm_right] at this
  exact congrArg Fin.val (Fin.rev_injective (Fin.castAdd_inj.1 this))

theorem exists_blockPerm {σ : Perm (Fin (m + m))} (h : IsMatching (blockWord cc bb) σ) :
    ∃ w : Perm (Fin m), (∀ x, cc (Fin.rev (w x)) = bb x) ∧ blockPerm w = σ := by
  have right : ∀ x : Fin m, (σ (Fin.natAdd m x)).val < m := fun x => by
    by_contra hx
    have := h.sign (Fin.natAdd m x)
    have hlt := (σ (Fin.natAdd m x)).isLt
    have e : σ (Fin.natAdd m x) = Fin.natAdd m ⟨(σ (Fin.natAdd m x)).val - m, by omega⟩ :=
      Fin.ext (by simp only [Fin.coe_natAdd]; omega)
    rw [e, blockWord_right, blockWord_right] at this
    simp at this
  have eR : ∀ x, σ (Fin.natAdd m x) = Fin.castAdd m ⟨(σ (Fin.natAdd m x)).val, right x⟩ :=
    fun x => Fin.ext rfl
  let f : Fin m → Fin m := fun x => Fin.rev ⟨(σ (Fin.natAdd m x)).val, right x⟩
  have hf : Function.Injective f := fun x x' e => by
    have e' := congrArg Fin.val (Fin.rev_injective e)
    exact (Fin.natAdd_inj m).1 (σ.injective (Fin.ext e'))
  let w := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf)
  have hwx : ∀ x, Fin.rev (w x) = ⟨(σ (Fin.natAdd m x)).val, right x⟩ := fun x => by
    simp [w, f]
  refine ⟨w, fun x => ?_, ?_⟩
  · have := h.col (Fin.natAdd m x)
    rw [eR, blockWord_left, blockWord_right] at this
    rw [hwx]; exact this
  · ext1 z
    refine Fin.addCases (fun k => ?_) (fun x => ?_) z
    · rw [blockPerm_left]
      set x := w.symm (Fin.rev k)
      have hk : Fin.rev (w x) = k := by simp [x]
      rw [hwx] at hk
      have : σ (Fin.natAdd m x) = Fin.castAdd m k := by rw [eR, hk]
      rw [← this, h.invol]
    · rw [blockPerm_right, hwx]; exact (eR x).symm

/-- The degree of `D_{σ_w}`: `Σ_x (b_x·b_x)/2 (1 + ⟨b_x, λ⟩) + Σ_{x < y, w x < w y} b_x·b_y`. -/
theorem mdeg_blockPerm {w : Perm (Fin m)} (hw : ∀ x, cc (Fin.rev (w x)) = bb x) (ℓ : I → ℤ) :
    mdeg C ℓ (blockWord cc bb) (blockPerm w) =
      (∑ x, di C (bb x) * (1 + ℓ (bb x))) +
        ∑ x, ∑ y, if x < y ∧ w x < w y then C.dot (bb x) (bb y) else 0 := by
  rw [mdeg_eq_alt C (isMatching_blockPerm hw) ℓ]
  have cn := castAdd_lt_natAdd (m₁ := m) (m₂ := m)
  have nc : ∀ (x k : Fin m), ¬ Fin.natAdd m x < Fin.castAdd m k := fun x k h =>
    lt_asymm h (cn k x)
  -- reindexing the negative endpoints by `k = rev (w x)`
  let e : Fin m ≃ Fin m := w.trans Fin.revPerm
  have he : ∀ x, e x = Fin.rev (w x) := fun x => rfl
  have hes : ∀ x, w.symm (Fin.rev (e x)) = x := fun x => by simp [he]
  congr 1
  · rw [Fin.sum_univ_add, ← Equiv.sum_comp e]
    simp only [blockPerm_left, blockPerm_right, cn, nc, if_true, if_false, Finset.sum_const_zero,
      add_zero, arcDeg, blockWord_left, he, hw, sgn_false]
    refine Finset.sum_congr rfl fun x _ => by ring
  · rw [Fin.sum_univ_add]
    have z2 : ∀ x : Fin m, ∑ b, pairDeg C (blockWord cc bb) (blockPerm w) (Fin.natAdd m x) b = 0 :=
      fun x => Finset.sum_eq_zero fun b _ => by
        simp only [pairDeg, blockPerm_right]
        rw [if_neg fun h => nc x _ (h.1.trans h.2.1), if_neg fun h => nc x _ h.2.1, add_zero]
    simp only [z2, Finset.sum_const_zero, add_zero]
    rw [← Equiv.sum_comp e]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Fin.sum_univ_add, ← Equiv.sum_comp e]
    have z1 : ∀ y : Fin m, pairDeg C (blockWord cc bb) (blockPerm w) (Fin.castAdd m (e x))
        (Fin.natAdd m y) = 0 := fun y => by
      simp only [pairDeg, blockPerm_left, blockPerm_right]
      rw [if_neg fun h => nc _ _ h.2.2, if_neg fun h => nc _ _ h.1, add_zero]
    simp only [z1, Finset.sum_const_zero, add_zero]
    refine Finset.sum_congr rfl fun y _ => ?_
    have hc : ∀ x, cc (e x) = bb x := fun x => by rw [he, hw]
    have h1 : Fin.castAdd m (e y) < Fin.castAdd m (e x) ↔ w x < w y := by
      rw [he, he, Fin.lt_iff_val_lt_val, Fin.coe_castAdd, Fin.coe_castAdd, ← Fin.lt_iff_val_lt_val,
        Fin.rev_lt_rev]
    have h2 : Fin.natAdd m x < Fin.natAdd m y ↔ x < y := by
      rw [Fin.lt_iff_val_lt_val, Fin.coe_natAdd, Fin.coe_natAdd, Fin.lt_iff_val_lt_val]; omega
    rw [pairDeg, blockPerm_left, blockPerm_left, hes, hes, blockWord_left, blockWord_left, hc, hc]
    simp only [h1, h2, cn, true_and, if_true, sgn_false]
    split_ifs <;> first | (exfalso; tauto) | ring1

theorem arcProd_blockPerm {M : Type*} [CommMonoid M] (wt : I → M) {w : Perm (Fin m)}
    (hw : ∀ x, cc (Fin.rev (w x)) = bb x) :
    arcProd wt (blockWord cc bb) (blockPerm w) = ∏ x, wt (bb x) := by
  have cn := castAdd_lt_natAdd (m₁ := m) (m₂ := m)
  have nc : ∀ (x k : Fin m), ¬ Fin.natAdd m x < Fin.castAdd m k := fun x k h =>
    lt_asymm h (cn k x)
  unfold arcProd
  rw [Fin.prod_univ_add, ← Equiv.prod_comp (w.trans Fin.revPerm)]
  simp only [blockPerm_left, blockPerm_right, blockWord_left, cn, nc, if_true, if_false,
    Finset.prod_const_one, mul_one, Equiv.trans_apply, Fin.revPerm_apply, hw]

end Block

end UDot

end Categorification.QuantumGroup
