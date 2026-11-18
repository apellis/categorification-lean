/-
Copyright (c) 2026 The Categorification Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Categorification Authors
-/
import Categorification.WeightedKLR.RedStrands.CyclotomicCoverSequenceClass
import Categorification.KLR.CyclotomicWordRestriction

/-!
# Laurent polynomials for pairs of Stendhal loadings

A finite deletion recursion for the graded Cartan entries in Webster,
arXiv:1309.3796v2, §4.7, Lemmas 4.36–4.37 and Theorem 4.38. An ordered loading
lists black colours and red dominant multiplicities from left to right.
-/

namespace Categorification.Stendhal
open KLR KLR.CycKLR QuantumGroup QuantumGroup.UDot
open LieLean.QuantumGroup

variable {I : Type*}

/-- The black coroot pairing at the right end of a loading. -/
def cornerPrefixPair (C : CartanDatum I) (i : I) (w : List (I ⊕ (I →₀ ℕ))) : ℤ :=
  (w.map (Sum.elim (fun j => -A C i j) (fun wt => (wt i : ℤ)))).sum

/-- The grading shift and prefix quantum integer of a terminal-black deletion. -/
noncomputable def cornerDeletionCoeff (C : CartanDatum I) (i : I)
    (u p : List (I ⊕ (I →₀ ℕ))) : LaurentPolynomial ℤ :=
  LaurentPolynomial.T (di C i * (cornerPrefixPair C i u - 1)) *
    qIntU (qUnitLP ^ di C i) (cornerPrefixPair C i p)

private theorem marked_remainder_length {J : Type*} {w : List J} {m : List J × J × List J}
    (h : m ∈ markedWords w) : (m.1 ++ m.2.2).length + 1 = w.length := by
  induction w generalizing m with
  | nil => simp [markedWords] at h
  | cons a w ih =>
    simp only [markedWords, List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨m, hm, rfl⟩
    · rfl
    · simpa [List.cons_append, Nat.add_right_comm, Nat.add_left_comm] using ih hm

variable [DecidableEq I]

private noncomputable def cornerPolynomialRev (C : CartanDatum I) :
    (s t : List (I ⊕ (I →₀ ℕ))) → LaurentPolynomial ℤ
  | .inl i :: u, w =>
    (((markedWords w.reverse).attach).map (fun mark =>
      if Sum.inl i = mark.val.2.1 then
        cornerDeletionCoeff C i u.reverse mark.val.1 *
          cornerPolynomialRev C u (mark.val.1 ++ mark.val.2.2).reverse else 0)).sum
  | .inr r :: w, .inl i :: u =>
    (((markedWords (.inr r :: w).reverse).attach).map (fun mark =>
      if Sum.inl i = mark.val.2.1 then
        cornerDeletionCoeff C i u.reverse mark.val.1 *
          cornerPolynomialRev C u (mark.val.1 ++ mark.val.2.2).reverse else 0)).sum
  | .inr r :: u, .inr s :: v => if r = s then cornerPolynomialRev C u v else 0
  | [], [] => 1
  | _, _ => 0
termination_by s t => s.length + t.length
decreasing_by
  all_goals simp_wf
  · have h := marked_remainder_length mark.property
    simp only [List.length_reverse, List.length_append] at h ⊢
    omega
  · have h := marked_remainder_length mark.property
    simp only [List.length_reverse, List.length_cons, List.length_append] at h ⊢
    omega
  · omega

/-- The Laurent polynomial computed by deleting terminal strands in a pair of loadings. -/
noncomputable def cornerPolynomial (C : CartanDatum I) (s t : List (I ⊕ (I →₀ ℕ))) :
    LaurentPolynomial ℤ :=
  cornerPolynomialRev C s.reverse t.reverse

@[simp] theorem cornerPolynomial_empty (C : CartanDatum I) : cornerPolynomial C [] [] = 1 := by
  simp [cornerPolynomial, cornerPolynomialRev]

/-- Remove a terminal black strand on the left and sum over its possible partners. -/
theorem cornerPolynomial_terminalBlack (C : CartanDatum I) (i : I)
    (u w : List (I ⊕ (I →₀ ℕ))) :
    cornerPolynomial C (u ++ [.inl i]) w =
      (((markedWords w).attach).map (fun mark =>
        if Sum.inl i = mark.val.2.1 then
          cornerDeletionCoeff C i u mark.val.1 *
            cornerPolynomial C u (mark.val.1 ++ mark.val.2.2) else 0)).sum := by
  simp [cornerPolynomial, cornerPolynomialRev]
  exact congrArg (fun v =>
    (((markedWords v).attach).map (fun mark =>
      if Sum.inl i = mark.val.2.1 then
        cornerDeletionCoeff C i u mark.val.1 *
          cornerPolynomialRev C u.reverse (mark.val.2.2.reverse ++ mark.val.1.reverse) else 0)).sum)
    (List.reverse_reverse w)

/-- If only the right loading ends in black, take it first in the deletion recursion. -/
theorem cornerPolynomial_terminalBlack_right (C : CartanDatum I) (i : I)
    (u w : List (I ⊕ (I →₀ ℕ))) (r : I →₀ ℕ) :
    cornerPolynomial C (w ++ [.inr r]) (u ++ [.inl i]) =
      (((markedWords (w ++ [.inr r])).attach).map (fun mark =>
        if Sum.inl i = mark.val.2.1 then
          cornerDeletionCoeff C i u mark.val.1 *
            cornerPolynomial C u (mark.val.1 ++ mark.val.2.2) else 0)).sum := by
  calc
    _ = cornerPolynomial C (u ++ [.inl i]) (w ++ [.inr r]) := by
      simp only [cornerPolynomial, List.reverse_append, List.reverse_singleton, List.singleton_append,
        cornerPolynomialRev]
    _ = _ := cornerPolynomial_terminalBlack C i u (w ++ [.inr r])

/-- Remove the same terminal red weight from both loadings. -/
@[simp] theorem cornerPolynomial_terminalRed (C : CartanDatum I)
    (u v : List (I ⊕ (I →₀ ℕ))) (r : I →₀ ℕ) :
    cornerPolynomial C (u ++ [.inr r]) (v ++ [.inr r]) = cornerPolynomial C u v := by
  simp [cornerPolynomial, cornerPolynomialRev]

omit [DecidableEq I] in
/-- Relabeling the red strands by their weight preserves the cover coroot pairing. -/
theorem cornerPrefixPair_map (C : CartanDatum I) {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ)
    (i : I) (w : List (I ⊕ Fin ℓ)) :
    cornerPrefixPair C i (w.map (Sum.map id Λ)) =
      prefixPair (extendedCartanDatum C Λ) cyclotomicCoverExponent (.inl i) w := by
  let a := A (extendedCartanDatum C Λ) (Sum.inl i)
  have h (x : I ⊕ Fin ℓ) :
      Sum.elim (fun j => -A C i j) (fun wt : I →₀ ℕ => (wt i : ℤ))
        (Sum.map id Λ x) = -a x := by
    cases x with
    | inl j => rfl
    | inr r => simp [a, cover_black_red]
  simp only [cornerPrefixPair, List.map_map, Function.comp_def, h, prefixPair,
    cyclotomicCoverExponent, Sum.elim_inl, Nat.cast_zero, zero_sub]
  induction w with
  | nil => simp
  | cons x w ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

omit [DecidableEq I] in
/-- A Stendhal loading of fixed content has the total coroot pairing of that block. -/
theorem cornerPrefixPair_eq_content (C : CartanDatum I) {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ)
    (i : I) {ν : Multiset I} {w : List (I ⊕ Fin ℓ)} (hw : (w : Multiset _) = stendhalWeight ℓ ν) :
    cornerPrefixPair C i (w.map (Sum.map id Λ)) =
      (∑ r, (Λ r i : ℤ)) - (ν.map (A C i)).sum := by
  rw [cornerPrefixPair_map]
  change 0 - (w.map (A (extendedCartanDatum C Λ) (Sum.inl i))).sum = _
  have hblack (j : I) : A (extendedCartanDatum C Λ) (.inl i) (.inl j) = A C i j := rfl
  rw [← Multiset.sum_coe, ← Multiset.map_coe, hw, stendhalWeight, Multiset.map_add,
    Multiset.sum_add, Multiset.map_map, Multiset.map_map]
  simp only [Function.comp_def, hblack, cover_black_red]
  have hred : (Multiset.map (fun r : Fin ℓ => -(Λ r i : ℤ)) Finset.univ.val).sum =
      -(∑ r, (Λ r i : ℤ)) := by
    change (∑ r : Fin ℓ, -(Λ r i : ℤ)) = _
    exact (Finset.sum_neg_distrib (s := Finset.univ) (f := fun r : Fin ℓ => (Λ r i : ℤ)))
  rw [hred]
  ring

end Categorification.Stendhal
