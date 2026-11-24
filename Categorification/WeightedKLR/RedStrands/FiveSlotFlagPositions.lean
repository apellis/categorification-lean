/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FiveSlotFlagRepresentation
import Categorification.KLR.DividedPowerIdempotents
import Categorification.KLR.PolNu

/-!
# Positions of the two polynomial flags

Webster, arXiv:1309.3796v2, proof of Lemma 6.8 after (6.21). The two
black positions carry the two polynomial flag relations. Their degree bounds
are sums over the red strands before those positions.
-/

namespace Categorification.Stendhal.FiveSlotFlag

open KLR KLRAlgebra TypeA Equiv

local notation "m" => Multiset.card weight

/-- The first black position. -/
def firstBlack (s : Seq weight) : Fin m :=
  ((List.finRange m).find? fun p => (s.lbl p).isLeft).getD ⟨0, by decide⟩

/-- The second black position. -/
def secondBlack (s : Seq weight) : Fin m :=
  ((List.finRange m).reverse.find? fun p => (s.lbl p).isLeft).getD ⟨0, by decide⟩

/-- The set of red labels strictly before a given position. -/
def redsBefore (s : Seq weight) (p : Fin m) : Finset (Fin 3) :=
  Finset.univ.filter fun r => ∃ b : Fin m, b < p ∧ s.lbl b = .inr r

/-- The sum of the red exponents strictly before a given position. -/
def flagBound (Λ : Fin 3 → Unit →₀ ℕ) (s : Seq weight) (p : Fin m) : ℕ :=
  ∑ r ∈ redsBefore s p, Λ r ()

private def initial : Seq weight := Seq.ofList [.inr 0, .inr 1, .inr 2, .inl (), .inl ()]
  (by decide)

/-- Both flags are placed at actual black slots, and their exponents are
weakly increasing along the loading. -/
theorem blackPositions (s : Seq weight) :
    s.lbl (firstBlack s) = .inl () ∧ s.lbl (secondBlack s) = .inl () ∧
      firstBlack s < secondBlack s ∧ redsBefore s (firstBlack s) ⊆ redsBefore s (secondBlack s) := by
  obtain ⟨w, rfl⟩ := Seq.exists_smul_eq initial s
  have h : ∀ w : Perm (Fin m), let t := w • initial
      t.lbl (firstBlack t) = .inl () ∧ t.lbl (secondBlack t) = .inl () ∧
        firstBlack t < secondBlack t := by decide +kernel
  obtain ⟨h₁, h₂, hlt⟩ := h w
  refine ⟨h₁, h₂, hlt, ?_⟩
  intro r hr
  obtain ⟨_, b, hb, hbr⟩ := Finset.mem_filter.1 hr
  exact Finset.mem_filter.2 ⟨Finset.mem_univ r, b, hb.trans hlt, hbr⟩

/-- Violated loadings have no red before the first flag. -/
theorem firstBound_eq_zero_of_violated (Λ : Fin 3 → Unit →₀ ℕ) (s : Seq weight)
    (hs : IsViolated s) : flagBound Λ s (firstBlack s) = 0 := by
  obtain ⟨w, rfl⟩ := Seq.exists_smul_eq initial s
  have h : ∀ w : Perm (Fin m), ((w • initial).lbl ⟨0, by decide⟩).isLeft →
      redsBefore (w • initial) (firstBlack (w • initial)) = ∅ := by decide +kernel
  obtain ⟨_, hs⟩ := hs
  rw [flagBound, h w hs, Finset.sum_empty]

/-- With a black followed by a red, the swap carries both black slots
by the positional permutation. It adds precisely that red to the flags
of the moving black. -/
theorem slots_black_red (s : Seq weight) (j : ℕ) (h : j + 1 < m) (r : Fin 3)
    (hb : s.lbl ⟨j, by omega⟩ = .inl ())
    (hr : s.lbl ⟨j + 1, h⟩ = .inr r) :
    let t := sadj m j • s
    firstBlack t = sadj m j (firstBlack s) ∧ secondBlack t = sadj m j (secondBlack s) ∧
    (if firstBlack s = ⟨j, by omega⟩ then
      r ∉ redsBefore s (firstBlack s) ∧
        redsBefore t (firstBlack t) = insert r (redsBefore s (firstBlack s)) ∧
        redsBefore t (secondBlack t) = redsBefore s (secondBlack s)
    else
      secondBlack s = ⟨j, by omega⟩ ∧ r ∉ redsBefore s (secondBlack s) ∧
        redsBefore t (secondBlack t) = insert r (redsBefore s (secondBlack s)) ∧
        redsBefore t (firstBlack t) = redsBefore s (firstBlack s)) := by
  obtain ⟨w, rfl⟩ := Seq.exists_smul_eq initial s
  have hm : m = 5 := by decide
  let p : Fin 4 := ⟨j, by omega⟩
  have hf : ∀ (w : Perm (Fin m)) (p : Fin 4) (r : Fin 3),
      let s := w • initial
      let a : Fin m := ⟨p.val, lt_of_lt_of_le p.isLt (by decide)⟩
      let b : Fin m := ⟨p.val + 1, lt_of_lt_of_le (Nat.succ_lt_succ p.isLt) (by decide)⟩
      let t := sadj m p.val • s
      s.lbl a = .inl () → s.lbl b = .inr r →
      firstBlack t = sadj m p.val (firstBlack s) ∧ secondBlack t = sadj m p.val (secondBlack s) ∧
      (if firstBlack s = a then
        r ∉ redsBefore s (firstBlack s) ∧
          redsBefore t (firstBlack t) = insert r (redsBefore s (firstBlack s)) ∧
          redsBefore t (secondBlack t) = redsBefore s (secondBlack s)
      else
        secondBlack s = a ∧ r ∉ redsBefore s (secondBlack s) ∧
          redsBefore t (secondBlack t) = insert r (redsBefore s (secondBlack s)) ∧
          redsBefore t (firstBlack t) = redsBefore s (firstBlack s)) := by decide +kernel
  exact hf w p r hb hr

/-- A black crossing is between the two flag positions and their red
prefixes agree. -/
theorem slots_black_black (s : Seq weight) (j : ℕ) (h : j + 1 < m)
    (hb : s.lbl ⟨j, by omega⟩ = .inl ())
    (hc : s.lbl ⟨j + 1, h⟩ = .inl ()) :
    firstBlack s = ⟨j, by omega⟩ ∧ secondBlack s = ⟨j + 1, h⟩ ∧
      redsBefore s (firstBlack s) = redsBefore s (secondBlack s) := by
  obtain ⟨w, rfl⟩ := Seq.exists_smul_eq initial s
  have hm : m = 5 := by decide
  let p : Fin 4 := ⟨j, by omega⟩
  have hf : ∀ (w : Perm (Fin m)) (p : Fin 4),
      let s := w • initial
      let a : Fin m := ⟨p.val, lt_of_lt_of_le p.isLt (by decide)⟩
      let b : Fin m := ⟨p.val + 1, lt_of_lt_of_le (Nat.succ_lt_succ p.isLt) (by decide)⟩
      s.lbl a = .inl () → s.lbl b = .inl () →
      firstBlack s = a ∧ secondBlack s = b ∧
        redsBefore s (firstBlack s) = redsBefore s (secondBlack s) := by decide +kernel
  exact hf w p hb hc

/-- A red crossing carries the black positions and leaves both red
prefix sets unchanged. -/
theorem slots_red_red (s : Seq weight) (j : ℕ) (h : j + 1 < m)
    (hb : (s.lbl ⟨j, by omega⟩).isRight) (hc : (s.lbl ⟨j + 1, h⟩).isRight) :
    let t := sadj m j • s
    firstBlack t = sadj m j (firstBlack s) ∧ secondBlack t = sadj m j (secondBlack s) ∧
      redsBefore t (firstBlack t) = redsBefore s (firstBlack s) ∧
      redsBefore t (secondBlack t) = redsBefore s (secondBlack s) := by
  obtain ⟨w, rfl⟩ := Seq.exists_smul_eq initial s
  have hm : m = 5 := by decide
  let p : Fin 4 := ⟨j, by omega⟩
  have hf : ∀ (w : Perm (Fin m)) (p : Fin 4),
      let s := w • initial
      let a : Fin m := ⟨p.val, lt_of_lt_of_le p.isLt (by decide)⟩
      let b : Fin m := ⟨p.val + 1, lt_of_lt_of_le (Nat.succ_lt_succ p.isLt) (by decide)⟩
      let t := sadj m p.val • s
      (s.lbl a).isRight → (s.lbl b).isRight →
      firstBlack t = sadj m p.val (firstBlack s) ∧ secondBlack t = sadj m p.val (secondBlack s) ∧
        redsBefore t (firstBlack t) = redsBefore s (firstBlack s) ∧
        redsBefore t (secondBlack t) = redsBefore s (secondBlack s) := by decide +kernel
  exact hf w p hb hc

end Categorification.Stendhal.FiveSlotFlag
