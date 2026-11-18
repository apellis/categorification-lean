/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.RedStrands.DoubleBoundary
import Mathlib.Data.List.Induction

/-!
# Moving upward strands to the left

In the proof of Theorem 4.29 of B. Webster, *Knot invariants and higher representation
theory*, arXiv:1309.3796v2, §4.5, an upward strand moves left across a red or downward
strand. Crossing a downward strand of the same colour can also produce terms which factor
through the boundary obtained by deleting the pair. Here we prove the induction on signed
boundaries underlying that proof. The local diagram relations are hypotheses.
-/

namespace Categorification.Stendhal.DoubleBoundary

variable {I : Type*} {ℓ : ℕ}

/-- A property of ordered boundaries evaluated on a word whenever its red labels occur in
the prescribed order. -/
def OnWord (P : DoubleBoundary I ℓ → Prop) (w : List (DoubleStrand I ℓ)) : Prop :=
  ∀ h : w.filterMap DoubleStrand.redLabel = List.finRange ℓ, P ⟨w, h⟩

/-- The signed-boundary induction in Webster, arXiv:1309.3796v2, §4.5, proof of Theorem
4.29. To apply this to membership of the identity in the all-down ideal, the far-left
upward identity vanishes by violation. The red crossing moves the upward strand to the
left by the two bigon relations drawn in (4.4e); the proof text cites (4.4d). The
mixed black relations (2.3c) and (2.4a) permit a shorter term only at equal colours.
These diagrammatic inputs are explicit local closure hypotheses here. -/
theorem induction_moveUpLeft (P : DoubleBoundary I ℓ → Prop)
    (allDown : ∀ b, b.AllDown → P b)
    (leftUp : ∀ i R, OnWord P (.inl (true, i) :: R))
    (redUp : ∀ L R i r, OnWord P (L ++ .inl (true, i) :: .inr r :: R) →
      OnWord P (L ++ .inr r :: .inl (true, i) :: R))
    (downUp : ∀ L R i j, OnWord P (L ++ .inl (true, i) :: .inl (false, j) :: R) →
      (j = i → OnWord P (L ++ R)) → OnWord P (L ++ .inl (false, j) :: .inl (true, i) :: R))
    (b : DoubleBoundary I ℓ) : P b := by
  suffices hw : ∀ w : List (DoubleStrand I ℓ), OnWord P w from hw b.word b.redOrder
  intro w
  induction hn : w.length using Nat.strong_induction_on generalizing w with
  | h n shorter =>
    by_cases hu : ∃ i : I, Sum.inl (true, i) ∈ w
    · obtain ⟨i, hi⟩ := hu
      obtain ⟨L, R, rfl⟩ := List.append_of_mem hi
      clear hi
      induction L using List.reverseRecOn generalizing i R with
      | nil => exact leftUp i R
      | append_singleton L a move =>
        simp only [List.append_assoc, List.singleton_append] at hn ⊢
        have step (j : I) (a' : DoubleStrand I ℓ) :
            OnWord P (L ++ .inl (true, j) :: a' :: R) :=
          move j (a' :: R) (by simpa only [List.length_append, List.length_cons] using hn)
        cases a with
        | inr r => exact redUp L R i r (step i (.inr r))
        | inl a =>
          obtain ⟨direction, j⟩ := a
          cases direction with
          | true => exact step j (.inl (true, i))
          | false =>
            refine downUp L R i j (step i (.inl (false, j))) fun _ => ?_
            apply shorter (L ++ R).length _ (L ++ R) rfl
            simp only [List.length_append, List.length_cons] at hn ⊢
            omega
    · intro h
      apply allDown
      exact fun i hi => hu ⟨i, hi⟩

end Categorification.Stendhal.DoubleBoundary
