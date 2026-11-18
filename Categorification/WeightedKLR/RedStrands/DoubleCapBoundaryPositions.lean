/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCapSuccessorTransfer
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapDot

/-!
# Exterior positions in the signed cap induction

In the geometric argument for Webster, arXiv:1309.3796v2, §4.5, Lemma 4.28,
any entire move disjoint from a cap block interchanges with it. These two
positions are discharged for every generator and every physical presentation.
-/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory StringDiagrams QuantumGroup QuantumGroup.UDot KL3.Diagram

universe w u v
variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y} {Λ : Fin ℓ → X}
  {k : Type w} [CommRing k] (P : Presentation.{w,max u v} (signature RD Λ) k)
  {a t : Obj (signature RD Λ)} {M : Type*} [AddCommGroup M] [Module k M]
  (π : (P.obj a ⟶ P.obj t) →ₗ[k] M)

local notation "B" => DoubleStrand I ℓ

theorem CapPredecessor.rows_whisk (m : CapPredecessor I ℓ) (L R u v : List B) :
    signedWhisk L R (m.rows u v) = m.rows (L ++ u) (v ++ R) := by
  cases m with
  | dot | cup => rfl
  | cross x y h => exact signedCrossLayers_whisk ..

private theorem reindexDgEq (μ : X) {s t s' t' : List B} {A D A' D' : List (SignedLayer I ℓ)}
    (h : signedDg RD Λ P μ s t A = signedDg RD Λ P μ s t D) (hs : s = s') (ht : t = t')
    (hA : A = A') (hD : D = D') :
    signedDg RD Λ P μ s' t' A' = signedDg RD Λ P μ s' t' D' := by subst_vars; exact h

/-- A preceding move lying entirely to the left of the cap span. -/
theorem capSuccessor_before (m : CapPredecessor I ℓ) (u mid U : List B) (l : Letter I) (R : List B) :
    CapSuccessorAt k (fun f => π (P.diag f)) m u (mid ++ [Sum.inl l.dual] ++ U ++ [Sum.inl l] ++ R)
      (u ++ m.top ++ mid) U l R := by
  refine capSuccessorAt_of_slide P π m u (mid ++ [Sum.inl l.dual] ++ U ++ [Sum.inl l] ++ R)
    (u ++ m.top ++ mid) U l R (by simp [List.append_assoc])
    (u ++ m.bottom ++ mid) U l R (by simp [List.append_assoc]) id (m.rows u (mid ++ U ++ R))
    (by simpa only [List.append_assoc] using m.chain u (mid ++ U ++ R)) (m.appendsForward u (mid ++ U ++ R))
    (by rw [m.signedCrossings_rows]; omega) ?_
  intro μ d
  apply Or.inl
  apply sub_eq_zero.mpr
  have hc : signedChain (m.bottom ++ mid) (m.rows [] mid) (m.top ++ mid) := by simpa using m.chain [] mid
  apply reindexDgEq P μ (signedCapBlock_disjointLeft RD Λ P μ u U l R hc d) <;>
    simp only [CapPredecessor.rows_whisk, List.append_assoc, List.cons_append, List.nil_append, List.append_nil, id_eq]

/-- A preceding move lying entirely to the right of the cap span. -/
theorem capSuccessor_after (m : CapPredecessor I ℓ) (L U : List B) (l : Letter I) (mid v : List B) :
    CapSuccessorAt k (fun f => π (P.diag f)) m (L ++ [Sum.inl l.dual] ++ U ++ [Sum.inl l] ++ mid) v
      L U l (mid ++ m.top ++ v) := by
  refine capSuccessorAt_of_slide P π m (L ++ [Sum.inl l.dual] ++ U ++ [Sum.inl l] ++ mid) v
    L U l (mid ++ m.top ++ v) (by simp [List.append_assoc])
    L U l (mid ++ m.bottom ++ v) (by simp [List.append_assoc]) id (m.rows (L ++ U ++ mid) v)
    (by simpa only [List.append_assoc] using m.chain (L ++ U ++ mid) v) (m.appendsForward (L ++ U ++ mid) v)
    (by rw [m.signedCrossings_rows]; omega) ?_
  intro μ d
  apply Or.inl
  apply sub_eq_zero.mpr
  have hc : signedChain (mid ++ m.bottom) (m.rows mid []) (mid ++ m.top) := by simpa using m.chain mid []
  apply reindexDgEq P μ (signedCapBlock_disjointRight RD Λ P μ L U l v hc d) <;>
    simp only [CapPredecessor.rows_whisk, List.append_assoc, List.cons_append, List.nil_append, id_eq]

/-- The stationary cap leg acquires the preceding dot without a crossing correction. -/
theorem capSuccessor_dotLeft (L U : List B) (l : Letter I) (R : List B) :
    CapSuccessorAt k (fun f => π (P.diag f)) (.dot l.dual) L (U ++ [Sum.inl l] ++ R) L U l R := by
  refine capSuccessorAt_of_slide P π (.dot l.dual) L (U ++ [Sum.inl l] ++ R) L U l R
    (by simp [CapPredecessor.top, List.append_assoc])
    L U l R (by simp [CapPredecessor.bottom, List.append_assoc]) (· + 1) [] rfl appendsForward_nil (by simp [signedCrossings, CapPredecessor.cost]) ?_
  intro μ d
  apply Or.inl
  apply sub_eq_zero.mpr
  apply reindexDgEq P μ (signedCapBlock_dotLeft RD Λ P μ L U l R d) <;>
    simp [CapPredecessor.rows, CapPredecessor.bottom, List.append_assoc]

/-- A red or black strand entering through the right end is incorporated in
the same cap, increasing its interior length by one. -/
theorem capSuccessor_crossEnterRight (L U : List B) (l : Letter I) (x : B) (R : List B) :
    CapSuccessorAt k (fun f => π (P.diag f)) (.cross x (Sum.inl l) (by cases x <;> trivial))
      (L ++ [Sum.inl l.dual] ++ U) R L U l (x :: R) := by
  refine capSuccessorAt_of_slide P π (.cross x (Sum.inl l) (by cases x <;> trivial))
    (L ++ [Sum.inl l.dual] ++ U) R L U l (x :: R) (by simp [CapPredecessor.top,List.append_assoc])
    L (U ++ [x]) l R (by simp [CapPredecessor.bottom,List.append_assoc]) id [] (by simp [signedChain,List.append_assoc]) appendsForward_nil
    (by simp [CapPredecessor.cost,signedCrossings]) ?_
  intro μ d
  apply Or.inl
  apply sub_eq_zero.mpr
  rw [List.append_nil]
  apply congrArg
  exact signedCapBlock_enterRight L U x l R d

end Categorification.Stendhal.DoubleDiagram
