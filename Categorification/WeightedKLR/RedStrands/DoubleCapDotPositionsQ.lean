/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCapBoundaryPositions
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapDotRightQ
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapDotInsideQ

/-!
# All dot successors of the signed cap induction

Webster, arXiv:1309.3796v2, §4.5, Lemma 4.28. A dot lies outside the two cap
legs, on a leg, or on one of the intervening black strands. All five positions
satisfy the crossing-count successor statement in the common signed presentation.

This is the version of `DoubleCapDotPositions` in which the black strands carry the relations of
Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3, Definition 1.1, `r = 1`; `CLQ.pres RD k sc`) instead
of the KL III relations. Each declaration carries the suffix `Q`.
-/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory StringDiagrams QuantumGroup QuantumGroup.UDot KL3.Diagram
universe w u v
variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (Λ : Fin ℓ → X)
  {k : Type w} [CommRing k] (sc : KL3.Diagram.CL.CLScalars C k) (P : Presentation.{w,max u v} (signature RD Λ) k)
  (Q : I → I → MvPolynomial (Fin 2) k) (e : Fin ℓ → I →₀ ℕ) (t : I → I → k)
local notation "A" => signedCapKLPresentationQ RD Λ sc P Q e t
local notation "B" => DoubleStrand I ℓ
variable {a z : Obj (signature RD Λ)} {M : Type*} [AddCommGroup M] [Module k M]
  (π : ((signedCapKLPresentationQ RD Λ sc P Q e t).obj a ⟶ (signedCapKLPresentationQ RD Λ sc P Q e t).obj z) →ₗ[k] M)

theorem capSuccessor_dotInsideQ (L U V : List B) (s l : Letter I) (R : List B) :
    CapSuccessorAt k (fun f => π ((A).diag f)) (.dot s) (L ++ [Sum.inl l.dual] ++ U) (V ++ [Sum.inl l] ++ R)
      L (U ++ [Sum.inl s] ++ V) l R := by
  let m : CapPredecessor I ℓ := .dot s
  refine capSuccessorAt_of_slide (A) π m (L ++ [Sum.inl l.dual] ++ U) (V ++ [Sum.inl l] ++ R)
    L (U ++ [Sum.inl s] ++ V) l R (by simp [m,CapPredecessor.top,List.append_assoc])
    L (U ++ [Sum.inl s] ++ V) l R (by simp [m,CapPredecessor.bottom,List.append_assoc])
    id (m.rows (L ++ U) (V ++ R)) (by
      simpa [m,CapPredecessor.top,CapPredecessor.bottom,List.append_assoc] using m.chain (L ++ U) (V ++ R))
    (m.appendsForward (L ++ U) (V ++ R)) (by simp [m.signedCrossings_rows,m,CapPredecessor.cost]) ?_
  intro μ d
  apply Or.inr
  refine ⟨U.length + V.length, by simp [m,CapPredecessor.cost], ?_⟩
  apply capDot_bound_congr RD Λ (A) μ (signedCapBlock_dotInsideQ RD Λ sc P Q e t μ L U V s l R d) <;>
    simp [m,CapPredecessor.rows,CapPredecessor.bottom,capSweepDot,List.append_assoc]

theorem capSuccessor_dotRightQ (L U : List B) (l : Letter I) (R : List B) :
    CapSuccessorAt k (fun f => π ((A).diag f)) (.dot l) (L ++ [Sum.inl l.dual] ++ U) R L U l R := by
  refine capSuccessorAt_of_slide (A) π (.dot l) (L ++ [Sum.inl l.dual] ++ U) R L U l R
    (by simp [CapPredecessor.top,List.append_assoc])
    L U l R (by simp [CapPredecessor.bottom,List.append_assoc]) (· + 1) [] rfl appendsForward_nil
    (by simp [CapPredecessor.cost,signedCrossings]) ?_
  intro μ d
  by_cases h : U = []
  · subst U
    apply Or.inl
    apply sub_eq_zero.mpr
    apply capDot_eq_congr RD Λ (A) μ (signedCapBlock_dotRight_nilQ RD Λ sc P Q e t μ L l R d) <;>
      simp [CapPredecessor.rows,CapPredecessor.bottom,capSweepDot,List.append_assoc]
  · refine Or.inr ⟨U.length - 1, ?_, ?_⟩
    · have := List.length_pos_iff.mpr h
      simp only [CapPredecessor.cost,Nat.zero_add]; omega
    · apply capDot_bound_congr RD Λ (A) μ (signedCapBlock_dotRightQ RD Λ sc P Q e t μ L U l R d) <;>
        simp [CapPredecessor.rows,CapPredecessor.bottom,capSweepDot,List.append_assoc]

/-- The entire dot family in `pushesTerminalCaps_of_positions`, without local
hypotheses in any of the five positions. -/
theorem capSuccessor_allDotsQ (x : Letter I) (u v L U : List B) (l : Letter I) (R : List B)
    (pos : DotPlacement (Sum.inl l.dual) (Sum.inl l) u (Sum.inl x) v L U R) :
    CapSuccessorAt k (fun f => π ((A).diag f)) (.dot x) u v L U l R := by
  cases pos
  · apply capSuccessor_before (A) π (.dot x)
  · apply capSuccessor_dotLeft (A) π
  · apply capSuccessor_dotInsideQ RD Λ sc P Q e t π
  · apply capSuccessor_dotRightQ RD Λ sc P Q e t π
  · apply capSuccessor_after (A) π (.dot x)

end Categorification.Stendhal.DoubleDiagram
