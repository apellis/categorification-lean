/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCapBoundaryPositions
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapDotSweep
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapCrossing
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapBraid

/-!
# Crossing successors of the signed cap induction

Webster, arXiv:1309.3796v2, §4.5, Lemma 4.28. Crossings through the interior use the signed braid relation. Crossings at the
right edge and across both cap legs lower the crossing filtration.
-/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory StringDiagrams QuantumGroup QuantumGroup.UDot KL3.Diagram
universe w u v
variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (Λ : Fin ℓ → X)
  {k : Type w} [CommRing k] (P : Presentation.{w,max u v} (signature RD Λ) k)
  (Q : I → I → MvPolynomial (Fin 2) k) (e : Fin ℓ → I →₀ ℕ) (t : I → I → k)
local notation "A" => signedCapKLPresentation RD Λ P Q e t
local notation "B" => DoubleStrand I ℓ
variable {a z : Obj (signature RD Λ)} {M : Type*} [AddCommGroup M] [Module k M]
  (π : ((signedCapKLPresentation RD Λ P Q e t).obj a ⟶ (signedCapKLPresentation RD Λ P Q e t).obj z) →ₗ[k] M)

theorem capSuccessor_crossInside (L U V R : List B) (l : Letter I) (x y : B) (h : CanCross x y) :
    CapSuccessorAt k (fun f => π ((A).diag f)) (.cross x y h) (L ++ [Sum.inl l.dual] ++ U)
      (V ++ [Sum.inl l] ++ R) L (U ++ [y,x] ++ V) l R := by
  let m : CapPredecessor I ℓ := .cross x y h
  refine capSuccessorAt_of_slide (A) π m (L ++ [Sum.inl l.dual] ++ U) (V ++ [Sum.inl l] ++ R)
    L (U ++ [y,x] ++ V) l R (by simp [m,CapPredecessor.top,List.append_assoc])
    L (U ++ [x,y] ++ V) l R (by simp [m,CapPredecessor.bottom,List.append_assoc])
    id (m.rows (L ++ U) (V ++ R)) (by
      simpa [m,CapPredecessor.top,CapPredecessor.bottom,List.append_assoc] using m.chain (L ++ U) (V ++ R))
    (m.appendsForward (L ++ U) (V ++ R)) (by simp [m.signedCrossings_rows,m,CapPredecessor.cost]) ?_
  intro μ d
  refine Or.inr ⟨U.length + 2 + V.length, by simp [m,CapPredecessor.cost]; omega, ?_⟩
  have hb := signedCapKL_hasCapBraidBound RD Λ P Q e t μ (L ++ [Sum.inl l.dual] ++ U) x y l (V ++ R) h
  apply capDot_bound_congr RD Λ (A) μ (signedCapBlock_crossInside RD Λ (A) μ L U V R l d h hb) <;>
    simp [m,CapPredecessor.rows,CapPredecessor.bottom,List.append_assoc]

theorem capSuccessor_crossLast (L U R : List B) (l : Letter I) (x : B) :
    CapSuccessorAt k (fun f => π ((A).diag f)) (.cross (Sum.inl l) x (by cases x <;> trivial))
      (L ++ [Sum.inl l.dual] ++ U) R L (U ++ [x]) l R := by
  refine capSuccessorAt_of_lower (A) π _ _ _ _ _ _ _
    (by simp [CapPredecessor.top,List.append_assoc]) (U.length + 1)
    (by simp [CapPredecessor.cost]) ?_
  intro μ d
  exact signedCapKL_capBlock_crossLast RD Λ P μ Q e t L U R l x d

theorem capSuccessor_crossBoth (L R : List B) (l : Letter I) :
    CapSuccessorAt k (fun f => π ((A).diag f)) (.cross (Sum.inl l) (Sum.inl l.dual) trivial)
      L R L [] l R := by
  exact capSuccessorAt_of_lower (A) π _ _ _ _ _ _ _ (by simp [CapPredecessor.top,List.append_assoc])
    0 (by simp [CapPredecessor.cost]) (fun μ d => signedCapKL_capBlock_crossBoth RD Λ P μ Q e t L R l d)

private theorem crossBound_reindex (μ : X) {s z s' z' : List B} {g g' : List (SignedLayer I ℓ)} {n : ℕ}
    (h : signedDg RD Λ (A) μ s z g ∈ signedCrossingSpan RD Λ (A) μ s z n)
    (hs : s = s') (hz : z = z') (hg : g = g') :
    signedDg RD Λ (A) μ s' z' g' ∈ signedCrossingSpan RD Λ (A) μ s' z' n := by subst_vars; exact h

theorem capSuccessor_crossFirst (L U R : List B) (x : B) (l : Letter I) :
    CapSuccessorAt k (fun f => π ((A).diag f)) (.cross x (Sum.inl l.dual) (by cases x <;> trivial))
      L (U ++ [Sum.inl l] ++ R) L (x :: U) l R := by
  refine capSuccessorAt_of_lower (A) π _ _ _ _ _ _ _
    (by simp [CapPredecessor.top,List.append_assoc]) (U.length + 1)
    (by simp [CapPredecessor.cost]) ?_
  intro μ d
  apply crossBound_reindex RD Λ P Q e t μ (signedCapKL_capBlock_crossFirst RD Λ P μ Q e t L U R x l d) <;>
    simp [CapPredecessor.bottom,CapPredecessor.rows,List.append_assoc]

theorem capSuccessor_crossEnterLeft (L U R : List B) (x : B) (l : Letter I) :
    CapSuccessorAt k (fun f => π ((A).diag f)) (.cross (Sum.inl l.dual) x (by cases x <;> trivial))
      L (U ++ [Sum.inl l] ++ R) (L ++ [x]) U l R := by
  refine capSuccessorAt_of_slide (A) π _ _ _ _ _ _ _ (by simp [CapPredecessor.top,List.append_assoc])
    L (x :: U) l R (by simp [CapPredecessor.bottom,List.append_assoc]) id [] (by simp [signedChain,List.append_assoc])
    appendsForward_nil (by simp [CapPredecessor.cost,signedCrossings]) ?_
  intro μ d
  refine Or.inr ⟨U.length, by simp [CapPredecessor.cost], ?_⟩
  apply capDot_bound_congr RD Λ (A) μ (signedCapKL_capBlock_enterLeft RD Λ P μ Q e t L U R x l d) <;>
    simp [CapPredecessor.rows,CapPredecessor.bottom,List.append_assoc]

/-- All eight placements of an admissible crossing in the terminal-cap induction. -/
theorem capSuccessor_allCrossings (x y : B) (h : CanCross x y) (u v L U : List B) (l : Letter I)
    (R : List B) (pos : PairPlacement (Sum.inl l.dual) (Sum.inl l) u y x v L U R) :
    CapSuccessorAt k (fun f => π ((A).diag f)) (.cross x y h) u v L U l R := by
  cases pos
  · apply capSuccessor_before (A) π (.cross _ _ h)
  · apply capSuccessor_crossEnterLeft RD Λ P Q e t π
  · apply capSuccessor_crossFirst RD Λ P Q e t π
  · apply capSuccessor_crossBoth RD Λ P Q e t π
  · apply capSuccessor_crossInside RD Λ P Q e t π
  · apply capSuccessor_crossLast RD Λ P Q e t π
  · apply capSuccessor_crossEnterRight (A) π
  · apply capSuccessor_after (A) π (.cross _ _ h)

end Categorification.Stendhal.DoubleDiagram
