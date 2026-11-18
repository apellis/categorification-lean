/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCapBoundaryPositions
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapDotSweep
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapRightSweep
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapCupLower

/-!
# Cup successors of the signed cap induction

Webster, arXiv:1309.3796v2, §4.5, Lemma 4.28. Cups can create one or both cap endpoints or a pair of interior strands.
The endpoint zigzags leave a forward sweep through the intervening strands.
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

theorem capSuccessor_cupEnterRight (L U : List B) (l : Letter I) (R : List B) :
    CapSuccessorAt k (fun f => π ((A).diag f)) (.cup l) (L ++ [Sum.inl l.dual] ++ U) R
      L U l (Sum.inl l.dual :: R) := by
  refine capSuccessorAt_of_forward (A) π _ _ _ _ _ _ _
    (by simp [CapPredecessor.top,List.append_assoc]) (rightCupSweep L U l R)
    (fun d => by simpa [CapPredecessor.bottom,List.append_assoc] using rightCupSweep_chain L U l R d)
    (fun d _ _ _ _ hp g hg => hp.rightCupSweep RD Λ g L U l R d hg)
    (by intro d; simp [rightCupSweep_crossings,CapPredecessor.cost]) ?_
  intro μ d
  by_cases h : U = []
  · subst U
    apply Or.inl
    apply sub_eq_zero.mpr
    apply capDot_eq_congr RD Λ (A) μ (signedCapKL_cupRight_nil RD Λ P Q e t μ L l R d) <;>
      simp [CapPredecessor.rows,CapPredecessor.bottom,cupRightCapBlock,List.append_assoc]
  · refine Or.inr ⟨U.length - 1, ?_, ?_⟩
    · have := List.length_pos_iff.mpr h
      simp only [CapPredecessor.cost,Nat.zero_add]; omega
    · apply capDot_bound_congr RD Λ (A) μ (signedCapKL_cupRight RD Λ P Q e t μ L U l R d) <;>
        simp [CapPredecessor.rows,CapPredecessor.bottom,cupRightCapBlock,List.append_assoc]


private theorem append_forward {F G : List (SignedLayer I ℓ)}
    (hF : AppendsForward (RD := RD) (Λ := Λ) F) (hG : AppendsForward (RD := RD) (Λ := Λ) G) :
    AppendsForward (RD := RD) (Λ := Λ) (F ++ G) := by
  intro a b c p hp g hg
  let ls := signedLayers RD Λ b.start F
  let ms := signedLayers RD Λ b.start G
  have he : Diagram.layers g = ls ++ ms := by simpa [ls,ms,signedLayers] using hg
  have hc := Diagram.chain g
  rw [he] at hc
  obtain ⟨hf,hg'⟩ := Chain.of_append hc
  let u := Diagram.mk ls hf
  let v := Diagram.mk ms hg'
  have eu : g = u ≫ v := Diagram.ext he
  rw [eu,← Category.assoc]
  exact hG (p ≫ u) (hF p hp u rfl) v (by rw [hf.start_eq]; rfl)

theorem capSuccessor_cupEnterLeft (L U : List B) (l : Letter I) (R : List B) :
    CapSuccessorAt k (fun f => π ((A).diag f)) (.cup l) L (U ++ [Sum.inl l] ++ R)
      (L ++ [Sum.inl l]) U l R := by
  let dots (d : ℕ) : List (SignedLayer I ℓ) := List.replicate d (L,.black (.dot l),U ++ R)
  have hd (d : ℕ) : signedChain (L ++ [Sum.inl l] ++ U ++ R) (dots d) (L ++ [Sum.inl l] ++ U ++ R) := by
    induction d with
    | zero => rfl
    | succ d ih => exact (show signedChain _ [(L,.black (.dot l),U ++ R)] _ by
        simp [signedChain,Move.top,Move.bottom,List.append_assoc]).append ih
  refine capSuccessorAt_of_forward (A) π _ _ _ _ _ _ _ (by simp [CapPredecessor.top,List.append_assoc])
    (fun d => sweepBlackLeft L U l R ++ dots d)
    (fun d => by simpa only [CapPredecessor.bottom,List.append_assoc,List.nil_append,List.cons_append] using
      (sweepBlackLeft_chain L U l R).append (hd d)) ?_ ?_ ?_
  · intro d
    apply append_forward RD Λ (fun _ hp g hg => hp.sweepBlackLeft g L U l R hg)
    intro _ _ _ f hf g hg
    exact hf.postcompose_blackDots RD Λ _ g _ hg (fun y hy => by
      rw [List.eq_of_mem_replicate hy]; exact ⟨_,_,_,rfl⟩)
  · intro d
    have hz : signedCrossings (dots d) = 0 := by
      induction d with
      | zero => rfl
      | succ d ih => exact ih
    simp [signedCrossings_append,sweepBlackLeft_crossings,hz,CapPredecessor.cost]
  · intro μ d
    apply Or.inl
    apply sub_eq_zero.mpr
    apply capDot_eq_congr RD Λ (A) μ (signedCapKL_cupLeft RD Λ P Q e t μ L U l R d) <;>
      simp [dots,CapPredecessor.rows,CapPredecessor.bottom,List.append_assoc]

private theorem cup_lower_reindex (μ : X) {s t' u v : List B} {F G : List (SignedLayer I ℓ)}
    {n : ℕ} (h : signedDg RD Λ (A) μ s t' F ∈ signedCrossingSpan RD Λ (A) μ s t' n)
    (hs : s=u) (ht : t'=v) (hF : F=G) :
    signedDg RD Λ (A) μ u v G ∈ signedCrossingSpan RD Λ (A) μ u v n := by
  subst_vars
  exact h

theorem capSuccessor_cupFirst (L U : List B) (l : Letter I) (R : List B) :
    CapSuccessorAt k (fun f => π ((A).diag f)) (.cup l.dual) L (U ++ [Sum.inl l] ++ R)
      L (Sum.inl l :: U) l R := by
  refine capSuccessorAt_of_lower (A) π _ _ _ _ _ _ _ (by simp [CapPredecessor.top,List.append_assoc])
    U.length (by simp [CapPredecessor.cost]) ?_
  intro μ d
  apply cup_lower_reindex RD Λ P Q e t μ (signedCapBlock_cupFirst RD Λ (A)
    (signedCapKL_reflectedBlack RD Λ P Q e t) μ L U l R d) <;>
    simp [CapPredecessor.rows,CapPredecessor.bottom,List.append_assoc]

theorem capSuccessor_cupLast (L U : List B) (l : Letter I) (R : List B) :
    CapSuccessorAt k (fun f => π ((A).diag f)) (.cup l.dual) (L ++ [Sum.inl l.dual] ++ U) R
      L (U ++ [Sum.inl l.dual]) l R := by
  refine capSuccessorAt_of_lower (A) π _ _ _ _ _ _ _ (by simp [CapPredecessor.top,List.append_assoc])
    U.length (by simp [CapPredecessor.cost]) ?_
  intro μ d
  apply cup_lower_reindex RD Λ P Q e t μ (signedCapBlock_cupLast RD Λ (A)
    (signedCapKL_reflectedBlack RD Λ P Q e t) μ L U l R d) <;>
    simp [CapPredecessor.rows,CapPredecessor.bottom,List.append_assoc]

theorem capSuccessor_cupInside (L U V : List B) (x l : Letter I) (R : List B) :
    CapSuccessorAt k (fun f => π ((A).diag f)) (.cup x) (L ++ [Sum.inl l.dual] ++ U) (V ++ [Sum.inl l] ++ R)
      L (U ++ [Sum.inl x,Sum.inl x.dual] ++ V) l R := by
  refine capSuccessorAt_of_lower (A) π _ _ _ _ _ _ _ (by simp [CapPredecessor.top,List.append_assoc])
    (U.length+V.length+1) (by simp [CapPredecessor.cost]; omega) ?_
  intro μ d
  apply cup_lower_reindex RD Λ P Q e t μ (signedCapBlock_cupInside RD Λ (A)
    (signedCapKL_reflectedBlack RD Λ P Q e t) μ L U V x l R d) <;>
    simp [CapPredecessor.rows,CapPredecessor.bottom,List.append_assoc]

/-- All eight relative placements of a preceding cup in the signed cap induction.
The both-endpoints case is supplied for the chosen projection, since bubble
evaluation uses the violating quotient. The other seven positions follow
from the local relations of the common signed KL presentation. -/
theorem capSuccessor_allCups
    (bubble : ∀ (L R : List B) (l : Letter I),
      CapSuccessorAt k (fun f => π ((A).diag f)) (.cup l.dual) L R L [] l R)
    (x : Letter I) (u v L U : List B) (l : Letter I) (R : List B)
    (pos : PairPlacement (Sum.inl l.dual) (Sum.inl l) u (Sum.inl x) (Sum.inl x.dual) v L U R) :
    CapSuccessorAt k (fun f => π ((A).diag f)) (.cup x) u v L U l R := by
  generalize hy : (Sum.inl x : B) = y at pos
  generalize hz : (Sum.inl x.dual : B) = z at pos
  cases pos with
  | before => subst_vars; apply capSuccessor_before (A) π (.cup x)
  | enterLeft =>
    subst_vars
    have h : x = l := by simpa using congrArg Letter.dual (Sum.inl.inj hz)
    subst x
    apply capSuccessor_cupEnterLeft RD Λ P Q e t π
  | first =>
    subst_vars
    have h := Sum.inl.inj hy
    subst x
    simpa using capSuccessor_cupFirst RD Λ P Q e t π _ _ l _
  | both =>
    have h := Sum.inl.inj hy
    subst x
    apply bubble
  | inside => subst_vars; apply capSuccessor_cupInside RD Λ P Q e t π
  | last =>
    subst_vars
    have h : x = l.dual := by simpa using congrArg Letter.dual (Sum.inl.inj hz)
    subst x
    apply capSuccessor_cupLast RD Λ P Q e t π
  | enterRight =>
    subst_vars
    have h := Sum.inl.inj hy
    subst x
    apply capSuccessor_cupEnterRight RD Λ P Q e t π
  | after => subst_vars; apply capSuccessor_after (A) π (.cup x)

end Categorification.Stendhal.DoubleDiagram
