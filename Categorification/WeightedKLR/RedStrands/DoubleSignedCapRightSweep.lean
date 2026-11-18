/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapRightCup
import Categorification.WeightedKLR.RedStrands.DoubleCapPresentation
import Categorification.WeightedKLR.RedStrands.DoubleSignedBubbleSweep
import Categorification.WeightedKLR.RedStrands.DoubleCapSuccessorTransfer

/-!
# Straightening the right cup zigzag over a signed word

Webster, arXiv:1309.3796v2, §4.5, Lemma 4.28, using KL III,
arXiv:0807.3250v1, proof of Proposition 3.11. Successive pitchforks
replace the moving cap leg by the surviving strand crossing the interval
to the right. The errors have strictly fewer crossings than the interval.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe w u v
variable {I : Type u} {ℓ : ℕ}
local notation "B" => DoubleStrand I ℓ
local notation "bl(" b ")" => (Sum.inl b : B)

/-- Move one black strand from the left side of a signed word to its right. -/
def sweepBlackRight (L : List B) (l : Letter I) : List B → List B → List (SignedLayer I ℓ)
  | [], _ => []
  | x :: U, R => signedCrossLayers L (bl(l)) x (U ++ R) ++ sweepBlackRight (L ++ [x]) l U R

private theorem black_can_cross (l : Letter I) (x : B) : CanCross (bl(l)) x := by
  cases x <;> trivial

theorem sweepBlackRight_chain (L : List B) (l : Letter I) (U R : List B) :
    signedChain (L ++ [bl(l)] ++ U ++ R) (sweepBlackRight L l U R) (L ++ U ++ [bl(l)] ++ R) := by
  induction U generalizing L with
  | nil => simp [sweepBlackRight,signedChain]
  | cons x U ih =>
    have hu := signedCrossLayers_chain L (black_can_cross l x) (U ++ R)
    have hv := ih (L ++ [x])
    simp only [List.append_assoc,List.cons_append,List.nil_append] at hu hv ⊢
    exact hu.append hv

theorem sweepBlackRight_snoc (L : List B) (l : Letter I) (U : List B) (x : B) (R : List B) :
    sweepBlackRight L l (U ++ [x]) R =
      sweepBlackRight L l U (x :: R) ++ signedCrossLayers (L ++ U) (bl(l)) x R := by
  induction U generalizing L with
  | nil => simp [sweepBlackRight]
  | cons y U ih => simp [sweepBlackRight,ih,List.append_assoc]

/-- The forward strand diagram remaining after a right cup zigzag. The dots
are on the input strand and precede the crossings. -/
def rightCupSweep (L U : List B) (l : Letter I) (R : List B) (d : ℕ) :=
  List.replicate d (L, Move.black (.dot l.dual), U ++ R) ++ sweepBlackRight L l.dual U R

theorem rightCupSweep_chain (L U : List B) (l : Letter I) (R : List B) (d : ℕ) :
    signedChain (L ++ [bl(l.dual)] ++ U ++ R) (rightCupSweep L U l R d) (L ++ U ++ [bl(l.dual)] ++ R) := by
  apply signedChain.append _ (sweepBlackRight_chain L l.dual U R)
  induction d with
  | zero => rfl
  | succ d ih =>
    exact (show signedChain _ [(L,.black (.dot l.dual),U ++ R)] _ by
      simp [signedChain,Move.bottom,Move.top,List.append_assoc]).append ih

theorem rightCupSweep_snoc (L U : List B) (l : Letter I) (x : B) (R : List B) (d : ℕ) :
    rightCupSweep L (U ++ [x]) l R d =
      rightCupSweep L U l (x :: R) d ++ signedCrossLayers (L ++ U) (bl(l.dual)) x R := by
  simp only [rightCupSweep,sweepBlackRight_snoc,List.append_assoc,List.singleton_append]

theorem sweepBlackRight_crossings (L : List B) (l : Letter I) (U R : List B) :
    signedCrossings (sweepBlackRight L l U R) = U.length := by
  induction U generalizing L with
  | nil => rfl
  | cons x U ih =>
    rw [sweepBlackRight,signedCrossings_append,signedCrossLayers_crossings _ (black_can_cross l x) _,
      ih,List.length_cons,Nat.add_comm]

theorem rightCupSweep_crossings (L U : List B) (l : Letter I) (R : List B) (d : ℕ) :
    signedCrossings (rightCupSweep L U l R d) = U.length := by
  have zero : signedCrossings (List.replicate d (L,.black (.dot l.dual),U ++ R)) = 0 := by
    induction d with
    | zero => rfl
    | succ d ih => exact ih
  rw [rightCupSweep,signedCrossings_append,zero,sweepBlackRight_crossings,Nat.zero_add]

variable {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (Λ : Fin ℓ → X) {k : Type w} [CommRing k]
  (P : Presentation.{w,max u v} (signature RD Λ) k)
  (Q : I → I → MvPolynomial (Fin 2) k) (exponents : Fin ℓ → I →₀ ℕ) (t : I → I → k)
  (μ : X)
local notation "capP" => signedCapKLPresentation RD Λ P Q exponents t
local notation "ev" => signedDg RD Λ capP μ

/-- A rightward sweep appends only physical forward moves. -/
theorem ForwardPath.sweepBlackRight {a b c : Obj (signature RD Λ)} {p : a ⟶ b} (hp : ForwardPath a p)
    (g : b ⟶ c) (L : List B) (l : Letter I) (U R : List B)
    (hg : Diagram.layers g = signedLayers RD Λ b.start (DoubleDiagram.sweepBlackRight L l U R)) :
    ForwardPath a (p ≫ g) := by
  induction U generalizing b L with
  | nil =>
    have he := Diagram.chain g
    rw [hg] at he
    subst c
    have e : g = 𝟙 b := Diagram.ext hg
    simpa [e] using hp
  | cons x U ih =>
    let A := signedLayers RD Λ b.start (signedCrossLayers L (bl(l)) x (U ++ R))
    let F := signedLayers RD Λ b.start (DoubleDiagram.sweepBlackRight (L ++ [x]) l U R)
    have he : Diagram.layers g = A ++ F := by simpa [A,F,DoubleDiagram.sweepBlackRight,signedLayers] using hg
    have hc := Diagram.chain g
    rw [he] at hc
    obtain ⟨ha,hf⟩ := Chain.of_append hc
    let v := Diagram.mk A ha
    let z := Diagram.mk F hf
    have e : g = v ≫ z := Diagram.ext he
    rw [e,← Category.assoc]
    apply ih ((CapPredecessor.cross (bl(l)) x (black_can_cross l x)).appendsForward L (U ++ R) p hp v rfl)
      z (L ++ [x])
    rw [ha.start_eq]
    rfl

/-- The normal diagram of a right cup zigzag appends to an existing forward
path without introducing a cap. -/
theorem ForwardPath.rightCupSweep {a b c : Obj (signature RD Λ)} {p : a ⟶ b} (hp : ForwardPath a p)
    (g : b ⟶ c) (L U : List B) (l : Letter I) (R : List B) (d : ℕ)
    (hg : Diagram.layers g = signedLayers RD Λ b.start (DoubleDiagram.rightCupSweep L U l R d)) :
    ForwardPath a (p ≫ g) := by
  let ds : List (SignedLayer I ℓ) := List.replicate d (L,Move.black (.dot l.dual),U ++ R)
  let A := signedLayers RD Λ b.start ds
  let F := signedLayers RD Λ b.start (DoubleDiagram.sweepBlackRight L l.dual U R)
  have he : Diagram.layers g = A ++ F := by simpa [A,F,ds,DoubleDiagram.rightCupSweep,signedLayers] using hg
  have hc := Diagram.chain g
  rw [he] at hc
  obtain ⟨ha,hf⟩ := Chain.of_append hc
  let v := Diagram.mk A ha
  let z := Diagram.mk F hf
  have e : g = v ≫ z := Diagram.ext he
  rw [e,← Category.assoc]
  have h := hp.postcompose_blackDots RD Λ b.start v ds rfl (fun x hx => by
    rw [List.eq_of_mem_replicate hx]; exact ⟨_,_,_,rfl⟩)
  apply h.sweepBlackRight RD Λ z L l.dual U R
  rw [ha.start_eq]
  rfl

private theorem capKL_pitchfork (L : List B) (x : B) (l : Letter I) (R : List B) :
    let a := L ++ [x] ++ R
    let b := L ++ [bl(l),x,bl(l.dual)] ++ R
    ev a b (signedCupFromRight L x l R) - ev a b (signedCupFromLeft L x l R) ∈
      signedCrossingSpan RD Λ capP μ a b 0 := by
  cases x with
  | inl m =>
    exact signedCup_black RD Λ capP (signedCapKL_reflectedBlack RD Λ P Q exponents t) μ L l R m
  | inr r =>
    let K := addBlackKLRelations RD Λ P
    let T := addRedCupRelations RD Λ K
    let T' := signedCapBubblePresentation RD Λ P Q exponents
    have hold : T.RelationsHold T' := fun j => T'.lin_rel_self (.inl (.inl (.inl j)))
    have h := signedDg_eq_of_ideal_le RD Λ T capP
      (fun a b => ((Presentation.relationsHold_iff_ideal_le T T').mp hold a b).trans
        (signedCapBubble_ideal_le_KL RD Λ P Q exponents t a b)) μ _ _
      (signedCup_red RD Λ K μ L l R r)
    dsimp only
    rw [h,sub_self]
    exact Submodule.zero_mem _

/-- The outside-left cup straightens exactly in the common signed presentation. -/
theorem signedCapKL_cupLeft (L U : List B) (l : Letter I) (R : List B) (d : ℕ) :
    ev (L ++ U ++ [bl(l)] ++ R) (L ++ [bl(l)] ++ U ++ R)
      ((L,.black (.cup l),U ++ [bl(l)] ++ R) :: signedCapBlock (L ++ [bl(l)]) U l R d) =
    ev (L ++ U ++ [bl(l)] ++ R) (L ++ [bl(l)] ++ U ++ R)
      (sweepBlackLeft L U l R ++ List.replicate d (L,.black (.dot l),U ++ R)) := by
  let K := addMixedCupPitchforkRelations RD Λ (addRedUpRelations RD Λ k (addRedUpSlideRelations RD Λ
    (addRedCapRelations RD Λ (addRedCupRelations RD Λ P)))) t
  let T := addBlackAdjunctionRelations RD Λ K
  let T' := signedCapBraidPresentation RD Λ P Q exponents t
  have hold : T.RelationsHold T' := fun j => T'.lin_rel_self (.inl j)
  exact signedDg_eq_of_ideal_le RD Λ T capP
    (fun a b => ((Presentation.relationsHold_iff_ideal_le T T').mp hold a b).trans
      ((signedCapBraid_ideal_le RD Λ P Q exponents t a b).trans (signedCap_ideal_le_KL RD Λ P Q exponents t a b)))
    μ _ _ (signedCapBlock_cupLeft RD Λ K μ L U l R d)

/-- With empty interior the two adjacent bends cancel exactly, including all dots. -/
theorem signedCapKL_cupRight_nil (L : List B) (l : Letter I) (R : List B) (d : ℕ) :
    ev (L ++ [bl(l.dual)] ++ [] ++ R) (L ++ [] ++ [bl(l.dual)] ++ R) (cupRightCapBlock L [] l R d) =
    ev (L ++ [bl(l.dual)] ++ [] ++ R) (L ++ [] ++ [bl(l.dual)] ++ R) (rightCupSweep L [] l R d) := by
  let K := addMixedCupPitchforkRelations RD Λ (addRedUpRelations RD Λ k (addRedUpSlideRelations RD Λ
    (addRedCapRelations RD Λ (addRedCupRelations RD Λ P)))) t
  let T := addBlackAdjunctionRelations RD Λ K
  let T' := signedCapBraidPresentation RD Λ P Q exponents t
  have hold : T.RelationsHold T' := fun j => T'.lin_rel_self (.inl j)
  have h := signedDg_eq_of_ideal_le RD Λ T capP
    (fun a b => ((Presentation.relationsHold_iff_ideal_le T T').mp hold a b).trans
      ((signedCapBraid_ideal_le RD Λ P Q exponents t a b).trans (signedCap_ideal_le_KL RD Λ P Q exponents t a b)))
    μ _ _ (signedCapBlock_cupRight_nil RD Λ K μ L l R d)
  rw [List.append_nil (L ++ [bl(l.dual)]),List.append_nil L]
  simpa only [List.append_nil,List.nil_append,rightCupSweep,sweepBlackRight] using h

/-- In the common signed KL presentation the right-hand cup zigzag over a
nonempty signed word differs from the forward dotted right sweep by diagrams
with strictly fewer crossings, as in Webster v2, §4.5, Lemma 4.28. -/
theorem signedCapKL_cupRight (L U : List B) (l : Letter I) (R : List B) (d : ℕ) :
    ev (L ++ [bl(l.dual)] ++ U ++ R) (L ++ U ++ [bl(l.dual)] ++ R) (cupRightCapBlock L U l R d) -
        ev (L ++ [bl(l.dual)] ++ U ++ R) (L ++ U ++ [bl(l.dual)] ++ R) (rightCupSweep L U l R d) ∈
      signedCrossingSpan RD Λ capP μ (L ++ [bl(l.dual)] ++ U ++ R) (L ++ U ++ [bl(l.dual)] ++ R) (U.length-1) := by
  induction U using List.reverseRecOn generalizing R with
  | nil =>
    rw [signedCapKL_cupRight_nil RD Λ P Q exponents t μ L l R d,sub_self]
    exact Submodule.zero_mem _
  | append_singleton U x ih =>
    let X₁ := signedCrossLayers (L ++ U) (bl(l.dual)) x R
    let s := (L ++ [bl(l.dual)] ++ U) ++ [x] ++ R
    let b := (L ++ U) ++ [bl(l.dual),x] ++ R
    let z := (L ++ U) ++ [x,bl(l.dual)] ++ R
    have hs : (L ++ [bl(l.dual)] ++ (U ++ [x]) ++ R) = s := by simp [s,List.append_assoc]
    have hz : (L ++ (U ++ [x]) ++ [bl(l.dual)] ++ R) = z := by simp [z,List.append_assoc]
    rw [hs,hz,rightCupSweep_snoc]
    have step := signedCapBlock_cupRight_last RD Λ capP μ L U l R x d
      (capKL_pitchfork RD Λ P Q exponents t μ (L ++ [bl(l.dual)] ++ U) x l R)
    have ha : (L ++ [bl(l.dual)] ++ U ++ (x :: R)) = s := by simp [s,List.append_assoc]
    have hb : (L ++ U ++ [bl(l.dual)] ++ (x :: R)) = b := by simp [b,List.append_assoc]
    have hc := cupRightCapBlock_chain L U l (x :: R) d
    have hn := rightCupSweep_chain L U l (x :: R) d
    rw [ha,hb] at hc hn
    have hx : signedChain b X₁ z := signedCrossLayers_chain (L ++ U) (black_can_cross l.dual x) R
    have hbudget : (U ++ [x]).length-1 = U.length := by simp
    rw [hbudget]
    change ev s z _ - ev s z _ ∈ _ at step ⊢
    suffices derr : ev s z (cupRightCapBlock L U l (x :: R) d ++ X₁) -
        ev s z (rightCupSweep L U l (x :: R) d ++ X₁) ∈ signedCrossingSpan RD Λ capP μ s z U.length by
      dsimp only [X₁] at derr
      simpa only [sub_add_sub_cancel] using Submodule.add_mem _ step derr
    by_cases empty : U = []
    · subst U
      have h := signedCapKL_cupRight_nil RD Λ P Q exponents t μ L l (x :: R) d
      rw [ha,hb] at h
      rw [← signedDg_comp RD Λ capP μ hc hx,← signedDg_comp RD Λ capP μ hn hx,h,sub_self]
      exact Submodule.zero_mem _
    · have h := ih (x :: R)
      rw [ha,hb] at h
      have er := signedDg_replace_span RD Λ capP μ (show signedChain s [] s from rfl) hc hn hx h
      have n : signedCrossings X₁ = 1 := signedCrossLayers_crossings _ (black_can_cross l.dual x) _
      have hn' : 0 < U.length := List.length_pos_iff.mpr empty
      rw [show signedCrossings ([] : List (SignedLayer I ℓ))=0 from rfl,n,
        show 0 + (U.length-1) + 1 = U.length by omega] at er
      exact er

end Categorification.Stendhal.DoubleDiagram
