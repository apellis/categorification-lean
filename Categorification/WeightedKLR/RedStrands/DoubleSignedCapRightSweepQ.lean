/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapRightSweep
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapRightCup
import Categorification.WeightedKLR.RedStrands.DoubleCapPresentationQ
import Categorification.WeightedKLR.RedStrands.DoubleSignedBubbleSweepQ
import Categorification.WeightedKLR.RedStrands.DoubleCapSuccessorTransfer
import Categorification.WeightedKLR.RedStrands.DoubleSignedCupPitchforkQ
import Categorification.WeightedKLR.RedStrands.DoubleCapSuccessorUnits

/-!
# Straightening the right cup zigzag over a signed word

Webster, arXiv:1309.3796v2, §4.5, Lemma 4.28, using KL III,
arXiv:0807.3250v1, proof of Proposition 3.11. Successive pitchforks
replace the moving cap leg by the surviving strand crossing the interval
to the right. The errors have strictly fewer crossings than the interval.

This is the version of `DoubleSignedCapRightSweep` in which the black strands carry the relations of
Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3, Definition 1.1, `r = 1`; `CLQ.pres RD k sc`) instead
of the KL III relations. Each declaration carries the suffix `Q`.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe w u v
variable {I : Type u} {ℓ : ℕ}
local notation "B" => DoubleStrand I ℓ
local notation "bl(" b ")" => (Sum.inl b : B)

private theorem black_can_cross (l : Letter I) (x : B) : CanCross (bl(l)) x := by
  cases x <;> trivial

theorem sweepBlackRight_chainQ (L : List B) (l : Letter I) (U R : List B) :
    signedChain (L ++ [bl(l)] ++ U ++ R) (sweepBlackRight L l U R) (L ++ U ++ [bl(l)] ++ R) := by
  induction U generalizing L with
  | nil => simp [sweepBlackRight,signedChain]
  | cons x U ih =>
    have hu := signedCrossLayers_chain L (black_can_cross l x) (U ++ R)
    have hv := ih (L ++ [x])
    simp only [List.append_assoc,List.cons_append,List.nil_append] at hu hv ⊢
    exact hu.append hv

theorem rightCupSweep_chainQ (L U : List B) (l : Letter I) (R : List B) (d : ℕ) :
    signedChain (L ++ [bl(l.dual)] ++ U ++ R) (rightCupSweep L U l R d) (L ++ U ++ [bl(l.dual)] ++ R) := by
  apply signedChain.append _ (sweepBlackRight_chainQ L l.dual U R)
  induction d with
  | zero => rfl
  | succ d ih =>
    exact (show signedChain _ [(L,.black (.dot l.dual),U ++ R)] _ by
      simp [signedChain,Move.bottom,Move.top,List.append_assoc]).append ih

theorem sweepBlackRight_crossingsQ (L : List B) (l : Letter I) (U R : List B) :
    signedCrossings (sweepBlackRight L l U R) = U.length := by
  induction U generalizing L with
  | nil => rfl
  | cons x U ih =>
    rw [sweepBlackRight,signedCrossings_append,signedCrossLayers_crossings _ (black_can_cross l x) _,
      ih,List.length_cons,Nat.add_comm]

theorem rightCupSweep_crossingsQ (L U : List B) (l : Letter I) (R : List B) (d : ℕ) :
    signedCrossings (rightCupSweep L U l R d) = U.length := by
  have zero : signedCrossings (List.replicate d (L,.black (.dot l.dual),U ++ R)) = 0 := by
    induction d with
    | zero => rfl
    | succ d ih => exact ih
  rw [rightCupSweep,signedCrossings_append,zero,sweepBlackRight_crossingsQ,Nat.zero_add]

variable {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (Λ : Fin ℓ → X) {k : Type w} [CommRing k] (sc : KL3.Diagram.CL.CLScalars C k)
  (P : Presentation.{w,max u v} (signature RD Λ) k)
  (Q : I → I → MvPolynomial (Fin 2) k) (exponents : Fin ℓ → I →₀ ℕ) (t : I → I → k)
  (μ : X)
local notation "capP" => signedCapKLPresentationQ RD Λ sc P Q exponents t
local notation "ev" => signedDg RD Λ capP μ

private theorem capKL_pitchforkQ (L : List B) (x : B) (l : Letter I) (R : List B) :
    let a := L ++ [x] ++ R
    let b := L ++ [bl(l),x,bl(l.dual)] ++ R
    ∃ c : kˣ, ev a b (signedCupFromRight L x l R) - (c : k) • ev a b (signedCupFromLeft L x l R) ∈
      signedCrossingSpan RD Λ capP μ a b 0 := by
  cases x with
  | inl m =>
    exact signedCup_blackQ RD Λ sc capP (signedCapKL_reflectedBlackQ RD Λ sc P Q exponents t) μ L l R m
  | inr r =>
    let K := addBlackKLRelationsQ RD Λ sc P
    let T := addRedCupRelations RD Λ K
    let T' := signedCapBubblePresentationOf RD Λ (CLQ.pres RD k sc) P Q exponents
    have hold : T.RelationsHold T' := fun j => T'.lin_rel_self (.inl (.inl (.inl j)))
    have h := signedDg_eq_of_ideal_le RD Λ T capP
      (fun a b => ((Presentation.relationsHold_iff_ideal_le T T').mp hold a b).trans
        (signedCapBubbleOf_ideal_le RD Λ (CLQ.pres RD k sc) P Q exponents t a b)) μ _ _
      (signedCup_red RD Λ K μ L l R r)
    refine ⟨1, ?_⟩
    rw [h, Units.val_one, one_smul, sub_self]
    exact Submodule.zero_mem _

/-- The outside-left cup straightens exactly in the common signed presentation. -/
theorem signedCapKL_cupLeftQ (L U : List B) (l : Letter I) (R : List B) (d : ℕ) :
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
      ((signedCapBraid_ideal_le RD Λ P Q exponents t a b).trans (signedCap_ideal_le_KLQ RD Λ sc P Q exponents t a b)))
    μ _ _ (signedCapBlock_cupLeft RD Λ K μ L U l R d)

/-- With empty interior the two adjacent bends cancel exactly, including all dots. -/
theorem signedCapKL_cupRight_nilQ (L : List B) (l : Letter I) (R : List B) (d : ℕ) :
    ev (L ++ [bl(l.dual)] ++ [] ++ R) (L ++ [] ++ [bl(l.dual)] ++ R) (cupRightCapBlock L [] l R d) =
    ev (L ++ [bl(l.dual)] ++ [] ++ R) (L ++ [] ++ [bl(l.dual)] ++ R) (rightCupSweep L [] l R d) := by
  let K := addMixedCupPitchforkRelations RD Λ (addRedUpRelations RD Λ k (addRedUpSlideRelations RD Λ
    (addRedCapRelations RD Λ (addRedCupRelations RD Λ P)))) t
  let T := addBlackAdjunctionRelations RD Λ K
  let T' := signedCapBraidPresentation RD Λ P Q exponents t
  have hold : T.RelationsHold T' := fun j => T'.lin_rel_self (.inl j)
  have h := signedDg_eq_of_ideal_le RD Λ T capP
    (fun a b => ((Presentation.relationsHold_iff_ideal_le T T').mp hold a b).trans
      ((signedCapBraid_ideal_le RD Λ P Q exponents t a b).trans (signedCap_ideal_le_KLQ RD Λ sc P Q exponents t a b)))
    μ _ _ (signedCapBlock_cupRight_nil RD Λ K μ L l R d)
  rw [List.append_nil (L ++ [bl(l.dual)]),List.append_nil L]
  simpa only [List.append_nil,List.nil_append,rightCupSweep,sweepBlackRight] using h

/-- In the common signed presentation with `U_Q(g)` black relations, the right-hand cup
zigzag over a signed word differs from a unit multiple of the forward dotted right sweep by
diagrams with strictly fewer crossings, as in Webster v3, §4.5, Lemma 4.29. The unit is the
product of the cup pitchfork scalars of the black strands passed. -/
theorem signedCapKL_cupRightQ (L U : List B) (l : Letter I) (R : List B) (d : ℕ) :
    ∃ c : kˣ,
    ev (L ++ [bl(l.dual)] ++ U ++ R) (L ++ U ++ [bl(l.dual)] ++ R) (cupRightCapBlock L U l R d) -
        (c : k) • ev (L ++ [bl(l.dual)] ++ U ++ R) (L ++ U ++ [bl(l.dual)] ++ R) (rightCupSweep L U l R d) ∈
      signedCrossingSpan RD Λ capP μ (L ++ [bl(l.dual)] ++ U ++ R) (L ++ U ++ [bl(l.dual)] ++ R) (U.length-1) := by
  induction U using List.reverseRecOn generalizing R with
  | nil =>
    refine ⟨1, ?_⟩
    rw [signedCapKL_cupRight_nilQ RD Λ sc P Q exponents t μ L l R d, Units.val_one, one_smul, sub_self]
    exact Submodule.zero_mem _
  | append_singleton U x ih =>
    let X₁ := signedCrossLayers (L ++ U) (bl(l.dual)) x R
    let s := (L ++ [bl(l.dual)] ++ U) ++ [x] ++ R
    let b := (L ++ U) ++ [bl(l.dual),x] ++ R
    let z := (L ++ U) ++ [x,bl(l.dual)] ++ R
    have hs : (L ++ [bl(l.dual)] ++ (U ++ [x]) ++ R) = s := by simp [s,List.append_assoc]
    have hz : (L ++ (U ++ [x]) ++ [bl(l.dual)] ++ R) = z := by simp [z,List.append_assoc]
    rw [hs,hz,rightCupSweep_snoc]
    obtain ⟨c₁, hpf⟩ := capKL_pitchforkQ RD Λ sc P Q exponents t μ (L ++ [bl(l.dual)] ++ U) x l R
    have step := signedCapBlock_cupRight_last_smul RD Λ capP μ L U l R x d (c₁ : k) hpf
    have ha : (L ++ [bl(l.dual)] ++ U ++ (x :: R)) = s := by simp [s,List.append_assoc]
    have hb : (L ++ U ++ [bl(l.dual)] ++ (x :: R)) = b := by simp [b,List.append_assoc]
    have hc := cupRightCapBlock_chain L U l (x :: R) d
    have hn := rightCupSweep_chainQ L U l (x :: R) d
    rw [ha,hb] at hc hn
    have hx : signedChain b X₁ z := signedCrossLayers_chain (L ++ U) (black_can_cross l.dual x) R
    have hbudget : (U ++ [x]).length-1 = U.length := by simp
    rw [hbudget]
    change ev s z _ - _ • ev s z _ ∈ _ at step
    suffices derr : ∃ c₂ : kˣ, ev s z (cupRightCapBlock L U l (x :: R) d ++ X₁) -
        (c₂ : k) • ev s z (rightCupSweep L U l (x :: R) d ++ X₁) ∈
          signedCrossingSpan RD Λ capP μ s z U.length by
      obtain ⟨c₂, h₂⟩ := derr
      refine ⟨c₁ * c₂, ?_⟩
      have e : ev s z (cupRightCapBlock L (U ++ [x]) l R d) -
          ((c₁ * c₂ : kˣ) : k) • ev s z (rightCupSweep L U l (x :: R) d ++ X₁) =
          (ev s z (cupRightCapBlock L (U ++ [x]) l R d) -
            (c₁ : k) • ev s z (cupRightCapBlock L U l (x :: R) d ++ X₁)) +
          (c₁ : k) • (ev s z (cupRightCapBlock L U l (x :: R) d ++ X₁) -
            (c₂ : k) • ev s z (rightCupSweep L U l (x :: R) d ++ X₁)) := by
        rw [Units.val_mul, smul_sub, smul_smul]; abel
      dsimp only [X₁] at e h₂ ⊢
      rw [e]
      exact Submodule.add_mem _ step (Submodule.smul_mem _ _ h₂)
    by_cases empty : U = []
    · subst U
      refine ⟨1, ?_⟩
      have h := signedCapKL_cupRight_nilQ RD Λ sc P Q exponents t μ L l (x :: R) d
      rw [ha,hb] at h
      rw [← signedDg_comp RD Λ capP μ hc hx,← signedDg_comp RD Λ capP μ hn hx,h,Units.val_one,
        one_smul,sub_self]
      exact Submodule.zero_mem _
    · obtain ⟨c₂, h⟩ := ih (x :: R)
      refine ⟨c₂, ?_⟩
      rw [ha,hb] at h
      have er := signedDg_replace_span_smul RD Λ capP μ (show signedChain s [] s from rfl) hc hn hx
        (c₂ : k) h
      have n : signedCrossings X₁ = 1 := signedCrossLayers_crossings _ (black_can_cross l.dual x) _
      have hn' : 0 < U.length := List.length_pos_iff.mpr empty
      rw [show signedCrossings ([] : List (SignedLayer I ℓ))=0 from rfl,n,
        show 0 + (U.length-1) + 1 = U.length by omega] at er
      simpa only [List.nil_append] using er

end Categorification.Stendhal.DoubleDiagram
