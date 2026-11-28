/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721TraceCyclicMatTwo
import Categorification.WeightedKLR.Rigidity.CupCapProp721FDotTrace

/-!
# The two-step trace of `𝔈_i² ⊣ 𝔉_i²` is symmetric against the crossing, on modules

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, Theorem 4.31
and §5.1, as used in §7.3, proof of Proposition 7.21. On right `T^λ`-modules the crossing on
`𝔉_i² = Ind Ind` is defined as the conjugate, along the composite of the adjunctions
`𝔉_i ⊣ 𝔈_i` (induction ⊣ restriction), of the crossing on `𝔈_i²` (`indCrossOfEq`). Its conjugate
along the composite of the adjunctions `𝔈_i ⊣ 𝔉_i` of Theorem 4.31
(`CupCap.blackEFAdjunction`) is the same, provided the two-step trace is symmetric against the
crossing (`CupCap.conjugateEquiv_resAct₂_eq_of_trace`).

That symmetry is transported, through the repaired Lemma 4.29 (`clOpEquivQ`), from the
composite of the adjunctions along the matrix maps of the downward black strand
(`DoubleDiagram.blackResIndAdjunctionQ`); the transport carries minus the crossing of `T^λ` to
the diagonal matrix of the black-action crossing (`clOpEquivQ_neg_appendedCross`), and the
two-step trace of the matrix adjunctions is symmetric against it when the black-action crossing
`crossNatQ` is cyclic for the composite completed adjunctions
(`KLR.Diagram.MatEnd.resIndTrace₂_cyclic`).

## Main results

* `CupCap.clBlackResIndAdjunctionQ_trace_cross`: the two-step trace of the composite of
  `clBlackResIndAdjunctionQ` is symmetric against the crossing, given the cyclicity `hcyc` of the
  completed black-action crossing.
* `CupCap.clBlackResIndAdjunctionQ_conjugate_blackCross`: under `hcyc`, the conjugate of
  `blackCross` along the composite of `clBlackResIndAdjunctionQ` is `indCrossOfEq`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open CategoryTheory CategoryTheory.Idempotents QuantumGroup QuantumGroup.UDot StringDiagrams
  KLR TwoRep CyclotomicAction DoubleDiagram KL3.Diagram MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section CL

open scoped Classical

-- `OrdSeq` carries a second `Fintype` instance; the matrix rings use `Subtype.fintype`.
attribute [-instance] Categorification.Stendhal.instFintypeOrdSeq

variable {I : Type} {ℓ : ℕ} {Λ : Fin ℓ → I →₀ ℕ} {C : CartanDatum I}
  {k : Type} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {hQ : IsRouquierQ C Q}

variable {P : Presentation.{0, 0}
    (signature (coordinateDatum Λ C) (redWeight (cyclotomicCoverWeightDatum Λ C))) k}
  (hP : CoverRelsNegligible.{0, 0, 0} Λ C hQ (coverDotCentral Λ C hQ)
    (blockWeight (cyclotomicCoverWeightDatum Λ C) (cyclotomicCoverHighest (I := I) (ℓ := ℓ)) 0 :
      I ⊕ Fin ℓ → ℤ) P)
  (hwf : P.WFDom)
  (i : I) (ν : Multiset I)

local notation "RDc" => coordinateDatum Λ C
local notation "KL" => blackScalarsQ Λ C hQ
local notation "Pin" => addDownRelations (RDc) (Subtype.val ∘ coordinateRedWeights Λ C)
  (affineCoverQ (clDownwardQ (KL)) Λ) (signedCapPresentationOf (RDc)
    (redWeight (cyclotomicCoverWeightDatum Λ C)) (CLQ.pres (RDc) k (KL)) P (clDownwardQ (KL)) Λ
    fun i j => (CL.CLScalars.t (KL) i j : k))
local notation "PD" => clDownwardBlockQ Λ C hQ P
local notation "hPD" => clDownwardBlockQ_reflectedBlack P
local notation "νᵢ" => (Singleton.singleton i : Multiset I) + ν
local notation "νᵢᵢ" => (Singleton.singleton i : Multiset I) + ((Singleton.singleton i :
  Multiset I) + ν)
local notation "Ma" μ:max => DoubleDiagram.blackResIndAdjunctionQ (Pin) (CL.CLScalars.t (KL)) i μ
  (clDownwardBlockQ_reflectedBlack P)
local notation "F₁" => blackAct (PD) [(false, i)] (wt_downRightWeight i ν)
local notation "F₂" => blackAct (PD) [(false, i)] (wt_downRightWeight i ((Singleton.singleton i :
  Multiset I) + ν))

variable (P) in
/-- **The completed black-action crossing is cyclic for the composite completed adjunctions**
`Fᵢ Fᵢ ⊣ Eᵢ Eᵢ` and `Eᵢ Eᵢ ⊣ Fᵢ Fᵢ` (the statement used by Theorem 4.31 for the crossing). -/
def BlackCrossCyclicQ : Prop :=
  conjugateEquiv
      ((blackCompletedAdjunctionOpQ (PD) (hPD) i (wt_downRightWeight i (νᵢ))
          (wt_upDownRightWeight i (νᵢ))).comp
        (blackCompletedAdjunctionOpQ (PD) (hPD) i (wt_downRightWeight i ν)
          (wt_upDownRightWeight i ν)))
      ((blackCompletedAdjunctionOpQ (PD) (hPD) i (wt_downRightWeight i (νᵢ))
          (wt_upDownRightWeight i (νᵢ))).comp
        (blackCompletedAdjunctionOpQ (PD) (hPD) i (wt_downRightWeight i ν)
          (wt_upDownRightWeight i ν)))
      (conjugateEquiv
        ((blackCompletedAdjunctionQ (PD) (hPD) i (wt_downRightWeight i ν)
            (wt_upDownRightWeight i ν)).comp
          (blackCompletedAdjunctionQ (PD) (hPD) i (wt_downRightWeight i (νᵢ))
            (wt_upDownRightWeight i (νᵢ))))
        ((blackCompletedAdjunctionQ (PD) (hPD) i (wt_downRightWeight i ν)
            (wt_upDownRightWeight i ν)).comp
          (blackCompletedAdjunctionQ (PD) (hPD) i (wt_downRightWeight i (νᵢ))
            (wt_upDownRightWeight i (νᵢ))))
        (KLR.Diagram.MatEnd.compCompletion (F₁) (F₂) (crossNatQ (PD) (hPD) i ν))) =
    KLR.Diagram.MatEnd.compCompletion (F₁) (F₂) (crossNatQ (PD) (hPD) i ν)

theorem op_neg_appendedCross_commute (a : (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ) :
    op (-appendedCross Q Λ i ν) * appendBlackOp Q Λ i (νᵢ) (appendBlackOp Q Λ i ν a) =
      appendBlackOp Q Λ i (νᵢ) (appendBlackOp Q Λ i ν a) * op (-appendedCross Q Λ i ν) := by
  rw [MulOpposite.op_neg, neg_mul, mul_neg, op_appendedCross_commute]

/-- **The two-step trace of `𝔈_i² ⊣ 𝔉_i²` is symmetric against the crossing** (Webster,
arXiv:1309.3796v3, Theorem 4.31), for the composite of the adjunctions
`clBlackResIndAdjunctionQ` with an auxiliary presentation `P` as in Theorem 4.30, given the
cyclicity `hcyc` of the completed black-action crossing: transported from the all-down matrix
rings through the repaired Lemma 4.29. -/
theorem clBlackResIndAdjunctionQ_trace_cross (hcyc : BlackCrossCyclicQ (Q := Q) (hQ := hQ) P i ν)
    (w : Corner (appendBlackOp Q Λ i (νᵢ)))
    (hw : appendBlackOp Q Λ i (νᵢ) (appendBlackOp Q Λ i ν 1) * w.1 = w.1) :
    resIndTrace₂ (clBlackResIndAdjunctionQ.{0, 0} hP hwf i ν)
        (clBlackResIndAdjunctionQ.{0, 0} hP hwf i (νᵢ)) (op (appendedCross Q Λ i ν) • w)
        (smul_fixed₂ (op_appendedCross_commute Q Λ i ν) w hw) =
      resIndTrace₂ (clBlackResIndAdjunctionQ.{0, 0} hP hwf i ν)
        (clBlackResIndAdjunctionQ.{0, 0} hP hwf i (νᵢ))
        (Corner.twoStepRightElem (op (appendedCross Q Λ i ν)) w
          (unitGen (appendBlackOp Q Λ i ν)))
        (twoStepRightElem_fixed₂ w hw) := by
  have h2 := KLR.Diagram.MatEnd.resIndTrace₂_cyclic (F₁) (F₂)
    (appendDown_injective i) (blackAct_downObj (PD) i)
    (appendDown_injective i) (blackAct_downObj (PD) i)
    (blackCompletedAdjunctionQ (PD) (hPD) i (wt_downRightWeight i ν) (wt_upDownRightWeight i ν))
    (blackCompletedAdjunctionOpQ (PD) (hPD) i (wt_downRightWeight i ν)
      (wt_upDownRightWeight i ν))
    (blackUp_downSum_generated (Pin) (CL.CLScalars.t (KL)) i ν).choose_spec.choose
    (blackUp_downSum_generated (Pin) (CL.CLScalars.t (KL)) i ν).choose_spec.choose_spec.choose
    (blackUp_downSum_generated (Pin) (CL.CLScalars.t (KL)) i ν).choose_spec.choose_spec.choose_spec
    (blackCompletedAdjunctionQ (PD) (hPD) i (wt_downRightWeight i (νᵢ))
      (wt_upDownRightWeight i (νᵢ)))
    (blackCompletedAdjunctionOpQ (PD) (hPD) i (wt_downRightWeight i (νᵢ))
      (wt_upDownRightWeight i (νᵢ)))
    (blackUp_downSum_generated (Pin) (CL.CLScalars.t (KL)) i (νᵢ)).choose_spec.choose
    (blackUp_downSum_generated (Pin) (CL.CLScalars.t (KL)) i (νᵢ)).choose_spec.choose_spec.choose
    (blackUp_downSum_generated (Pin) (CL.CLScalars.t (KL)) i
      (νᵢ)).choose_spec.choose_spec.choose_spec
    (crossNatQ (PD) (hPD) i ν) hcyc
  have h3 := resIndTrace₂_cyclic_of_eq (Ma ν) (Ma (νᵢ))
    (clOpEquivQ_neg_appendedCross hP hwf i ν)
    (transport_commute₂ (clOpEquivQ hP hwf ν) (clOpEquivQ hP hwf (νᵢ)) (clOpEquivQ hP hwf (νᵢᵢ))
      (clOpEquiv_appendBlackQ hP hwf i ν) (clOpEquiv_appendBlackQ hP hwf i (νᵢ))
      (op_neg_appendedCross_commute i ν))
    (KLR.Diagram.MatEnd.natEmb_comp_commute (F₁) (F₂)
      (appendDown_injective i) (blackAct_downObj (PD) i)
      (appendDown_injective i) (blackAct_downObj (PD) i) (crossNatQ (PD) (hPD) i ν)) h2
  have h4 := resIndTrace₂_transport_cyclic (clOpEquivQ hP hwf ν) (clOpEquivQ hP hwf (νᵢ))
    (clOpEquivQ hP hwf (νᵢᵢ)) (clOpEquiv_appendBlackQ hP hwf i ν)
    (clOpEquiv_appendBlackQ hP hwf i (νᵢ)) (Ma ν) (Ma (νᵢ))
    (op_neg_appendedCross_commute i ν) h3
  have hneg : ∀ a, (-op (appendedCross Q Λ i ν)) *
      appendBlackOp Q Λ i (νᵢ) (appendBlackOp Q Λ i ν a) =
        appendBlackOp Q Λ i (νᵢ) (appendBlackOp Q Λ i ν a) * (-op (appendedCross Q Λ i ν)) :=
    fun a => by rw [neg_mul, mul_neg, op_appendedCross_commute]
  exact resIndTrace₂_cyclic_of_neg _ _ (op_appendedCross_commute Q Λ i ν) hneg
    (resIndTrace₂_cyclic_of_eq _ _ (MulOpposite.op_neg (appendedCross Q Λ i ν)).symm hneg
      (op_neg_appendedCross_commute i ν) h4) w hw

/-- **The conjugate of the crossing along `𝔈_i² ⊣ 𝔉_i²` is the crossing on `𝔉_i²`** (Webster,
arXiv:1309.3796v3, Theorem 4.31 and §5.1), for the composite of the adjunctions
`clBlackResIndAdjunctionQ` with an auxiliary presentation `P` as in Theorem 4.30, given the
cyclicity `hcyc` of the completed black-action crossing. -/
theorem clBlackResIndAdjunctionQ_conjugate_blackCross (hsym : KLRSymm Q)
    (hcyc : BlackCrossCyclicQ (Q := Q) (hQ := hQ) P i ν) :
    conjugateEquiv ((clBlackResIndAdjunctionQ.{0, 0} hP hwf i (νᵢ)).comp
          (clBlackResIndAdjunctionQ.{0, 0} hP hwf i ν))
        ((clBlackResIndAdjunctionQ.{0, 0} hP hwf i (νᵢ)).comp
          (clBlackResIndAdjunctionQ.{0, 0} hP hwf i ν)) (blackCross Q Λ i ν) =
      indCrossOfEq Λ hsym i i (rfl : ({i} : Multiset I) + ν = _) rfl rfl rfl := by
  refine (conjugateEquiv_resAct₂_eq_of_trace _ _ (op_appendedCross_fix Q Λ i ν)
    (op_appendedCross_commute Q Λ i ν) _ (fun _ => rfl)
    (clBlackResIndAdjunctionQ_trace_cross hP hwf i ν hcyc)).trans ?_
  rw [indCrossOfEq, resCrossOfEq_self]
  rfl

end CL

end Categorification.Stendhal.CupCap
