/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackRouqMatrixSumInvQ
import Categorification.WeightedKLR.RedStrands.BlackRouqModuleCaps
import Categorification.WeightedKLR.RedStrands.BlackModuleEFTransportQ
import Categorification.WeightedKLR.RedStrands.DoubleCLNewStrandQ
import Categorification.Algebra.InductionAlongSumInvTransport
import Categorification.Diagrams.KLR.MatEndNatEmbNeg

/-!
# Brundan's inversion relations for Webster's functors on `T^λ`-modules

Brundan, arXiv:1501.00350v1, (1.8) and (1.9), for Webster's functors on right modules over the
tensor product algebra `T^λ` (arXiv:1309.3796v3, §4.6, Theorem 4.31): `Fᵢ` is induction along
the map adding a black strand and `Eᵢ` restriction along it. The rightward crossing
`blackModuleSigma` is built from the unit and counit of `Fᵢ ⊣ Eᵢ` and the crossing of two new
strands, which acts as `-ψ` (the convention of Khovanov–Lauda III); the dot is the dot on the
new strand.

* `clBlackModuleSumInvToQ`: for `⟨i, λ⟩ ≤ 0` (with `λ` the right weight of content `i + ν`),
  the rightward crossing together with the dotted counits `Eᵢ x^m ε` has an explicit inverse
  among endofunctors of the module category;
* `clBlackModuleSumInvFromQ`: for `0 ≤ ⟨i, λ⟩`, the same with the dotted units `η x^m Eᵢ`.

Both come from the statements on the all-down matrix ring (`blackMatrixSumInvToQ`,
`blackMatrixSumInvFromQ`), transported through the repaired Lemma 4.29 (`clOpEquivQ`), under
which the new-strand dot is the black-action dot (`clOpEquivQ_appendedDot`) and the new-strand
crossing is minus the black-action crossing (`clOpEquivQ_neg_appendedCross`). The presentation
`P` is subject to the hypotheses of Webster's Theorem 4.30 in the library: negligible cover
relations (`CoverRelsNegligible`) and well-founded domains (`WFDom`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory CategoryTheory.Idempotents QuantumGroup QuantumGroup.UDot StringDiagrams
  KLR TwoRep CyclotomicAction DoubleDiagram KL3.Diagram InductionAlong MulOpposite

open scoped Classical

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 2000] InductionAlong.instModuleInd InductionAlong.Res.instModule

universe u w

variable {I : Type u} {ℓ : ℕ} {Λ : Fin ℓ → I →₀ ℕ} {C : CartanDatum I}
  {k : Type u} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {hQ : IsRouquierQ C Q}

local notation "RDc" => coordinateDatum Λ C
local notation "KL" => blackScalarsQ Λ C hQ

variable {P : Presentation.{u, u}
    (signature (coordinateDatum Λ C) (redWeight (cyclotomicCoverWeightDatum Λ C))) k}
  (hP : CoverRelsNegligible.{u, u, w} Λ C hQ (coverDotCentral Λ C hQ)
    (blockWeight (cyclotomicCoverWeightDatum Λ C) (cyclotomicCoverHighest (I := I) (ℓ := ℓ)) 0 :
      I ⊕ Fin ℓ → ℤ) P)
  (hwf : P.WFDom)
  (i : I) (ν : Multiset I)

local notation "Pin" => addDownRelations (RDc) (Subtype.val ∘ coordinateRedWeights Λ C)
  (affineCoverQ (clDownwardQ KL) Λ) (signedCapPresentationOf (RDc)
    (redWeight (cyclotomicCoverWeightDatum Λ C)) (CLQ.pres (RDc) k KL) P (clDownwardQ KL) Λ
    fun i j => (CL.CLScalars.t KL i j : k))

/-- Under the repaired Lemma 4.29, the new-strand crossing `-ψ_n` of `T^λ` is the crossing element
`blackMatrixCrossQ` of the all-down matrix ring (the diagonal matrix of minus the black-action
crossing). -/
theorem clOpEquivQ_appendedCross :
    clOpEquivQ hP hwf ({i} + ({i} + ν)) (op (appendedCross Q Λ i ν)) =
      blackMatrixCrossQ (Pin) (CL.CLScalars.t KL) i ν (clDownwardBlockQ_reflectedBlack P) := by
  rw [blackMatrixCrossQ, KLR.Diagram.MatEnd.natEmb_neg, MulOpposite.op_neg,
    ← clOpEquivQ_neg_appendedCross hP hwf i ν, MulOpposite.op_neg, map_neg, neg_neg]
  exact (appendDown_injective i).comp (appendDown_injective i)

/-- **Brundan (1.8) for Webster's functors on `T^λ`-modules** (Webster, arXiv:1309.3796v3,
§4.6, Theorem 4.31, with the repaired Lemma 4.29 and Theorem 4.30): for `⟨i, λ⟩ ≤ 0`, with `λ`
the right weight of content `i + ν`, the rightward crossing `blackModuleSigma` of `Fᵢ ⊣ Eᵢ`
(the same-colour crossing acting as `-ψ`) together with the dotted counits `Eᵢ x^m ε` has an
explicit inverse, for a presentation `P` with negligible cover relations
(`CoverRelsNegligible`) and well-founded domains (`WFDom`). -/
def clBlackModuleSumInvToQ (hsym : KLRSymm Q)
    (hn : ip (RDc) i (downRightWeight (RDc) (coordinateRedWeights Λ C) ({i} + ν)) ≤ 0) :
    SumInvTo (blackModuleSigma Λ hsym i ν)
      (fun m => Functor.whiskerLeft (blackEOfEq Q Λ i (rfl : ({i} : Multiset I) + ν = _))
        (powComp (indDotOfEq Q Λ i rfl) m) ≫ (blackAdjOfEq Q Λ i rfl).counit)
      (-ip (RDc) i (downRightWeight (RDc) (coordinateRedWeights Λ C) ({i} + ν))).toNat :=
  blackModuleSumInvTo Λ hsym i ν fun M =>
    sumInvTo_transport (clOpEquivQ hP hwf ν) (clOpEquivQ hP hwf ({i} + ν))
      (clOpEquivQ hP hwf ({i} + ({i} + ν))) (clOpEquiv_appendBlackQ hP hwf i ν)
      (clOpEquiv_appendBlackQ hP hwf i ({i} + ν)) M
      (ModuleCat.of _ (ClMatViewQ hP hwf i ν M)) (toClMatViewQ hP hwf i ν M)
      (toClMatView_smulQ hP hwf i ν M) (op_appendedCross_commute Q Λ i ν)
      (blackMatrixCrossQ_commute (Pin) (CL.CLScalars.t KL) i ν (clDownwardBlockQ_reflectedBlack P))
      (clOpEquivQ_appendedCross hP hwf i ν)
      (intertwines_of_commute (op_appendedDot_commute Q Λ i ν))
      (blackMatrixDotQ_intertwines (Pin) (CL.CLScalars.t KL) i ν
        (clDownwardBlockQ_reflectedBlack P))
      (clOpEquivQ_appendedDot hP hwf i ν)
      (blackMatrixSumInvToQ (Pin) (CL.CLScalars.t KL) i ν (clDownwardBlockQ_reflectedBlack P)
        (ModuleCat.of _ (ClMatViewQ hP hwf i ν M)) hn)

/-- Under the repaired Lemma 4.29, the new-strand dot of `T^λ` is the dot element
`blackMatrixDotQ` of the all-down matrix ring. -/
theorem clOpEquivQ_appendedDot_eq :
    clOpEquivQ hP hwf ({i} + ν) (op (appendedDot Q Λ i ν)) =
      blackMatrixDotQ (Pin) (CL.CLScalars.t KL) i ν (clDownwardBlockQ_reflectedBlack P) :=
  clOpEquivQ_appendedDot hP hwf i ν

/-- **Brundan (1.9) for Webster's functors on `T^λ`-modules** (Webster, arXiv:1309.3796v3,
§4.6, Theorem 4.31, with the repaired Lemma 4.29 and Theorem 4.30): for `0 ≤ ⟨i, λ⟩`, with `λ`
the right weight of content `i + ν`, the rightward crossing `blackModuleSigma` (the same-colour
crossing acting as `-ψ`) together with the dotted units `η x^m Eᵢ` has an explicit inverse, for a
presentation `P` with negligible cover relations (`CoverRelsNegligible`) and well-founded
domains (`WFDom`). -/
def clBlackModuleSumInvFromQ (hsym : KLRSymm Q)
    (hn : 0 ≤ ip (RDc) i (downRightWeight (RDc) (coordinateRedWeights Λ C) ({i} + ν))) :
    SumInvFrom (blackModuleSigma Λ hsym i ν)
      (fun m => (blackAdjOfEq Q Λ i (rfl : ({i} : Multiset I) + ({i} + ν) = _)).unit ≫
        Functor.whiskerRight (powComp (indDotOfEq Q Λ i rfl) m) (blackEOfEq Q Λ i rfl))
      (ip (RDc) i (downRightWeight (RDc) (coordinateRedWeights Λ C) ({i} + ν))).toNat :=
  blackModuleSumInvFrom Λ hsym i ν fun M => by
    have hd' := blackMatrixDotQ_intertwines (Pin) (CL.CLScalars.t KL) i ({i} + ν)
      (clDownwardBlockQ_reflectedBlack P)
    have hdd := clOpEquivQ_appendedDot_eq hP hwf i ({i} + ν)
    exact sumInvFrom_transport (clOpEquivQ hP hwf ν) (clOpEquivQ hP hwf ({i} + ν))
      (clOpEquivQ hP hwf ({i} + ({i} + ν))) (clOpEquiv_appendBlackQ hP hwf i ν)
      (clOpEquiv_appendBlackQ hP hwf i ({i} + ν)) M
      (ModuleCat.of _ (ClMatViewQ hP hwf i ν M)) (toClMatViewQ hP hwf i ν M)
      (toClMatView_smulQ hP hwf i ν M) (op_appendedCross_commute Q Λ i ν)
      (blackMatrixCrossQ_commute (Pin) (CL.CLScalars.t KL) i ν (clDownwardBlockQ_reflectedBlack P))
      (clOpEquivQ_appendedCross hP hwf i ν)
      (intertwines_of_commute (op_appendedDot_commute Q Λ i ({i} + ν)))
      hd' hdd
      (blackMatrixSumInvFromQ (Pin) (CL.CLScalars.t KL) i ν (clDownwardBlockQ_reflectedBlack P)
        (ModuleCat.of _ (ClMatViewQ hP hwf i ν M)) hn)

end Categorification.Stendhal
