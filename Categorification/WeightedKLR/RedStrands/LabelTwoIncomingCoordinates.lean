/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoMiddleTerminalAugmentation

/-!
# Incoming coordinates in the label-two middle quotient

For Webster, arXiv:1309.3796v2, §8.2, calculate the two terminal
augmentation coordinates of the incoming exterior diagram and its final
black-crossing translate.
-/


noncomputable section
namespace Categorification.Stendhal.LabelTwo

open KLR KLRAlgebra Categorification.Webster.LabelTwo
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable (k : Type) [Field k]

local notation "ν" => (({()} : Multiset Unit) + {()})
local notation "q" => parameter k
local notation "g" => leftStandardUnit q weights loading loading_ordered
local notation "π" => tensorOfKLR q weights ν
local notation "E" => seqIdem q weights loading loading_ordered
local notation "J" => LinearEquiv.symm (terminalToTwoMiddle k)

private abbrev algToEnd :=
  (middlePolynomialEquiv k).symm.trans (middleEndomorphismEquiv k)

/-- The unit of the separated factor evaluates to the middle generator. -/
theorem middleToFixed_one_val : (middleToFixed k (1 : Middle k)).val = g := by
  change (algToEnd k (1 : Middle k)) g = g
  rw [map_one]
  rfl

private theorem algToEnd_y₂ : algToEnd k (y₂ : Middle k) = dotEnd k 1 := by
  have h : (middlePolynomialEquiv k).symm (y₂ : Middle k) = squareQuotientVariable k 1 :=
    (middlePolynomialEquiv k).symm_apply_eq.mpr (middlePolynomialEquiv_variable_one k).symm
  exact (congrArg (fun a : SquareQuotient k => middleEndomorphismEquiv k a) h).trans
    (middleDotQuotientAction_X k 1)

/-- The second dot evaluates to a dot on the right black strand. -/
theorem middleToFixed_y₂_val :
    (middleToFixed k (y₂ : Middle k)).val = rightMiddleDot k • g := by
  change (algToEnd k (y₂ : Middle k)) g = _
  rw [algToEnd_y₂]
  have hg : E • g = g := by
    have h := (middleToFixed k (1 : Middle k)).property
    change E • (middleToFixed k (1 : Middle k)).val = _ at h
    simpa only [middleToFixed_one_val] using h
  have he : π (e loading) = E := by
    apply congrArg (TensorProductAlgebra.mk q weights ν)
    apply Subtype.ext
    exact (StendhalAlgebraAllOrders.e_mul_redOrderedIdem loading).trans (ite_eq_left loading_ordered)
  have mul_proj (a b : KLRAlgebra k (stendhalQ q weights) (stendhalWeight 2 ν)) :
      π (a * b) = π a * π b := by simp only [tensorOfKLR, map_mul]
  have hc : E * rightMiddleDot k = rightMiddleDot k * E := by
    rw [← he]
    unfold rightMiddleDot
    rw [← mul_proj, ← mul_proj, e_mul_x]
  have hz (t : Seq (stendhalWeight 2 ν)) (ht : IsRedOrdered t)
      (a : TensorProductAlgebra k q weights ν) (hlt : StendhalLT loading t) :
      (seqIdem q weights t ht * a) • (rightMiddleDot k • g) = 0 := by
    rw [mul_smul, seqIdem_smul_leftStandard_eq_zero q weights loading_ordered ht hlt]
  change leftStandardLift (Q := q) (Λ := weights) loading loading_ordered (rightMiddleDot k • g) hz g = _
  apply leftStandardLift_unit (Q := q) (Λ := weights)
  rw [← mul_smul, hc, mul_smul, hg]

private theorem fixedAugmentation_middleToFixed (a : Middle k) :
    fixedAugmentation k (middleToFixed k a) = specialize a :=
  congrArg specialize ((middleToFixed k).symm_apply_apply a)

/-- The incoming pair of shuffle coordinates as an explicit diagram. -/
theorem incomingDiagram_val :
    (J (middleToFixed k (1 : Middle k), middleToFixed k (y₂ : Middle k))).val =
      π (ψw [1]) • g + π (ψw [2,1]) • (rightMiddleDot k • g) := by
  rw [terminalToTwoMiddle_symm_apply, middleToFixed_one_val, middleToFixed_y₂_val]

/-- The translated incoming pair as an explicit diagram. -/
theorem incomingDiagram_translate_val :
    (J (0, middleToFixed k (1 : Middle k))).val = π (ψw [2,1]) • g := by
  rw [terminalToTwoMiddle_symm_apply, middleToFixed_one_val]
  simp only [Submodule.coe_zero, smul_zero, zero_add]

/-- The two specialized coordinates of the incoming diagram. -/
theorem incomingDiagram_coordinates :
    terminalCutDotSumEquiv k (terminalQuotientMap k
      (J (middleToFixed k (1 : Middle k), middleToFixed k (y₂ : Middle k)))) = (1, -DualNumber.eps) := by
  rw [terminalCutDotSumEquiv_apply, fixedAugmentation_middleToFixed, fixedAugmentation_middleToFixed,
    map_one, specialize_y₂]

/-- The two specialized coordinates of the translated incoming diagram. -/
theorem incomingDiagram_translate_coordinates :
    terminalCutDotSumEquiv k (terminalQuotientMap k
      (J (0, middleToFixed k (1 : Middle k)))) = (0, 1) := by
  rw [terminalCutDotSumEquiv_apply, map_zero, fixedAugmentation_middleToFixed, map_one]

end Categorification.Stendhal.LabelTwo
