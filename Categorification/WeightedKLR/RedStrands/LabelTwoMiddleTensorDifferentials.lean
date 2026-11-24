/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoMiddleOrdinaryTensor

/-!
# Tensor differentials at the label-two middle cut

The ordinary balanced tensor with the actual reflected dot-sum
coefficient turns the middle sum differential into zero and the
difference into multiplication by twice the dual-number variable.
-/

noncomputable section

namespace Categorification.Stendhal.LabelTwo

open KLR KLRAlgebra MulOpposite Categorification.Webster.LabelTwo
open scoped DualNumber

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable (k : Type) [Field k]
local notation "blackWeight" => (({()} : Multiset Unit) + {()})
local notation "Ambient" => TensorProductAlgebra k (parameter k) weights blackWeight
local notation "S" => Standard k
local notation "E" => seqIdem (parameter k) weights loading loading_ordered
local notation "g" => leftStandardUnit (parameter k) weights loading loading_ordered
local notation "N" => MiddleTensorCoefficient k
local notation "Tens" => BalancedTensor k k Ambient N S
local notation "W" => fixSub k S E
local notation "Qmod" => StandardDotSumQuotient k
local notation "Fixed" => fixSub k Qmod E
local notation "LeftDot" => leftMiddleDot k
local notation "RightDot" => rightMiddleDot k

private def fixedGeneratorTensor (z : Fixed) : Tens :=
  BalancedTensor.tmul (show N from z.val) g

private def fixedEval :
    Tens ≃ₗ[k] fixSub k N (op E) :=
  leftStandardTensorEquivFixed (parameter k) weights loading loading_ordered N
    (coefficient_kills_higher k)

private theorem fixedGeneratorTensor_eq (z : Fixed) :
    (fixedEval k) (fixedGeneratorTensor k z) = (middleFixedReflectionEquiv k).symm z := by
  apply Subtype.ext
  calc
    _ = op E • (show N from z.val) :=
      leftStandardTensorEquivFixed_tmul_generator (parameter k) weights loading loading_ordered N
        (coefficient_kills_higher k) z.val
    _ = _ := ((middleFixedReflectionEquiv k).symm z).property

private theorem middleStandardTensorEquiv_fixed (z : Fixed) :
    middleStandardTensorEquiv k (fixedGeneratorTensor k z) = middleCutDotSumEquiv k z := by
  change middleCutDotSumEquiv k ((middleFixedReflectionEquiv k) ((fixedEval k) _)) = _
  exact congrArg (middleCutDotSumEquiv k) <|
    (congrArg (middleFixedReflectionEquiv k) (fixedGeneratorTensor_eq k z)).trans
      ((middleFixedReflectionEquiv k).apply_symm_apply z)

private theorem fixedGeneratorTensor_surjective : Function.Surjective (fixedGeneratorTensor k) := by
  intro t
  refine ⟨middleFixedReflectionEquiv k (fixedEval k t), (fixedEval k).injective ?_⟩
  rw [fixedGeneratorTensor_eq, LinearEquiv.symm_apply_apply]

private abbrev reflected := tensorReflect (Q := parameter k) (Λ := weights) (ν := blackWeight)

private theorem reflectedDot (j : Fin (Multiset.card (stendhalWeight 2 blackWeight))) :
    reflected k (tensorOfKLR (parameter k) weights blackWeight (KLRAlgebra.x j)) =
      op (tensorOfKLR (parameter k) weights blackWeight (KLRAlgebra.x j)) := by
  let q := stendhalTensorProjection (Q := parameter k) weights blackWeight
  let d : KLRAlgebra k (stendhalQ (parameter k) weights) (stendhalWeight 2 blackWeight) :=
    KLRAlgebra.x j
  change tensorReflect (q d) = op (q d)
  exact (tensorReflect_projection d).trans (congrArg (fun b => op (q b)) (hflip_x j))

private theorem reflectedLeftDot : reflected k LeftDot = op LeftDot :=
  reflectedDot k ⟨1, by decide⟩

private theorem reflectedRightDot : reflected k RightDot = op RightDot :=
  reflectedDot k ⟨3, by decide⟩

private theorem generatorPlus : diagramPlus k g = (LeftDot + RightDot) • (g : S) := by
  change dotEnd k 0 g + dotEnd k 1 g = _
  rw [add_smul, dotEnd_zero_gen, dotEnd_one_gen]

private theorem generatorMinus : diagramMinus k g = (LeftDot - RightDot) • (g : S) := by
  change dotEnd k 0 g - dotEnd k 1 g = _
  rw [sub_smul, dotEnd_zero_gen, dotEnd_one_gen]

private theorem tensorMap_on_fixed (f : Module.End Ambient S) (a : Ambient)
    (hf : f g = a • g) (hr : reflected k a = op a)
    (z v : W) (hz : v.val = a • z.val) :
    BalancedTensor.mapRight f (fixedGeneratorTensor k (fixedQuotientMap k z)) =
      fixedGeneratorTensor k (fixedQuotientMap k v) := by
  let q : S →ₗ[Ambient] Qmod := (LinearMap.range (diagramPlus k)).mkQ
  let m : N := q z.val
  have hq : ((reflected k a).unop • q z.val : Qmod) = q v.val :=
    (congrArg (fun b : Ambientᵐᵒᵖ => (b.unop • q z.val : Qmod)) hr).trans
      ((q.map_smul a z.val).symm.trans (congrArg q hz.symm))
  have hm : (op a • m : N) = (show N from q v.val) :=
    (middleTensorCoefficient_op_smul k a m).trans hq
  change BalancedTensor.mapRight f (BalancedTensor.tmul m g) =
    (BalancedTensor.tmul (show N from q v.val) g : Tens)
  calc
    _ = BalancedTensor.tmul m (f g) := BalancedTensor.mapRight_tmul f m g
    _ = BalancedTensor.tmul m (a • g) := congrArg (BalancedTensor.tmul m) hf
    _ = BalancedTensor.tmul (op a • m) g := (BalancedTensor.op_smul_tmul m a g).symm
    _ = _ := congrArg (fun m' : N => (BalancedTensor.tmul m' g : Tens)) hm

private abbrev tensorGenerator (b : Middle k) : Tens :=
  fixedGeneratorTensor k (fixedQuotientMap k (middleToFixed k b))

private theorem tensorGenerator_surjective : Function.Surjective (tensorGenerator k) :=
  (fixedGeneratorTensor_surjective k).comp <|
    (fixedQuotientMap_surj k).comp (middleToFixed k).surjective

private theorem middleStandardTensorEquiv_plus_generator (b : Middle k) :
    middleStandardTensorEquiv k (BalancedTensor.mapRight (diagramPlus k) (tensorGenerator k b)) = 0 := by
  have hv (w : W) : (fixedPlus k w).val = (LeftDot + RightDot) • w.val := by
    change dotEnd k 0 w.val + dotEnd k 1 w.val = _
    rw [add_smul, leftMiddleDot_smul_middle_fixed, rightMiddleDot_smul_middle_fixed]
  have hr : reflected k (LeftDot + RightDot) = op (LeftDot + RightDot) := by
    rw [map_add, reflectedLeftDot, reflectedRightDot, op_add]
  let z := middleToFixed k b
  have ht := tensorMap_on_fixed k (diagramPlus k) _ (generatorPlus k) hr z (fixedPlus k z) (hv z)
  calc
    _ = middleStandardTensorEquiv k (fixedGeneratorTensor k (fixedQuotientMap k (fixedPlus k z))) :=
      congrArg (middleStandardTensorEquiv k) ht
    _ = middleCutDotSumEquiv k (fixedQuotientMap k (fixedPlus k z)) :=
      middleStandardTensorEquiv_fixed k _
    _ = middleCutDotSumEquiv k (fixedQuotientMap k (middleToFixed k (plus b))) :=
      congrArg (fun w => middleCutDotSumEquiv k (fixedQuotientMap k w)) (fixedPlus_transport k b)
    _ = specialize (plus b) := middleCutDotSumEquiv_specialize k _
    _ = 0 := by
      change specialize ((y₁ + y₂) * b) = 0
      simp

/-- The first periodic diagram differential vanishes after ordinary tensor
with the reflected dot-sum quotient. -/
theorem middleStandardTensorEquiv_plus (t : Tens) :
    middleStandardTensorEquiv k (BalancedTensor.mapRight (diagramPlus k) t) = 0 := by
  obtain ⟨b, rfl⟩ := tensorGenerator_surjective k t
  exact middleStandardTensorEquiv_plus_generator k b

private theorem middleStandardTensorEquiv_minus_generator (b : Middle k) :
    middleStandardTensorEquiv k (BalancedTensor.mapRight (diagramMinus k) (tensorGenerator k b)) =
      (ε + ε) * middleStandardTensorEquiv k (tensorGenerator k b) := by
  have hv (w : W) : (fixedMinus k w).val = (LeftDot - RightDot) • w.val := by
    change dotEnd k 0 w.val - dotEnd k 1 w.val = _
    rw [sub_smul, leftMiddleDot_smul_middle_fixed, rightMiddleDot_smul_middle_fixed]
  have hr : reflected k (LeftDot - RightDot) = op (LeftDot - RightDot) := by
    rw [map_sub, reflectedLeftDot, reflectedRightDot, op_sub]
  let z := middleToFixed k b
  have ht := tensorMap_on_fixed k (diagramMinus k) _ (generatorMinus k) hr z (fixedMinus k z) (hv z)
  calc
    _ = middleStandardTensorEquiv k (fixedGeneratorTensor k (fixedQuotientMap k (fixedMinus k z))) :=
      congrArg (middleStandardTensorEquiv k) ht
    _ = middleCutDotSumEquiv k (fixedQuotientMap k (fixedMinus k z)) :=
      middleStandardTensorEquiv_fixed k _
    _ = middleCutDotSumEquiv k (fixedQuotientMap k (middleToFixed k (minus b))) :=
      congrArg (fun w => middleCutDotSumEquiv k (fixedQuotientMap k w)) (fixedMinus_transport k b)
    _ = specialize (minus b) := middleCutDotSumEquiv_specialize k _
    _ = (ε + ε) * specialize b := by
      change specialize ((y₁ - y₂) * b) = (ε + ε) * specialize b
      simp [sub_eq_add_neg]
    _ = (ε + ε) * middleCutDotSumEquiv k (fixedQuotientMap k z) :=
      congrArg ((ε + ε) * ·) (middleCutDotSumEquiv_specialize k b).symm
    _ = _ := congrArg ((ε + ε) * ·) (middleStandardTensorEquiv_fixed k _).symm

/-- The second periodic diagram differential becomes multiplication by twice
the dual-number variable after ordinary tensor with the reflected quotient. -/
theorem middleStandardTensorEquiv_minus (t : Tens) :
    middleStandardTensorEquiv k (BalancedTensor.mapRight (diagramMinus k) t) =
      (ε + ε) * middleStandardTensorEquiv k t := by
  obtain ⟨b, rfl⟩ := tensorGenerator_surjective k t
  exact middleStandardTensorEquiv_minus_generator k b

end Categorification.Stendhal.LabelTwo
