/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoIncomingLiftTensor
import Categorification.WeightedKLR.RedStrands.LabelTwoIncomingLiftReturn

/-!
# A nonzero incoming exterior tensor map

Return the incoming lift through the black-crossing translate. The returned
diagram is the first dot sum, which the balanced tensor readout detects.
-/

set_option backward.isDefEq.respectTransparency false

namespace Categorification.Stendhal.LabelTwo

open KLR KLRAlgebra
noncomputable section

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable (k : Type) [Field k]
local notation "ν" => (({()} : Multiset Unit) + {()})
local notation "μ" => stendhalWeight 2 ν
local notation "T" => TensorProductAlgebra k (parameter k) weights ν
local notation "S" => Standard k
local notation "B" => StandardDotSumQuotient k
local notation "U" => LinearMap.range (diagramPlus k)
local notation "q" => Submodule.mkQ (LinearMap.range (diagramPlus k))
local notation "E" => seqIdem (parameter k) weights loading loading_ordered

private def rightCut : Seq μ := labelTwoExteriorRightLoading

private theorem right_ordered : IsRedOrdered rightCut := by
  unfold IsRedOrdered
  decide +kernel

private abbrev incomingDivided :
    Submodule T (leftStandard («ν» := ν) (parameter k) weights rightCut right_ordered) :=
  labelTwoRightExteriorDividedStandard (parameter k)

local notation "g" => leftStandardUnit (parameter k) weights loading loading_ordered
local notation "A₀" => rightCut
private def middleCut : Seq μ := labelTwoMiddleLoading
local notation "B₀" => middleCut
local notation "H" => KLRAlgebra k (stendhalQ (parameter k) weights) μ
local notation "π" => tensorOfKLR (parameter k) weights ν
local notation "pA" => ((x ⟨2, by decide⟩ : H) * ψ 2 * e A₀)
local notation "w" => (ψ 1 * ψ 2 : H)
local notation "vWord" => (ψ 2 * (ψ 1 * e B₀) : H)
local notation "x₃" => (x ⟨3, by decide⟩ : H)
local notation "uWord" => (pA * (ψ 1 * e B₀))
private theorem rawMiddleOrdered : IsRedOrdered B₀ := by
  unfold middleCut IsRedOrdered
  decide +kernel


private def projectedIncomingGenerator : incomingDivided k :=
  (labelTwoRightExteriorProjection (parameter k)).rangeRestrict
    (leftStandardUnit («ν» := ν) (parameter k) weights rightCut right_ordered)

private theorem projectedIncomingGenerator_val :
    (projectedIncomingGenerator k).val =
      π pA • leftStandardUnit («ν» := ν) (parameter k) weights rightCut right_ordered :=
  labelTwoRightExteriorProjection_generator (parameter k)

open Categorification.Webster.LabelTwo

private def liftedIncomingVector : S :=
  ((terminalToTwoMiddle k).symm
    (middleToFixed k (1 : Middle k), middleToFixed k (y₂ : Middle k))).val

private theorem liftedIncomingVector_quotient :
    q (liftedIncomingVector k) = normalizedIncoming k (projectedIncomingGenerator k) := by
  let F := labelTwoExteriorToMiddle (parameter k)
  let C := exteriorMiddleQuotientEquiv k
  have h := congrArg (fun v => C (F v)) (projectedIncomingGenerator_val k)
  exact (h.trans (exteriorMiddleQuotientEquiv_projected_generator k)).symm

/-- The incoming lift is a vector of the actual preimage submodule. -/
def liftedIncoming : incomingLiftSubmodule k :=
  ⟨liftedIncomingVector k, ⟨projectedIncomingGenerator k, (liftedIncomingVector_quotient k).symm⟩⟩

private theorem middle_generator_fixed : E • g = g := by
  have h := (middleToFixed k (1 : Middle k)).property
  change E • (middleToFixed k (1 : Middle k)).val = _ at h
  simpa only [middleToFixed_one_val] using h

private theorem projected_middle_idem_fixes :
    π (e B₀ : H) • g = g := by
  have hB : B₀ = loading := exterior_middle_loading_alignment
  have he : π (e B₀ : H) = E := by
    change stendhalTensorProjection (Q := parameter k) weights ν (e B₀) = E
    rw [hB, stendhalTensorProjection_e weights ν loading loading_ordered]
  exact (congrArg (fun a : T => a • g) he).trans (middle_generator_fixed k)

private theorem projected_mul (a b : H) : π (a * b) = π a * π b := by
  simp only [tensorOfKLR, map_mul]

private theorem projected_add (a b : H) : π (a + b) = π a + π b := by
  simp only [tensorOfKLR, map_add]


private theorem liftedIncomingVector_eq_word : liftedIncomingVector k = π uWord • g := by
  have hu : uWord = (ψ 1 * e B₀) + ψ 2 * (ψ 1 * (x₃ * e B₀)) :=
    labelTwo_otherExterior_generator_expansion (stendhalQ (parameter k) weights)
  change ((terminalToTwoMiddle k).symm
    (middleToFixed k (1 : Middle k), middleToFixed k (y₂ : Middle k))).val = _
  rw [incomingDiagram_val, hu]
  simp only [tensorOfKLR, ψw_cons, ψw_nil, mul_one, map_add, map_mul, add_smul, mul_smul,
    rightMiddleDot, projected_middle_idem_fixes]

private theorem transport_loading_generator_equation
    {s t : Seq μ} (hs : IsRedOrdered s) (ht : IsRedOrdered t) (hst : s = t)
    (a b : T)
    (h : a • leftStandardUnit («ν» := ν) (parameter k) weights s hs =
      b • leftStandardUnit («ν» := ν) (parameter k) weights s hs) :
    a • leftStandardUnit («ν» := ν) (parameter k) weights t ht =
      b • leftStandardUnit («ν» := ν) (parameter k) weights t ht := by
  subst t
  exact h

private abbrev sumWord : H := x ⟨1, by decide⟩ + x ⟨3, by decide⟩
private abbrev braidWord : H := ψ 1 * ψ 2 * ψ 1

private theorem incoming_return_word : w * uWord = braidWord k * e B₀ := by
  have ht : (ψ 2 : H) * uWord = (ψ 2 : H) * (ψ 1 * e B₀) :=
    labelTwo_otherExterior_generator_translate (stendhalQ (parameter k) weights)
  rw [mul_assoc (ψ 1), ht]
  simp only [braidWord, mul_assoc]

private theorem normalized_middleBraid :
    π (braidWord k) • g = π (sumWord k) • g :=
  transport_loading_generator_equation k rawMiddleOrdered loading_ordered
    exterior_middle_loading_alignment (π (braidWord k)) (π (sumWord k))
    (labelTwo_otherExterior_middleBraid (parameter k))

private theorem diagramPlus_eval :
    π (sumWord k) • g = diagramPlus k g := by
  change π (sumWord k) • g = dotEnd k 0 g + dotEnd k 1 g
  rw [dotEnd_zero_gen, dotEnd_one_gen]
  exact (congrArg (· • g) (projected_add k _ _)).trans (add_smul _ _ _)

private theorem liftedIncoming_return :
    π w • (liftedIncoming k).val = diagramPlus k g := by
  change π w • liftedIncomingVector k = diagramPlus k g
  rw [liftedIncomingVector_eq_word, ← mul_smul, ← projected_mul, incoming_return_word,
    projected_mul, mul_smul, projected_middle_idem_fixes]
  exact (normalized_middleBraid k).trans (diagramPlus_eval k)


private def projectedIncomingTranslate : incomingDivided k :=
  π (ψ 2 : H) • projectedIncomingGenerator k

private theorem projectedIncomingTranslate_val :
    (projectedIncomingTranslate k).val =
      π (ψ 2 : H) • (π pA • leftStandardUnit («ν» := ν) (parameter k) weights rightCut right_ordered) :=
  congrArg (π (ψ 2 : H) • ·) (projectedIncomingGenerator_val k)

private theorem incomingTranslate_normalized :
    normalizedIncoming k (projectedIncomingTranslate k) = π (ψ 2 * ψ 1 : H) • q g := by
  let F := labelTwoExteriorToMiddle (parameter k)
  let C := exteriorMiddleQuotientEquiv k
  have h := congrArg (fun v => C (F v)) (projectedIncomingTranslate_val k)
  have hd := h.trans (exteriorMiddleQuotientEquiv_projected_translate k)
  change normalizedIncoming k (projectedIncomingTranslate k) =
    q ((terminalToTwoMiddle k).symm (0, middleToFixed k (1 : Middle k))).val at hd
  rw [incomingDiagram_translate_val, (q).map_smul] at hd
  simpa only [ψw_cons, ψw_nil, mul_one, tensorOfKLR] using hd


open MulOpposite Categorification
local notation "N" => IncomingLiftCoefficient k
local notation "J" => incomingLiftSubmodule k
local notation "reflection" => (tensorReflect : T →ₐ[k] Tᵐᵒᵖ)

private theorem reflection_incoming_word :
    (reflection (π (ψ 2 * ψ 1 : H))).unop = π w := by
  have h := congrArg unop
    (tensorReflect_projection (Q := parameter k) (Λ := weights) («ν» := ν) (ψ 2 * ψ 1 : H))
  change (reflection (π (ψ 2 * ψ 1 : H))).unop = π (hflip (ψ 2 * ψ 1 : H)) at h
  rwa [hflip_mul, hflip_ψ, hflip_ψ] at h

/-- The actual lift tensored with the incoming translate has nonzero
left-dot coefficient in the middle quotient tensor. -/
theorem incomingLiftTensorReadout_incoming_translate :
    incomingLiftTensorReadout k (BalancedTensor.tmul (show N from liftedIncoming k)
      (normalizedIncoming k (projectedIncomingTranslate k))) = 1 := by
  let m : N := liftedIncoming k
  let a : T := π (ψ 2 * ψ 1 : H)
  let b : B := q g
  let F := incomingLiftTensorReadout k
  have h : (op a • m : N) = (show N from incomingLiftDotSumGenerator k) := by
    have hr : (reflection a).unop = π w := reflection_incoming_word k
    exact (incomingLiftCoefficient_op_smul k a m).trans
      ((congrArg (fun c : T => c • (show incomingLiftSubmodule k from m)) hr).trans
        (Subtype.ext (liftedIncoming_return k)))
  calc
    _ = F (BalancedTensor.tmul m (a • b)) :=
      congrArg (fun v : B => F (BalancedTensor.tmul m v)) (incomingTranslate_normalized k)
    _ = F (BalancedTensor.tmul (op a • m) b) :=
      congrArg F (BalancedTensor.op_smul_tmul (k := k) («B» := k) m a b).symm
    _ = 1 := (congrArg (fun z : N => F (BalancedTensor.tmul z b)) h).trans
      (incomingLiftTensorReadout_dotSum_generator k)

/-- The incoming exterior map remains nonzero after tensoring with the
reflected preimage of its image. -/
theorem incomingLiftTensorMap_nonzero :
    BalancedTensor.mapRight (k := k) («B» := k) (M := N) (normalizedIncoming k) ≠ 0 := by
  intro h
  let z : BalancedTensor k k T N (incomingDivided k) :=
    BalancedTensor.tmul (show N from liftedIncoming k) (projectedIncomingTranslate k)
  have hz := DFunLike.congr_fun h z
  change BalancedTensor.tmul (show N from liftedIncoming k)
    (normalizedIncoming k (projectedIncomingTranslate k)) = 0 at hz
  have hc := incomingLiftTensorReadout_incoming_translate k
  rw [hz, map_zero] at hc
  exact zero_ne_one hc

end
end Categorification.Stendhal.LabelTwo
