/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoIncomingLiftCut
import Categorification.WeightedKLR.RedStrands.LeftStandardTensorFixed
import Categorification.WeightedKLR.RedStrands.BoundaryHomReflection

/-!
# The balanced tensor readout on the label-two incoming preimage

The left-dot coefficient descends to the tensor of the reflected incoming
preimage with the actual middle dot-sum quotient.
-/

namespace Categorification.Stendhal.LabelTwo

open KLR KLRAlgebra
noncomputable section

section QuotientTensor

variable {𝕜 R M X : Type*} [CommRing 𝕜] [Ring R] [Algebra 𝕜 R]
  [AddCommGroup M] [Module 𝕜 M]
  [AddCommGroup X] [Module 𝕜 X] [Module R X] [IsScalarTower 𝕜 R X]

private def descendRightQuotient (W : Submodule R X) (f : X →ₗ[𝕜] M →ₗ[𝕜] 𝕜)
    (hf : W.restrictScalars 𝕜 ≤ LinearMap.ker f) : M →ₗ[𝕜] (X ⧸ W) →ₗ[𝕜] 𝕜 :=
  (((W.restrictScalars 𝕜).liftQ f hf).comp
    (Submodule.Quotient.restrictScalarsEquiv 𝕜 W).symm.toLinearMap).flip

private theorem descendRightQuotient_mk (W : Submodule R X) (f : X →ₗ[𝕜] M →ₗ[𝕜] 𝕜)
    (hf : W.restrictScalars 𝕜 ≤ LinearMap.ker f) (m : M) (x : X) :
    descendRightQuotient W f hf m (W.mkQ x) = f x m := rfl

variable [Module Rᵐᵒᵖ M] [SMulCommClass 𝕜 Rᵐᵒᵖ M]

private def descendBalancedRightQuotient (W : Submodule R X) (f : X →ₗ[𝕜] M →ₗ[𝕜] 𝕜)
    (hf : W.restrictScalars 𝕜 ≤ LinearMap.ker f)
    (hb : ∀ (m : M) (a : R) (x : X), f x (MulOpposite.op a • m) = f (a • x) m) :
    BalancedTensor 𝕜 𝕜 R M (X ⧸ W) →ₗ[𝕜] 𝕜 :=
  BalancedTensor.lift (descendRightQuotient W f hf) (fun m a b => by
    obtain ⟨x,rfl⟩ := W.mkQ_surjective b
    rw [← W.mkQ.map_smul, descendRightQuotient_mk, descendRightQuotient_mk]
    exact hb m a x)

private theorem descendBalancedRightQuotient_tmul (W : Submodule R X)
    (f : X →ₗ[𝕜] M →ₗ[𝕜] 𝕜) (hf : W.restrictScalars 𝕜 ≤ LinearMap.ker f)
    (hb : ∀ (m : M) (a : R) (x : X), f x (MulOpposite.op a • m) = f (a • x) m)
    (m : M) (x : X) :
    descendBalancedRightQuotient W f hf hb (BalancedTensor.tmul m (W.mkQ x)) = f x m :=
  (BalancedTensor.lift_tmul (descendRightQuotient W f hf) _ m (W.mkQ x)).trans
    (descendRightQuotient_mk W f hf m x)

end QuotientTensor

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

local notation "g" => leftStandardUnit (parameter k) weights loading loading_ordered
local notation "fElt" => leftMiddleDot k + rightMiddleDot k

open MulOpposite Categorification

local notation "J" => incomingLiftSubmodule k

private abbrev reflection : T →ₐ[k] Tᵐᵒᵖ := tensorReflect

private def reflectedAction : Tᵐᵒᵖ →+* T :=
  (RingEquiv.opOp T).symm.toRingHom.comp (reflection k).toRingHom.op

/-- The incoming preimage viewed as a right module by horizontal reflection. -/
def IncomingLiftCoefficient : Type := J

local notation "N" => IncomingLiftCoefficient k

instance : AddCommGroup N := inferInstanceAs (AddCommGroup J)
instance : Module k N := inferInstanceAs (Module k J)
instance : Module Tᵐᵒᵖ N := Module.compHom J (reflectedAction k)

/-- The right action on the incoming preimage is the reflected left action. -/
theorem incomingLiftCoefficient_op_smul (a : T) (z : N) :
    (op a • z : N) = ((reflection k a).unop • (show J from z) : J) := rfl

instance : IsScalarTower k Tᵐᵒᵖ N where
  smul_assoc c a z := by
    obtain ⟨b, rfl⟩ := op_surjective a
    change (op (c • b) • z : N) = c • (op b • z)
    rw [incomingLiftCoefficient_op_smul, incomingLiftCoefficient_op_smul]
    change (reflection k (c • b)).unop • (show J from z) =
      c • ((reflection k b).unop • (show J from z))
    rw [map_smul, unop_smul, smul_assoc]

instance : SMulCommClass k Tᵐᵒᵖ N where
  smul_comm c a z := by
    obtain ⟨b, rfl⟩ := op_surjective a
    rw [incomingLiftCoefficient_op_smul, incomingLiftCoefficient_op_smul]
    exact smul_comm c (reflection k b).unop (show J from z)

private theorem coefficient_kills_higher (s : Seq μ) (hs : IsRedOrdered s)
    (hlt : StendhalLT loading s) (z : N) : op (seqIdem (parameter k) weights s hs) • z = 0 := by
  rw [incomingLiftCoefficient_op_smul, unop_tensorReflect_e]
  apply Subtype.ext
  exact seqIdem_smul_leftStandard_eq_zero (parameter k) weights loading_ordered hs hlt
    (show J from z).val

local notation "𝓦" => fixSub k N (op E)
local notation "BT" => BalancedTensor k k T N S

private def tensorFixed : BT ≃ₗ[k] 𝓦 :=
  leftStandardTensorEquivFixed (parameter k) weights loading loading_ordered N
    (coefficient_kills_higher k)

private def liftTensorPreReadout : BT →ₗ[k] k :=
  ((middleY₁Readout k).comp (((J).subtype).restrictScalars k)).comp
    ((𝓦).subtype.comp (tensorFixed k).toLinearMap)

private theorem liftTensorPreReadout_generator (z : N) :
    liftTensorPreReadout k (BalancedTensor.tmul z g) =
      middleY₁Readout k (show J from z).val := by
  have h := leftStandardTensorEquivFixed_tmul_generator (parameter k) weights loading loading_ordered N
    (coefficient_kills_higher k) z
  have h0 : (tensorFixed k (BalancedTensor.tmul z g)).val = op E • z := h
  rw [incomingLiftCoefficient_op_smul, unop_tensorReflect_e] at h0
  exact (congrArg (fun x : J => middleY₁Readout k x.val) h0).trans
    (middleY₁Readout_project_eq k (show J from z).val)

private theorem dotSum_reflection_fixed : (reflection k fElt).unop = fElt := by
  let π := stendhalTensorProjection (Q := parameter k) weights ν
  let H := KLRAlgebra k (stendhalQ (parameter k) weights) μ
  let z : H := x ⟨1, by decide⟩ + x ⟨3, by decide⟩
  have h : π z = fElt := π.map_add _ _
  have h' := congrArg unop
    (tensorReflect_projection (Q := parameter k) (Λ := weights) («ν» := ν) z)
  change (reflection k (π z)).unop = π (hflip z) at h'
  have hfix : hflip z = z := by
    unfold z
    rw [hflip_add, hflip_x, hflip_x]
  rw [hfix, h] at h'
  exact h'

private theorem liftTensorPreReadout_kills_plus (z : N) (s : S) :
    liftTensorPreReadout k (BalancedTensor.tmul z (diagramPlus k s)) = 0 := by
  obtain ⟨a,rfl⟩ := leftStandard_exists_smul_unit
    (Q := parameter k) (Λ := weights) loading loading_ordered s
  have hg : diagramPlus k g = fElt • g := by
    change dotEnd k 0 g + dotEnd k 1 g = fElt • g
    rw [dotEnd_zero_gen, dotEnd_one_gen, add_smul]
  rw [map_smul, ← BalancedTensor.op_smul_tmul, hg, ← BalancedTensor.op_smul_tmul,
    liftTensorPreReadout_generator]
  change middleY₁Readout k ((show J from op fElt • (op a • z)).val) = 0
  have he := incomingLiftCoefficient_op_smul k fElt (op a • z)
  rw [dotSum_reflection_fixed k] at he
  exact (congrArg (fun x : J => middleY₁Readout k x.val) he).trans
    (middleY₁Readout_middleDotElt_incomingLift_zero k (show J from op a • z))

private def liftTensorPreBil : S →ₗ[k] N →ₗ[k] k :=
  ((BalancedTensor.mkBil k k T N S).compr₂ (liftTensorPreReadout k)).flip

private theorem liftTensorPreBil_kills :
    (U).restrictScalars k ≤ LinearMap.ker (liftTensorPreBil k) := by
  rintro _ ⟨s,rfl⟩
  apply LinearMap.mem_ker.mpr
  ext m
  exact liftTensorPreReadout_kills_plus k m s

private theorem liftTensorPreBil_balanced (m : N) (a : T) (s : S) :
    liftTensorPreBil k s (op a • m) = liftTensorPreBil k (a • s) m :=
  congrArg (liftTensorPreReadout k) (BalancedTensor.op_smul_tmul m a s)

/-- The middle left-dot coefficient defines a balanced tensor readout
after imposing the dot-sum relation on the middle standard. -/
def incomingLiftTensorReadout : BalancedTensor k k T N B →ₗ[k] k :=
  descendBalancedRightQuotient U (liftTensorPreBil k) (liftTensorPreBil_kills k)
    (liftTensorPreBil_balanced k)

private theorem incomingLiftTensorReadout_mk (m : N) (s : S) :
    incomingLiftTensorReadout k (BalancedTensor.tmul m (q s)) =
      liftTensorPreReadout k (BalancedTensor.tmul m s) :=
  descendBalancedRightQuotient_tmul U _ _ _ m s

/-- The dot sum of the middle generator, viewed in the incoming preimage. -/
def incomingLiftDotSumGenerator : J :=
  ⟨diagramPlus k g, by
    change q (diagramPlus k g) ∈ LinearMap.range (normalizedIncoming k)
    have h : q (diagramPlus k g) = 0 :=
      (Submodule.Quotient.mk_eq_zero U).mpr ⟨g,rfl⟩
    rw [h]
    exact Submodule.zero_mem _⟩

/-- The tensor of the incoming lift's dot-sum generator and the middle
quotient generator is detected by the left-dot coefficient. -/
theorem incomingLiftTensorReadout_dotSum_generator :
    incomingLiftTensorReadout k (BalancedTensor.tmul (show N from incomingLiftDotSumGenerator k) (q g)) = 1 := by
  rw [incomingLiftTensorReadout_mk, liftTensorPreReadout_generator]
  exact middleY₁Readout_diagramPlus_generator k

end
end Categorification.Stendhal.LabelTwo
