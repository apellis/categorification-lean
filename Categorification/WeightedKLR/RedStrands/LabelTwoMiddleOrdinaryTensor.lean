/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LeftStandardTensorFixed
import Categorification.WeightedKLR.RedStrands.LabelTwoMiddleSupport

/-!
# The ordinary tensor at Webster's label-two middle cut

The reflected diagrammatic dot-sum coefficient has ordinary tensor with
the middle standard equal to its middle-idempotent subspace, whose
coordinates are the separated dual-number specialization of §8.2.
-/

noncomputable section
namespace Categorification.Stendhal.LabelTwo
open KLR KLRAlgebra MulOpposite Categorification.Webster.LabelTwo

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable (k : Type) [Field k]
local notation "blackWeight" => (({()} : Multiset Unit) + {()})
local notation "Ambient" => TensorProductAlgebra k (parameter k) weights blackWeight
local notation "S" => Standard k
local notation "E" => seqIdem (parameter k) weights loading loading_ordered
local notation "Qmod" => StandardDotSumQuotient k

/-- The right dot-sum coefficient with its ground field action. -/
def MiddleTensorCoefficient : Type := StandardDotSumQuotient k

local notation "N" => MiddleTensorCoefficient k

instance : AddCommGroup N := inferInstanceAs (AddCommGroup Qmod)
instance : Module k N := inferInstanceAs (Module k Qmod)
instance : Module Ambientᵐᵒᵖ N := inferInstanceAs (Module Ambientᵐᵒᵖ (rightMiddleDotSumQuotient k))

private abbrev reflect :=
  tensorReflect (Q := parameter k) (Λ := weights) (ν := blackWeight)

/-- The reflected right action is horizontal reflection followed by the left action. -/
theorem middleTensorCoefficient_op_smul (a : Ambient) (z : N) :
    (op a • z : N) = ((reflect k a).unop • (show Qmod from z) : Qmod) := rfl

/-- A scalar regarded as a right diagram acts by the ground-field scalar. -/
theorem middleTensorCoefficient_algebraMap_smul (c : k) (z : N) :
    (op (algebraMap k Ambient c) • z : N) = c • z := by
  rw [middleTensorCoefficient_op_smul, AlgHom.commutes]
  exact algebraMap_smul Ambient c (show Qmod from z)

instance : IsScalarTower k Ambientᵐᵒᵖ N where
  smul_assoc c a z := by
    obtain ⟨b, rfl⟩ := op_surjective a
    change (op (c • b) • z : N) = c • (op b • z)
    rw [middleTensorCoefficient_op_smul, middleTensorCoefficient_op_smul]
    change (reflect k (c • b)).unop • (show Qmod from z) =
      c • ((reflect k b).unop • (show Qmod from z))
    rw [map_smul, unop_smul, smul_assoc]

instance : SMulCommClass k Ambientᵐᵒᵖ N where
  smul_comm c a z := by
    obtain ⟨b, rfl⟩ := op_surjective a
    rw [middleTensorCoefficient_op_smul, middleTensorCoefficient_op_smul]
    exact smul_comm c (reflect k b).unop (show Qmod from z)

/-- The reflected coefficient is killed by all loading idempotents strictly above the middle cut. -/
theorem coefficient_kills_higher (s : Seq (stendhalWeight 2 blackWeight))
    (hs : IsRedOrdered s) (hlt : StendhalLT loading s) (z : N) :
    op (seqIdem (parameter k) weights s hs) • z = 0 :=
  rightMiddleDotSumQuotient_kills_higher k s hs hlt
    (show rightMiddleDotSumQuotient k from z)

private theorem coefficient_middle_idem (z : N) :
    (op E • z : N) = (E • (show Qmod from z) : Qmod) := by
  rw [middleTensorCoefficient_op_smul, unop_tensorReflect_e]

/-- Reflection identifies the fixed subspaces at the same loading. -/
def middleFixedReflectionEquiv :
    fixSub k N (op E) ≃ₗ[k] fixSub k Qmod E where
  toFun z := ⟨z.val, (coefficient_middle_idem k z.val).symm.trans z.property⟩
  invFun z := ⟨z.val, (coefficient_middle_idem k z.val).trans z.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The ordinary tensor of the reflected dot-sum coefficient with the actual
middle standard is the dual-number vector space of the separated factor. -/
def middleStandardTensorEquiv :
    BalancedTensor k k Ambient N S ≃ₗ[k] DualNumber k :=
  (leftStandardTensorEquivFixed (parameter k) weights loading loading_ordered N
    (coefficient_kills_higher k)).trans
      ((middleFixedReflectionEquiv k).trans (middleCutDotSumEquiv k))

end Categorification.Stendhal.LabelTwo
