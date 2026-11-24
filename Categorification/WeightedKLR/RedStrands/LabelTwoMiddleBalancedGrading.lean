/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoMiddleGradedAugmentation
import Categorification.WeightedKLR.RedStrands.LabelTwoMiddleFixedGrading
import Categorification.WeightedKLR.RedStrands.LabelTwoMiddleTensorDifferentials
import Categorification.WeightedKLR.RedStrands.BoundaryHomReflection

/-!
# The graded ordinary tensor at the label-two middle cut

Horizontal reflection preserves the grading of the dot-sum quotient.
Tensoring a fixed vector with the degree-zero generator gives the
graded ordinary tensor with the actual middle standard.
-/

noncomputable section

set_option maxHeartbeats 3200000
set_option maxRecDepth 2048

namespace Categorification.Stendhal.LabelTwo

open KLR Categorification.Graded Categorification.Webster.LabelTwo DirectSum MulOpposite
open scoped DualNumber

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable (k : Type) [Field k]

local notation "ν₂" => (({()} : Multiset Unit) + {()})
local notation "A₂" => TensorProductAlgebra k (parameter k) weights ν₂
local notation "S" => Standard k
local notation "g" => leftStandardUnit (parameter k) weights loading loading_ordered
local notation "E" => seqIdem (parameter k) weights loading loading_ordered
local notation "𝒜₂" => middleTensorGrade k (labelTwoGradingDatum k)
local notation "ℳ₂" => middleStandardGrade k (labelTwoGradingDatum k)
local notation "𝒬" => middleDotSumQuotientGrade k
local notation "Qmod" => StandardDotSumQuotient k
local notation "N" => MiddleTensorCoefficient k
local notation "T" => BalancedTensor k k A₂ N S

/-- The reflected right coefficient retains the grading of the diagram quotient. -/
def middleTensorCoefficientGrade : ℤ → Submodule k N := 𝒬

local notation "𝒩₂" => middleTensorCoefficientGrade k

private theorem labelTwo_degPsi_symm (a b : Unit ⊕ Fin 2) :
    (labelTwoGradingDatum k).degΨ a b = (labelTwoGradingDatum k).degΨ b a := by
  cases a <;> cases b <;> rfl

/-- Right action by a homogeneous diagram adds its degree on the reflected coefficient. -/
theorem middleTensorCoefficient_smul_mem_grade {i j : ℤ} {a : A₂} {z : N}
    (hz : z ∈ 𝒩₂ i) (ha : a ∈ 𝒜₂ j) : op a • z ∈ 𝒩₂ (i + j) := by
  have h : (tensorReflect (Q := parameter k) (Λ := weights) (ν := ν₂) a).unop ∈ 𝒜₂ j :=
    (tensorReflection (labelTwoGradingDatum k) (labelTwo_degPsi_symm k)).mem_grade' ha
  change (op a • z : N) ∈ 𝒬 (i + j)
  rw [middleTensorCoefficient_op_smul, add_comm i j]
  exact (middleDotSumQuotientGFin k).gradedSMul.smul_mem h (show (z : Qmod) ∈ 𝒬 i from hz)

/-- The usual total grading on the actual balanced tensor. -/
def middleOrdinaryTensorGrade : ℤ → Submodule k T := balancedGrading k A₂ 𝒩₂ ℳ₂

/-- The ordinary ambient balanced tensor has the direct sum decomposition of its total grading. -/
@[instance_reducible] def middleOrdinaryTensorDecomposition : Decomposition (middleOrdinaryTensorGrade k) := by
  letI : Decomposition 𝒩₂ := (middleDotSumQuotientGFin k).decomposition
  letI : Decomposition ℳ₂ := (middleStandardGFin k (labelTwoGradingDatum k)).decomposition
  letI : SetLike.GradedSMul 𝒜₂ ℳ₂ := (middleStandardGFin k (labelTwoGradingDatum k)).gradedSMul
  exact balancedDecomposition 𝒜₂ (fun {_ _ _ _} hz ha => middleTensorCoefficient_smul_mem_grade k hz ha)


local notation "W" => fixSub k Qmod E
/-- The grading on the fixed subspace of the actual middle dot-sum quotient. -/
def middleFixedQuotientGrade : ℤ → Submodule k W :=
  fun d => Submodule.comap (Submodule.subtype W) (𝒬 d)

local notation "𝒲" => middleFixedQuotientGrade k
local notation "𝒯" => middleOrdinaryTensorGrade k

local instance : Decomposition 𝒬 := (middleDotSumQuotientGFin k).decomposition

private theorem middleFixed_homogeneous :
    (W).IsHomogeneous 𝒬 := by
  let : SetLike.GradedSMul 𝒜₂ 𝒬 := (middleDotSumQuotientGFin k).gradedSMul
  intro d z hz
  change E • z = z at hz
  change E • (decompose 𝒬 z d : Qmod) = (decompose 𝒬 z d : Qmod)
  have he : E ∈ 𝒜₂ 0 := mk_e_mem_tensorProductGrade (labelTwoGradingDatum k) ν₂ loading loading_ordered
  exact (decompose_smul_of_mem_zero (𝒜 := 𝒜₂) 𝒬 he z d).symm.trans
    (congrArg (fun x : Qmod => (decompose 𝒬 x d : Qmod)) hz)

private def fixedMiddleToTensor : W ≃ₗ[k] T :=
  ((leftStandardTensorEquivFixed (parameter k) weights loading loading_ordered N
    (coefficient_kills_higher k)).trans (middleFixedReflectionEquiv k)).symm

private theorem fixedMiddleToTensor_apply (z : W) :
    fixedMiddleToTensor k z = BalancedTensor.tmul (show N from z.val) (show S from g) :=
  leftStandardTensorEquivFixed_symm_apply (parameter k) weights loading loading_ordered N
    (coefficient_kills_higher k) ((middleFixedReflectionEquiv k).symm z)

private theorem fixedMiddleToTensor_preserves : PreservesGrading 𝒲 𝒯
    (fixedMiddleToTensor k).toLinearMap := by
  intro d z hz
  change fixedMiddleToTensor k z ∈ 𝒯 d
  rw [fixedMiddleToTensor_apply k z]
  have h := tmul_mem_balancedGrading (B := k) (A := A₂) (ℳ := 𝒩₂) (𝒩 := ℳ₂)
    (show (show N from z.val) ∈ 𝒩₂ d from hz) (middleStandardGenerator_mem_grade k)
  rw [add_zero] at h
  exact h

/-- Recover the actual graded ordinary tensor by tensoring a fixed quotient vector with
the degree-zero generator of the middle standard. -/
def middleFixedToOrdinaryTensorGradedEquiv : 𝒲 ≃ᵍ[k] 𝒯 := by
  letI : Decomposition 𝒲 := submoduleDecomposition 𝒬 (middleFixed_homogeneous k)
  letI : Decomposition 𝒯 := middleOrdinaryTensorDecomposition k
  exact GradedEquiv.ofPreserves (fixedMiddleToTensor k) (fixedMiddleToTensor_preserves k)

/-- The actual middle standard quotient of its loading projective is homogeneous. -/
theorem middleStandardQuotient_mem_grade {d : ℤ} {x : lIdeal E}
    (hx : x.val ∈ 𝒜₂ d) : (Submodule.Quotient.mk x : S) ∈ ℳ₂ d := by
  let : SetLike.GradedSMul 𝒜₂ ℳ₂ := (middleStandardGFin k (labelTwoGradingDatum k)).gradedSMul
  rw [leftStandard_mk_eq_smul_unit loading loading_ordered x]
  have h := SetLike.GradedSMul.smul_mem (A := 𝒜₂) (B := ℳ₂) hx
    (middleStandardGenerator_mem_grade k)
  change _ ∈ ℳ₂ (d + 0) at h
  simpa only [add_zero] using h

/-- Scalar and epsilon coordinates of the actual ambient tensor have degrees
zero and two respectively. -/
theorem middleStandardTensorEquiv_mem_grade_iff (t : T) (d : ℤ) :
    t ∈ 𝒯 d ↔ (d ≠ 0 → (middleStandardTensorEquiv k t).fst = 0) ∧
      (d ≠ 2 → (middleStandardTensorEquiv k t).snd = 0) := by
  let e := middleFixedToOrdinaryTensorGradedEquiv k
  have h : t ∈ 𝒯 d ↔ (e.toLinearEquiv.symm t).val ∈ 𝒬 d := by
    constructor
    · intro ht
      exact e.symm_map_mem' ht
    · intro hz
      have hz' : e.toLinearEquiv.symm t ∈ 𝒲 d := hz
      exact (e.toLinearEquiv.apply_symm_apply t) ▸ e.map_mem' hz'
  exact h.trans (middleCutDotSum_mem_grade_iff k (e.toLinearEquiv.symm t) d)

end Categorification.Stendhal.LabelTwo
