/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.FundamentalBraidTargetHead
import Categorification.WeightedKLR.Rigidity.FundamentalBraidGradedCoend
import Categorification.WeightedKLR.Rigidity.GradedMiddleCupCap
import Categorification.WeightedKLR.RedStrands.BraidingAuxiliaryDerived
/-!
# The graded middle head in the reversed target order

In the fundamental case of Webster, arXiv:1309.3796v2, §7.2,
Proposition 7.11, the reversed-order middle character is concentrated
in auxiliary weight zero. Restrict the scalar weight module along this
character to express the target in the weight category of the braid.
-/

noncomputable section
namespace Categorification.Stendhal.FundamentalCorner
open KLR KLRAlgebra BraidedStendhalAlgebra QuantumGroup DirectSum
local notation "ν" => ({()} : Multiset Unit)
local notation "C" => CartanDatum.ofGraph (⊥ : SimpleGraph Unit)
local notation "K" => ViolOrderCorner (k := ℚ) (Q := Q) (Λ := wt) («ν» := ν) [1,0]
local notation "D" => grading
local notation "V" => violAuxiliaryGrade («ν» := ν) D
local notation "E" => braidProject (e crossedMiddle)

/-- The target character kills elements of nonzero auxiliary degree. -/
theorem fundamentalBraidTargetCharacter_auxiliary_zero {j : ℤ} (hj : j ≠ 0) {r : K} (hr : r.val ∈ V j) :
    fundamentalBraidTargetCharacter r = 0 := by
  have he : E ∈ V 0 := Graded.mem_map_of_mem _ (violMk ℚ Q wt ν).toLinearMap
    (Graded.mem_map_of_mem _ (ofKLR ℚ Q wt ν).toLinearMap (grading.e_mem_grade crossedMiddle))
  have hv : fundamentalBraidTargetCharacter r • E ∈ V j := by
    rw [← fundamentalBraidTargetCorner_scalar]
    simpa only [zero_add,add_zero] using SetLike.GradedMul.mul_mem (SetLike.GradedMul.mul_mem he hr) he
  have hzero : fundamentalBraidTargetCharacter r • E = 0 :=
    Submodule.disjoint_def.mp ((Decomposition.isInternal (V)).submodule_iSupIndep.pairwiseDisjoint hj)
      _ hv ((V 0).smul_mem _ he)
  apply (smul_eq_zero.mp hzero).resolve_right
  intro h
  apply fundamentalBraidCycle_ne_zero
  rw [← fundamentalBraidCycle_supported,h,mul_zero]

open CategoryTheory DG MulOpposite Coevaluation
open scoped DG.DegreeZero
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
local notation "hK" => isIdempotentElem_violMk_redProj ℚ Q wt ν [1,0]
local notation "Ugrade" => Graded.oppositeGrade (Graded.cornerGrading V hK)
local instance fundamentalCharacterTargetCornerGrades : GradedAlgebra (Graded.cornerGrading V hK) :=
  fundamentalBraidCoendTargetCornerGrades
local instance fundamentalCharacterTargetInternal : InternalGrading Kᵐᵒᵖ := gradedAlgebraInternalGrading Ugrade
local instance fundamentalCharacterTargetBigraded : BigradedDGRing Kᵐᵒᵖ := gradedAlgebraBigradedDGRing Ugrade
local instance fundamentalTargetScalarInternal : InternalGrading ℚ := scalarInternalGrading ℚ
local instance fundamentalTargetScalarBigraded : BigradedDGRing ℚ := scalarBigradedDGRing ℚ

/-- The reversed-order middle character as a dg ring morphism. -/
def fundamentalBraidGradedTargetCharacter : Kᵐᵒᵖ →ᵈᵍ+* ℚ :=
  oppositeScalarCharacter fundamentalBraidTargetCharacter

/-- The target character respects the diagram weights. -/
theorem fundamentalBraidGradedTargetCharacter_mem_weight {j : ℤ} {a : Kᵐᵒᵖ} (ha : a ∈ Ugrade j) :
    fundamentalBraidGradedTargetCharacter a ∈ wgrading (M := ℚ) j :=
  oppositeScalarCharacter_mem_weight fundamentalBraidTargetCharacter
    (fun hj hz => fundamentalBraidTargetCharacter_auxiliary_zero hj hz) ha

local notation "Fχ" => WeightCategory.mapFunctor fundamentalBraidGradedTargetCharacter fundamentalBraidGradedTargetCharacter_mem_weight
local notation "ground" => CatModule.representable (WeightCategory.mk 0 : WeightCategory ℚ)

/-- The target middle simple on the reversed-order weight category. -/
def fundamentalBraidGradedTargetHead : CatModule.{0} (WeightCategory Kᵐᵒᵖ) :=
  (CatModule.precomp Fχ).obj ground

/-- Homogeneous diagrams act by the reversed middle character. -/
theorem fundamentalBraidGradedTargetHead_act {j l : WeightCategory Kᵐᵒᵖ} (a : j ⟶ l)
    (z : fundamentalBraidGradedTargetHead.obj j) :
    ((fundamentalBraidGradedTargetHead.act a) z).val = fundamentalBraidTargetCharacter a.val.unop * z.val := rfl

end Categorification.Stendhal.FundamentalCorner
