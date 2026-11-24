/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.FundamentalBraidTargetWeightEquiv
import Categorification.WeightedKLR.Rigidity.FundamentalBraidNormalizedCup
import Categorification.WeightedKLR.Rigidity.GradedMiddleTor

/-!
# Evaluation after the positive fundamental braid

Webster, arXiv:1309.3796v2, §7.1, Definition 7.4, and §7.2, Proposition 7.11.
Relabelling transports the cap by its adjunction with restriction along
the middle character. Applying the positive braid and the reversed-order
cap to the normalized cup produces two scalar summands.
-/

noncomputable section
namespace Categorification.Stendhal.FundamentalCorner
open CategoryTheory DG BraidedStendhalAlgebra QuantumGroup CatModule Coevaluation
open scoped DG.DegreeZero
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance] fundamentalBraidCoendTargetCornerGrades fundamentalBraidCoendTargetInternal
  fundamentalBraidCoendTargetBigraded fundamentalBraidSourceOrderedInternal fundamentalBraidSourceOrderedBigraded
  fundamentalTargetScalarInternal fundamentalTargetScalarBigraded
local notation "ν" => ({()} : Multiset Unit)
local notation "K" κ:arg => ViolOrderCorner (k := ℚ) (Q := Q) (Λ := wt) («ν» := ν) κ
local notation "U" => K ([1,0] : List (Fin 2))
local notation "T" => TensorProductAlgebra ℚ Q wt ν
local notation "V" => violAuxiliaryGrade («ν» := ν) grading

local notation "F" => fundamentalBraidTargetWeightFunctor
local notation "χ" => WeightCategory.mapFunctor gradedMiddleCharacter gradedMiddleCharacter_mem_weight
local notation "υ" => WeightCategory.mapFunctor fundamentalBraidGradedTargetCharacter fundamentalBraidGradedTargetCharacter_mem_weight

local notation "sT" j:arg => WeightCategory.shiftFunctor Tᵐᵒᵖ j
local notation "sU" j:arg => WeightCategory.shiftFunctor Uᵐᵒᵖ j
local notation "field" => CatModule.representable (WeightCategory.mk 0 : WeightCategory ℚ)

private def capAfterEquivalence {D₁ D₂ S : Type*} [Category D₁] [Category D₂] [Category S]
    (E : D₁ ≌ D₂) {c : D₁ ⥤ S} {u : S ⥤ D₁} (a : c ⊣ u) {c' : D₂ ⥤ S} {u' : S ⥤ D₂} (b : c' ⊣ u')
    (h : u ⋙ E.functor ≅ u') : E.functor ⋙ c' ≅ c := by
  let q := b.leftAdjointUniq ((E.symm.toAdjunction.comp a).ofNatIsoRight h)
  exact Functor.isoWhiskerLeft E.functor q ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight E.unitIso.symm c ≪≫ c.leftUnitor

universe v
variable [CatModule.HasDerivedCategory.{v,0} (WeightCategory Uᵐᵒᵖ)]
  [CatModule.HasDerivedCategory.{v,0} (WeightCategory Tᵐᵒᵖ)]
  [CatModule.HasDerivedCategory.{v,0} (WeightCategory ℚ)]
local notation "Qh" => CatModule.DerivedCategory.Q
local notation "Ceq" => fundamentalBraidTargetDerivedWeightEquivalence
local notation "I" A:arg j:arg => CatModule.DerivedCategory.internalShift A j
local notation "line" j:arg => Functor.obj CatModule.DerivedCategory.Q (CatModule.representable (WeightCategory.mk j : WeightCategory ℚ))

/-- The unshifted graded evaluation in the reversed fundamental red order. -/
def fundamentalBraidTargetCap := characterCap fundamentalBraidGradedTargetCharacter fundamentalBraidGradedTargetCharacter_mem_weight

/-- Evaluation after restriction to the reversed order agrees as a functor
with evaluation in the ordered diagram algebra. -/
def fundamentalBraidTargetCap_restrictIso :
    CatModule.DerivedCategory.restrict F ⋙ fundamentalBraidTargetCap ≅ gradedMiddleCap := by
  let h := CatModule.DerivedCategory.restrictNatIso fundamentalBraidTargetCharacterCompIso
      (fun _ => WeightCategory.mem_grading_zero_of_val_eq_one _ rfl) (fun _ => WeightCategory.d_eq_zero_of_val_eq_one _ rfl)
      (fun _ => WeightCategory.mem_grading_zero_of_val_eq_one _ rfl) (fun _ => WeightCategory.d_eq_zero_of_val_eq_one _ rfl)
  exact capAfterEquivalence Ceq (characterCapCupAdjunction gradedMiddleCharacter gradedMiddleCharacter_mem_weight)
    (characterCapCupAdjunction fundamentalBraidGradedTargetCharacter fundamentalBraidGradedTargetCharacter_mem_weight)
    ((CatModule.DerivedCategory.restrictCompIso F χ).symm ≪≫ h)

private def targetDerivedShiftedRestriction (j : ℤ) :
    (CatModule.DerivedCategory.restrict F).obj ((I (Tᵐᵒᵖ) j).obj ((Qh).obj gradedMiddleSimple)) ≅
      (I (Uᵐᵒᵖ) j).obj ((Qh).obj fundamentalBraidGradedTargetHead) :=
  (CatModule.DerivedCategory.restrict F).mapIso ((CatModule.DerivedCategory.QCompInternalShiftIso Tᵐᵒᵖ j).app gradedMiddleSimple) ≪≫
    (CatModule.DerivedCategory.QCompRestrictIso F).app ((CatModule.precomp (sT j)).obj gradedMiddleSimple) ≪≫
    (Qh).mapIso (fundamentalBraidTargetShiftedRestriction j) ≪≫
    ((CatModule.DerivedCategory.QCompInternalShiftIso Uᵐᵒᵖ j).app fundamentalBraidGradedTargetHead).symm

open CategoryTheory.Limits
/-- The cap of the translated reversed middle character has the two scalar
summands obtained from the ordered length-two projective resolution. -/
def fundamentalBraidTargetCap_translatedHeadIso (j : ℤ) :
    fundamentalBraidTargetCap.obj ((I (Uᵐᵒᵖ) j).obj ((Qh).obj fundamentalBraidGradedTargetHead)) ≅
      (line (0-j)) ⊞ (line (2-j))⟦(2 : ℤ)⟧ :=
  fundamentalBraidTargetCap.mapIso (targetDerivedShiftedRestriction j).symm ≪≫
    fundamentalBraidTargetCap_restrictIso.app _ ≪≫ gradedMiddleCap_shiftedSimpleIso j

local notation "κ₀" => List.finRange 2
local notation "κ₁" => ([1,0] : List (Fin 2))
local notation "he" => isIdempotentElem_violMk_redProj ℚ Q wt ν
local notation "h₀" => redProj_mem_violAuxiliaryGrade grading
attribute [local instance] fundamentalBraidCoendSourceCornerGrades fundamentalBraidCoendSourceInternal
  fundamentalBraidCoendSourceBigraded
local notation "DF" => diagramCornerWeightDerivedRightTensor V (he κ₀) (he κ₁) (h₀ κ₀) (h₀ κ₁)
local notation "R" => CatModule.DerivedCategory.restrict fundamentalBraidSourceWeightFunctor

variable [CatModule.HasDerivedCategory.{v,0} (WeightCategory (K κ₀)ᵐᵒᵖ)]
/-- Apply the normalized cup to the field, braid the two fundamental
strands, and evaluate in the reversed order. The two scalar terms have
weights minus one and one, in cohomological degrees zero and minus two. -/
def fundamentalBraidCappedCupIso :
    fundamentalBraidTargetCap.obj ((DF).obj ((R).obj (gradedMiddleCup.obj ((Qh).obj field)))) ≅
      (line (-1)) ⊞ (line 1)⟦(2 : ℤ)⟧ :=
  fundamentalBraidTargetCap.mapIso fundamentalBraidNormalizedCupIso ≪≫
    fundamentalBraidTargetCap_translatedHeadIso 1

end Categorification.Stendhal.FundamentalCorner
