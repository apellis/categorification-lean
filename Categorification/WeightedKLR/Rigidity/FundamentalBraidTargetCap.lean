/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.FundamentalBraidTargetWeightEquiv
import Categorification.WeightedKLR.Rigidity.FundamentalBraidNormalizedCup
import Categorification.WeightedKLR.Rigidity.FundamentalQuantumTrace

/-!
# Evaluation after the positive fundamental braid

Webster, arXiv:1309.3796v2, §7.1, Definition 7.4 and Proposition 7.11.
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
/-- After the normalized cup and positive braid at scalar weight j,
reversed evaluation gives scalar lines at j−1 and j+1. -/
def fundamentalBraidCappedCup_scalarIso (j : ℤ) :
    fundamentalBraidTargetCap.obj ((DF).obj ((R).obj (gradedMiddleCup.obj (line j)))) ≅
      (line (j-1)) ⊞ (line (j+1))⟦(2 : ℤ)⟧ := by
  have zeroSub : 0-(1-j) = j-1 := by omega
  have twoSub : 2-(1-j) = j+1 := by omega
  exact fundamentalBraidTargetCap.mapIso (fundamentalBraidNormalizedCup_scalarIso j) ≪≫
    (by simpa only [zeroSub, twoSub] using fundamentalBraidTargetCap_translatedHeadIso (1-j))

/-- Apply the normalized cup to the field, braid the two fundamental
strands, and evaluate in the reversed order. The two scalar terms have
weights minus one and one, in cohomological degrees zero and minus two. -/
def fundamentalBraidCappedCupIso :
    fundamentalBraidTargetCap.obj ((DF).obj ((R).obj (gradedMiddleCup.obj ((Qh).obj field)))) ≅
      (line (-1)) ⊞ (line 1)⟦(2 : ℤ)⟧ :=
  fundamentalBraidTargetCap.mapIso fundamentalBraidNormalizedCupIso ≪≫
    fundamentalBraidTargetCap_translatedHeadIso 1

private local instance targetCapCommShift : fundamentalBraidTargetCap.CommShift ℤ := by
  unfold fundamentalBraidTargetCap characterCap
  infer_instance

private local instance capCornerTensorCommShift : (DF).CommShift ℤ := by
  unfold diagramCornerWeightDerivedRightTensor
  apply diagramWeightDerivedTensor_commShift

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

local notation "E" => (R) ⋙ (DF) ⋙ fundamentalBraidTargetCap

/-- For a scalar generator of weight j shifted by [n], the normalized cup,
positive braid and reversed evaluation have summands at weights j−1 and
j+1 with shifts [n] and [n+2], respectively. -/
def fundamentalBraidCappedCup_shiftedScalarIso (j n : ℤ) :
    (gradedMiddleCup ⋙ E).obj ((line j)⟦n⟧) ≅
      (line (j-1))⟦n⟧ ⊞ (line (j+1))⟦n+2⟧ := by
  let sh := shiftFunctor (CatModule.DerivedCategory.{v,0} (WeightCategory ℚ)) n
  let e := (E).mapIso (gradedMiddleCup_shiftIso n (line j)) ≪≫
    ((E).commShiftIso n).app (gradedMiddleCup.obj (line j))
  exact e ≪≫ sh.mapIso (fundamentalBraidCappedCup_scalarIso j) ≪≫
    sh.mapBiprod (line (j-1)) ((line (j+1))⟦(2 : ℤ)⟧) ≪≫
    biprod.mapIso (Iso.refl _) ((shiftFunctorAdd' _ (2 : ℤ) n (n+2) (by omega)).app (line (j+1))).symm

/-- On each shifted scalar generator the positive braid followed by the
reversed cap gives the clockwise circle of Webster, arXiv:1309.3796v2,
Proposition 7.13, with an additional cohomological shift [1]. -/
def fundamentalBraidCappedCup_clockwiseIso (j n : ℤ) :
    (gradedMiddleCup ⋙ E).obj ((line j)⟦n⟧) ≅
      ((gradedMiddleCup ⋙ gradedFundamentalQuantumTrace).obj ((line j)⟦n⟧))⟦(1 : ℤ)⟧ := by
  let sh := shiftFunctor (CatModule.DerivedCategory.{v,0} (WeightCategory ℚ)) (1 : ℤ)
  let e := sh.mapIso (gradedFundamentalClockwiseCircle_shiftedIso j n) ≪≫
    sh.mapBiprod ((line (j-1))⟦n-1⟧) ((line (j+1))⟦n+1⟧) ≪≫
    biprod.mapIso ((shiftFunctorAdd' _ (n-1) (1 : ℤ) n (by omega)).app (line (j-1))).symm
      ((shiftFunctorAdd' _ (n+1) (1 : ℤ) (n+2) (by omega)).app (line (j+1))).symm
  exact fundamentalBraidCappedCup_shiftedScalarIso j n ≪≫ e.symm

end Categorification.Stendhal.FundamentalCorner
