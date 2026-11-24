/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DiagramWeightTensorInternal
import Categorification.Algebra.DiagramWeightTensorDerived
import Categorification.WeightedKLR.Rigidity.FundamentalBraidGradedCharacterComparison

/-!
# Positive braid on the normalized fundamental cup

Webster, arXiv:1309.3796v2, §7.1, Definition 7.4 and Proposition 7.11.
Over the rationals, the braid on the normalized fundamental cup on the field
is the reversed-order middle character in cohomological degree zero with
internal translation one.
-/

noncomputable section
namespace Categorification.Stendhal.FundamentalCorner
open CategoryTheory DG BraidedStendhalAlgebra CatModule
open scoped DG.DegreeZero
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance] fundamentalBraidCoendSourceCornerGrades fundamentalBraidCoendTargetCornerGrades
  fundamentalBraidCoendSourceInternal fundamentalBraidCoendTargetInternal
  fundamentalBraidCoendSourceBigraded fundamentalBraidCoendTargetBigraded
  fundamentalBraidSourceOrderedInternal fundamentalBraidSourceOrderedBigraded
  fundamentalTargetScalarInternal fundamentalTargetScalarBigraded
local notation "ν" => ({()} : Multiset Unit)
local notation "κ₀" => List.finRange 2
local notation "κ₁" => ([1,0] : List (Fin 2))
local notation "K" => ViolOrderCorner (k := ℚ) (Q := Q) (Λ := wt) («ν» := ν) κ₀
local notation "U" => ViolOrderCorner (k := ℚ) (Q := Q) (Λ := wt) («ν» := ν) κ₁
local notation "T" => TensorProductAlgebra ℚ Q wt ν
local notation "V" => violAuxiliaryGrade («ν» := ν) grading
local notation "he" => isIdempotentElem_violMk_redProj ℚ Q wt ν
local notation "h₀" => redProj_mem_violAuxiliaryGrade grading
local notation "DF" => diagramCornerWeightDerivedRightTensor V (he κ₀) (he κ₁) (h₀ κ₀) (h₀ κ₁)
local notation "r" => CatModule.precomp fundamentalBraidSourceWeightFunctor
local notation "R" => CatModule.DerivedCategory.restrict fundamentalBraidSourceWeightFunctor
local notation "Qh" => CatModule.DerivedCategory.Q
local notation "I" X:arg => CatModule.DerivedCategory.internalShift X 1
local notation "unit" => CatModule.representable (WeightCategory.mk 0 : WeightCategory ℚ)

local notation "Fsrc" => fundamentalBraidSourceWeightFunctor
local notation "SI" => WeightCategory.shiftFunctor Kᵐᵒᵖ 1
local notation "TI" => WeightCategory.shiftFunctor Tᵐᵒᵖ 1

private def commuteSourceTranslation : Fsrc ⋙ TI ≅ SI ⋙ Fsrc :=
  NatIso.ofComponents (fun _ => WeightCategory.isoOfEq rfl) (fun f => by
    apply WeightCategory.hom_ext
    change _ * _ = _ * _
    simp [WeightCategory.isoOfEq]
    rfl)

private def normalizedSourceIso : (r).obj normalizedMiddleSimple ≅
    (CatModule.precomp SI).obj fundamentalBraidSourceGradedHead :=
  ((CatModule.precompCompIso Fsrc TI).app gradedMiddleSimple).symm ≪≫
    (CatModule.precompNatIso commuteSourceTranslation
      (fun _ => WeightCategory.mem_grading_zero_of_val_eq_one _ rfl)
      (fun _ => WeightCategory.d_eq_zero_of_val_eq_one _ rfl)
      (fun _ => WeightCategory.mem_grading_zero_of_val_eq_one _ rfl)
      (fun _ => WeightCategory.d_eq_zero_of_val_eq_one _ rfl)).app gradedMiddleSimple ≪≫
    (CatModule.precompCompIso SI Fsrc).app gradedMiddleSimple

private def cancelTranslatedShift {S D : Type*} [Category S] [Category D] [HasShift S ℤ] [HasShift D ℤ]
    (F : S ⥤ D) [F.CommShift ℤ] (s : S ⥤ S) (t : D ⥤ D) [t.CommShift ℤ]
    (Y : S) (Z : D) (shifted : F.obj Y ≅ Z⟦(1 : ℤ)⟧) (internal : F.obj (s.obj Y) ≅ t.obj (F.obj Y)) :
    F.obj ((s.obj Y)⟦(-1 : ℤ)⟧) ≅ t.obj Z :=
  (F.commShiftIso (-1 : ℤ)).app (s.obj Y) ≪≫
    (shiftFunctor _ (-1 : ℤ)).mapIso (internal ≪≫ t.mapIso shifted ≪≫ (t.commShiftIso (1 : ℤ)).app Z) ≪≫
    (shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by decide)).app (t.obj Z)

universe z
variable [CatModule.HasDerivedCategory.{z,0} (WeightCategory Kᵐᵒᵖ)]
  [CatModule.HasDerivedCategory.{z,0} (WeightCategory Uᵐᵒᵖ)]

private def braidInternal (Y : CatModule.DerivedCategory.{z,0} (WeightCategory Kᵐᵒᵖ)) :
    (DF).obj ((I (Kᵐᵒᵖ)).obj Y) ≅ (I (Uᵐᵒᵖ)).obj ((DF).obj Y) := by
  unfold diagramCornerWeightDerivedRightTensor
  exact diagramWeightDerivedTensorInternalIso _ _ _ _ Y

private local instance normalizedCornerTensorCommShift : (DF).CommShift ℤ := by
  unfold diagramCornerWeightDerivedRightTensor
  apply diagramWeightDerivedTensor_commShift

/-- The source middle character with the two shifts in the normalized
fundamental cup braids to the internally translated target character. -/
def fundamentalBraidNormalizedHeadIso :
    (DF).obj (((I (Kᵐᵒᵖ)).obj ((Qh).obj fundamentalBraidSourceGradedHead))⟦(-1 : ℤ)⟧) ≅
      (I (Uᵐᵒᵖ)).obj ((Qh).obj fundamentalBraidGradedTargetHead) :=
  cancelTranslatedShift DF (I (Kᵐᵒᵖ)) (I (Uᵐᵒᵖ)) ((Qh).obj fundamentalBraidSourceGradedHead)
    ((Qh).obj fundamentalBraidGradedTargetHead) fundamentalBraidGradedDerivedTargetIso
    (braidInternal ((Qh).obj fundamentalBraidSourceGradedHead))

variable [CatModule.HasDerivedCategory.{z,0} (WeightCategory ℚ)]
  [CatModule.HasDerivedCategory.{z,0} (WeightCategory Tᵐᵒᵖ)]

/-- The normalized graded cup on the field, restricted to the diagonal braid
source, braids to the reversed middle character translated by one. -/
def fundamentalBraidNormalizedCupIso :
    (DF).obj ((R).obj (gradedMiddleCup.obj ((Qh).obj unit))) ≅
      (I (Uᵐᵒᵖ)).obj ((Qh).obj fundamentalBraidGradedTargetHead) := by
  let e := ((CatModule.DerivedCategory.QCompRestrictIso fundamentalBraidSourceWeightFunctor).app normalizedMiddleSimple) ≪≫
    (Qh).mapIso normalizedSourceIso ≪≫
    ((CatModule.DerivedCategory.QCompInternalShiftIso Kᵐᵒᵖ 1).app fundamentalBraidSourceGradedHead).symm
  let e' := (R).mapIso gradedMiddleCup_fieldIso ≪≫ ((R).commShiftIso (-1 : ℤ)).app ((Qh).obj normalizedMiddleSimple) ≪≫
    (shiftFunctor _ (-1 : ℤ)).mapIso e
  exact (DF).mapIso e' ≪≫ fundamentalBraidNormalizedHeadIso
end Categorification.Stendhal.FundamentalCorner
