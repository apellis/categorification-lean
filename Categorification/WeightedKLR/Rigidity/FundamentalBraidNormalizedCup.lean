/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DiagramWeightTensorInternal
import Categorification.Algebra.DiagramWeightTensorDerived
import Categorification.WeightedKLR.Rigidity.FundamentalBraidGradedCharacterComparison
import Categorification.WeightedKLR.Rigidity.GradedMiddleScalarRepresentables

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
local notation "I" X:arg j:arg => CatModule.DerivedCategory.internalShift X j
local notation "unit" => CatModule.representable (WeightCategory.mk 0 : WeightCategory ℚ)

local notation "Fsrc" => fundamentalBraidSourceWeightFunctor
local notation "SI" j:arg => WeightCategory.shiftFunctor Kᵐᵒᵖ j
local notation "TI" j:arg => WeightCategory.shiftFunctor Tᵐᵒᵖ j

private def commuteSourceTranslation (t : ℤ) : Fsrc ⋙ TI t ≅ SI t ⋙ Fsrc :=
  NatIso.ofComponents (fun _ => WeightCategory.isoOfEq rfl) (fun f => by
    apply WeightCategory.hom_ext
    change _ * _ = _ * _
    simp [WeightCategory.isoOfEq]
    rfl)

private def translatedSourceIso (t : ℤ) : (r).obj ((CatModule.precomp (TI t)).obj gradedMiddleSimple) ≅
    (CatModule.precomp (SI t)).obj fundamentalBraidSourceGradedHead :=
  ((CatModule.precompCompIso Fsrc (TI t)).app gradedMiddleSimple).symm ≪≫
    (CatModule.precompNatIso (commuteSourceTranslation t)
      (fun _ => WeightCategory.mem_grading_zero_of_val_eq_one _ rfl)
      (fun _ => WeightCategory.d_eq_zero_of_val_eq_one _ rfl)
      (fun _ => WeightCategory.mem_grading_zero_of_val_eq_one _ rfl)
      (fun _ => WeightCategory.d_eq_zero_of_val_eq_one _ rfl)).app gradedMiddleSimple ≪≫
    (CatModule.precompCompIso (SI t) Fsrc).app gradedMiddleSimple

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

private def braidInternal (t : ℤ) (Y : CatModule.DerivedCategory.{z,0} (WeightCategory Kᵐᵒᵖ)) :
    (DF).obj ((I (Kᵐᵒᵖ) t).obj Y) ≅ (I (Uᵐᵒᵖ) t).obj ((DF).obj Y) := by
  unfold diagramCornerWeightDerivedRightTensor
  exact diagramWeightDerivedTensorInternalIso _ _ _ _ Y

private local instance normalizedCornerTensorCommShift : (DF).CommShift ℤ := by
  unfold diagramCornerWeightDerivedRightTensor
  apply diagramWeightDerivedTensor_commShift

private def translatedHeadIso (t : ℤ) :
    (DF).obj (((I (Kᵐᵒᵖ) t).obj ((Qh).obj fundamentalBraidSourceGradedHead))⟦(-1 : ℤ)⟧) ≅
      (I (Uᵐᵒᵖ) t).obj ((Qh).obj fundamentalBraidGradedTargetHead) :=
  cancelTranslatedShift DF (I (Kᵐᵒᵖ) t) (I (Uᵐᵒᵖ) t) ((Qh).obj fundamentalBraidSourceGradedHead)
    ((Qh).obj fundamentalBraidGradedTargetHead) fundamentalBraidGradedDerivedTargetIso
    (braidInternal t ((Qh).obj fundamentalBraidSourceGradedHead))

/-- The auxiliary and cohomological shifts of the normalized cup cancel
the cohomological shift of the braid on the middle character. -/
def fundamentalBraidNormalizedHeadIso :
    (DF).obj (((I (Kᵐᵒᵖ) 1).obj ((Qh).obj fundamentalBraidSourceGradedHead))⟦(-1 : ℤ)⟧) ≅
      (I (Uᵐᵒᵖ) 1).obj ((Qh).obj fundamentalBraidGradedTargetHead) :=
  translatedHeadIso 1

variable [CatModule.HasDerivedCategory.{z,0} (WeightCategory ℚ)]
  [CatModule.HasDerivedCategory.{z,0} (WeightCategory Tᵐᵒᵖ)]

local notation "line" j:arg => Functor.obj CatModule.DerivedCategory.Q (CatModule.representable (WeightCategory.mk j : WeightCategory ℚ))

/-- The positive braid on the normalized cup at scalar weight j gives the
reversed middle character translated by 1−j in cohomological degree zero. -/
def fundamentalBraidNormalizedCup_scalarIso (j : ℤ) :
    (DF).obj ((R).obj (gradedMiddleCup.obj (line j))) ≅
      (I (Uᵐᵒᵖ) (1-j)).obj ((Qh).obj fundamentalBraidGradedTargetHead) := by
  let t := 1-j
  let e := (R).mapIso ((CatModule.DerivedCategory.QCompInternalShiftIso Tᵐᵒᵖ t).app gradedMiddleSimple) ≪≫
    ((CatModule.DerivedCategory.QCompRestrictIso fundamentalBraidSourceWeightFunctor).app
      ((CatModule.precomp (TI t)).obj gradedMiddleSimple)) ≪≫
    (Qh).mapIso (translatedSourceIso t) ≪≫
    ((CatModule.DerivedCategory.QCompInternalShiftIso Kᵐᵒᵖ t).app fundamentalBraidSourceGradedHead).symm
  let e' := (R).mapIso (gradedMiddleCup_scalarIso j) ≪≫
    ((R).commShiftIso (-1 : ℤ)).app ((I (Tᵐᵒᵖ) t).obj ((Qh).obj gradedMiddleSimple)) ≪≫
    (shiftFunctor _ (-1 : ℤ)).mapIso e
  exact (DF).mapIso e' ≪≫ translatedHeadIso t

/-- The normalized graded cup on the field, restricted to the diagonal braid
source, braids to the reversed middle character translated by one. -/
def fundamentalBraidNormalizedCupIso :
    (DF).obj ((R).obj (gradedMiddleCup.obj ((Qh).obj unit))) ≅
      (I (Uᵐᵒᵖ) 1).obj ((Qh).obj fundamentalBraidGradedTargetHead) := by
  simpa only [sub_zero] using fundamentalBraidNormalizedCup_scalarIso 0
end Categorification.Stendhal.FundamentalCorner
