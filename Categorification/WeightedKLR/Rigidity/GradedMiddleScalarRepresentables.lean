/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.GradedMiddleTor

/-!
# The fundamental cup and cap on shifted scalar representables

In the fundamental example of Webster, arXiv:1309.3796v2, §7.1, the cut
(0,1) gives the graded middle character. Moving the generating weight of the
input scalar representable moves both output lines by the same amount.
-/

noncomputable section
namespace Categorification.Stendhal.FundamentalCorner
open CategoryTheory CategoryTheory.Limits DG CatModule MulOpposite Coevaluation
open scoped DG.DegreeZero
attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
local notation "T" => TensorProductAlgebra ℚ Q wt ({()} : Multiset Unit)
local notation "G" => Graded.oppositeGrade (tensorProductGrade grading ({()} : Multiset Unit))
local instance : InternalGrading Tᵐᵒᵖ := gradedAlgebraInternalGrading G
local instance : BigradedDGRing Tᵐᵒᵖ := gradedAlgebraBigradedDGRing G
local instance : InternalGrading ℚ := scalarInternalGrading ℚ
local instance : BigradedDGRing ℚ := scalarBigradedDGRing ℚ
local notation "Fχ" => WeightCategory.mapFunctor gradedMiddleCharacter gradedMiddleCharacter_mem_weight
local notation "scalar" j:arg => representable (⟨j⟩ : WeightCategory ℚ)

private def translatedMiddleCharacter (j : ℤ) :
    (precomp (WeightCategory.shiftFunctor Tᵐᵒᵖ 1)).obj ((precomp Fχ).obj (scalar j)) ≅
      (precomp (WeightCategory.shiftFunctor Tᵐᵒᵖ (1-j))).obj gradedMiddleSimple := by
  have h (k : WeightCategory Tᵐᵒᵖ) : (k.as+1)-j = (k.as+(1-j))-0 := by omega
  refine CatModule.isoMk (fun k => ?_) ?_ ?_ ?_
  · exact {
      toFun := fun x => ⟨x.val, (h k) ▸ x.property⟩
      invFun := fun y => ⟨y.val, (h k).symm ▸ y.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  · intro _ _ _; exact Iff.rfl
  · intro _ _; rfl
  · intro _ _ _ _; rfl

universe v
variable [CatModule.HasDerivedCategory.{v,0} (WeightCategory ℚ)]
  [CatModule.HasDerivedCategory.{v,0} (WeightCategory Tᵐᵒᵖ)]
local notation "line" j:arg => CatModule.DerivedCategory.Q.obj (scalar j)
local notation "translate" t:arg => CatModule.DerivedCategory.internalShift Tᵐᵒᵖ t
local notation "headObj" => CatModule.DerivedCategory.Q.obj gradedMiddleSimple

private instance : gradedMiddleCap.CommShift ℤ := by unfold gradedMiddleCap characterCap; infer_instance
/-- The normalized middle cup commutes with cohomological shifts of the input. -/
def gradedMiddleCup_shiftIso (n : ℤ) (X : CatModule.DerivedCategory.{v,0} (WeightCategory ℚ)) :
    gradedMiddleCup.obj (X⟦n⟧) ≅ (gradedMiddleCup.obj X)⟦n⟧ := by
  let F := CatModule.DerivedCategory.restrict Fχ ⋙ translate 1
  let e := (F.commShiftIso n).app X
  exact (shiftFunctor _ (-1 : ℤ)).mapIso e ≪≫ (shiftFunctorComm _ n (-1)).app (F.obj X)

/-- On the scalar representable generated at j, the normalized cup gives
the translated middle head with its generator at j−1 and shift [−1]. -/
def gradedMiddleCup_scalarIso (j : ℤ) :
    gradedMiddleCup.obj (line j) ≅ ((translate (1-j)).obj headObj)⟦(-1 : ℤ)⟧ := by
  let c := characterCupObjIso gradedMiddleCharacter gradedMiddleCharacter_mem_weight (scalar j)
  let a := (translate 1).mapIso c ≪≫
    (CatModule.DerivedCategory.QCompInternalShiftIso Tᵐᵒᵖ 1).app _ ≪≫
    CatModule.DerivedCategory.Q.mapIso (translatedMiddleCharacter j) ≪≫
    ((CatModule.DerivedCategory.QCompInternalShiftIso Tᵐᵒᵖ (1-j)).app gradedMiddleSimple).symm
  exact (shiftFunctor _ (-1 : ℤ)).mapIso a

/-- The normalized cup and cap take a scalar representable at j to scalar
representables at j−1 and j+1 in opposite odd cohomological shifts. -/
def gradedMiddleCupCap_scalarIso (j : ℤ) :
    (gradedMiddleCup ⋙ gradedMiddleCap).obj (line j) ≅
      (line (j-1))⟦(-1 : ℤ)⟧ ⊞ (line (j+1))⟦(1 : ℤ)⟧ := by
  let sh := shiftFunctor (CatModule.DerivedCategory.{v,0} (WeightCategory ℚ)) (-1 : ℤ)
  have h₀ : 0-(1-j) = j-1 := by omega
  have h₂ : 2-(1-j) = j+1 := by omega
  let r : gradedMiddleCap.obj ((translate (1-j)).obj headObj) ≅ (line (j-1)) ⊞ (line (j+1))⟦(2 : ℤ)⟧ := by
    simpa only [Functor.comp_obj, h₀, h₂] using gradedMiddleCap_shiftedSimpleIso (1-j)
  let e₁ := gradedMiddleCap.mapIso (gradedMiddleCup_scalarIso j)
  let e₂ := (gradedMiddleCap.commShiftIso (-1 : ℤ)).app ((translate (1-j)).obj headObj)
  let e₃ := sh.mapBiprod (line (j-1)) ((line (j+1))⟦(2 : ℤ)⟧)
  let e₄ := biprod.mapIso (Iso.refl (sh.obj (line (j-1))))
    ((shiftFunctorAdd' _ (2 : ℤ) (-1) 1 (by decide)).app (line (j+1))).symm
  exact e₁ ≪≫ e₂ ≪≫ sh.mapIso r ≪≫ e₃ ≪≫ e₄

/-- Both scalar lines translate by the input cohomological shift. -/
def gradedMiddleCupCap_shiftedScalarIso (j n : ℤ) :
    (gradedMiddleCup ⋙ gradedMiddleCap).obj ((line j)⟦n⟧) ≅
      (line (j-1))⟦n-1⟧ ⊞ (line (j+1))⟦n+1⟧ := by
  let sh := shiftFunctor (CatModule.DerivedCategory.{v,0} (WeightCategory ℚ)) n
  let e₁ := gradedMiddleCap.mapIso (gradedMiddleCup_shiftIso n (line j)) ≪≫
    (gradedMiddleCap.commShiftIso n).app (gradedMiddleCup.obj (line j))
  let e₂ := sh.mapBiprod ((line (j-1))⟦(-1 : ℤ)⟧) ((line (j+1))⟦(1 : ℤ)⟧)
  let e₃ := biprod.mapIso
    ((shiftFunctorAdd' _ (-1 : ℤ) n (n-1) (by omega)).app (line (j-1))).symm
    ((shiftFunctorAdd' _ (1 : ℤ) n (n+1) (by omega)).app (line (j+1))).symm
  exact e₁ ≪≫ sh.mapIso (gradedMiddleCupCap_scalarIso j) ≪≫ e₂ ≪≫ e₃

end Categorification.Stendhal.FundamentalCorner
