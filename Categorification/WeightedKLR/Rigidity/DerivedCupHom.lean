/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.DerivedCupCap
import Categorification.Algebra.ProjectiveKProjective
import DG.Category.Derived.DGBimodule

/-!
# The cup as derived Hom

Webster, arXiv:1309.3796v2, Definition 7.4. After forgetting the internal
grading, the scalar derived Hom with the cup coefficient computes the
cup. The cap with the same coefficient is its left adjoint before applying
the cup shift, and evaluates on the regular module to the coefficient.
-/

noncomputable section

namespace Categorification.Stendhal.Coevaluation

open CategoryTheory DG MulOpposite
open scoped DG.DegreeZero

universe u v

variable (k A : Type u) [Field k] [Ring A] [Algebra k A]
  (L : Type u) [AddCommGroup L] [Module k L] [Module A L] [IsScalarTower k A L]

private instance : SMulCommClass A k L where
  smul_comm a c x := smul_algebra_smul_comm c a x

local notation "M" => InDegreeZero (OpBimodule A L)
local notation "B" => DGBimodule.catBimodule k Aᵐᵒᵖ M
omit [Ring A] [Algebra k A] [Module A L] [IsScalarTower k A L] in
private theorem coefficientKProjective : IsKProjective.{u} k M :=
  InDegreeZero.isKProjective

local notation "hM" => coefficientKProjective k A L
local notation "hB" => DGBimodule.catBimodule_left_isKProjective k Aᵐᵒᵖ M hM

variable [CatModule.HasDerivedCategory.{v,u} (SingleObj k)]
  [CatModule.HasDerivedCategory.{v,u} (SingleObj Aᵐᵒᵖ)]
  [HasDerivedCategory.{v,u} k] [HasDerivedCategory.{v,u} Aᵐᵒᵖ]

/-- Webster, arXiv:1309.3796v2, Definition 7.4. The unshifted scalar derived
Hom with the cup coefficient, carrying the opposite algebra action. -/
def cupRHomFunctor : DerivedCategory.{v,u} k ⥤ DerivedCategory.{v,u} Aᵐᵒᵖ :=
  (CatModule.DerivedCategory.singleObjEquivalence k).inverse ⋙
    CatModule.DerivedCategory.rhom.{v,v} B hB ⋙
    (CatModule.DerivedCategory.singleObjEquivalence Aᵐᵒᵖ).functor

/-- The ungraded derived Hom cup with its cohomological normalization. -/
def shiftedCupRHomFunctor (shift : ℤ) : DerivedCategory.{v,u} k ⥤ DerivedCategory.{v,u} Aᵐᵒᵖ :=
  cupRHomFunctor k A L ⋙ shiftFunctor (DerivedCategory.{v,u} Aᵐᵒᵖ) shift

/-- On a dg scalar module the cup is computed by the dg Hom complex.
No further resolution of the input is needed over the parameter field. -/
def cupRHomObjIso (X : DGModuleCat.{u} k) :
    (cupRHomFunctor k A L).obj (DG.DerivedCategory.Q.obj X) ≅
      (CatModule.DerivedCategory.singleObjEquivalence Aᵐᵒᵖ).functor.obj
        (CatModule.DerivedCategory.Q.obj ((B).homFunctor.obj (DGModuleCat.toCatModuleObj X))) := by
  let F := CatModule.DerivedCategory.singleObjEquivalence k
  let H := CatModule.DerivedCategory.rhom.{v,v} B hB
  let G := CatModule.DerivedCategory.singleObjEquivalence Aᵐᵒᵖ
  let X' := DGModuleCat.toCatModuleObj X
  have hX : F.inverse.obj (DG.DerivedCategory.Q.obj X) ≅ CatModule.DerivedCategory.Q.obj X' :=
    F.inverse.mapIso (DG.DerivedCategory.singleObjEquivalenceObjIso X).symm ≪≫
      F.unitIso.symm.app (CatModule.DerivedCategory.Q.obj X')
  exact G.functor.mapIso
    (H.mapIso hX ≪≫ (CatModule.DerivedCategory.QCompRhomIso B hB).app X')

/-- The cap with the same left coefficient, computed by dg bimodule tensor. -/
def capBimoduleFunctor : DerivedCategory.{v,u} Aᵐᵒᵖ ⥤ DerivedCategory.{v,u} k :=
  DGBimodule.derivedTensor.{v,v,v,v} k Aᵐᵒᵖ M hM

/-- The cap with the same coefficient is left adjoint to the unshifted cup.
The adjunction is the scalar tensor–Hom adjunction on derived categories. -/
def capBimoduleCupRHomAdjunction :
    capBimoduleFunctor k A L ⊣ cupRHomFunctor k A L :=
  (((CatModule.DerivedCategory.singleObjEquivalence Aᵐᵒᵖ).symm.toAdjunction).comp
    (CatModule.DerivedCategory.derivedTensorAdjunction.{v,v} B hB)).comp
    ((CatModule.DerivedCategory.singleObjEquivalence k).toAdjunction)

/-- The cap sends the right regular Webster module to the coefficient. -/
def capBimoduleRegularIso :
    (capBimoduleFunctor k A L).obj (DG.DerivedCategory.Q.obj (DGModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ)) ≅
      DG.DerivedCategory.Q.obj (DGModuleCat.of k M) :=
  DGBimodule.derivedTensorSelfIso.{v,v,v,v} k Aᵐᵒᵖ M hM

end Categorification.Stendhal.Coevaluation
