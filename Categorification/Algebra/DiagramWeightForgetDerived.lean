/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DiagramWeightForgetTensor
import Categorification.Algebra.DiagramWeightTensorShift
import Categorification.Algebra.DerivedTensor

/-!
# Forgetting the weights of a graded derived diagram tensor

For a homogeneous coefficient bimodule `M` with weight decomposition `G`, the derived tensor
with the graded coefficient `D = diagramWeightBimodule G` and the derived tensor with `M` are
compared by the derived functors forgetting the weights:

`weightForgetDerived A ∘ (D ⊗ᴸ -) ≅ (M ⊗ᴸ_B -) ∘ weightForgetDerived B`

(`Categorification.diagramWeightForgetDerivedIso`). Both sides are computed on K-projective
dg modules over `C_B`, whose weight sums are K-projective, where they agree by
`Categorification.diagramWeightForgetTensorIso`. This is the comparison of the graded derived
tensors of B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
Definition 6.6, with the ungraded ones.
-/

noncomputable section

namespace Categorification

open CategoryTheory DG MulOpposite
open scoped DG.DegreeZero

universe u v w

variable {A B M : Type u} [Ring A] [Ring B] [InternalGrading A] [InternalGrading B]
  [BigradedDGRing A] [BigradedDGRing B] [AddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M]
  [SMulCommClass A Bᵐᵒᵖ M]
  (G : ℤ → AddSubgroup M) [DirectSum.Decomposition G]
  (hl : ∀ {i j : ℤ} {a : A} {x : M}, a ∈ wgrading i → x ∈ G j → a • x ∈ G (i+j))
  (hr : ∀ {i j : ℤ} {b : B} {x : M}, b ∈ wgrading i → x ∈ G j → op b • x ∈ G (j+i))
  [CatModule.HasDerivedCategory.{v,u} (WeightCategory A)]
  [CatModule.HasDerivedCategory.{v,u} (WeightCategory B)]

local notation "D" => diagramWeightBimodule G hl hr

/-- Forgetting the weights commutes with tensoring by a diagram coefficient on homotopy
categories. -/
def diagramWeightForgetTensorHomotopyIso :
    diagramWeightTensorHomotopy G hl hr ⋙ CatModule.weightForgetHomotopy A ≅
      CatModule.weightForgetHomotopy B ⋙
        DG.HomotopyCategory.tensorFunctor A (InDegreeZero M) :=
  CategoryTheory.Quotient.natIsoLift _
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (diagramWeightTensorHomotopyFactors G hl hr) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (CatModule.weightForgetHomotopyFactors A) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (diagramWeightForgetTensorIso G hl hr) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (DG.HomotopyCategory.tensorFunctorQuotientIso A (InDegreeZero M)).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (CatModule.weightForgetHomotopyFactors B).symm _ ≪≫
      Functor.associator _ _ _)

/-- Two functors out of a category agree when they agree after an equivalence. -/
def isoOfEquivalenceFunctor {C₁ C₂ E : Type*} [Category C₁] [Category C₂] [Category E]
    (e : C₁ ≌ C₂) {F₁ F₂ : C₂ ⥤ E} (h : e.functor ⋙ F₁ ≅ e.functor ⋙ F₂) : F₁ ≅ F₂ :=
  (Functor.leftUnitor F₁).symm ≪≫ Functor.isoWhiskerRight e.counitIso.symm F₁ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft e.inverse h ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e.counitIso F₂ ≪≫
    Functor.leftUnitor F₂

variable [DG.HasDerivedCategory.{w,u} A] [DG.HasDerivedCategory.{w,u} B]

local notation "KB" => CatModule.HomotopyCategory.subcategoryKProjective (WeightCategory B)
local notation "KB'" => DG.HomotopyCategory.subcategoryKProjective B

/-- Forgetting the weights of K-projective objects. -/
def weightForgetKProjective : (KB).FullSubcategory ⥤ (KB').FullSubcategory :=
  ObjectProperty.lift _ ((KB).ι ⋙ CatModule.weightForgetHomotopy B)
    fun p => CatModule.weightForgetHomotopy_obj_mem_subcategoryKProjective p.property

/-- The graded side of the comparison, on K-projective objects. -/
def diagramWeightForgetDerivedIsoLeft :
    (CatModule.DerivedCategory.kProjectiveEquivalence (WeightCategory B)).functor ⋙
        (diagramWeightDerivedTensor G hl hr ⋙ CatModule.weightForgetDerived A) ≅
      (KB).ι ⋙ (diagramWeightTensorHomotopy G hl hr ⋙ CatModule.weightForgetHomotopy A) ⋙
        DG.DerivedCategory.Qh.{w} :=
  let E := CatModule.DerivedCategory.kProjectiveEquivalence (WeightCategory B)
  let R := (KB).ι ⋙ diagramWeightTensorHomotopy G hl hr ⋙ CatModule.DerivedCategory.Qh
  let h₁ : E.functor ⋙ diagramWeightDerivedTensor G hl hr ≅ R :=
    (Functor.associator E.functor E.inverse R).symm ≪≫
      Functor.isoWhiskerRight E.unitIso.symm R ≪≫ Functor.leftUnitor R
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight h₁ (CatModule.weightForgetDerived A) ≪≫
    Functor.isoWhiskerLeft ((KB).ι ⋙ diagramWeightTensorHomotopy G hl hr)
      (CatModule.QhCompWeightForgetDerivedIso A)

/-- The ungraded side of the comparison, on K-projective objects. -/
def diagramWeightForgetDerivedIsoRight :
    (CatModule.DerivedCategory.kProjectiveEquivalence (WeightCategory B)).functor ⋙
        (CatModule.weightForgetDerived B ⋙ derivedTensor.{w} A B M) ≅
      (KB).ι ⋙ (CatModule.weightForgetHomotopy B ⋙
        DG.HomotopyCategory.tensorFunctor A (InDegreeZero M)) ⋙ DG.DerivedCategory.Qh.{w} :=
  let E' := DG.DerivedCategory.kProjectiveEquivalence.{w} B
  let R := (KB').ι ⋙ DG.HomotopyCategory.tensorFunctor A (InDegreeZero M) ⋙
    DG.DerivedCategory.Qh.{w}
  let h₂ : E'.functor ⋙ derivedTensor.{w} A B M ≅ R :=
    (Functor.associator E'.functor E'.inverse R).symm ≪≫
      Functor.isoWhiskerRight E'.unitIso.symm R ≪≫ Functor.leftUnitor R
  Functor.isoWhiskerLeft (KB).ι
      (Functor.associator CatModule.DerivedCategory.Qh (CatModule.weightForgetDerived B)
        (derivedTensor.{w} A B M)).symm ≪≫
    Functor.isoWhiskerLeft (KB).ι (Functor.isoWhiskerRight
      (CatModule.QhCompWeightForgetDerivedIso B) (derivedTensor.{w} A B M)) ≪≫
    Functor.isoWhiskerLeft weightForgetKProjective h₂

/-- **Forgetting the weights commutes with the derived diagram tensor**:
`weightForgetDerived A ∘ (D ⊗ᴸ -) ≅ (M ⊗ᴸ_B -) ∘ weightForgetDerived B`. -/
def diagramWeightForgetDerivedIso :
    diagramWeightDerivedTensor G hl hr ⋙ CatModule.weightForgetDerived A ≅
      CatModule.weightForgetDerived B ⋙ derivedTensor.{w} A B M :=
  isoOfEquivalenceFunctor (CatModule.DerivedCategory.kProjectiveEquivalence (WeightCategory B))
    (diagramWeightForgetDerivedIsoLeft G hl hr ≪≫
      Functor.isoWhiskerLeft (KB).ι
        (Functor.isoWhiskerRight (diagramWeightForgetTensorHomotopyIso G hl hr) _) ≪≫
      (diagramWeightForgetDerivedIsoRight (A := A) (B := B) (M := M)).symm)

end Categorification
