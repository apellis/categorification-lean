/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.MapDerivedNatTrans

/-!
# Relations between whiskered transformations on derived categories

For exact functors `F₁, F₂, F₃` between abelian categories, a transformation
`X : F₁ ⋙ F₂ ⟶ F₁' ⋙ F₂'` gives `NatTrans.derivedComp X : F₁ᴰ ⋙ F₂ᴰ ⟶ F₁'ᴰ ⋙ F₂'ᴰ`, the
conjugate of `X.mapDerivedCategory` by `Functor.mapDerivedCategoryCompIso`. Its whiskerings
are the derived whiskerings of `X` up to `Functor.mapDerivedCategoryTripleIso`
(`NatTrans.whiskerLeft_derivedComp_tripleIso`, `NatTrans.whiskerRight_derivedComp_tripleIso`).
Hence relations between whiskered transformations, such as the braid relation, pass to derived
categories (`NatTrans.derivedComp_braid`), and so does a vanishing composite
(`NatTrans.derivedComp_comp_eq_zero`).
-/

noncomputable section

namespace CategoryTheory

open Category Limits

universe w₁ w₂ w₃ w₄ w₅ w₆

variable {C₁ : Type*} [Category* C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type*} [Category* C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  {C₃ : Type*} [Category* C₃] [Abelian C₃] [HasDerivedCategory.{w₃} C₃]
  {C₄ : Type*} [Category* C₄] [Abelian C₄] [HasDerivedCategory.{w₄} C₄]

namespace NatTrans

section

variable {C₂' : Type*} [Category* C₂'] [Abelian C₂'] [HasDerivedCategory.{w₅} C₂']
  {F₁ : C₁ ⥤ C₂} [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  {F₁' : C₁ ⥤ C₂'} [F₁'.Additive] [PreservesFiniteLimits F₁'] [PreservesFiniteColimits F₁']
  {F₂ : C₂ ⥤ C₃} [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  {F₂' : C₂' ⥤ C₃} [F₂'.Additive] [PreservesFiniteLimits F₂'] [PreservesFiniteColimits F₂']

/-- A transformation of composites on derived categories: `X.mapDerivedCategory` conjugated by
`mapDerivedCategoryCompIso`. -/
def derivedComp (X : F₁ ⋙ F₂ ⟶ F₁' ⋙ F₂') :
    F₁.mapDerivedCategory ⋙ F₂.mapDerivedCategory ⟶
      F₁'.mapDerivedCategory ⋙ F₂'.mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso F₁ F₂).hom ≫ X.mapDerivedCategory ≫
    (Functor.mapDerivedCategoryCompIso F₁' F₂').inv

theorem derivedComp_comp {C₂'' : Type*} [Category* C₂''] [Abelian C₂'']
    [HasDerivedCategory.{w₆} C₂''] {F₁'' : C₁ ⥤ C₂''} [F₁''.Additive] [PreservesFiniteLimits F₁'']
    [PreservesFiniteColimits F₁''] {F₂'' : C₂'' ⥤ C₃} [F₂''.Additive] [PreservesFiniteLimits F₂'']
    [PreservesFiniteColimits F₂''] (X : F₁ ⋙ F₂ ⟶ F₁' ⋙ F₂') (Y : F₁' ⋙ F₂' ⟶ F₁'' ⋙ F₂'') :
    derivedComp X ≫ derivedComp Y = derivedComp (X ≫ Y) := by
  simp only [derivedComp, assoc, Iso.inv_hom_id_assoc, mapDerivedCategory_comp]

theorem derivedComp_comp_eq_zero {C₂'' : Type*} [Category* C₂''] [Abelian C₂'']
    [HasDerivedCategory.{w₆} C₂''] {F₁'' : C₁ ⥤ C₂''} [F₁''.Additive] [PreservesFiniteLimits F₁'']
    [PreservesFiniteColimits F₁''] {F₂'' : C₂'' ⥤ C₃} [F₂''.Additive] [PreservesFiniteLimits F₂'']
    [PreservesFiniteColimits F₂''] {X : F₁ ⋙ F₂ ⟶ F₁' ⋙ F₂'} {Y : F₁' ⋙ F₂' ⟶ F₁'' ⋙ F₂''}
    (h : X ≫ Y = 0) : derivedComp X ≫ derivedComp Y = 0 := by
  rw [derivedComp_comp, h, derivedComp, mapDerivedCategory_zero, zero_comp, comp_zero]

end

end NatTrans

namespace Functor

variable (F₁ : C₁ ⥤ C₂) [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  (F₂ : C₂ ⥤ C₃) [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  (F₃ : C₃ ⥤ C₄) [F₃.Additive] [PreservesFiniteLimits F₃] [PreservesFiniteColimits F₃]

/-- The identification of the composite of three derived functors with the derived functor of
the composite. -/
def mapDerivedCategoryTripleIso :
    F₁.mapDerivedCategory ⋙ F₂.mapDerivedCategory ⋙ F₃.mapDerivedCategory ≅
      (F₁ ⋙ F₂ ⋙ F₃).mapDerivedCategory :=
  isoWhiskerLeft _ (mapDerivedCategoryCompIso F₂ F₃) ≪≫ mapDerivedCategoryCompIso F₁ (F₂ ⋙ F₃)

theorem mapDerivedCategoryTripleIso_hom_eq : (mapDerivedCategoryTripleIso F₁ F₂ F₃).hom =
    whiskerRight (mapDerivedCategoryCompIso F₁ F₂).hom F₃.mapDerivedCategory ≫
      (mapDerivedCategoryCompIso (F₁ ⋙ F₂) F₃).hom :=
  (mapDerivedCategoryCompIso_assoc _ _ _).symm

end Functor

namespace NatTrans

variable {F₁ F₁' : C₁ ⥤ C₂} [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [F₁'.Additive] [PreservesFiniteLimits F₁'] [PreservesFiniteColimits F₁']
  {F₂ F₂' : C₂ ⥤ C₃} [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [F₂'.Additive] [PreservesFiniteLimits F₂'] [PreservesFiniteColimits F₂']
  {F₃ F₃' : C₃ ⥤ C₄} [F₃.Additive] [PreservesFiniteLimits F₃] [PreservesFiniteColimits F₃]
  [F₃'.Additive] [PreservesFiniteLimits F₃'] [PreservesFiniteColimits F₃']

@[reassoc]
theorem whiskerLeft_derivedComp_tripleIso (X : F₂ ⋙ F₃ ⟶ F₂' ⋙ F₃') :
    Functor.whiskerLeft F₁.mapDerivedCategory (derivedComp X) ≫
        (Functor.mapDerivedCategoryTripleIso F₁ F₂' F₃').hom =
      (Functor.mapDerivedCategoryTripleIso F₁ F₂ F₃).hom ≫
        (Functor.whiskerLeft F₁ X).mapDerivedCategory := by
  simp only [Functor.mapDerivedCategoryTripleIso, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    derivedComp, Functor.whiskerLeft_comp, assoc]
  rw [← Functor.whiskerLeft_comp_assoc _ (Functor.mapDerivedCategoryCompIso F₂' F₃').inv,
    Iso.inv_hom_id, Functor.whiskerLeft_id', id_comp, ← mapDerivedCategory_whiskerLeft]

@[reassoc]
theorem whiskerRight_derivedComp_tripleIso (X : F₁ ⋙ F₂ ⟶ F₁' ⋙ F₂') :
    Functor.whiskerRight (derivedComp X) F₃.mapDerivedCategory ≫
        (Functor.mapDerivedCategoryTripleIso F₁' F₂' F₃).hom =
      (Functor.mapDerivedCategoryTripleIso F₁ F₂ F₃).hom ≫
        (Functor.whiskerRight X F₃).mapDerivedCategory := by
  simp only [Functor.mapDerivedCategoryTripleIso_hom_eq, derivedComp, Functor.whiskerRight_comp,
    assoc]
  rw [← Functor.whiskerRight_comp_assoc (Functor.mapDerivedCategoryCompIso F₁' F₂').inv,
    Iso.inv_hom_id, Functor.whiskerRight_id', id_comp, ← mapDerivedCategory_whiskerRight]

/-- **The braid relation passes to derived categories.** -/
theorem derivedComp_braid {X₂₃ : F₂ ⋙ F₃ ⟶ F₂ ⋙ F₃} {X₁₂ : F₁ ⋙ F₂ ⟶ F₁ ⋙ F₂}
    (h : Functor.whiskerLeft F₁ X₂₃ ≫ Functor.whiskerRight X₁₂ F₃ ≫
        Functor.whiskerLeft F₁ X₂₃ =
      Functor.whiskerRight X₁₂ F₃ ≫ Functor.whiskerLeft F₁ X₂₃ ≫
        Functor.whiskerRight X₁₂ F₃) :
    Functor.whiskerLeft F₁.mapDerivedCategory (derivedComp X₂₃) ≫
        Functor.whiskerRight (derivedComp X₁₂) F₃.mapDerivedCategory ≫
          Functor.whiskerLeft F₁.mapDerivedCategory (derivedComp X₂₃) =
      Functor.whiskerRight (derivedComp X₁₂) F₃.mapDerivedCategory ≫
        Functor.whiskerLeft F₁.mapDerivedCategory (derivedComp X₂₃) ≫
          Functor.whiskerRight (derivedComp X₁₂) F₃.mapDerivedCategory := by
  rw [← cancel_mono (Functor.mapDerivedCategoryTripleIso F₁ F₂ F₃).hom]
  simp only [assoc, whiskerRight_derivedComp_tripleIso, whiskerLeft_derivedComp_tripleIso,
    whiskerRight_derivedComp_tripleIso_assoc, whiskerLeft_derivedComp_tripleIso_assoc]
  simp only [← mapDerivedCategory_comp]
  rw [h]

end NatTrans

end CategoryTheory
