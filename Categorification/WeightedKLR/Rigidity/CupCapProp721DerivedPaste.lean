/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721DerivedSquare

/-!
# Pasting commuting squares of exact functors on derived categories

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21. The isomorphism `𝕂 ∘ 𝔈_i² ≅ 𝔈_i² ∘ 𝕂` is the pasting of two copies of
`𝕂 ∘ 𝔈_i ≅ 𝔈_i ∘ 𝕂`. This file records how `CupCap.derivedSquareIso` behaves under pasting
(`CupCap.derivedSquareIso_squarePaste`) and under a change of the right-hand functor
(`CupCap.derivedSquareIso_trans_whiskerLeft`), so that a 2-morphism identity for a pasted module
square becomes one for the pasting of the derived squares.

## Main definitions and results

* `CupCap.squarePaste`: the vertical pasting of two commuting squares of functors.
* `CupCap.derivedSquareIso_trans_whiskerLeft`.
* `CupCap.derivedSquareIso_squarePaste`.
-/

open CategoryTheory Limits

noncomputable section

namespace Categorification.Stendhal.CupCap

universe w₁ w₂ w₃ w₄ w₅ w₆

section Paste

variable {C₁ C₂ C₃ C₄ C₅ C₆ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
  [Category* C₄] [Category* C₅] [Category* C₆]

/-- **Pasting of two commuting squares**: from `X₁ ⋙ K ≅ K₁ ⋙ Y₁` and `X₂ ⋙ K₁ ≅ K₂ ⋙ Y₂`,
the square `(X₂ ⋙ X₁) ⋙ K ≅ K₂ ⋙ (Y₂ ⋙ Y₁)`. -/
def squarePaste {X₁ : C₂ ⥤ C₃} {X₂ : C₁ ⥤ C₂} {K : C₃ ⥤ C₄} {K₁ : C₂ ⥤ C₅} {K₂ : C₁ ⥤ C₆}
    {Y₁ : C₅ ⥤ C₄} {Y₂ : C₆ ⥤ C₅} (e₁ : X₁ ⋙ K ≅ K₁ ⋙ Y₁) (e₂ : X₂ ⋙ K₁ ≅ K₂ ⋙ Y₂) :
    (X₂ ⋙ X₁) ⋙ K ≅ K₂ ⋙ (Y₂ ⋙ Y₁) :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft X₂ e₁ ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight e₂ Y₁ ≪≫ Functor.associator _ _ _

theorem squarePaste_hom_app {X₁ : C₂ ⥤ C₃} {X₂ : C₁ ⥤ C₂} {K : C₃ ⥤ C₄} {K₁ : C₂ ⥤ C₅}
    {K₂ : C₁ ⥤ C₆} {Y₁ : C₅ ⥤ C₄} {Y₂ : C₆ ⥤ C₅} (e₁ : X₁ ⋙ K ≅ K₁ ⋙ Y₁)
    (e₂ : X₂ ⋙ K₁ ≅ K₂ ⋙ Y₂) (x : C₁) :
    (squarePaste e₁ e₂).hom.app x = e₁.hom.app (X₂.obj x) ≫ Y₁.map (e₂.hom.app x) := by
  simp [squarePaste]

end Paste

section Derived

variable {C₁ C₂ C₃ C₄ C₅ C₆ : Type*} [Category* C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  [Category* C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  [Category* C₃] [Abelian C₃] [HasDerivedCategory.{w₃} C₃]
  [Category* C₄] [Abelian C₄] [HasDerivedCategory.{w₄} C₄]
  [Category* C₅] [Abelian C₅] [HasDerivedCategory.{w₅} C₅]
  [Category* C₆] [Abelian C₆] [HasDerivedCategory.{w₆} C₆]

section Whisker

variable {X : C₁ ⥤ C₂} [X.Additive] [PreservesFiniteLimits X] [PreservesFiniteColimits X]
  {K : C₂ ⥤ C₃} [K.Additive] [PreservesFiniteLimits K] [PreservesFiniteColimits K]
  {K' : C₁ ⥤ C₄} [K'.Additive] [PreservesFiniteLimits K'] [PreservesFiniteColimits K']
  {Y Y' : C₄ ⥤ C₃} [Y.Additive] [PreservesFiniteLimits Y] [PreservesFiniteColimits Y]
  [Y'.Additive] [PreservesFiniteLimits Y'] [PreservesFiniteColimits Y']

/-- **Changing the right-hand functor of a square along an isomorphism**:
`derivedSquareIso (e ≪≫ K' γ) = derivedSquareIso e ≪≫ K'^D γ^D`. -/
theorem derivedSquareIso_trans_whiskerLeft (e : X ⋙ K ≅ K' ⋙ Y) (γ : Y ≅ Y') :
    (derivedSquareIso (e ≪≫ Functor.isoWhiskerLeft K' γ)).hom =
      (derivedSquareIso e).hom ≫
        Functor.whiskerLeft K'.mapDerivedCategory γ.hom.mapDerivedCategory := by
  simp only [derivedSquareIso, Iso.trans_hom, Iso.symm_hom, mapDerivedCategoryIsoOfIso_hom_eq,
    Functor.isoWhiskerLeft_hom, NatTrans.mapDerivedCategory_comp,
    NatTrans.whiskerLeft_mapDerivedCategory, Category.assoc, Iso.inv_hom_id_assoc]

end Whisker

section PasteDerived

variable {X₁ : C₂ ⥤ C₃} [X₁.Additive] [PreservesFiniteLimits X₁] [PreservesFiniteColimits X₁]
  {X₂ : C₁ ⥤ C₂} [X₂.Additive] [PreservesFiniteLimits X₂] [PreservesFiniteColimits X₂]
  {K : C₃ ⥤ C₄} [K.Additive] [PreservesFiniteLimits K] [PreservesFiniteColimits K]
  {K₁ : C₂ ⥤ C₅} [K₁.Additive] [PreservesFiniteLimits K₁] [PreservesFiniteColimits K₁]
  {K₂ : C₁ ⥤ C₆} [K₂.Additive] [PreservesFiniteLimits K₂] [PreservesFiniteColimits K₂]
  {Y₁ : C₅ ⥤ C₄} [Y₁.Additive] [PreservesFiniteLimits Y₁] [PreservesFiniteColimits Y₁]
  {Y₂ : C₆ ⥤ C₅} [Y₂.Additive] [PreservesFiniteLimits Y₂] [PreservesFiniteColimits Y₂]

/-- **`derivedSquareIso` of a pasting is the pasting of the `derivedSquareIso`s**, through
`Functor.mapDerivedCategoryCompIso` on both composites. -/
theorem derivedSquareIso_squarePaste (e₁ : X₁ ⋙ K ≅ K₁ ⋙ Y₁) (e₂ : X₂ ⋙ K₁ ≅ K₂ ⋙ Y₂) :
    Functor.whiskerRight (Functor.mapDerivedCategoryCompIso X₂ X₁).hom K.mapDerivedCategory ≫
        (derivedSquareIso (squarePaste e₁ e₂)).hom =
      (squarePaste (derivedSquareIso e₁) (derivedSquareIso e₂)).hom ≫
        Functor.whiskerLeft K₂.mapDerivedCategory
          (Functor.mapDerivedCategoryCompIso Y₂ Y₁).hom := by
  have hX := Functor.mapDerivedCategoryCompIso_assoc X₂ X₁ K
  have hM := Functor.mapDerivedCategoryCompIso_assoc X₂ K₁ Y₁
  have hY := Functor.mapDerivedCategoryCompIso_assoc K₂ Y₂ Y₁
  have hL := NatTrans.mapDerivedCategory_whiskerLeft (F := X₂) e₁.hom
  have hR := NatTrans.mapDerivedCategory_whiskerRight (G := Y₁) e₂.hom
  have hA : (squarePaste e₁ e₂).hom =
      Functor.whiskerLeft X₂ e₁.hom ≫ Functor.whiskerRight e₂.hom Y₁ := by
    ext x
    simp [squarePaste]
  ext x
  have hX' := congrArg (fun t => NatTrans.app t x) hX
  have hM' := congrArg (fun t => NatTrans.app t x) hM
  have hY' := congrArg (fun t => NatTrans.app t x) hY
  have hL' := congrArg (fun t => NatTrans.app t x) hL
  have hR' := congrArg (fun t => NatTrans.app t x) hR
  simp only [NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app] at hX' hM' hY' hL' hR'
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    squarePaste_hom_app, derivedSquareIso, Iso.trans_hom, Iso.symm_hom,
    mapDerivedCategoryIsoOfIso_hom_eq, hA, NatTrans.mapDerivedCategory_comp, Functor.map_comp,
    Category.assoc]
  have hM'' : (Functor.mapDerivedCategoryCompIso X₂ (K₁ ⋙ Y₁)).hom.app x =
      (Functor.mapDerivedCategoryCompIso K₁ Y₁).inv.app (X₂.mapDerivedCategory.obj x) ≫
        Y₁.mapDerivedCategory.map ((Functor.mapDerivedCategoryCompIso X₂ K₁).hom.app x) ≫
          (Functor.mapDerivedCategoryCompIso (X₂ ⋙ K₁) Y₁).hom.app x := by
    rw [hM', Iso.inv_hom_id_app_assoc]
  have hY'' : (Functor.mapDerivedCategoryCompIso (K₂ ⋙ Y₂) Y₁).hom.app x =
      Y₁.mapDerivedCategory.map ((Functor.mapDerivedCategoryCompIso K₂ Y₂).inv.app x) ≫
        (Functor.mapDerivedCategoryCompIso Y₂ Y₁).hom.app (K₂.mapDerivedCategory.obj x) ≫
          (Functor.mapDerivedCategoryCompIso K₂ (Y₂ ⋙ Y₁)).hom.app x := by
    rw [← hY', ← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
      Category.id_comp]
  rw [reassoc_of% hX', reassoc_of% hL', hM'', Category.assoc, Category.assoc, reassoc_of% hR', hY'']
  simp only [Category.assoc, Iso.hom_inv_id_app]
  exact congrArg _ (congrArg _ (congrArg _ (congrArg _ (congrArg _ (congrArg _
    (Category.comp_id _))))))

end PasteDerived

end Derived

end Categorification.Stendhal.CupCap
