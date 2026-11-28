/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.MapDerivedNatTrans
import Categorification.Algebra.DegreewiseTensor

/-!
# Commuting squares of exact functors on derived categories

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21. The compatibility of `𝕂 ∘ 𝔈_i ≅ 𝔈_i ∘ 𝕂` with the 2-morphisms of `𝒰` is proved
on modules as an identity `(K ∘ α) ≫ φ' = φ ≫ (β ∘ K)` of natural transformations between
composites of exact functors. This file passes such identities to Mathlib's derived categories:
for a natural isomorphism `φ : X ⋙ K ≅ K' ⋙ Y` of exact functors, `CupCap.derivedSquareIso φ`
is the induced isomorphism `X^D ⋙ K^D ≅ K'^D ⋙ Y^D` of derived functors, and
`CupCap.derivedSquareIso_whisker` lifts the identity.

## Main definitions and results

* `CupCap.mapDerivedCategoryIsoOfIso_hom_eq`: `mapDerivedCategoryIsoOfIso e` has underlying
  natural transformation `e.hom.mapDerivedCategory`.
* `CupCap.derivedSquareIso`, `CupCap.derivedSquareIso_whisker`.
-/

open CategoryTheory Limits

noncomputable section

namespace Categorification.Stendhal.CupCap

universe w₁ w₂ w₃ w₄

section Iso

variable {C₁ C₂ : Type*} [Category* C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  [Category* C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  {F G : C₁ ⥤ C₂} [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- The isomorphism of derived functors induced by an isomorphism of exact functors is the
derived natural transformation of its underlying natural transformation. -/
theorem mapDerivedCategoryIsoOfIso_hom_eq (e : F ≅ G) :
    (mapDerivedCategoryIsoOfIso e).hom = e.hom.mapDerivedCategory :=
  NatTrans.derivedCategory_ext fun X => by
    rw [NatTrans.mapDerivedCategory_app_Q_obj]
    exact congrArg (fun t => NatTrans.app t X)
      ((Localization.whiskeringLeftFunctor' DerivedCategory.Q
        (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ)) (DerivedCategory C₂)).map_preimage
        (F.mapDerivedCategoryFactors.hom ≫
          Functor.whiskerRight (NatIso.mapHomologicalComplex e _).hom _ ≫
          G.mapDerivedCategoryFactors.inv))

end Iso

section Square

variable {C₁ C₂ C₃ C₄ : Type*} [Category* C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  [Category* C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  [Category* C₃] [Abelian C₃] [HasDerivedCategory.{w₃} C₃]
  [Category* C₄] [Abelian C₄] [HasDerivedCategory.{w₄} C₄]
  {X X' : C₁ ⥤ C₂} [X.Additive] [PreservesFiniteLimits X] [PreservesFiniteColimits X]
  [X'.Additive] [PreservesFiniteLimits X'] [PreservesFiniteColimits X']
  {K : C₂ ⥤ C₃} [K.Additive] [PreservesFiniteLimits K] [PreservesFiniteColimits K]
  {K' : C₁ ⥤ C₄} [K'.Additive] [PreservesFiniteLimits K'] [PreservesFiniteColimits K']
  {Y Y' : C₄ ⥤ C₃} [Y.Additive] [PreservesFiniteLimits Y] [PreservesFiniteColimits Y]
  [Y'.Additive] [PreservesFiniteLimits Y'] [PreservesFiniteColimits Y']

/-- The isomorphism `X^D ⋙ K^D ≅ K'^D ⋙ Y^D` of derived functors induced by an isomorphism
`X ⋙ K ≅ K' ⋙ Y` of exact functors. -/
def derivedSquareIso (e : X ⋙ K ≅ K' ⋙ Y) :
    X.mapDerivedCategory ⋙ K.mapDerivedCategory ≅
      K'.mapDerivedCategory ⋙ Y.mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫ mapDerivedCategoryIsoOfIso e ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

/-- **Compatibility with 2-morphisms passes to derived categories**: if
`(K ∘ α) ≫ e' = e ≫ (β ∘ K')` for natural isomorphisms `e : X ⋙ K ≅ K' ⋙ Y` and
`e' : X' ⋙ K ≅ K' ⋙ Y'` of exact functors, then the same identity holds for the derived
natural transformations and the induced isomorphisms `CupCap.derivedSquareIso`. -/
theorem derivedSquareIso_whisker (e : X ⋙ K ≅ K' ⋙ Y) (e' : X' ⋙ K ≅ K' ⋙ Y') {α : X ⟶ X'}
    {β : Y ⟶ Y'} (h : Functor.whiskerRight α K ≫ e'.hom = e.hom ≫ Functor.whiskerLeft K' β) :
    Functor.whiskerRight α.mapDerivedCategory K.mapDerivedCategory ≫ (derivedSquareIso e').hom =
      (derivedSquareIso e).hom ≫
        Functor.whiskerLeft K'.mapDerivedCategory β.mapDerivedCategory := by
  simp only [derivedSquareIso, Iso.trans_hom, Iso.symm_hom, mapDerivedCategoryIsoOfIso_hom_eq,
    NatTrans.whiskerRight_mapDerivedCategory, NatTrans.whiskerLeft_mapDerivedCategory,
    Category.assoc, Iso.inv_hom_id_assoc]
  rw [← NatTrans.mapDerivedCategory_comp_assoc, h, NatTrans.mapDerivedCategory_comp_assoc]

end Square

end Categorification.Stendhal.CupCap
