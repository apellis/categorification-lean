/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.Adjunction

/-!
# Natural transformations of exact functors on derived categories

For exact functors `F, G : C₁ ⥤ C₂` between abelian categories, a natural transformation
`τ : F ⟶ G` induces `τ.mapDerivedCategory : F.mapDerivedCategory ⟶ G.mapDerivedCategory`
(Mathlib). This file records that this construction respects the structure used to transfer
relations between 2-morphisms from module categories to derived categories:

* composition and identities (`NatTrans.mapDerivedCategory_comp`, `_id`);
* the additive structure (`_add`, `_zero`, `_neg`, `_sub`);
* whiskering, through `Functor.mapDerivedCategoryCompIso`
  (`NatTrans.mapDerivedCategory_whiskerRight`, `NatTrans.mapDerivedCategory_whiskerLeft`).

Each is checked on the objects `Q X`, using that natural transformations out of a localization
are determined there (`Localization.natTrans_ext`).
-/

noncomputable section

namespace CategoryTheory

open Category Limits

universe w₁ w₂ w₃

variable {C₁ : Type*} [Category* C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type*} [Category* C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  {C₃ : Type*} [Category* C₃] [Abelian C₃] [HasDerivedCategory.{w₃} C₃]

namespace NatTrans

/-- Natural transformations out of `D(C₁)` agree once they agree on the objects `Q X`. -/
theorem derivedCategory_ext {F₁ F₂ : DerivedCategory C₁ ⥤ DerivedCategory C₂}
    {α β : F₁ ⟶ F₂} (h : ∀ X : CochainComplex C₁ ℤ,
      α.app (DerivedCategory.Q.obj X) = β.app (DerivedCategory.Q.obj X)) : α = β :=
  Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ)) h

variable {F G H : C₁ ⥤ C₂} [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]

@[simp]
theorem mapDerivedCategory_id : (𝟙 F : F ⟶ F).mapDerivedCategory = 𝟙 _ :=
  derivedCategory_ext fun X => by simp [mapDerivedCategory_app_Q_obj]

@[simp, reassoc]
theorem mapDerivedCategory_comp (σ : F ⟶ G) (τ : G ⟶ H) :
    (σ ≫ τ).mapDerivedCategory = σ.mapDerivedCategory ≫ τ.mapDerivedCategory :=
  derivedCategory_ext fun X => by simp [mapDerivedCategory_app_Q_obj]

omit [HasDerivedCategory C₁] [HasDerivedCategory C₂] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] [PreservesFiniteLimits G] [PreservesFiniteColimits G] in
theorem mapHomologicalComplex_add_app (σ τ : F ⟶ G) (X : CochainComplex C₁ ℤ) :
    (mapHomologicalComplex (σ + τ) (ComplexShape.up ℤ)).app X =
      (mapHomologicalComplex σ (ComplexShape.up ℤ)).app X +
        (mapHomologicalComplex τ (ComplexShape.up ℤ)).app X := by
  ext n
  simp

@[simp]
theorem mapDerivedCategory_add (σ τ : F ⟶ G) :
    (σ + τ).mapDerivedCategory = σ.mapDerivedCategory + τ.mapDerivedCategory :=
  derivedCategory_ext fun X => by
    simp [mapDerivedCategory_app_Q_obj, mapHomologicalComplex_add_app, Functor.map_add]

@[simp]
theorem mapDerivedCategory_zero : (0 : F ⟶ G).mapDerivedCategory = 0 :=
  derivedCategory_ext fun X => by
    have h : (mapHomologicalComplex (0 : F ⟶ G) (ComplexShape.up ℤ)).app X = 0 := by
      ext n
      simp
    simp [mapDerivedCategory_app_Q_obj, h]

@[simp]
theorem mapDerivedCategory_neg (σ : F ⟶ G) :
    (-σ).mapDerivedCategory = -σ.mapDerivedCategory := by
  rw [eq_neg_iff_add_eq_zero, ← mapDerivedCategory_add, neg_add_cancel, mapDerivedCategory_zero]

@[simp]
theorem mapDerivedCategory_sub (σ τ : F ⟶ G) :
    (σ - τ).mapDerivedCategory = σ.mapDerivedCategory - τ.mapDerivedCategory := by
  rw [sub_eq_add_neg, mapDerivedCategory_add, mapDerivedCategory_neg, ← sub_eq_add_neg]

/-- Isomorphisms of exact functors give isomorphisms on derived categories. -/
@[simps]
def mapDerivedCategoryIso (e : F ≅ G) : F.mapDerivedCategory ≅ G.mapDerivedCategory where
  hom := e.hom.mapDerivedCategory
  inv := e.inv.mapDerivedCategory
  hom_inv_id := by rw [← mapDerivedCategory_comp, e.hom_inv_id, mapDerivedCategory_id]
  inv_hom_id := by rw [← mapDerivedCategory_comp, e.inv_hom_id, mapDerivedCategory_id]

end NatTrans

/-! ### Whiskering -/

namespace NatTrans

variable {F F' : C₁ ⥤ C₂} [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F'.Additive] [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
  {G G' : C₂ ⥤ C₃} [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [G'.Additive] [PreservesFiniteLimits G'] [PreservesFiniteColimits G']

/-- **Right whiskering commutes with passing to derived categories.** -/
theorem mapDerivedCategory_whiskerRight (σ : F ⟶ F') :
    (Functor.mapDerivedCategoryCompIso F G).hom ≫
        (Functor.whiskerRight σ G).mapDerivedCategory =
      Functor.whiskerRight σ.mapDerivedCategory G.mapDerivedCategory ≫
        (Functor.mapDerivedCategoryCompIso F' G).hom :=
  derivedCategory_ext fun X => by
    simp only [comp_app, Functor.whiskerRight_app, Functor.mapDerivedCategoryCompIso_hom_app_Q_obj,
      mapDerivedCategory_app_Q_obj, Functor.map_comp, assoc, Iso.inv_hom_id_app_assoc]
    rw [← Functor.map_comp_assoc G.mapDerivedCategory (F'.mapDerivedCategoryFactors.inv.app X),
      Iso.inv_hom_id_app, Functor.map_id, id_comp,
      Functor.mapDerivedCategoryFactors_hom_naturality_assoc]
    congr 2
    simp only [← Functor.map_comp_assoc]
    congr 2
    ext n
    simp

/-- **Left whiskering commutes with passing to derived categories.** -/
theorem mapDerivedCategory_whiskerLeft (τ : G ⟶ G') :
    (Functor.mapDerivedCategoryCompIso F G).hom ≫
        (Functor.whiskerLeft F τ).mapDerivedCategory =
      Functor.whiskerLeft F.mapDerivedCategory τ.mapDerivedCategory ≫
        (Functor.mapDerivedCategoryCompIso F G').hom :=
  derivedCategory_ext fun X => by
    simp only [comp_app, Functor.whiskerLeft_app, Functor.mapDerivedCategoryCompIso_hom_app_Q_obj,
      mapDerivedCategory_app_Q_obj, assoc, Iso.inv_hom_id_app_assoc]
    rw [← τ.mapDerivedCategory.naturality_assoc]
    erw [mapDerivedCategory_app_Q_obj]
    simp only [assoc, Iso.inv_hom_id_app_assoc]
    congr 2
    simp only [← Functor.map_comp_assoc]
    congr 2
    ext n
    simp

/-- Right whiskering on derived categories, through `mapDerivedCategoryCompIso`. -/
theorem whiskerRight_mapDerivedCategory (σ : F ⟶ F') :
    Functor.whiskerRight σ.mapDerivedCategory G.mapDerivedCategory =
      (Functor.mapDerivedCategoryCompIso F G).hom ≫
        (Functor.whiskerRight σ G).mapDerivedCategory ≫
          (Functor.mapDerivedCategoryCompIso F' G).inv := by
  rw [reassoc_of% (mapDerivedCategory_whiskerRight (G := G) σ), Iso.hom_inv_id, comp_id]

/-- Left whiskering on derived categories, through `mapDerivedCategoryCompIso`. -/
theorem whiskerLeft_mapDerivedCategory (τ : G ⟶ G') :
    Functor.whiskerLeft F.mapDerivedCategory τ.mapDerivedCategory =
      (Functor.mapDerivedCategoryCompIso F G).hom ≫
        (Functor.whiskerLeft F τ).mapDerivedCategory ≫
          (Functor.mapDerivedCategoryCompIso F G').inv := by
  rw [reassoc_of% (mapDerivedCategory_whiskerLeft (F := F) τ), Iso.hom_inv_id, comp_id]

end NatTrans

namespace Functor

variable {C₄ : Type*} [Category* C₄] [Abelian C₄] [HasDerivedCategory C₄]
  (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (G : C₂ ⥤ C₃) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (H : C₃ ⥤ C₄) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]

/-- **Associativity of `mapDerivedCategoryCompIso`.** -/
theorem mapDerivedCategoryCompIso_assoc :
    whiskerRight (mapDerivedCategoryCompIso F G).hom H.mapDerivedCategory ≫
        (mapDerivedCategoryCompIso (F ⋙ G) H).hom =
      whiskerLeft F.mapDerivedCategory (mapDerivedCategoryCompIso G H).hom ≫
        (mapDerivedCategoryCompIso F (G ⋙ H)).hom :=
  NatTrans.derivedCategory_ext fun X => by
    have e1 : (mapDerivedCategoryCompIso G H).hom.app (F.mapDerivedCategory.obj
        (DerivedCategory.Q.obj X)) =
        (G.mapDerivedCategory ⋙ H.mapDerivedCategory).map (F.mapDerivedCategoryFactors.hom.app X) ≫
          (mapDerivedCategoryCompIso G H).hom.app
            (DerivedCategory.Q.obj ((F.mapHomologicalComplex _).obj X)) ≫
          (G ⋙ H).mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app X) := by
      erw [NatTrans.naturality_assoc]
      rw [← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id, Category.comp_id]
      rfl
    rw [NatTrans.comp_app, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, e1]
    simp only [mapDerivedCategoryCompIso_hom_app_Q_obj, Functor.comp_map, Functor.map_comp,
      Category.assoc]
    rw [← H.mapDerivedCategory.map_comp_assoc ((F ⋙ G).mapDerivedCategoryFactors.inv.app X),
      Iso.inv_hom_id_app, Functor.map_id, Category.id_comp,
      ← (G ⋙ H).mapDerivedCategory.map_comp_assoc (F.mapDerivedCategoryFactors.inv.app X),
      Iso.inv_hom_id_app, Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc,
      Functor.mapDerivedCategoryFactors_hom_naturality_assoc]
    congr 3
    rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
    congr 2
    ext n
    simp

end Functor

namespace NatTrans

end NatTrans

/-! ### Adjunctions -/

namespace Adjunction

variable {F : C₁ ⥤ C₂} {G : C₂ ⥤ C₁} [F.Additive] [G.Additive]

/-- An adjunction of additive functors induces one on cochain complexes, degreewise. -/
@[simps!]
def mapCochainComplex (adj : F ⊣ G) :
    F.mapHomologicalComplex (ComplexShape.up ℤ) ⊣ G.mapHomologicalComplex (ComplexShape.up ℤ) :=
  Adjunction.mkOfUnitCounit
    { unit :=
        { app K :=
            { f n := adj.unit.app (K.X n)
              comm' i j _ := (adj.unit.naturality (K.d i j)).symm }
          naturality K L f := by
            ext n
            exact adj.unit.naturality (f.f n) }
      counit :=
        { app K :=
            { f n := adj.counit.app (K.X n)
              comm' i j _ := (adj.counit.naturality (K.d i j)).symm }
          naturality K L f := by
            ext n
            exact adj.counit.naturality (f.f n) }
      left_triangle := by
        ext K n
        simp
      right_triangle := by
        ext K n
        simp }

variable [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- The square `Q ⋙ F.mapDerivedCategory ≅ F.mapHomologicalComplex ⋙ Q`. -/
instance catCommSqMapDerivedCategory (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] :
    CatCommSq (F.mapHomologicalComplex (ComplexShape.up ℤ)) DerivedCategory.Q DerivedCategory.Q
      F.mapDerivedCategory :=
  ⟨F.mapDerivedCategoryFactors.symm⟩

/-- **An adjunction of exact functors induces an adjunction on derived categories.** -/
def mapDerivedCategory (adj : F ⊣ G) : F.mapDerivedCategory ⊣ G.mapDerivedCategory :=
  adj.mapCochainComplex.localization DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ)) DerivedCategory.Q
    (HomologicalComplex.quasiIso C₂ (ComplexShape.up ℤ)) F.mapDerivedCategory G.mapDerivedCategory

theorem mapDerivedCategory_unit_app (adj : F ⊣ G) (X : CochainComplex C₁ ℤ) :
    adj.mapDerivedCategory.unit.app (DerivedCategory.Q.obj X) =
      DerivedCategory.Q.map (adj.mapCochainComplex.unit.app X) ≫
        G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex _).obj X) ≫
          G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app X) :=
  Adjunction.localization_unit_app _ _ _ _ _ _ _ _

theorem mapDerivedCategory_counit_app (adj : F ⊣ G) (X : CochainComplex C₂ ℤ) :
    adj.mapDerivedCategory.counit.app (DerivedCategory.Q.obj X) =
      F.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app X) ≫
        F.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex _).obj X) ≫
          DerivedCategory.Q.map (adj.mapCochainComplex.counit.app X) :=
  Adjunction.localization_counit_app _ _ _ _ _ _ _ _

end Adjunction

end CategoryTheory
