/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Categorification.TwoRep.RightwardCrossing
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Additive functors as 1-morphisms

Only additive functors are retained between the original preadditive categories;
2-morphisms are the usual natural transformations. This restriction is necessary:
right whiskering by an arbitrary, nonadditive functor need not preserve addition.
The ordinary/bicategorical adjunction bridges keep both maps unchanged. The mate
and braid transport lemmas retain the explicit associators of the ordinary functors.
-/

open CategoryTheory
namespace Categorification.TwoRep
universe v u

/-- Preadditive categories, with additive functors as their 1-morphisms. -/
structure AdditiveCat where
  carrier : Type u
  [category : Category.{v} carrier]
  [preadditive : Preadditive carrier]

namespace AdditiveCat
attribute [instance] category preadditive
instance : CoeSort AdditiveCat.{v,u} (Type u) := ⟨carrier⟩

def of (C : Type u) [Category.{v} C] [Preadditive C] : AdditiveCat.{v,u} := ⟨C⟩

instance : CategoryStruct AdditiveCat.{v,u} where
  Hom C D := C ⥤+ D
  id C := AdditiveFunctor.of (𝟭 C)
  comp F G := AdditiveFunctor.of (F.obj ⋙ G.obj)

instance homCategory (C D : AdditiveCat.{v,u}) : Category (C ⟶ D) :=
  inferInstanceAs (Category (C ⥤+ D))

instance (C D : AdditiveCat.{v,u}) : Preadditive (C ⟶ D) :=
  inferInstanceAs (Preadditive (C ⥤+ D))

instance : Bicategory AdditiveCat.{v,u} where
  homCategory := homCategory
  whiskerLeft F _ _ η := ObjectProperty.homMk (Functor.whiskerLeft F.obj η.hom)
  whiskerRight η H := ObjectProperty.homMk (Functor.whiskerRight η.hom H.obj)
  associator F G H := ObjectProperty.isoMk _ (Functor.associator F.obj G.obj H.obj)
  leftUnitor F := ObjectProperty.isoMk _ (Functor.leftUnitor F.obj)
  rightUnitor F := ObjectProperty.isoMk _ (Functor.rightUnitor F.obj)
  id_whiskerLeft {_ _} {f g} η := by
    apply ObjectProperty.hom_ext
    ext X
    change η.hom.app X = 𝟙 _ ≫ η.hom.app X ≫ 𝟙 _
    simp
  comp_whiskerLeft := by
    intro a b c d f g h h' η
    apply ObjectProperty.hom_ext
    ext X
    change η.hom.app (g.obj.obj (f.obj.obj X)) =
      𝟙 _ ≫ η.hom.app (g.obj.obj (f.obj.obj X)) ≫ 𝟙 _
    simp
  id_whiskerRight f g := by
    apply ObjectProperty.hom_ext
    ext X
    exact g.obj.map_id _
  comp_whiskerRight η θ i := by
    apply ObjectProperty.hom_ext
    ext X
    exact i.obj.map_comp _ _
  whiskerRight_id {_ _} {f g} η := by
    apply ObjectProperty.hom_ext
    ext X
    change η.hom.app X = 𝟙 _ ≫ η.hom.app X ≫ 𝟙 _
    simp
  whiskerRight_comp η g h := by
    apply ObjectProperty.hom_ext
    ext X
    change h.obj.map (g.obj.map (η.hom.app X)) =
      𝟙 _ ≫ h.obj.map (g.obj.map (η.hom.app X)) ≫ 𝟙 _
    simp
  whisker_assoc f _ _ η h := by
    apply ObjectProperty.hom_ext
    ext X
    change h.obj.map (η.hom.app (f.obj.obj X)) =
      𝟙 _ ≫ h.obj.map (η.hom.app (f.obj.obj X)) ≫ 𝟙 _
    simp
  whisker_exchange η θ := by
    apply ObjectProperty.hom_ext
    ext X
    exact (θ.hom.naturality (η.hom.app X)).symm
  pentagon f g h i := by
    apply ObjectProperty.hom_ext
    ext X
    change i.obj.map (𝟙 _) ≫ 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _
    simp
  triangle f g := by
    apply ObjectProperty.hom_ext
    ext X
    change 𝟙 _ ≫ 𝟙 _ = g.obj.map (𝟙 _)
    simp

instance : AdditiveWhiskering AdditiveCat.{v,u} where
  whiskerLeft_add _ _ _ _ _ := rfl
  add_whiskerRight η θ H := by
    apply ObjectProperty.hom_ext
    ext X
    exact H.obj.map_add

@[simp] theorem id_obj (C : AdditiveCat.{v,u}) : (𝟙 C : C ⟶ C).obj = 𝟭 C := rfl
@[simp] theorem comp_obj {C D E : AdditiveCat.{v,u}} (F : C ⟶ D) (G : D ⟶ E) :
    (F ≫ G).obj = F.obj ⋙ G.obj := rfl

/-- Ordinary adjunctions between additive functors give bicategorical adjunctions. -/
def ofAdjunction {C D : AdditiveCat.{v,u}} {F : C ⟶ D} {G : D ⟶ C}
    (adj : CategoryTheory.Adjunction F.obj G.obj) : Bicategory.Adjunction F G where
  unit := ObjectProperty.homMk adj.unit
  counit := ObjectProperty.homMk adj.counit
  left_triangle := by
    rw [leftZigzag_eq]
    apply ObjectProperty.hom_ext
    ext X
    change F.obj.map (adj.unit.app X) ≫ 𝟙 (F.obj.obj (G.obj.obj (F.obj.obj X))) ≫ adj.counit.app (F.obj.obj X) = 𝟙 (F.obj.obj X) ≫ 𝟙 (F.obj.obj X)
    simpa only [comp_obj, id_obj, CategoryTheory.Functor.comp_obj, CategoryTheory.Functor.id_obj, Category.id_comp, Category.comp_id] using adj.left_triangle_components X
  right_triangle := by
    rw [rightZigzag_eq]
    apply ObjectProperty.hom_ext
    ext X
    change adj.unit.app (G.obj.obj X) ≫ 𝟙 (G.obj.obj (F.obj.obj (G.obj.obj X))) ≫ G.obj.map (adj.counit.app X) = 𝟙 (G.obj.obj X) ≫ 𝟙 (G.obj.obj X)
    simpa only [comp_obj, id_obj, CategoryTheory.Functor.comp_obj, CategoryTheory.Functor.id_obj, Category.id_comp, Category.comp_id] using adj.right_triangle_components X

/-- Recover the ordinary adjunction, keeping its unit and counit unchanged. -/
def toAdjunction {C D : AdditiveCat.{v,u}} {F : C ⟶ D} {G : D ⟶ C}
    (adj : Bicategory.Adjunction F G) : CategoryTheory.Adjunction F.obj G.obj where
  unit := adj.unit.hom
  counit := adj.counit.hom
  left_triangle_components X := by
    have h := adj.left_triangle
    rw [leftZigzag_eq] at h
    have h' := congrArg (fun t => t.hom.app X) h
    change F.obj.map (adj.unit.hom.app X) ≫ 𝟙 (F.obj.obj (G.obj.obj (F.obj.obj X))) ≫ adj.counit.hom.app (F.obj.obj X) = 𝟙 (F.obj.obj X) ≫ 𝟙 (F.obj.obj X) at h'
    simpa only [comp_obj, id_obj, CategoryTheory.Functor.comp_obj, CategoryTheory.Functor.id_obj, Category.id_comp, Category.comp_id] using h'
  right_triangle_components X := by
    have h := adj.right_triangle
    rw [rightZigzag_eq] at h
    have h' := congrArg (fun t => t.hom.app X) h
    change adj.unit.hom.app (G.obj.obj X) ≫ 𝟙 (G.obj.obj (F.obj.obj (G.obj.obj X))) ≫ G.obj.map (adj.counit.hom.app X) = 𝟙 (G.obj.obj X) ≫ 𝟙 (G.obj.obj X) at h'
    simpa only [comp_obj, id_obj, CategoryTheory.Functor.comp_obj, CategoryTheory.Functor.id_obj, Category.id_comp, Category.comp_id] using h'

open CategoryTheory.Bicategory in
/-- The rightward mate is the usual natural-transformation mate, not a new crossing. -/
theorem sigma_hom {A B C : AdditiveCat.{v,u}} {E₁ : A ⟶ B} {R₁ : B ⟶ A}
    {E₂ : B ⟶ C} {R₂ : C ⟶ B} (η : 𝟙 B ⟶ E₂ ≫ R₂)
    (τ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) (ε : R₁ ≫ E₁ ⟶ 𝟙 B) :
    (RightwardCrossing.sigma η τ ε).hom =
      Functor.whiskerLeft (R₁.obj ⋙ E₁.obj) η.hom ≫
      Functor.whiskerRight (Functor.whiskerLeft R₁.obj τ.hom) R₂.obj ≫
      Functor.whiskerRight ε.hom (E₂.obj ⋙ R₂.obj) := by
  rw [RightwardCrossing.sigma_eq]
  ext X
  change 𝟙 _ ≫ η.hom.app (E₁.obj.obj (R₁.obj.obj X)) ≫ 𝟙 _ ≫ 𝟙 _ ≫
      R₂.obj.map (τ.hom.app (R₁.obj.obj X)) ≫ 𝟙 _ ≫ 𝟙 _ ≫
      R₂.obj.map (E₂.obj.map (ε.hom.app X)) ≫ 𝟙 _ =
    η.hom.app (E₁.obj.obj (R₁.obj.obj X)) ≫ R₂.obj.map (τ.hom.app (R₁.obj.obj X)) ≫
      R₂.obj.map (E₂.obj.map (ε.hom.app X))
  simp only [Category.id_comp, Category.comp_id]

open CategoryTheory.Bicategory in
/-- Transport the actual natural braid, with its associators, to additive 1-cells. -/
theorem braid_of {A B C D : AdditiveCat.{v,u}} (F : A ⟶ B) (G : B ⟶ C) (H : C ⟶ D)
    (τ : F ≫ G ⟶ F ≫ G) (υ : G ≫ H ⟶ G ≫ H)
    (h : let l := Functor.whiskerRight τ.hom H.obj
         let r := (Functor.associator F.obj G.obj H.obj).hom ≫
           Functor.whiskerLeft F.obj υ.hom ≫ (Functor.associator F.obj G.obj H.obj).inv
         l ≫ r ≫ l = r ≫ l ≫ r) :
    F ◁ υ ≫ ((α_ F G H).inv ≫ τ ▷ H ≫ (α_ F G H).hom) ≫ F ◁ υ =
      ((α_ F G H).inv ≫ τ ▷ H ≫ (α_ F G H).hom) ≫ F ◁ υ ≫
      ((α_ F G H).inv ≫ τ ▷ H ≫ (α_ F G H).hom) := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext X
  have hx := congrArg (fun t => t.app X) h
  change H.obj.map (τ.hom.app X) ≫ (𝟙 _ ≫ υ.hom.app (F.obj.obj X) ≫ 𝟙 _) ≫
      H.obj.map (τ.hom.app X) =
    (𝟙 _ ≫ υ.hom.app (F.obj.obj X) ≫ 𝟙 _) ≫ H.obj.map (τ.hom.app X) ≫
      (𝟙 _ ≫ υ.hom.app (F.obj.obj X) ≫ 𝟙 _) at hx
  change υ.hom.app (F.obj.obj X) ≫ (𝟙 _ ≫ H.obj.map (τ.hom.app X) ≫ 𝟙 _) ≫
      υ.hom.app (F.obj.obj X) =
    (𝟙 _ ≫ H.obj.map (τ.hom.app X) ≫ 𝟙 _) ≫ υ.hom.app (F.obj.obj X) ≫
      (𝟙 _ ≫ H.obj.map (τ.hom.app X) ≫ 𝟙 _)
  simpa only [comp_obj, Functor.comp_obj, Category.id_comp, Category.comp_id, Category.assoc] using hx.symm

end AdditiveCat
end Categorification.TwoRep
