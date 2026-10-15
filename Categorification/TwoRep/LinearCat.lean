/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Basic
import Categorification.TwoRep.RightwardCrossing
import Categorification.TwoRep.Zigzag

/-!
# `k`-linear categories with additive `k`-linear functors as 1-morphisms

The bicategory `LinearCat k` has objects the preadditive `k`-linear categories, 1-morphisms
the additive `k`-linear functors and 2-morphisms all natural transformations. Its categories of
1-morphisms are `k`-linear, and whiskering is `k`-linear on both sides (`precomp`, `postcomp`).
This is the target bicategory required by `TwoRep.RouqUpKLR` and `TwoRep.RouqSoundness` for a
Rouquier family with polynomial (KLR) relations; it is the analogue of `TwoRep.AdditiveCat`
with the `k`-linear structure retained, and is where the weight-indexed cyclotomic family of
KL III Thm. 1.2 lives.

Right whiskering by a functor that is not `k`-linear need not preserve scalar multiples, which
is why 1-morphisms are required to be `k`-linear.
-/

open CategoryTheory

namespace Categorification.TwoRep

universe w v u

variable (k : Type w) [CommRing k]

/-- Preadditive `k`-linear categories. -/
structure LinearCat where
  carrier : Type u
  [category : Category.{v} carrier]
  [preadditive : Preadditive carrier]
  [linear : Linear k carrier]

namespace LinearCat

attribute [instance] category preadditive linear

instance : CoeSort (LinearCat.{w, v, u} k) (Type u) := ⟨carrier⟩

/-- A preadditive `k`-linear category as an object of `LinearCat k`. -/
abbrev of (C : Type u) [Category.{v} C] [Preadditive C] [Linear k C] : LinearCat.{w, v, u} k := ⟨C⟩

section Functors

variable (C D : Type*) [Category C] [Category D] [Preadditive C] [Preadditive D] [Linear k C]
  [Linear k D]

/-- Additive `k`-linear functors. -/
def linearFunctor : ObjectProperty (C ⥤ D) := fun F => F.Additive ∧ F.Linear k

/-- The category of additive `k`-linear functors. -/
abbrev LinFun := (linearFunctor k C D).FullSubcategory

variable {k C D}

/-- An additive `k`-linear functor as an object of `LinFun k C D`. -/
def LinFun.of (F : C ⥤ D) [F.Additive] [F.Linear k] : LinFun k C D := ⟨F, ⟨inferInstance, inferInstance⟩⟩

instance (F : LinFun k C D) : F.obj.Additive := F.property.1

instance (F : LinFun k C D) : F.obj.Linear k := F.property.2

end Functors

instance : CategoryStruct (LinearCat.{w, v, u} k) where
  Hom C D := LinFun k C D
  id C := LinFun.of (𝟭 C)
  comp F G := LinFun.of (F.obj ⋙ G.obj)

instance homCategory (C D : LinearCat.{w, v, u} k) : Category (C ⟶ D) :=
  inferInstanceAs (Category (LinFun k C D))

instance (C D : LinearCat.{w, v, u} k) : Preadditive (C ⟶ D) :=
  inferInstanceAs (Preadditive (LinFun k C D))

instance (C D : LinearCat.{w, v, u} k) : Linear k (C ⟶ D) :=
  inferInstanceAs (Linear k (LinFun k C D))

instance : Bicategory (LinearCat.{w, v, u} k) where
  homCategory := homCategory k
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

open CategoryTheory.Bicategory

@[simp] theorem id_obj (C : LinearCat.{w, v, u} k) : (𝟙 C : C ⟶ C).obj = 𝟭 C := rfl

@[simp] theorem comp_obj {C D E : LinearCat.{w, v, u} k} (F : C ⟶ D) (G : D ⟶ E) :
    (F ≫ G).obj = F.obj ⋙ G.obj := rfl

@[simp] theorem whiskerLeft_hom {C D E : LinearCat.{w, v, u} k} (F : C ⟶ D) {G H : D ⟶ E}
    (η : G ⟶ H) : (F ◁ η).hom = Functor.whiskerLeft F.obj η.hom := rfl

@[simp] theorem whiskerRight_hom {C D E : LinearCat.{w, v, u} k} {F G : C ⟶ D} (η : F ⟶ G)
    (H : D ⟶ E) : (η ▷ H).hom = Functor.whiskerRight η.hom H.obj := rfl

@[simp] theorem smul_hom {C D : LinearCat.{w, v, u} k} {F G : C ⟶ D} (c : k) (η : F ⟶ G) :
    (c • η).hom = c • η.hom := rfl

instance : AdditiveWhiskering (LinearCat.{w, v, u} k) where
  whiskerLeft_add _ _ _ _ _ := rfl
  add_whiskerRight η θ H := by
    apply ObjectProperty.hom_ext
    ext X
    exact H.obj.map_add

instance precomp_linear (a b c : LinearCat.{w, v, u} k) (f : a ⟶ b) :
    (Bicategory.precomp c f).Linear k where
  map_smul _ _ := rfl

instance postcomp_linear (a b c : LinearCat.{w, v, u} k) (g : b ⟶ c) :
    (Bicategory.postcomp a g).Linear k where
  map_smul η r := by
    apply ObjectProperty.hom_ext
    ext X
    exact g.obj.map_smul r (η.hom.app X)

/-- Ordinary adjunctions between additive `k`-linear functors give bicategorical adjunctions. -/
def ofAdjunction {C D : LinearCat.{w, v, u} k} {F : C ⟶ D} {G : D ⟶ C}
    (adj : CategoryTheory.Adjunction F.obj G.obj) : Bicategory.Adjunction F G where
  unit := ObjectProperty.homMk adj.unit
  counit := ObjectProperty.homMk adj.counit
  left_triangle := by
    rw [leftZigzag_eq]
    apply ObjectProperty.hom_ext
    ext X
    change F.obj.map (adj.unit.app X) ≫ 𝟙 (F.obj.obj (G.obj.obj (F.obj.obj X))) ≫
      adj.counit.app (F.obj.obj X) = 𝟙 (F.obj.obj X) ≫ 𝟙 (F.obj.obj X)
    simpa only [comp_obj, id_obj, Functor.comp_obj, Functor.id_obj, Category.id_comp,
      Category.comp_id] using adj.left_triangle_components X
  right_triangle := by
    rw [rightZigzag_eq]
    apply ObjectProperty.hom_ext
    ext X
    change adj.unit.app (G.obj.obj X) ≫ 𝟙 (G.obj.obj (F.obj.obj (G.obj.obj X))) ≫
      G.obj.map (adj.counit.app X) = 𝟙 (G.obj.obj X) ≫ 𝟙 (G.obj.obj X)
    simpa only [comp_obj, id_obj, Functor.comp_obj, Functor.id_obj, Category.id_comp,
      Category.comp_id] using adj.right_triangle_components X

@[simp] theorem ofAdjunction_unit_hom {C D : LinearCat.{w, v, u} k} {F : C ⟶ D} {G : D ⟶ C}
    (adj : CategoryTheory.Adjunction F.obj G.obj) : (ofAdjunction k adj).unit.hom = adj.unit :=
  rfl

@[simp] theorem ofAdjunction_counit_hom {C D : LinearCat.{w, v, u} k} {F : C ⟶ D} {G : D ⟶ C}
    (adj : CategoryTheory.Adjunction F.obj G.obj) :
    (ofAdjunction k adj).counit.hom = adj.counit :=
  rfl

end LinearCat

end Categorification.TwoRep
