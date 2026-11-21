/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.LinearCat

/-!
# Restricting a module category to full subcategories

Given a pseudofunctor `ℵ : B ⥤ LinearCat k` and, for every object `a`, a property `P a` of the
objects of `ℵ(a)` preserved by every functor `ℵ(f)`, the full subcategories `P a` form again a
pseudofunctor `ℵ.fullSub P hP : B ⥤ LinearCat k`, with the functors, 2-morphisms and constraints
of `ℵ` restricted.

This is how the category of finitely generated projective `Ř^λ`-modules is a module category
over the Cautis–Lauda 2-category (B. Webster, *Knot invariants and higher representation
theory*, arXiv:1309.3796v2, Cor. 3.27).
-/

noncomputable section

open CategoryTheory CategoryTheory.Bicategory

namespace Categorification.TwoRep.LinearCat

universe w v u w₁ v₁ u₁

variable {k : Type w} [CommRing k] {B : Type u₁} [Bicategory.{w₁, v₁} B]
  (ℵ : Pseudofunctor B (LinearCat.{w, v, u} k))
  (P : ∀ a, ObjectProperty (ℵ.obj a))
  (hP : ∀ {a b : B} (f : a ⟶ b) (X : ℵ.obj a), P a X → P b ((ℵ.map f).obj.obj X))

/-- The full subcategory `P a` of `ℵ(a)` as an object of `LinearCat k`. -/
abbrev fullSubObj (a : B) : LinearCat.{w, v, u} k := LinearCat.of k (P a).FullSubcategory

/-- The functor `ℵ(f)` restricted to the full subcategories. -/
abbrev fullSubFunctor {a b : B} (f : a ⟶ b) :
    (P a).FullSubcategory ⥤ (P b).FullSubcategory :=
  (P b).lift ((P a).ι ⋙ (ℵ.map f).obj) fun X => hP f X.obj X.property

instance {a b : B} (f : a ⟶ b) : (fullSubFunctor ℵ P hP f).Additive where
  map_add := by
    intro X Y φ ψ
    apply ObjectProperty.hom_ext
    exact (ℵ.map f).obj.map_add

instance {a b : B} (f : a ⟶ b) : (fullSubFunctor ℵ P hP f).Linear k where
  map_smul φ r := by
    apply ObjectProperty.hom_ext
    exact (ℵ.map f).obj.map_smul r φ.hom

/-- The natural transformation `ℵ(η)` restricted to the full subcategories. -/
@[simps]
def fullSubNatTrans {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
    fullSubFunctor ℵ P hP f ⟶ fullSubFunctor ℵ P hP g where
  app X := ObjectProperty.homMk ((ℵ.map₂ η).hom.app X.obj)
  naturality X Y φ := by
    apply ObjectProperty.hom_ext
    exact (ℵ.map₂ η).hom.naturality φ.hom

/-- The component at `X` of an isomorphism of additive `k`-linear functors. -/
abbrev isoApp {C D : LinearCat.{w, v, u} k} {F G : C ⟶ D} (e : F ≅ G) (X : C) :
    F.obj.obj X ≅ G.obj.obj X :=
  ((ObjectProperty.ι _).mapIso e).app X

/-- The restriction of the pseudofunctor `ℵ` to the full subcategories `P a`, for properties `P`
preserved by every `ℵ(f)`. -/
def fullSub : Pseudofunctor B (LinearCat.{w, v, u} k) where
  obj a := fullSubObj ℵ P a
  map f := LinFun.of (fullSubFunctor ℵ P hP f)
  map₂ η := ObjectProperty.homMk (fullSubNatTrans ℵ P hP η)
  mapId a := ObjectProperty.isoMk _
    (NatIso.ofComponents (fun X => ObjectProperty.isoMk _ (isoApp (ℵ.mapId a) X.obj))
      fun φ => by
        apply ObjectProperty.hom_ext; exact (ℵ.mapId a).hom.hom.naturality φ.hom)
  mapComp f g := ObjectProperty.isoMk _
    (NatIso.ofComponents (fun X => ObjectProperty.isoMk _ (isoApp (ℵ.mapComp f g) X.obj))
      fun φ => by
        apply ObjectProperty.hom_ext; exact (ℵ.mapComp f g).hom.hom.naturality φ.hom)
  map₂_id f := by
    apply ObjectProperty.hom_ext; ext X
    exact congrArg (fun θ => θ.hom.app X.obj) (ℵ.map₂_id f)
  map₂_comp η θ := by
    apply ObjectProperty.hom_ext; ext X
    exact congrArg (fun θ => θ.hom.app X.obj) (ℵ.map₂_comp η θ)
  map₂_whisker_left f _ _ η := by
    apply ObjectProperty.hom_ext; ext X
    exact congrArg (fun θ => θ.hom.app X.obj) (ℵ.map₂_whisker_left f η)
  map₂_whisker_right η h := by
    apply ObjectProperty.hom_ext; ext X
    exact congrArg (fun θ => θ.hom.app X.obj) (ℵ.map₂_whisker_right η h)
  map₂_associator f g h := by
    apply ObjectProperty.hom_ext; ext X
    exact congrArg (fun θ => θ.hom.app X.obj) (ℵ.map₂_associator f g h)
  map₂_left_unitor f := by
    apply ObjectProperty.hom_ext; ext X
    exact congrArg (fun θ => θ.hom.app X.obj) (ℵ.map₂_left_unitor f)
  map₂_right_unitor f := by
    apply ObjectProperty.hom_ext; ext X
    exact congrArg (fun θ => θ.hom.app X.obj) (ℵ.map₂_right_unitor f)

@[simp] theorem fullSub_obj (a : B) : (fullSub ℵ P hP).obj a = fullSubObj ℵ P a := rfl

@[simp] theorem fullSub_map_obj {a b : B} (f : a ⟶ b) :
    ((fullSub ℵ P hP).map f).obj = fullSubFunctor ℵ P hP f := rfl

/-- The inclusion functors of the full subcategories commute with the action. -/
theorem fullSub_map_obj_comp_ι {a b : B} (f : a ⟶ b) :
    ((fullSub ℵ P hP).map f).obj ⋙ (P b).ι = (P a).ι ⋙ (ℵ.map f).obj := rfl

end Categorification.TwoRep.LinearCat
