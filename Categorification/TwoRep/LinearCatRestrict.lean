/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqUpScalars

/-!
# Restriction of scalars from `LinearCat L` to `LinearCat k`

For a commutative `k`-algebra `L`, an `L`-linear category is `k`-linear through `k → L`, and an
`L`-linear functor is `k`-linear. This gives a strict pseudofunctor
`LinearCat.restrictScalars k L : LinearCat L ⥤ LinearCat k`, the identity on underlying
categories, functors and natural transformations.

It is used to regard the action of the Cautis–Lauda presentation on modules over Webster's
`Ř^λ`, which is `Ř^λ_λ`-linear, as a module category over the presentation over `k`
(Webster, arXiv:1309.3796v2, §3.4, the setting of Corollary 3.27).
-/

noncomputable section

open CategoryTheory CategoryTheory.Bicategory

namespace Categorification.TwoRep.LinearCat

universe wk wL v u

variable (k : Type wk) (L : Type wL) [CommRing k] [CommRing L] [Algebra k L]

/-- An `L`-linear category as a `k`-linear category. -/
abbrev restrictObj (C : LinearCat.{wL, v, u} L) : LinearCat.{wk, v, u} k :=
  letI := ScalarRestriction.linear k L C.carrier
  LinearCat.of k C.carrier

/-- An additive `L`-linear functor as an additive `k`-linear functor. -/
def restrictHom {C D : LinearCat.{wL, v, u} L} (F : C ⟶ D) :
    restrictObj k L C ⟶ restrictObj k L D :=
  @LinFun.of k _ C.carrier D.carrier _ _ _ _ (ScalarRestriction.linear k L C.carrier)
    (ScalarRestriction.linear k L D.carrier) F.obj _ (ScalarRestriction.functor F.obj)

@[simp] theorem restrictHom_obj {C D : LinearCat.{wL, v, u} L} (F : C ⟶ D) :
    (restrictHom k L F).obj = F.obj := rfl

/-- **Restriction of scalars** along `k → L`, as a strict pseudofunctor
`LinearCat L ⥤ LinearCat k`. -/
def restrictScalars : Pseudofunctor (LinearCat.{wL, v, u} L) (LinearCat.{wk, v, u} k) where
  obj := restrictObj k L
  map := restrictHom k L
  map₂ η := ObjectProperty.homMk η.hom
  mapId C := ObjectProperty.isoMk _ (Iso.refl _)
  mapComp F G := ObjectProperty.isoMk _ (Iso.refl _)
  map₂_id _ := rfl
  map₂_comp _ _ := rfl
  map₂_whisker_left _ _ _ η := by
    apply ObjectProperty.hom_ext; ext X
    change η.hom.app _ = 𝟙 _ ≫ η.hom.app _ ≫ 𝟙 _
    simp
  map₂_whisker_right η H := by
    apply ObjectProperty.hom_ext; ext X
    change H.obj.map (η.hom.app X) = 𝟙 _ ≫ H.obj.map (η.hom.app X) ≫ 𝟙 _
    simp
  map₂_associator F G H := by
    apply ObjectProperty.hom_ext; ext X
    change 𝟙 _ = 𝟙 _ ≫ H.obj.map (𝟙 _) ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _
    simp
  map₂_left_unitor F := by
    apply ObjectProperty.hom_ext; ext X
    change 𝟙 _ = 𝟙 _ ≫ F.obj.map (𝟙 _) ≫ 𝟙 _
    simp
  map₂_right_unitor F := by
    apply ObjectProperty.hom_ext; ext X
    change 𝟙 _ = 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _
    simp

@[simp] theorem restrictScalars_obj_carrier (C : LinearCat.{wL, v, u} L) :
    ((restrictScalars k L).obj C).carrier = C.carrier := rfl

@[simp] theorem restrictScalars_map_obj {C D : LinearCat.{wL, v, u} L} (F : C ⟶ D) :
    ((restrictScalars k L).map F).obj = F.obj := rfl

@[simp] theorem restrictScalars_map₂_hom {C D : LinearCat.{wL, v, u} L} {F G : C ⟶ D}
    (η : F ⟶ G) : ((restrictScalars k L).map₂ η).hom = η.hom := rfl

end Categorification.TwoRep.LinearCat
