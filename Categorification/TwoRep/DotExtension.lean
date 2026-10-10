/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.Karoubi
import Categorification.TwoRep.KarRealize
import Categorification.TwoRep.KernelExact
import Categorification.TwoRep.MatKarFunctor

/-!
# Extending a pseudofunctor to the additive Karoubi envelope

For a pseudofunctor `F : A ⥤ᵖ B`, additive on 2-morphisms, into a bicategory whose hom categories
are additive and idempotent complete, `DotExt.ext F hF : Kar A ⥤ᵖ B` is the extension of `F` to the
additive Karoubi envelope `Kar A = KarBicat (MatBicat A)` (J. Brundan, A. P. Ellis,
arXiv:1603.05928v3, §1.5): first to formal direct sums and idempotents, then realized in `B`, where
formal direct sums are biproducts and idempotents split.

This file proves that `ext F hF` restricts to `F` along the inclusion `DotExt.incl A : A ⥤ᵖ Kar A`
as a pseudofunctor: the isomorphisms `DotExt.inclIso F hF x : ext (incl x) ≅ F x` are natural in
2-morphisms (`DotExt.inclIso_naturality`) and compatible with the composition and identity
constraints (`DotExt.inclIso_mapComp`, `DotExt.inclIso_mapId`).
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory

universe w v u w' v' u' w₁ v₁ u₁

/-! ## Generic lemmas -/

/-- A biproduct over `PUnit`. -/
def biprodPUnitIso {D : Type*} [Category D] [Preadditive D] [HasFiniteBiproducts D] (X : D) :
    ⨁ (fun _ : PUnit => X) ≅ X where
  hom := biproduct.π (fun _ : PUnit => X) PUnit.unit
  inv := biproduct.ι (fun _ : PUnit => X) PUnit.unit
  hom_inv_id := by
    rw [← biproduct.total, Fintype.sum_unique]
  inv_hom_id := biproduct.ι_π_self _ _

theorem biprodPUnit_aux {D : Type*} [Category D] [Preadditive D] [HasFiniteBiproducts D]
    {X Y : D} (φ : X ⟶ Y) :
    (biproduct.π (fun _ : PUnit => X) PUnit.unit ≫ φ ≫
        biproduct.ι (fun _ : PUnit => Y) PUnit.unit) ≫
        (biprodPUnitIso Y).hom ≫ 𝟙 Y =
      ((biprodPUnitIso X).hom ≫ 𝟙 X) ≫ φ := by
  simp [biprodPUnitIso]

theorem iso_conj_aux {𝒞 : Type*} [Category 𝒞] {A A' B B' Z Z' : 𝒞} (R : A ≅ A') (R' : B ≅ B')
    (k : A' ⟶ B') (m' : B' ⟶ Z) (m : A' ⟶ Z') (n : Z' ⟶ Z) (h : k ≫ m' = m ≫ n) :
    (R.hom ≫ k ≫ R'.inv) ≫ (R'.hom ≫ m') = (R.hom ≫ m) ≫ n := by
  simp [h]

theorem comp_map₂_add {A' C₁ D₁ : Type*} [Bicategory A'] [Bicategory C₁] [Bicategory D₁]
    [∀ a b : A', Preadditive (a ⟶ b)] [∀ a b : C₁, Preadditive (a ⟶ b)]
    [∀ a b : D₁, Preadditive (a ⟶ b)] (F : Pseudofunctor A' C₁) (G : Pseudofunctor C₁ D₁)
    (hF : ∀ {a b : A'} {f g : a ⟶ b} (η θ : f ⟶ g), F.map₂ (η + θ) = F.map₂ η + F.map₂ θ)
    (hG : ∀ {a b : C₁} {f g : a ⟶ b} (η θ : f ⟶ g), G.map₂ (η + θ) = G.map₂ η + G.map₂ θ)
    {a b : A'} {f g : a ⟶ b} (η θ : f ⟶ g) :
    (F.comp G).map₂ (η + θ) = (F.comp G).map₂ η + (F.comp G).map₂ θ := by
  show G.map₂ (F.map₂ (η + θ)) = G.map₂ (F.map₂ η) + G.map₂ (F.map₂ θ)
  rw [hF, hG]

theorem comp_map₂_smul {R : Type*} [CommRing R] {A' C₁ D₁ : Type*} [Bicategory A'] [Bicategory C₁]
    [Bicategory D₁] [∀ a b : A', Preadditive (a ⟶ b)] [∀ a b : C₁, Preadditive (a ⟶ b)]
    [∀ a b : D₁, Preadditive (a ⟶ b)] [∀ a b : A', Linear R (a ⟶ b)]
    [∀ a b : C₁, Linear R (a ⟶ b)] [∀ a b : D₁, Linear R (a ⟶ b)]
    (F : Pseudofunctor A' C₁) (G : Pseudofunctor C₁ D₁)
    (hF : ∀ {a b : A'} {f g : a ⟶ b} (r : R) (η : f ⟶ g), F.map₂ (r • η) = r • F.map₂ η)
    (hG : ∀ {a b : C₁} {f g : a ⟶ b} (r : R) (η : f ⟶ g), G.map₂ (r • η) = r • G.map₂ η)
    {a b : A'} {f g : a ⟶ b} (r : R) (η : f ⟶ g) :
    (F.comp G).map₂ (r • η) = r • (F.comp G).map₂ η := by
  show G.map₂ (F.map₂ (r • η)) = r • G.map₂ (F.map₂ η)
  rw [hF, hG]

/-- In a biproduct over a type with one element, `π ≫ ι = 𝟙`. -/
theorem biproduct_π_ι_unique {D : Type*} [Category D] [Preadditive D] [HasFiniteBiproducts D]
    {ι : Type} [Fintype ι] [Unique ι] (X : ι → D) :
    biproduct.π X default ≫ biproduct.ι X default = 𝟙 _ := by
  rw [← biproduct.total, Fintype.sum_unique]

end Categorification.TwoRep

namespace Categorification

open CategoryTheory CategoryTheory.Limits

/-! ## Isomorphisms of additive functors out of an additive envelope, in any universes

`Mathlib`'s `Mat_.ext` asks the source and target categories to live in the same universes; the
statements below are the same with arbitrary universes (same proofs). -/

namespace MatExtGen

open Mat_

universe v₁ v₂ u₂ u₃

variable {C : Type u₂} [Category.{v₁} C] [Preadditive C] {D : Type u₃} [Category.{v₂} D]
  [Preadditive D]

/-- Every `F M` is the biproduct of the images of the summands of `M`. -/
def addIso (F : Mat_ C ⥤ D) [F.Additive] [HasFiniteBiproducts D] (M : Mat_ C) :
    F.obj M ≅ ⨁ fun i => F.obj ((embedding C).obj (M.X i)) :=
  F.mapIso (isoBiproductEmbedding M) ≪≫ F.mapBiproduct _

variable [HasFiniteBiproducts D]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma addIso_hom_π (F : Mat_ C ⥤ D) [F.Additive] (M : Mat_ C) (i : M.ι) :
    (addIso F M).hom ≫ biproduct.π _ i = F.map (M.isoBiproductEmbedding.hom ≫ biproduct.π _ i) := by
  dsimp [addIso]
  rw [biproduct.lift_π, Category.assoc]
  erw [biproduct.lift_π, ← F.map_comp]
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma ι_addIso_inv (F : Mat_ C ⥤ D) [F.Additive] (M : Mat_ C) (i : M.ι) :
    biproduct.ι _ i ≫ (addIso F M).inv = F.map (biproduct.ι _ i ≫ M.isoBiproductEmbedding.inv) := by
  dsimp [addIso, Functor.mapBiproduct, Functor.mapBicone]
  simp only [biproduct.ι_desc, biproduct.ι_desc_assoc, ← F.map_comp]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem addIso_naturality (F : Mat_ C ⥤ D) [F.Additive] {M N : Mat_ C} (f : M ⟶ N) :
    F.map f ≫ (addIso F N).hom =
      (addIso F M).hom ≫ biproduct.matrix fun i j => F.map ((embedding C).map (f i j)) := by
  classical
  ext i : 1
  simp only [Category.assoc, addIso_hom_π, isoBiproductEmbedding_hom,
    biproduct.lift_π, biproduct.matrix_π,
    ← cancel_epi (addIso F M).inv, Iso.inv_hom_id_assoc]
  ext j : 1
  simp only [ι_addIso_inv_assoc, isoBiproductEmbedding_inv,
    biproduct.ι_desc, ← F.map_comp]
  congr 1
  funext ⟨⟩ ⟨⟩
  simp [Mat_.comp_apply, dite_comp, comp_dite]

@[reassoc]
theorem addIso_naturality' (F : Mat_ C ⥤ D) [F.Additive] {M N : Mat_ C} (f : M ⟶ N) :
    (addIso F M).inv ≫ F.map f =
      biproduct.matrix (fun i j => F.map ((embedding C).map (f i j)) :) ≫ (addIso F N).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, addIso_naturality]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- **Two additive functors out of `Mat_ C` are isomorphic if their restrictions to `C` are.** -/
def ext {F G : Mat_ C ⥤ D} [F.Additive] [G.Additive] (α : embedding C ⋙ F ≅ embedding C ⋙ G) :
    F ≅ G :=
  NatIso.ofComponents
    (fun M => addIso F M ≪≫ (biproduct.mapIso fun i => α.app (M.X i)) ≪≫ (addIso G M).symm)
    fun f => by
      dsimp only [Iso.trans_hom, Iso.symm_hom, biproduct.mapIso_hom]
      simp only [addIso_naturality_assoc]
      simp only [biproduct.matrix_map_assoc, Category.assoc]
      simp only [addIso_naturality']
      simp only [biproduct.map_matrix_assoc]
      congr 3
      ext j k
      exact α.hom.naturality (f j k)

end MatExtGen

/-! ## Isomorphisms of additive functors out of an additive Karoubi envelope -/

namespace KarMatExt

open Idempotents

variable {E : Type*} [Category E] [Preadditive E] {D : Type*} [Category D] [Preadditive D]
  [HasFiniteBiproducts D]

/-- The inclusion `E ⥤ Karoubi (Mat_ E)`. -/
abbrev incl (E : Type*) [Category E] [Preadditive E] : E ⥤ Karoubi (Mat_ E) :=
  Mat_.embedding E ⋙ toKaroubi (Mat_ E)

/-- An additive endofunctor `S` of `E`, extended to `Karoubi (Mat_ E)`, restricts to `S`. -/
def inclShift (S : E ⥤ E) [S.Additive] :
    incl E ⋙ mapKaroubi S.mapMat_ ≅ S ⋙ incl E :=
  NatIso.ofComponents (fun x => StringDiagrams.Karoubi.mkIso (Iso.refl _) (by
    show S.mapMat_.map (𝟙 _) ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _
    rw [CategoryTheory.Functor.map_id]))
    (fun {x y} η => Karoubi.hom_ext _ _ (by
      simp only [Karoubi.comp_f, StringDiagrams.Karoubi.mkIso, Iso.refl_hom, Functor.comp_map,
        Functor.comp_obj, mapKaroubi_map_f, toKaroubi_map_f]
      erw [StringDiagrams.Karoubi.mkHom_f, StringDiagrams.Karoubi.mkHom_f]
      simp only [toKaroubi_obj_p]
      repeat (first | erw [Category.id_comp] | erw [Category.comp_id])
      apply CategoryTheory.Mat_.hom_ext
      intro i j
      rfl))

/-- **Two additive functors out of `Karoubi (Mat_ E)` are isomorphic as soon as their restrictions
to `E` are.** -/
def ext {G₁ G₂ : Karoubi (Mat_ E) ⥤ D} [G₁.Additive] [G₂.Additive]
    (γ : incl E ⋙ G₁ ≅ incl E ⋙ G₂) : G₁ ≅ G₂ :=
  (whiskeringLeftObjToKaroubiFullyFaithful (C := Mat_ E) (D := D)).preimageIso
    (MatExtGen.ext (F := toKaroubi (Mat_ E) ⋙ G₁) (G := toKaroubi (Mat_ E) ⋙ G₂) γ)

end KarMatExt

end Categorification

/-! ## The composition constraints of the realizations -/

namespace Categorification.KarBicat

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory StringDiagrams

universe w v u w₁ v₁ u₁

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, IsIdempotentComplete (a ⟶ b)]
  {𝒳 : Type u₁} [Bicategory.{w₁, v₁} 𝒳] (Q : Pseudofunctor 𝒳 (StringDiagrams.KarBicat B))

/-- The composition constraint of `realize Q` is that of `Q`, conjugated by `realizeIso`. -/
theorem toKar_map₂_realize_mapComp_hom {x y z : 𝒳} (f : x ⟶ y) (g : y ⟶ z) :
    (toKar B).map₂ ((realize Q).mapComp f g).hom =
      ((realizeIso Q (f ≫ g)).hom ≫ (Q.mapComp f g).hom ≫
        (Q.map f ◁ (realizeIso Q g).inv ≫ (realizeIso Q f).inv ▷ (toKar B).map (realizeMap Q g))) ≫
          ((toKar B).mapComp _ _).inv :=
  toKar_map₂_pre _

/-- The identity constraint of `realize Q` is that of `Q`, conjugated by `realizeIso`. -/
theorem toKar_map₂_realize_mapId_hom (x : 𝒳) :
    (toKar B).map₂ ((realize Q).mapId x).hom =
      ((realizeIso Q (𝟙 x)).hom ≫ (Q.mapId x).hom) ≫ ((toKar B).mapId _).inv :=
  toKar_map₂_pre _

end Categorification.KarBicat

namespace Categorification.MatBicat

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory StringDiagrams

universe w v u

attribute [local instance] uniqueSingleι uniqueCompι uniqueIdι

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [PreadditiveBicategory B] [∀ a b : B, HasFiniteBiproducts (a ⟶ b)]

/-- The realization of the identity of `MatBicat B` on 2-morphisms between matrices with one entry
each. -/
theorem realize_id_map₂_unique {a b : StringDiagrams.MatBicat B} {M N : a ⟶ b} [Unique M.ι]
    [Unique N.ι] (φ : M ⟶ N) :
    (realize (Pseudofunctor.id (StringDiagrams.MatBicat B))).map₂ φ =
      biproduct.π M.X default ≫ φ default default ≫ biproduct.ι N.X default := by
  show ((matIsoC (D := a.obj ⟶ b.obj) M).hom ≫ φ ≫ (matIsoC (D := a.obj ⟶ b.obj) N).inv)
    PUnit.unit PUnit.unit = _
  rw [comp_apply_unique, comp_apply_unique]
  rfl

/-- The composition constraint of the realization of the identity of `MatBicat B` at matrices with
one entry each. -/
theorem realize_id_mapComp_hom_unique {a b c : StringDiagrams.MatBicat B} (M : a ⟶ b) (N : b ⟶ c)
    [Unique M.ι] [Unique N.ι] :
    ((realize (Pseudofunctor.id (StringDiagrams.MatBicat B))).mapComp M N).hom =
      biproduct.π (M ≫ N).X default ≫ M.X default ◁ biproduct.ι N.X default ≫
        biproduct.ι M.X default ▷ ⨁ N.X := by
  show (((matIsoC (D := a.obj ⟶ c.obj) (M ≫ N)).hom ≫ 𝟙 _ ≫
    (M ◁ (matIsoC (D := b.obj ⟶ c.obj) N).inv ≫
      (matIsoC (D := a.obj ⟶ b.obj) M).inv ▷ StringDiagrams.MatBicat.single (⨁ N.X))) ≫
        singleCompInv (⨁ M.X) (⨁ N.X)) PUnit.unit PUnit.unit = _
  rw [comp_apply_unique, comp_apply_unique, comp_apply_unique, comp_apply_unique]
  simp only [StringDiagrams.MatBicat.whiskerLeft_eq, StringDiagrams.MatBicat.whiskerRight_eq,
    StringDiagrams.MatBicat.hcomp_apply, hcomp₂]
  erw [StringDiagrams.MatBicat.id_apply_self, StringDiagrams.MatBicat.id_apply_self]
  erw [StringDiagrams.MatBicat.id_apply_self]
  simp only [Bicategory.id_whiskerRight, Bicategory.whiskerLeft_id, Category.id_comp,
    Category.comp_id]
  exact Category.comp_id (obj := a.obj ⟶ c.obj) _

/-- The identity constraint of the realization of the identity of `MatBicat B`. -/
theorem realize_id_mapId_hom (a : StringDiagrams.MatBicat B) :
    ((realize (Pseudofunctor.id (StringDiagrams.MatBicat B))).mapId a).hom =
      biproduct.π (𝟙 a : a ⟶ a).X default := by
  show (((matIsoC (D := a.obj ⟶ a.obj) (𝟙 a)).hom ≫ 𝟙 _) ≫ 𝟙 _) PUnit.unit PUnit.unit = _
  rw [comp_apply_unique, comp_apply_unique]
  erw [StringDiagrams.MatBicat.id_apply_self]
  exact (Category.comp_id (obj := a.obj ⟶ a.obj) _).trans
    (Category.comp_id (obj := a.obj ⟶ a.obj) _)

end Categorification.MatBicat

/-! ## The extension to the additive Karoubi envelope -/

namespace Categorification.TwoRep.DotExt

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory StringDiagrams

universe w v u w' v' u'

attribute [local instance] MatBicat.uniqueSingleι MatBicat.uniqueCompι MatBicat.uniqueIdι

/-- A pseudofunctor is additive on 2-morphisms. (A structure rather than a bare proposition, so that
the instances of the constructions below at a particular pseudofunctor are compared
syntactically.) -/
structure AddHyp {A : Type u} [Bicategory.{w, v} A] [∀ a b : A, Preadditive (a ⟶ b)] {B : Type u'}
    [Bicategory.{w', v'} B] [∀ a b : B, Preadditive (a ⟶ b)] (F : Pseudofunctor A B) : Prop where
  map₂_add : ∀ {a b : A} {f g : a ⟶ b} (η θ : f ⟶ g), F.map₂ (η + θ) = F.map₂ η + F.map₂ θ

variable {A : Type u} [Bicategory.{w, v} A] [∀ a b : A, Preadditive (a ⟶ b)]
  [PreadditiveBicategory A] {B : Type u'} [Bicategory.{w', v'} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [PreadditiveBicategory B]
  [∀ a b : B, HasFiniteBiproducts (a ⟶ b)] [∀ a b : B, IsIdempotentComplete (a ⟶ b)]
  (F : Pseudofunctor A B) (hF : AddHyp F)

/-- The extension of `F` to formal direct sums. -/
abbrev mf : Pseudofunctor (StringDiagrams.MatBicat A) (StringDiagrams.MatBicat B) :=
  MatBicat.mapPseudofunctor F hF.map₂_add

/-- The extension of `F` to formal direct sums and idempotents, followed by the realization of
formal direct sums in `B`: a pseudofunctor into the idempotent completion of `B`. -/
abbrev kar : Pseudofunctor (Kar A) (StringDiagrams.KarBicat B) :=
  (KarBicat.mapPseudofunctor (mf F hF)).comp
    (KarBicat.mapPseudofunctor (MatBicat.realize (Pseudofunctor.id (StringDiagrams.MatBicat B))))

/-- **The extension of `F` to the additive Karoubi envelope** `Kar A`. -/
def ext : Pseudofunctor (Kar A) B :=
  KarBicat.realize (kar F hF)

variable (A) in
/-- The inclusion `A ⥤ᵖ Kar A`: `x ↦ ((x), 1)`. -/
abbrev incl : Pseudofunctor A (Kar A) :=
  (MatBicat.toMat A).comp (KarBicat.toKar (StringDiagrams.MatBicat A))

theorem kar_map₂_add {X Y : Kar A} {f g : X ⟶ Y} (η θ : f ⟶ g) :
    (kar F hF).map₂ (η + θ) = (kar F hF).map₂ η + (kar F hF).map₂ θ :=
  comp_map₂_add _ _
    (KarBicat.mapPseudofunctor_map₂_add _
      (MatBicat.mapPseudofunctor_map₂_add F hF.map₂_add))
    (KarBicat.mapPseudofunctor_map₂_add _ (MatBicat.realize_map₂_add _ (fun _ _ => rfl))) η θ

theorem kar_map₂_smul {R : Type*} [CommRing R] [∀ a b : A, Linear R (a ⟶ b)]
    [∀ a b : B, Linear R (a ⟶ b)]
    (hF' : ∀ {a b : A} {f g : a ⟶ b} (r : R) (η : f ⟶ g), F.map₂ (r • η) = r • F.map₂ η)
    {X Y : Kar A} {f g : X ⟶ Y} (r : R) (η : f ⟶ g) :
    (kar F hF).map₂ (r • η) = r • (kar F hF).map₂ η :=
  comp_map₂_smul _ _
    (KarBicat.mapPseudofunctor_map₂_smul _
      (MatBicat.mapPseudofunctor_map₂_smul F hF.map₂_add hF'))
    (KarBicat.mapPseudofunctor_map₂_smul _ (MatBicat.realize_map₂_smul _ (fun _ _ => rfl))) r η

/-- `ext F hF` is additive on 2-morphisms. -/
theorem ext_map₂_add {X Y : Kar A} {f g : X ⟶ Y} (η θ : f ⟶ g) :
    (ext F hF).map₂ (η + θ) = (ext F hF).map₂ η + (ext F hF).map₂ θ :=
  KarBicat.realize_map₂_add _ (kar_map₂_add F hF) η θ

/-- `ext F hF` is `R`-linear on 2-morphisms if `F` is. -/
theorem ext_map₂_smul {R : Type*} [CommRing R] [∀ a b : A, Linear R (a ⟶ b)]
    [∀ a b : B, Linear R (a ⟶ b)]
    (hF' : ∀ {a b : A} {f g : a ⟶ b} (r : R) (η : f ⟶ g), F.map₂ (r • η) = r • F.map₂ η)
    {X Y : Kar A} {f g : X ⟶ Y} (r : R) (η : f ⟶ g) :
    (ext F hF).map₂ (r • η) = r • (ext F hF).map₂ η :=
  KarBicat.realize_map₂_smul _ (kar_map₂_smul F hF hF') r η

theorem kar_map_incl_p {a b : A} (x : a ⟶ b) : ((kar F hF).map ((incl A).map x)).p = 𝟙 _ := by
  show (MatBicat.realize (Pseudofunctor.id _)).map₂
    ((mf F hF).map₂ (𝟙 _)) = 𝟙 _
  rw [PrelaxFunctor.map₂_id, PrelaxFunctor.map₂_id]

/-- The image of the inclusion of `x`, in the idempotent completion of `B`. -/
def karInclIso {a b : A} (x : a ⟶ b) :
    (kar F hF).map ((incl A).map x) ≅ (KarBicat.toKar B).map (F.map x) :=
  StringDiagrams.Karoubi.mkIso (biprodPUnitIso (F.map x)) (by
    rw [kar_map_incl_p]
    exact (Category.id_comp _).trans (Category.comp_id _).symm)

/-- **`ext F hF` extends `F`**: the image of the inclusion of `x` is isomorphic to `F x`. -/
def inclIso {a b : A} (x : a ⟶ b) : (ext F hF).map ((incl A).map x) ≅ F.map x :=
  (Idempotents.fullyFaithfulToKaroubi _).preimageIso
    (KarBicat.realizeIso (kar F hF) ((incl A).map x) ≪≫ karInclIso F hF x)

theorem toKar_map₂_inclIso_hom {a b : A} (x : a ⟶ b) :
    (KarBicat.toKar B).map₂ (inclIso F hF x).hom =
      (KarBicat.realizeIso (kar F hF) ((incl A).map x)).hom ≫ (karInclIso F hF x).hom :=
  (Idempotents.fullyFaithfulToKaroubi _).map_preimage _

/-- The `f`-component of the composition constraint of `kar F hF` on the inclusions. -/
theorem kar_mapComp_incl_hom_f {a b c : A} (x : a ⟶ b) (y : b ⟶ c) :
    ((kar F hF).mapComp ((incl A).map x) ((incl A).map y)).hom.f =
      (MatBicat.realize (Pseudofunctor.id (StringDiagrams.MatBicat B))).map₂
          ((mf F hF).mapComp (MatBicat.single x) (MatBicat.single y)).hom ≫
        ((MatBicat.realize (Pseudofunctor.id (StringDiagrams.MatBicat B))).mapComp
          ((mf F hF).map (MatBicat.single x))
          ((mf F hF).map (MatBicat.single y))).hom := by
  show (MatBicat.realize (Pseudofunctor.id (StringDiagrams.MatBicat B))).map₂
      (((mf F hF).mapComp (MatBicat.single x) (MatBicat.single y)).hom ≫
        hcomp₂ ((mf F hF).map₂ (𝟙 _))
          ((mf F hF).map₂ (𝟙 _))) ≫
      (((MatBicat.realize (Pseudofunctor.id (StringDiagrams.MatBicat B))).mapComp
          ((mf F hF).map (MatBicat.single x))
          ((mf F hF).map (MatBicat.single y))).hom ≫
        hcomp₂ ((MatBicat.realize (Pseudofunctor.id _)).map₂
            ((mf F hF).map₂ (𝟙 _)))
          ((MatBicat.realize (Pseudofunctor.id _)).map₂
            ((mf F hF).map₂ (𝟙 _)))) = _
  simp only [PrelaxFunctor.map₂_id, hcomp₂_id_id, Category.comp_id]

theorem bip_ι_π_assoc {a' c' : B} {J : Type} [Fintype J] [DecidableEq J] (f : J → (a' ⟶ c'))
    (j : J) {Z : a' ⟶ c'} (h : f j ⟶ Z) : biproduct.ι f j ≫ biproduct.π f j ≫ h = h :=
  biproduct.ι_π_self_assoc f j h

theorem bip_ι_π {a' c' : B} {J : Type} [Fintype J] [DecidableEq J] (f : J → (a' ⟶ c'))
    (j : J) : biproduct.ι f j ≫ biproduct.π f j = 𝟙 _ :=
  biproduct.ι_π_self f j

theorem whisker_ι_π_aux {a' b' c' : B} {J K : Type} [Fintype J] [Fintype K] [DecidableEq J]
    [DecidableEq K] (fX : J → (a' ⟶ b')) (fY : K → (b' ⟶ c')) (j : J) (k : K) :
    fX j ◁ biproduct.ι fY k ≫ biproduct.ι fX j ▷ (⨁ fY) ≫ biproduct.π fX j ▷ (⨁ fY) ≫
        𝟙 (fX j ≫ ⨁ fY) ≫ 𝟙 (fX j ≫ ⨁ fY) ≫ fX j ◁ biproduct.π fY k =
      𝟙 (fX j ≫ fY k) ≫ 𝟙 (fX j ≫ fY k) := by
  rw [← comp_whiskerRight_assoc, biproduct.ι_π_self, Bicategory.id_whiskerRight, Category.id_comp,
    Category.id_comp, Category.id_comp, ← Bicategory.whiskerLeft_comp, biproduct.ι_π_self,
    Bicategory.whiskerLeft_id, Category.id_comp]

/-- A one-element index type. -/
@[instance_reducible] def uniqueMapι {a b : StringDiagrams.MatBicat A} (M : a ⟶ b) [Unique M.ι] :
    Unique ((mf F hF).map M).ι :=
  inferInstanceAs (Unique M.ι)

attribute [local instance] uniqueMapι

theorem mapPseudofunctor_mapComp_single_apply {a b c : A} (x : a ⟶ b) (y : b ⟶ c)
    (i j : PUnit × PUnit) :
    ((mf F hF).mapComp (MatBicat.single x) (MatBicat.single y)).hom i j =
      (F.mapComp x y).hom := by
  obtain rfl : i = j := Subsingleton.elim _ _
  exact StringDiagrams.Mat_.permMat_apply_self (X := fun _ => F.map (x ≫ y))
    (Y := fun _ => F.map x ≫ F.map y) (Equiv.refl _) (fun _ => (F.mapComp x y).hom) i

theorem mapPseudofunctor_map₂_singleCompInv_apply {a b c : A} (x : a ⟶ b) (y : b ⟶ c)
    (i : PUnit × PUnit) (j : PUnit) :
    (mf F hF).map₂
        ((𝟙 (MatBicat.single x ≫ MatBicat.single y) ≫ 𝟙 (MatBicat.single x ≫ MatBicat.single y)) ≫
          MatBicat.singleCompInv x y) i j = 𝟙 _ := by
  show F.map₂ (((𝟙 _ ≫ 𝟙 _) ≫ MatBicat.singleCompInv x y) i j) = 𝟙 _
  obtain rfl : i = default := Subsingleton.elim _ _
  rw [MatBicat.comp_apply_unique, MatBicat.comp_apply_unique]
  erw [StringDiagrams.MatBicat.id_apply_self]
  erw [Category.id_comp, Category.id_comp]
  exact F.map₂_id _

theorem karInclIso_mapComp {a b c : A} (x : a ⟶ b) (y : b ⟶ c) :
    ((kar F hF).mapComp ((incl A).map x) ((incl A).map y)).hom ≫
        (karInclIso F hF x).hom ▷ (kar F hF).map ((incl A).map y) ≫
          (KarBicat.toKar B).map (F.map x) ◁ (karInclIso F hF y).hom =
      (kar F hF).map₂ ((incl A).mapComp x y).inv ≫ (karInclIso F hF (x ≫ y)).hom ≫
        (KarBicat.toKar B).map₂ (F.mapComp x y).hom ≫ ((KarBicat.toKar B).mapComp _ _).hom := by
  apply Idempotents.Karoubi.hom_ext
  show ((kar F hF).mapComp ((incl A).map x) ((incl A).map y)).hom.f ≫
      hcomp₂ ((biprodPUnitIso (F.map x)).hom ≫ 𝟙 (F.map x)) ((kar F hF).map ((incl A).map y)).p ≫
        hcomp₂ (𝟙 (F.map x)) ((biprodPUnitIso (F.map y)).hom ≫ 𝟙 (F.map y)) =
    (MatBicat.realize (Pseudofunctor.id (StringDiagrams.MatBicat B))).map₂
        ((mf F hF).map₂ ((𝟙 _ ≫ 𝟙 _) ≫ MatBicat.singleCompInv x y)) ≫
      ((biprodPUnitIso (F.map (x ≫ y))).hom ≫ 𝟙 _) ≫ (F.mapComp x y).hom ≫
        (𝟙 _ ≫ hcomp₂ (𝟙 (F.map x)) (𝟙 (F.map y)))
  rw [kar_mapComp_incl_hom_f, kar_map_incl_p, MatBicat.realize_id_map₂_unique,
    MatBicat.realize_id_map₂_unique, MatBicat.realize_id_mapComp_hom_unique]
  erw [mapPseudofunctor_mapComp_single_apply, mapPseudofunctor_map₂_singleCompInv_apply]
  simp only [hcomp₂, biprodPUnitIso]
  repeat erw [Category.assoc]
  congr 1
  erw [bip_ι_π_assoc, bip_ι_π_assoc]
  repeat erw [Category.id_comp]
  repeat erw [Category.comp_id]
  repeat erw [Bicategory.id_whiskerRight]
  repeat erw [Bicategory.whiskerLeft_id]
  congr 1
  exact whisker_ι_π_aux _ _ _ _

/-- The pasting argument behind `inclIso_mapComp`, in a form where all 1-morphisms have the same
objects. -/
theorem mapComp_aux {P₀ P₁ P₂ : B} {Ex Fx : P₀ ⟶ P₁} {Ey Fy : P₁ ⟶ P₂} {Exy Exy' Fxy : P₀ ⟶ P₂}
    {Kx : (KarBicat.toKar B).obj P₀ ⟶ (KarBicat.toKar B).obj P₁}
    {Ky : (KarBicat.toKar B).obj P₁ ⟶ (KarBicat.toKar B).obj P₂}
    {Kxy Kxy' : (KarBicat.toKar B).obj P₀ ⟶ (KarBicat.toKar B).obj P₂}
    (ρx : (KarBicat.toKar B).map Ex ≅ Kx) (ρy : (KarBicat.toKar B).map Ey ≅ Ky)
    (ρxy : (KarBicat.toKar B).map Exy ≅ Kxy) (ρxy' : (KarBicat.toKar B).map Exy' ≅ Kxy')
    (βx : Kx ≅ (KarBicat.toKar B).map Fx) (βy : Ky ≅ (KarBicat.toKar B).map Fy)
    (βxy : Kxy' ≅ (KarBicat.toKar B).map Fxy) (Kmc : Kxy ⟶ Kx ≫ Ky) (Ke : Kxy ⟶ Kxy')
    (m : Exy ⟶ Ex ≫ Ey) (ιx : Ex ⟶ Fx) (ιy : Ey ⟶ Fy) (ιxy : Exy' ⟶ Fxy) (e : Exy ⟶ Exy')
    (Fmc : Fxy ⟶ Fx ≫ Fy)
    (hm : (KarBicat.toKar B).map₂ m = (ρxy.hom ≫ Kmc ≫
      (Kx ◁ ρy.inv ≫ ρx.inv ▷ (KarBicat.toKar B).map Ey)) ≫ ((KarBicat.toKar B).mapComp _ _).inv)
    (hιx : (KarBicat.toKar B).map₂ ιx = ρx.hom ≫ βx.hom)
    (hιy : (KarBicat.toKar B).map₂ ιy = ρy.hom ≫ βy.hom)
    (hιxy : (KarBicat.toKar B).map₂ ιxy = ρxy'.hom ≫ βxy.hom)
    (he : (KarBicat.toKar B).map₂ e = ρxy.hom ≫ Ke ≫ ρxy'.inv)
    (hβ : Kmc ≫ βx.hom ▷ Ky ≫ (KarBicat.toKar B).map Fx ◁ βy.hom =
      Ke ≫ βxy.hom ≫ (KarBicat.toKar B).map₂ Fmc ≫ ((KarBicat.toKar B).mapComp _ _).hom) :
    m ≫ ιx ▷ Ey ≫ Fx ◁ ιy = e ≫ ιxy ≫ Fmc := by
  apply KarBicat.toKar_map₂_injective
  simp only [PrelaxFunctor.map₂_comp, Pseudofunctor.map₂_whisker_right,
    Pseudofunctor.map₂_whisker_left, hm, hιx, hιy, hιxy, he, Category.assoc,
    Iso.inv_hom_id_assoc, comp_whiskerRight, Bicategory.whiskerLeft_comp,
    inv_hom_whiskerRight_assoc]
  rw [whisker_exchange_assoc, whiskerLeft_inv_hom_assoc, reassoc_of% hβ]
  simp only [Iso.hom_inv_id, Category.comp_id]

/-- **`inclIso` is compatible with the composition constraints**: together with
`inclIso_naturality` and `inclIso_mapId`, the isomorphisms `ext (incl x) ≅ F x` are the components
of a pseudonatural isomorphism from `incl A ⋙ ext F hF` to `F`. -/
theorem inclIso_mapComp {a b c : A} (x : a ⟶ b) (y : b ⟶ c) :
    ((ext F hF).mapComp ((incl A).map x) ((incl A).map y)).hom ≫
        (inclIso F hF x).hom ▷ (ext F hF).map ((incl A).map y) ≫ F.map x ◁ (inclIso F hF y).hom =
      (ext F hF).map₂ ((incl A).mapComp x y).inv ≫ (inclIso F hF (x ≫ y)).hom ≫
        (F.mapComp x y).hom :=
  mapComp_aux _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (KarBicat.toKar_map₂_realize_mapComp_hom (kar F hF) _ _) (toKar_map₂_inclIso_hom F hF x)
    (toKar_map₂_inclIso_hom F hF y) (toKar_map₂_inclIso_hom F hF (x ≫ y))
    (KarBicat.toKar_map₂_realize_map₂ (kar F hF) _) (karInclIso_mapComp F hF x y)

theorem kar_map₂_incl {a b : A} {x y : a ⟶ b} (η : x ⟶ y) :
    (kar F hF).map₂ ((incl A).map₂ η) ≫ (karInclIso F hF y).hom =
      (karInclIso F hF x).hom ≫ (KarBicat.toKar B).map₂ (F.map₂ η) := by
  apply Idempotents.Karoubi.hom_ext
  show (MatBicat.realize (Pseudofunctor.id (StringDiagrams.MatBicat B))).map₂
      ((mf F hF).map₂ (MatBicat.mat1 η)) ≫
        (biprodPUnitIso (F.map y)).hom ≫ 𝟙 _ =
      ((biprodPUnitIso (F.map x)).hom ≫ 𝟙 _) ≫ F.map₂ η
  rw [MatBicat.realize_id_map₂_unique]
  exact biprodPUnit_aux (D := F.obj a ⟶ F.obj b) (F.map₂ η)

/-- The pasting argument behind `inclIso_naturality`. -/
theorem naturality_aux {P₀ P₁ : B} {Ex Ey Fx Fy : P₀ ⟶ P₁}
    {Kx Ky : (KarBicat.toKar B).obj P₀ ⟶ (KarBicat.toKar B).obj P₁}
    (ρx : (KarBicat.toKar B).map Ex ≅ Kx) (ρy : (KarBicat.toKar B).map Ey ≅ Ky)
    (βx : Kx ≅ (KarBicat.toKar B).map Fx) (βy : Ky ≅ (KarBicat.toKar B).map Fy) (Kη : Kx ⟶ Ky)
    (eη : Ex ⟶ Ey) (ιx : Ex ⟶ Fx) (ιy : Ey ⟶ Fy) (Fη : Fx ⟶ Fy)
    (he : (KarBicat.toKar B).map₂ eη = ρx.hom ≫ Kη ≫ ρy.inv)
    (hιx : (KarBicat.toKar B).map₂ ιx = ρx.hom ≫ βx.hom)
    (hιy : (KarBicat.toKar B).map₂ ιy = ρy.hom ≫ βy.hom)
    (hβ : Kη ≫ βy.hom = βx.hom ≫ (KarBicat.toKar B).map₂ Fη) :
    eη ≫ ιy = ιx ≫ Fη := by
  apply KarBicat.toKar_map₂_injective
  simp only [PrelaxFunctor.map₂_comp, he, hιx, hιy, Category.assoc, Iso.inv_hom_id_assoc, hβ]

/-- **Naturality**: the isomorphisms `inclIso` intertwine `ext F hF` on the image of a 2-morphism
and `F`. -/
theorem inclIso_naturality {a b : A} {x y : a ⟶ b} (η : x ⟶ y) :
    (ext F hF).map₂ ((incl A).map₂ η) ≫ (inclIso F hF y).hom =
      (inclIso F hF x).hom ≫ F.map₂ η :=
  naturality_aux _ _ _ _ _ _ _ _ _ (KarBicat.toKar_map₂_realize_map₂ (kar F hF) _)
    (toKar_map₂_inclIso_hom F hF x) (toKar_map₂_inclIso_hom F hF y) (kar_map₂_incl F hF η)

theorem mapPseudofunctor_mapId_apply (a : StringDiagrams.MatBicat A) (i j : PUnit) :
    ((mf F hF).mapId a).hom i j = (F.mapId a.obj).hom := by
  obtain rfl : i = j := Subsingleton.elim _ _
  exact StringDiagrams.Mat_.permMat_apply_self (X := fun _ => F.map (𝟙 a.obj))
    (Y := fun _ => 𝟙 (F.obj a.obj)) (Equiv.refl _) (fun _ => (F.mapId a.obj).hom) i

theorem karInclIso_mapId (a : A) :
    (kar F hF).map₂ ((incl A).mapId a).hom ≫ ((kar F hF).mapId ((incl A).obj a)).hom =
      (karInclIso F hF (𝟙 a)).hom ≫ (KarBicat.toKar B).map₂ (F.mapId a).hom ≫
        ((KarBicat.toKar B).mapId _).hom := by
  apply Idempotents.Karoubi.hom_ext
  show (MatBicat.realize (Pseudofunctor.id (StringDiagrams.MatBicat B))).map₂
        ((mf F hF).map₂ (𝟙 _ ≫ 𝟙 _)) ≫
      ((MatBicat.realize (Pseudofunctor.id (StringDiagrams.MatBicat B))).map₂
          (((mf F hF).mapId _).hom ≫ 𝟙 _) ≫
        ((MatBicat.realize (Pseudofunctor.id (StringDiagrams.MatBicat B))).mapId _).hom ≫ 𝟙 _) =
    ((biprodPUnitIso (F.map (𝟙 a))).hom ≫ 𝟙 _) ≫ (F.mapId a).hom ≫ 𝟙 _
  simp only [Category.comp_id, PrelaxFunctor.map₂_id, Category.id_comp]
  rw [MatBicat.realize_id_map₂_unique, MatBicat.realize_id_mapId_hom]
  erw [mapPseudofunctor_mapId_apply, Category.assoc, Category.assoc, bip_ι_π, Category.comp_id]
  rfl

/-- The pasting argument behind `inclIso_mapId`. -/
theorem mapId_aux {P₀ : B} {E E' Fi : P₀ ⟶ P₀}
    {K K' : (KarBicat.toKar B).obj P₀ ⟶ (KarBicat.toKar B).obj P₀}
    (ρ : (KarBicat.toKar B).map E ≅ K) (ρ' : (KarBicat.toKar B).map E' ≅ K')
    (β : K ≅ (KarBicat.toKar B).map Fi) (Ke : K ⟶ K') (Kid : K' ⟶ 𝟙 _) (e : E ⟶ E')
    (me : E' ⟶ 𝟙 P₀) (ι : E ⟶ Fi) (mF : Fi ⟶ 𝟙 P₀)
    (he : (KarBicat.toKar B).map₂ e = ρ.hom ≫ Ke ≫ ρ'.inv)
    (hme : (KarBicat.toKar B).map₂ me = (ρ'.hom ≫ Kid) ≫ ((KarBicat.toKar B).mapId P₀).inv)
    (hι : (KarBicat.toKar B).map₂ ι = ρ.hom ≫ β.hom)
    (hβ : Ke ≫ Kid = β.hom ≫ (KarBicat.toKar B).map₂ mF ≫ ((KarBicat.toKar B).mapId P₀).hom) :
    e ≫ me = ι ≫ mF := by
  apply KarBicat.toKar_map₂_injective
  simp only [PrelaxFunctor.map₂_comp, he, hme, hι, Category.assoc, Iso.inv_hom_id_assoc,
    reassoc_of% hβ, Iso.hom_inv_id, Category.comp_id]

/-- **`inclIso` is compatible with the identity constraints.** -/
theorem inclIso_mapId (a : A) :
    (ext F hF).map₂ ((incl A).mapId a).hom ≫ ((ext F hF).mapId ((incl A).obj a)).hom =
      (inclIso F hF (𝟙 a)).hom ≫ (F.mapId a).hom :=
  mapId_aux _ _ _ _ _ _ _ _ _ (KarBicat.toKar_map₂_realize_map₂ (kar F hF) _)
    (KarBicat.toKar_map₂_realize_mapId_hom (kar F hF) _) (toKar_map₂_inclIso_hom F hF (𝟙 a))
    (karInclIso_mapId F hF a)

/-! ### Hom-wise: `ext F hF` extends `F` as a functor on each hom category -/

instance mapFunctor_additive (a b : Kar A) : ((ext F hF).mapFunctor a b).Additive where
  map_add {_ _ η θ} := ext_map₂_add F hF η θ

/-- On each hom category, `ext F hF` restricted along `x ↦ ((x), 1)` is `F`. -/
def inclNatIso (a b : Kar A) :
    KarMatExt.incl (a.obj.obj ⟶ b.obj.obj) ⋙ (ext F hF).mapFunctor a b ≅
      F.mapFunctor a.obj.obj b.obj.obj :=
  NatIso.ofComponents (fun x => inclIso F hF x) (fun η => inclIso_naturality F hF η)

@[simp] theorem inclNatIso_hom_app (a b : Kar A) (x : a.obj.obj ⟶ b.obj.obj) :
    (inclNatIso F hF a b).hom.app x = (inclIso F hF x).hom := rfl

/-- **Additive functors commuting with `F` commute with `ext F hF`**: an isomorphism
`S ⋙ F ≅ F ⋙ T` on a hom category of `A`, with `S` and `T` additive, extends to
`S̃ ⋙ ext F hF ≅ ext F hF ⋙ T`, where `S̃` is `S` applied entrywise to matrices and idempotents. -/
def extNatIso (a b : Kar A) (S : (a.obj.obj ⟶ b.obj.obj) ⥤ (a.obj.obj ⟶ b.obj.obj)) [S.Additive]
    (T : ((ext F hF).obj a ⟶ (ext F hF).obj b) ⥤ ((ext F hF).obj a ⟶ (ext F hF).obj b))
    [T.Additive] (φ : S ⋙ F.mapFunctor a.obj.obj b.obj.obj ≅ F.mapFunctor a.obj.obj b.obj.obj ⋙ T) :
    mapKaroubi S.mapMat_ ⋙ (ext F hF).mapFunctor a b ≅
      (ext F hF).mapFunctor a b ⋙ T :=
  haveI : (mapKaroubi S.mapMat_).Additive := mapKaroubi_additive _
  haveI : ((ext F hF).mapFunctor a b).Additive := mapFunctor_additive F hF a b
  KarMatExt.ext
    (Functor.isoWhiskerRight (KarMatExt.inclShift S) ((ext F hF).mapFunctor a b) ≪≫
      Functor.isoWhiskerLeft S (inclNatIso F hF a b) ≪≫ φ ≪≫
      Functor.isoWhiskerRight (inclNatIso F hF a b).symm T)

end Categorification.TwoRep.DotExt
