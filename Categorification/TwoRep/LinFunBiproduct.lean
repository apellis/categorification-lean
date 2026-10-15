/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Categorification.TwoRep.LinearCat

/-!
# Finite biproducts of additive `k`-linear functors

For `k`-linear categories `C`, `D` with `D` having biproducts of shape `J` (`J` finite), the
category `LinFun k C D` of additive `k`-linear functors has biproducts of shape `J`: the
biproduct of `G : J → LinFun k C D` is the pointwise biproduct `X ↦ ⨁ⱼ (G j) X`, which is again
additive and `k`-linear. Hence the hom categories of the bicategory `LinearCat k` have finite
biproducts as soon as the targets do, and

* whiskering preserves them (`whiskerLeftBiproductIso : F ≫ ⨁ G ≅ ⨁ (F ≫ G j)` and
  `whiskerRightBiproductIso : (⨁ G) ≫ H ≅ ⨁ (G j ≫ H)`), since precomposition and
  postcomposition are additive;
* a finite family of adjunctions `L j ⊣ R j` gives an adjunction `⨁ L ⊣ ⨁ R`
  (`biproductAdjunction`) whose unit and counit are the diagonal matrices of the units and
  counits: `η = ∑ⱼ ηⱼ ≫ (ιⱼ ▷ Rⱼ) ≫ ((⨁ L) ◁ ιⱼ)` and `ε = ∑ⱼ ((⨁ R) ◁ πⱼ) ≫ (πⱼ ▷ Lⱼ) ≫ εⱼ`.

These are the sums of 1-morphisms used to assemble the 2-representation of Webster,
*Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3, Lemma `lem:g-action`, on the
route to KL III Thm. 1.2.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory

namespace Categorification.TwoRep

universe w v u

variable {k : Type w} [CommRing k]

section MapBiproduct

variable {X Y : Type*} [Category X] [Category Y] [Preadditive X] [Preadditive Y]
  (F : X ⥤ Y) [F.Additive] {J : Type} [Finite J] (f : J → X) [HasBiproduct f]
  [HasBiproduct (F.obj ∘ f)] (j : J)

@[reassoc]
theorem mapBiproduct_hom_π :
    (F.mapBiproduct f).hom ≫ biproduct.π (F.obj ∘ f) j = F.map (biproduct.π f j) :=
  biproduct.lift_π _ _

@[reassoc]
theorem map_ι_mapBiproduct_hom :
    F.map (biproduct.ι f j) ≫ (F.mapBiproduct f).hom = biproduct.ι (F.obj ∘ f) j := by
  classical
  refine biproduct.hom_ext _ _ fun j' => ?_
  rw [Category.assoc, mapBiproduct_hom_π, ← F.map_comp, biproduct.ι_π, biproduct.ι_π]
  split_ifs with h
  · subst h
    simp
  · simp

@[reassoc]
theorem ι_mapBiproduct_inv :
    biproduct.ι (F.obj ∘ f) j ≫ (F.mapBiproduct f).inv = F.map (biproduct.ι f j) :=
  biproduct.ι_desc _ _

@[reassoc]
theorem mapBiproduct_inv_map_π :
    (F.mapBiproduct f).inv ≫ F.map (biproduct.π f j) = biproduct.π (F.obj ∘ f) j := by
  rw [← mapBiproduct_hom_π, Iso.inv_hom_id_assoc]

end MapBiproduct

namespace LinearCat

namespace LinFun

section Pointwise

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D] [Linear k C]
  [Linear k D]

@[simp] theorem zero_hom_app (F G : LinFun k C D) (X : C) :
    (0 : F ⟶ G).hom.app X = 0 := rfl

@[simp] theorem add_hom_app {F G : LinFun k C D} (f g : F ⟶ G) (X : C) :
    (f + g).hom.app X = f.hom.app X + g.hom.app X := rfl

@[simp] theorem sum_hom_app {F G : LinFun k C D} {ι : Type*} (s : Finset ι) (f : ι → (F ⟶ G))
    (X : C) : (∑ i ∈ s, f i).hom.app X = ∑ i ∈ s, (f i).hom.app X := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_hom_app, ih]

variable {J : Type} [Finite J] [HasBiproductsOfShape J D] (G : J → LinFun k C D)

/-- The pointwise biproduct `X ↦ ⨁ⱼ (G j) X` of a finite family of functors. -/
@[simps]
abbrev pointwiseBiproduct : C ⥤ D where
  obj X := ⨁ fun j => (G j).obj.obj X
  map f := biproduct.map fun j => (G j).obj.map f
  map_id X := biproduct.hom_ext _ _ fun j => by simp
  map_comp f g := biproduct.hom_ext _ _ fun j => by simp

instance : (pointwiseBiproduct G).Additive where
  map_add {X Y f g} := biproduct.hom_ext _ _ fun j => by
    simp only [Functor.map_add, Preadditive.add_comp, biproduct.map_π,
      Preadditive.comp_add]

instance : (pointwiseBiproduct G).Linear k where
  map_smul f r := biproduct.hom_ext _ _ fun j => by
    simp only [Functor.map_smul, Linear.smul_comp, biproduct.map_π,
      Linear.comp_smul]

/-- The projection of the pointwise biproduct onto its `j`-th summand. -/
@[simps]
def pointwiseπ (j : J) : pointwiseBiproduct G ⟶ (G j).obj where
  app X := biproduct.π (fun j => (G j).obj.obj X) j
  naturality _ _ f := by simp

/-- The inclusion of the `j`-th summand into the pointwise biproduct. -/
@[simps]
def pointwiseι (j : J) : (G j).obj ⟶ pointwiseBiproduct G where
  app X := biproduct.ι (fun j => (G j).obj.obj X) j
  naturality _ _ f := by simp

/-- The pointwise biproduct as an additive `k`-linear functor. -/
abbrev pointwiseBiproductLinFun : LinFun k C D := LinFun.of (pointwiseBiproduct G)

/-- The biproduct bicone on the pointwise biproduct, with componentwise inclusions and
projections. -/
@[simps]
def pointwiseBicone : Bicone G where
  pt := pointwiseBiproductLinFun G
  π j := ObjectProperty.homMk (pointwiseπ G j)
  ι j := ObjectProperty.homMk (pointwiseι G j)
  ι_π j j' := by
    split_ifs with h
    · subst h
      apply ObjectProperty.hom_ext
      ext X
      exact biproduct.ι_π_self (fun j => (G j).obj.obj X) j
    · apply ObjectProperty.hom_ext
      ext X
      exact biproduct.ι_π_ne (fun j => (G j).obj.obj X) h

/-- The pointwise bicone is a bilimit. -/
def pointwiseBiconeIsBilimit : (pointwiseBicone G).IsBilimit := by
  have := Fintype.ofFinite J
  refine isBilimitOfTotal _ ?_
  apply ObjectProperty.hom_ext
  ext X
  rw [sum_hom_app]
  exact biproduct.total (f := fun j => (G j).obj.obj X)

instance : HasBiproductsOfShape J (LinFun k C D) where
  has_biproduct G := HasBiproduct.mk ⟨pointwiseBicone G, pointwiseBiconeIsBilimit G⟩

/-- The biproduct of additive `k`-linear functors is the pointwise biproduct. -/
def biproductIsoPointwise : ⨁ G ≅ pointwiseBiproductLinFun G :=
  (biproduct.uniqueUpToIso G (pointwiseBiconeIsBilimit G)).symm

@[reassoc (attr := simp)]
theorem ι_biproductIsoPointwise_hom (j : J) :
    biproduct.ι G j ≫ (biproductIsoPointwise G).hom = (pointwiseBicone G).ι j :=
  biproduct.ι_desc _ _

@[reassoc (attr := simp)]
theorem biproductIsoPointwise_inv_π (j : J) :
    (biproductIsoPointwise G).inv ≫ biproduct.π G j = (pointwiseBicone G).π j :=
  biproduct.lift_π _ _

instance [HasFiniteBiproducts D] : HasFiniteBiproducts (LinFun k C D) where
  out _ := inferInstance

end Pointwise

end LinFun

variable {J : Type} [Fintype J]

instance (C D : LinearCat.{w, v, u} k) [HasBiproductsOfShape J D] :
    HasBiproductsOfShape J (C ⟶ D) :=
  inferInstanceAs (HasBiproductsOfShape J (LinFun k C D))

instance (C D : LinearCat.{w, v, u} k) [HasFiniteBiproducts D] : HasFiniteBiproducts (C ⟶ D) :=
  inferInstanceAs (HasFiniteBiproducts (LinFun k C D))

instance precomp_additive (a b c : LinearCat.{w, v, u} k) (f : a ⟶ b) :
    (precomp c f).Additive where
  map_add := AdditiveWhiskering.whiskerLeft_add f _ _

instance postcomp_additive (a b c : LinearCat.{w, v, u} k) (g : b ⟶ c) :
    (postcomp a g).Additive where
  map_add := AdditiveWhiskering.add_whiskerRight _ _ g

section Whiskering

variable {a b c : LinearCat.{w, v, u} k} [HasBiproductsOfShape J c]

/-- Left whiskering preserves finite biproducts: `F ≫ ⨁ⱼ G j ≅ ⨁ⱼ (F ≫ G j)`. -/
def whiskerLeftBiproductIso (F : a ⟶ b) (G : J → (b ⟶ c)) :
    F ≫ ⨁ G ≅ ⨁ fun j => F ≫ G j :=
  (precomp c F).mapBiproduct G

/-- Right whiskering preserves finite biproducts: `(⨁ⱼ G j) ≫ H ≅ ⨁ⱼ (G j ≫ H)`. -/
def whiskerRightBiproductIso [HasBiproductsOfShape J b] (G : J → (a ⟶ b)) (H : b ⟶ c) :
    (⨁ G) ≫ H ≅ ⨁ fun j => G j ≫ H :=
  (postcomp a H).mapBiproduct G

variable (F : a ⟶ b) (G : J → (b ⟶ c)) (j : J)

@[reassoc (attr := simp)]
theorem whiskerLeft_ι_whiskerLeftBiproductIso_hom :
    F ◁ biproduct.ι G j ≫ (whiskerLeftBiproductIso F G).hom = biproduct.ι (fun j => F ≫ G j) j :=
  map_ι_mapBiproduct_hom (precomp c F) G j

@[reassoc (attr := simp)]
theorem whiskerLeftBiproductIso_hom_π :
    (whiskerLeftBiproductIso F G).hom ≫ biproduct.π (fun j => F ≫ G j) j = F ◁ biproduct.π G j :=
  mapBiproduct_hom_π (precomp c F) G j

@[reassoc (attr := simp)]
theorem ι_whiskerLeftBiproductIso_inv :
    biproduct.ι (fun j => F ≫ G j) j ≫ (whiskerLeftBiproductIso F G).inv = F ◁ biproduct.ι G j :=
  ι_mapBiproduct_inv (precomp c F) G j

@[reassoc (attr := simp)]
theorem whiskerLeftBiproductIso_inv_whiskerLeft_π :
    (whiskerLeftBiproductIso F G).inv ≫ F ◁ biproduct.π G j = biproduct.π (fun j => F ≫ G j) j :=
  mapBiproduct_inv_map_π (precomp c F) G j

variable [HasBiproductsOfShape J b] (G' : J → (a ⟶ b)) (H : b ⟶ c)

@[reassoc (attr := simp)]
theorem ι_whiskerRight_whiskerRightBiproductIso_hom :
    biproduct.ι G' j ▷ H ≫ (whiskerRightBiproductIso G' H).hom =
      biproduct.ι (fun j => G' j ≫ H) j :=
  map_ι_mapBiproduct_hom (postcomp a H) G' j

@[reassoc (attr := simp)]
theorem whiskerRightBiproductIso_hom_π :
    (whiskerRightBiproductIso G' H).hom ≫ biproduct.π (fun j => G' j ≫ H) j =
      biproduct.π G' j ▷ H :=
  mapBiproduct_hom_π (postcomp a H) G' j

@[reassoc (attr := simp)]
theorem ι_whiskerRightBiproductIso_inv :
    biproduct.ι (fun j => G' j ≫ H) j ≫ (whiskerRightBiproductIso G' H).inv =
      biproduct.ι G' j ▷ H :=
  ι_mapBiproduct_inv (postcomp a H) G' j

@[reassoc (attr := simp)]
theorem whiskerRightBiproductIso_inv_π_whiskerRight :
    (whiskerRightBiproductIso G' H).inv ≫ biproduct.π G' j ▷ H =
      biproduct.π (fun j => G' j ≫ H) j :=
  mapBiproduct_inv_map_π (postcomp a H) G' j

end Whiskering

section Adjunction

/-- A bicategorical adjunction in `LinearCat k` as an ordinary adjunction of the underlying
functors, with the same unit and counit (the inverse of `ofAdjunction`). -/
def toAdjunction {C D : LinearCat.{w, v, u} k} {F : C ⟶ D} {G : D ⟶ C}
    (adj : Bicategory.Adjunction F G) : CategoryTheory.Adjunction F.obj G.obj where
  unit := adj.unit.hom
  counit := adj.counit.hom
  left_triangle_components X := by
    have h := adj.left_triangle
    rw [leftZigzag_eq] at h
    have h' := congrArg (fun t => t.hom.app X) h
    change F.obj.map (adj.unit.hom.app X) ≫ 𝟙 (F.obj.obj (G.obj.obj (F.obj.obj X))) ≫
      adj.counit.hom.app (F.obj.obj X) = 𝟙 (F.obj.obj X) ≫ 𝟙 (F.obj.obj X) at h'
    simpa only [comp_obj, id_obj, Functor.comp_obj, Functor.id_obj, Category.id_comp,
      Category.comp_id] using h'
  right_triangle_components X := by
    have h := adj.right_triangle
    rw [rightZigzag_eq] at h
    have h' := congrArg (fun t => t.hom.app X) h
    change adj.unit.hom.app (G.obj.obj X) ≫ 𝟙 (G.obj.obj (F.obj.obj (G.obj.obj X))) ≫
      G.obj.map (adj.counit.hom.app X) = 𝟙 (G.obj.obj X) ≫ 𝟙 (G.obj.obj X) at h'
    simpa only [comp_obj, id_obj, Functor.comp_obj, Functor.id_obj, Category.id_comp,
      Category.comp_id] using h'

@[simp] theorem toAdjunction_unit {C D : LinearCat.{w, v, u} k} {F : C ⟶ D} {G : D ⟶ C}
    (adj : Bicategory.Adjunction F G) : (toAdjunction adj).unit = adj.unit.hom := rfl

@[simp] theorem toAdjunction_counit {C D : LinearCat.{w, v, u} k} {F : C ⟶ D} {G : D ⟶ C}
    (adj : Bicategory.Adjunction F G) : (toAdjunction adj).counit = adj.counit.hom := rfl

variable {C D : LinearCat.{w, v, u} k}

section Components

variable [HasBiproductsOfShape J D] (G : J → (C ⟶ D))

/-- The components of a biproduct of 1-morphisms satisfy `∑ⱼ πⱼ ιⱼ = 1` objectwise. -/
theorem biproduct_total_app (X : C) :
    ∑ j, (biproduct.π G j).hom.app X ≫ (biproduct.ι G j).hom.app X = 𝟙 _ := by
  have h := congrArg (fun t : (⨁ G ⟶ ⨁ G) => t.hom.app X) (biproduct.total (f := G))
  exact (LinFun.sum_hom_app _ _ X).symm.trans h

theorem biproduct_hom_ext_app {X : C} {Z : D} {f g : (⨁ G).obj.obj X ⟶ Z}
    (h : ∀ j, (biproduct.ι G j).hom.app X ≫ f = (biproduct.ι G j).hom.app X ≫ g) : f = g := by
  rw [← Category.id_comp f, ← Category.id_comp g, ← biproduct_total_app G X,
    Preadditive.sum_comp, Preadditive.sum_comp]
  exact Finset.sum_congr rfl fun j _ => by rw [Category.assoc, Category.assoc, h j]

theorem biproduct_hom_ext_app' {X : C} {Z : D} {f g : Z ⟶ (⨁ G).obj.obj X}
    (h : ∀ j, f ≫ (biproduct.π G j).hom.app X = g ≫ (biproduct.π G j).hom.app X) : f = g := by
  rw [← Category.comp_id f, ← Category.comp_id g, ← biproduct_total_app G X,
    Preadditive.comp_sum, Preadditive.comp_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [← Category.assoc, ← Category.assoc, h j]

end Components

variable [HasBiproductsOfShape J C] [HasBiproductsOfShape J D] {L : J → (C ⟶ D)}
  {R : J → (D ⟶ C)} (adj : ∀ j, Bicategory.Adjunction (L j) (R j))

/-- The unit of `⨁ L ⊣ ⨁ R`: the diagonal matrix of the units, `∑ⱼ ηⱼ ≫ (ιⱼ ▷ Rⱼ) ≫ ((⨁ L) ◁ ιⱼ)`. -/
def biproductUnit : 𝟙 C ⟶ (⨁ L) ≫ (⨁ R) :=
  ∑ j, (adj j).unit ≫ biproduct.ι L j ▷ R j ≫ (⨁ L) ◁ biproduct.ι R j

/-- The counit of `⨁ L ⊣ ⨁ R`: the diagonal matrix of the counits,
`∑ⱼ ((⨁ R) ◁ πⱼ) ≫ (πⱼ ▷ Lⱼ) ≫ εⱼ`. -/
def biproductCounit : (⨁ R) ≫ (⨁ L) ⟶ 𝟙 D :=
  ∑ j, (⨁ R) ◁ biproduct.π L j ≫ biproduct.π R j ▷ L j ≫ (adj j).counit

@[reassoc (attr := simp)]
theorem biproductUnit_whiskerLeft_π (j : J) :
    biproductUnit adj ≫ (⨁ L) ◁ biproduct.π R j = (adj j).unit ≫ biproduct.ι L j ▷ R j := by
  classical
  rw [biproductUnit, Preadditive.sum_comp, Finset.sum_eq_single j]
  · rw [Category.assoc, Category.assoc, ← Bicategory.whiskerLeft_comp, biproduct.ι_π_self,
      Bicategory.whiskerLeft_id, Category.comp_id]
  · intro b _ hb
    rw [Category.assoc, Category.assoc, ← Bicategory.whiskerLeft_comp, biproduct.ι_π_ne _ hb,
      AdditiveWhiskering.whiskerLeft_zero, comp_zero, comp_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

@[reassoc (attr := simp)]
theorem whiskerLeft_ι_biproductCounit (j : J) :
    (⨁ R) ◁ biproduct.ι L j ≫ biproductCounit adj = biproduct.π R j ▷ L j ≫ (adj j).counit := by
  classical
  rw [biproductCounit, Preadditive.comp_sum, Finset.sum_eq_single j]
  · rw [← Category.assoc, ← Bicategory.whiskerLeft_comp, biproduct.ι_π_self,
      Bicategory.whiskerLeft_id, Category.id_comp]
  · intro b _ hb
    rw [← Category.assoc, ← Bicategory.whiskerLeft_comp, biproduct.ι_π_ne _ (Ne.symm hb),
      AdditiveWhiskering.whiskerLeft_zero, zero_comp]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- The `(j, j)` entry of the unit of `⨁ L ⊣ ⨁ R` is the unit of `L j ⊣ R j`. -/
@[reassoc (attr := simp)]
theorem biproductUnit_π_π (j : J) :
    biproductUnit adj ≫ (⨁ L) ◁ biproduct.π R j ≫ biproduct.π L j ▷ R j = (adj j).unit := by
  rw [biproductUnit_whiskerLeft_π_assoc, ← Bicategory.comp_whiskerRight, biproduct.ι_π_self,
    Bicategory.id_whiskerRight, Category.comp_id]

/-- The `(j, j)` entry of the counit of `⨁ L ⊣ ⨁ R` is the counit of `L j ⊣ R j`. -/
@[reassoc (attr := simp)]
theorem ι_ι_biproductCounit (j : J) :
    biproduct.ι R j ▷ L j ≫ (⨁ R) ◁ biproduct.ι L j ≫ biproductCounit adj = (adj j).counit := by
  rw [whiskerLeft_ι_biproductCounit, ← Bicategory.comp_whiskerRight_assoc, biproduct.ι_π_self,
    Bicategory.id_whiskerRight, Category.id_comp]

/-- The component of `biproductUnit` at an object. -/
abbrev biproductUnitApp (X : C) : X ⟶ (⨁ R).obj.obj ((⨁ L).obj.obj X) :=
  (biproductUnit adj).hom.app X

/-- The component of `biproductCounit` at an object. -/
abbrev biproductCounitApp (Y : D) : (⨁ L).obj.obj ((⨁ R).obj.obj Y) ⟶ Y :=
  (biproductCounit adj).hom.app Y

theorem biproductUnitApp_π (j : J) (X : C) :
    biproductUnitApp adj X ≫ (biproduct.π R j).hom.app ((⨁ L).obj.obj X) =
      (adj j).unit.hom.app X ≫ (R j).obj.map ((biproduct.ι L j).hom.app X) :=
  congrArg (fun t => t.hom.app X) (biproductUnit_whiskerLeft_π adj j)

theorem ι_biproductCounitApp (j : J) (Y : D) :
    (biproduct.ι L j).hom.app ((⨁ R).obj.obj Y) ≫ biproductCounitApp adj Y =
      (L j).obj.map ((biproduct.π R j).hom.app Y) ≫ (adj j).counit.hom.app Y :=
  congrArg (fun t => t.hom.app Y) (whiskerLeft_ι_biproductCounit adj j)

/-- The unit of `L j ⊣ R j` at `X`, with its type written through the underlying functors. -/
private def unitApp (j : J) (X : C) : X ⟶ (R j).obj.obj ((L j).obj.obj X) :=
  (adj j).unit.hom.app X

/-- The counit of `L j ⊣ R j` at `Y`, with its type written through the underlying functors. -/
private def counitApp (j : J) (Y : D) : (L j).obj.obj ((R j).obj.obj Y) ⟶ Y :=
  (adj j).counit.hom.app Y

theorem biproduct_left_triangle_app (X : C) :
    (⨁ L).obj.map (biproductUnitApp adj X) ≫ biproductCounitApp adj ((⨁ L).obj.obj X) =
      𝟙 ((⨁ L).obj.obj X) := by
  refine biproduct_hom_ext_app L fun j => ?_
  have hn : (L j).obj.map (biproductUnitApp adj X) ≫
      (biproduct.ι L j).hom.app ((⨁ R).obj.obj ((⨁ L).obj.obj X)) =
      (biproduct.ι L j).hom.app X ≫ (⨁ L).obj.map (biproductUnitApp adj X) :=
    (biproduct.ι L j).hom.naturality _
  have hu : biproductUnitApp adj X ≫ (biproduct.π R j).hom.app ((⨁ L).obj.obj X) =
      unitApp adj j X ≫ (R j).obj.map ((biproduct.ι L j).hom.app X) :=
    biproductUnitApp_π adj j X
  have he : (biproduct.ι L j).hom.app ((⨁ R).obj.obj ((⨁ L).obj.obj X)) ≫
      biproductCounitApp adj ((⨁ L).obj.obj X) =
      (L j).obj.map ((biproduct.π R j).hom.app ((⨁ L).obj.obj X)) ≫
        counitApp adj j ((⨁ L).obj.obj X) :=
    ι_biproductCounitApp adj j _
  have hc : (L j).obj.map ((R j).obj.map ((biproduct.ι L j).hom.app X)) ≫
      counitApp adj j ((⨁ L).obj.obj X) =
      counitApp adj j ((L j).obj.obj X) ≫ (biproduct.ι L j).hom.app X :=
    (toAdjunction (adj j)).counit_naturality _
  have ht : (L j).obj.map (unitApp adj j X) ≫ counitApp adj j ((L j).obj.obj X) = 𝟙 _ :=
    (toAdjunction (adj j)).left_triangle_components X
  rw [Category.comp_id, ← Category.assoc, ← hn, Category.assoc, he, ← Category.assoc,
    ← Functor.map_comp, hu, Functor.map_comp, Category.assoc, hc, ← Category.assoc, ht,
    Category.id_comp]

theorem biproduct_right_triangle_app (Y : D) :
    biproductUnitApp adj ((⨁ R).obj.obj Y) ≫ (⨁ R).obj.map (biproductCounitApp adj Y) =
      𝟙 ((⨁ R).obj.obj Y) := by
  refine biproduct_hom_ext_app' R fun j => ?_
  have hn : (⨁ R).obj.map (biproductCounitApp adj Y) ≫ (biproduct.π R j).hom.app Y =
      (biproduct.π R j).hom.app ((⨁ L).obj.obj ((⨁ R).obj.obj Y)) ≫
        (R j).obj.map (biproductCounitApp adj Y) :=
    (biproduct.π R j).hom.naturality _
  have hu : biproductUnitApp adj ((⨁ R).obj.obj Y) ≫
      (biproduct.π R j).hom.app ((⨁ L).obj.obj ((⨁ R).obj.obj Y)) =
      unitApp adj j ((⨁ R).obj.obj Y) ≫
        (R j).obj.map ((biproduct.ι L j).hom.app ((⨁ R).obj.obj Y)) :=
    biproductUnitApp_π adj j _
  have he : (biproduct.ι L j).hom.app ((⨁ R).obj.obj Y) ≫ biproductCounitApp adj Y =
      (L j).obj.map ((biproduct.π R j).hom.app Y) ≫ counitApp adj j Y :=
    ι_biproductCounitApp adj j Y
  have hn' : unitApp adj j ((⨁ R).obj.obj Y) ≫
      (R j).obj.map ((L j).obj.map ((biproduct.π R j).hom.app Y)) =
      (biproduct.π R j).hom.app Y ≫ unitApp adj j ((R j).obj.obj Y) :=
    (toAdjunction (adj j)).unit_naturality _
  have ht : unitApp adj j ((R j).obj.obj Y) ≫ (R j).obj.map (counitApp adj j Y) = 𝟙 _ :=
    (toAdjunction (adj j)).right_triangle_components Y
  rw [Category.id_comp, Category.assoc, hn, ← Category.assoc, hu, Category.assoc,
    ← Functor.map_comp, he, Functor.map_comp, ← Category.assoc, hn', Category.assoc, ht,
    Category.comp_id]

/-- **Biproducts of adjunctions.** If `L j ⊣ R j` for each `j` in a finite type, then
`⨁ⱼ L j ⊣ ⨁ⱼ R j`, with unit `biproductUnit` and counit `biproductCounit` (the diagonal matrices
of the units and counits). -/
def biproductAdjunction : Bicategory.Adjunction (⨁ L) (⨁ R) where
  unit := biproductUnit adj
  counit := biproductCounit adj
  left_triangle := by
    rw [leftZigzag_eq]
    apply ObjectProperty.hom_ext
    ext X
    change (⨁ L).obj.map (biproductUnitApp adj X) ≫ 𝟙 _ ≫
      biproductCounitApp adj ((⨁ L).obj.obj X) = 𝟙 ((⨁ L).obj.obj X) ≫ 𝟙 _
    rw [Category.id_comp, Category.id_comp, biproduct_left_triangle_app]
  right_triangle := by
    rw [rightZigzag_eq]
    apply ObjectProperty.hom_ext
    ext Y
    change biproductUnitApp adj ((⨁ R).obj.obj Y) ≫ 𝟙 _ ≫
      (⨁ R).obj.map (biproductCounitApp adj Y) = 𝟙 ((⨁ R).obj.obj Y) ≫ 𝟙 _
    rw [Category.id_comp, Category.id_comp, biproduct_right_triangle_app]

@[simp] theorem biproductAdjunction_unit : (biproductAdjunction adj).unit = biproductUnit adj :=
  rfl

@[simp] theorem biproductAdjunction_counit :
    (biproductAdjunction adj).counit = biproductCounit adj :=
  rfl

end Adjunction

end LinearCat

end Categorification.TwoRep
