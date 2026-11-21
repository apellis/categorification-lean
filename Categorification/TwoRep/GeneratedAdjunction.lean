/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.GeneratedModification
import Categorification.TwoRep.LinFunBiproduct

/-!
# Strongly equivariant functors and adjunctions

Let `ℵ₁, ℵ₂` be 2-representations of a bicategory `B` and `f ⊣ g` an adjunction in `B`, so that
`ℵᵢ(f) ⊣ ℵᵢ(g)` (`Pseudofunctor.mapAdjunction`). A strongly equivariant functor
`β : ℵ₁ ⟶ ℵ₂` carries the unit of the first adjunction to the unit of the second, up to its
naturality isomorphisms (`map_unit_natApp`). Consequently, for a modification `Γ : β ⟶ β'`,
the adjunction isomorphisms of `ℵ₁` and `ℵ₂` intertwine the maps
`h ↦ β(h) ≫ Γ` (`homEquiv_natApp_map_modification`).

This is the adjunction step in B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v2, proof of Corollary 3.27 (2), which reduces `Hom(F_𝐢 P_∅, N)` to
`Hom(P_∅, E_𝐢 N)`.
-/

namespace Categorification.TwoRep.Generated

open CategoryTheory Bicategory Pseudofunctor.StrongTrans

universe w v u w₁ v₁ u₁

variable {k : Type w} [CommRing k] {B : Type u₁} [Bicategory.{w₁, v₁} B]
  {ℵ₁ ℵ₂ : Pseudofunctor B (LinearCat.{w, v, u} k)} {a c : B} {f : a ⟶ c} {g : c ⟶ a}

/-- The adjunction `ℵ(f) ⊣ ℵ(g)` of functors induced by an adjunction `f ⊣ g` in `B`. -/
noncomputable abbrev mapAdj (ℵ : Pseudofunctor B (LinearCat.{w, v, u} k)) (adj : f ⊣ g) :
    (ℵ.map f).obj ⊣ (ℵ.map g).obj :=
  LinearCat.toAdjunction (ℵ.mapAdjunction adj)

theorem mapAdj_unit_app (ℵ : Pseudofunctor B (LinearCat.{w, v, u} k)) (adj : f ⊣ g)
    (X : ℵ.obj a) :
    (mapAdj ℵ adj).unit.app X =
      (idApp ℵ a X).inv ≫ (ℵ.map₂ adj.unit).hom.app X ≫ (mapCompApp ℵ f g X).hom :=
  rfl

/-- **A strongly equivariant functor preserves units of adjunctions**, up to its naturality
isomorphisms. -/
theorem map_unit_natApp (β : ℵ₁ ⟶ ℵ₂) (adj : f ⊣ g) (X : ℵ₁.obj a) :
    (β.app a).obj.map ((mapAdj ℵ₁ adj).unit.app X) ≫ (natApp β g ((ℵ₁.map f).obj.obj X)).hom ≫
        (ℵ₂.map g).obj.map (natApp β f X).hom =
      (mapAdj ℵ₂ adj).unit.app ((β.app a).obj.obj X) := by
  have NN : (β.app a).obj.map ((ℵ₁.map₂ adj.unit).hom.app X) ≫ (natApp β (f ≫ g) X).hom =
      (natApp β (𝟙 a) X).hom ≫ (ℵ₂.map₂ adj.unit).hom.app ((β.app a).obj.obj X) :=
    congrArg (fun θ => θ.hom.app X) (β.naturality_naturality adj.unit)
  have NC : (natApp β (f ≫ g) X).hom ≫ (mapCompApp ℵ₂ f g ((β.app a).obj.obj X)).hom =
      (β.app a).obj.map (mapCompApp ℵ₁ f g X).hom ≫ 𝟙 _ ≫
        (natApp β g ((ℵ₁.map f).obj.obj X)).hom ≫ 𝟙 _ ≫
          (ℵ₂.map g).obj.map (natApp β f X).hom ≫ 𝟙 _ :=
    congrArg (fun θ => θ.hom.app X) (β.naturality_comp f g)
  have NI : (natApp β (𝟙 a) X).hom ≫ (idApp ℵ₂ a ((β.app a).obj.obj X)).hom =
      (β.app a).obj.map (idApp ℵ₁ a X).hom ≫ 𝟙 _ ≫ 𝟙 _ :=
    congrArg (fun θ => θ.hom.app X) (β.naturality_id a)
  simp only [Category.id_comp, Category.comp_id] at NC NI
  have NI' : (β.app a).obj.map (idApp ℵ₁ a X).inv ≫ (natApp β (𝟙 a) X).hom =
      (idApp ℵ₂ a ((β.app a).obj.obj X)).inv := by
    rw [← Iso.eq_comp_inv] at NI
    rw [NI, ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  rw [mapAdj_unit_app, mapAdj_unit_app, Functor.map_comp, Functor.map_comp, Category.assoc,
    Category.assoc, ← NC, ← Category.assoc ((β.app a).obj.map ((ℵ₁.map₂ adj.unit).hom.app X)),
    NN, ← Category.assoc, ← Category.assoc, NI', Category.assoc]

/-- **Adjunctions intertwine `h ↦ β(h) ≫ Γ`**: for an adjunction `f ⊣ g` in `B`, a
modification `Γ : β ⟶ β'` and `h : ℵ₁(f) X ⟶ Y`, transposing `β(h) ≫ Γ_Y` along
`ℵ₂(f) ⊣ ℵ₂(g)` gives `β(h♭) ≫ Γ_{ℵ₁(g) Y}`, where `h♭` is the transpose of `h` along
`ℵ₁(f) ⊣ ℵ₁(g)`, up to the naturality isomorphisms of `β` and `β'`. -/
theorem homEquiv_natApp_map_modification {β β' : ℵ₁ ⟶ ℵ₂} (Γ : Modification β β')
    (adj : f ⊣ g) {X : ℵ₁.obj a} {Y : ℵ₁.obj c} (h : (ℵ₁.map f).obj.obj X ⟶ Y) :
    (mapAdj ℵ₂ adj).homEquiv _ _
        ((natApp β f X).inv ≫ (β.app c).obj.map h ≫ (Γ.app c).hom.app Y) =
      (β.app a).obj.map ((mapAdj ℵ₁ adj).homEquiv X Y h) ≫
        (Γ.app a).hom.app ((ℵ₁.map g).obj.obj Y) ≫ (natApp β' g Y).hom := by
  have M : (Γ.app a).hom.app ((ℵ₁.map g).obj.obj Y) ≫ (natApp β' g Y).hom =
      (natApp β g Y).hom ≫ (ℵ₂.map g).obj.map ((Γ.app c).hom.app Y) :=
    congrArg (fun θ => θ.hom.app Y) (Γ.naturality g)
  have N' : (β.app a).obj.map ((ℵ₁.map g).obj.map h) ≫ (natApp β g Y).hom =
      (natApp β g ((ℵ₁.map f).obj.obj X)).hom ≫ (ℵ₂.map g).obj.map ((β.app c).obj.map h) :=
    (β.naturality g).hom.hom.naturality h
  rw [M, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, ← map_unit_natApp β adj X]
  simp only [Functor.map_comp, Category.assoc, Iso.map_hom_inv_id_assoc]
  rw [reassoc_of% N']

end Categorification.TwoRep.Generated
