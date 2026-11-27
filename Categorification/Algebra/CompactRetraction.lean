/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DG.Compact.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Compactness and coproducts along a functor with retractions on morphisms

Let `Φ : C ⥤ D` be an additive functor preserving coproducts, with additive retractions
`r : (Φ X ⟶ Φ Y) → (X ⟶ Y)` of `Φ.map` which are natural in the target:
`r (f ≫ Φ b) = r f ≫ b`. If `Φ X` is compact, then so is `X`
(`DG.MapRetraction.isCompact`). Such a `Φ` reflects isomorphisms and zero objects, so a
functor compared with coproduct-preserving functors through `Φ` preserves coproducts
(`DG.preservesColimitsOfShape_of_comparison`).

This is used to transfer compactness from ungraded to graded derived categories, for the graded
braiding functors of B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v3, Definition 6.6 and Theorem 6.15.
-/

universe w v v' u u'

noncomputable section

open CategoryTheory Limits

namespace DG

variable {C : Type u} [Category.{v} C] [Preadditive C] {D : Type u'} [Category.{v'} D]
  [Preadditive D] (Φ : C ⥤ D)

/-- Retractions of `Φ` on morphisms, natural in the source and in the target. -/
structure MapRetraction where
  /-- The retraction. -/
  r : ∀ {X Y : C}, (Φ.obj X ⟶ Φ.obj Y) →+ (X ⟶ Y)
  r_map : ∀ {X Y : C} (g : X ⟶ Y), r (Φ.map g) = g
  r_map_comp : ∀ {X X' Y : C} (a : X' ⟶ X) (f : Φ.obj X ⟶ Φ.obj Y), r (Φ.map a ≫ f) = a ≫ r f
  r_comp_map : ∀ {X Y Y' : C} (f : Φ.obj X ⟶ Φ.obj Y) (b : Y ⟶ Y'), r (f ≫ Φ.map b) = r f ≫ b

variable {Φ}

namespace MapRetraction

variable (ρ : MapRetraction Φ)
include ρ

/-- A functor with retractions on morphisms reflects isomorphisms. -/
theorem isIso_of_isIso_map {X Y : C} (f : X ⟶ Y) [IsIso (Φ.map f)] : IsIso f := by
  refine ⟨ρ.r (inv (Φ.map f)), ?_, ?_⟩
  · rw [← ρ.r_map_comp, IsIso.hom_inv_id, ← Φ.map_id, ρ.r_map]
  · rw [← ρ.r_comp_map, IsIso.inv_hom_id, ← Φ.map_id, ρ.r_map]

/-- A functor with retractions on morphisms reflects isomorphisms. -/
theorem reflectsIsomorphisms : Φ.ReflectsIsomorphisms :=
  ⟨fun f _ => ρ.isIso_of_isIso_map f⟩

/-- A functor with retractions on morphisms reflects zero objects. -/
theorem isZero_of_isZero_obj {X : C} (h : IsZero (Φ.obj X)) : IsZero X := by
  rw [IsZero.iff_id_eq_zero]
  rw [← ρ.r_map (𝟙 X), h.eq_of_src (Φ.map (𝟙 X)) (Φ.map 0), ρ.r_map]

variable [Φ.Additive]

/-- **Compactness along a functor with retractions**: if `Φ` preserves coproducts and `Φ X` is
compact, then `X` is compact. -/
theorem isCompact {X : C} (hΦ : ∀ ι : Type w, PreservesColimitsOfShape (Discrete ι) Φ)
    (hX : IsCompact.{w} (Φ.obj X)) : IsCompact.{w} X := by
  intro ι _ Y _
  have := hΦ ι
  have : HasCoproduct fun i => Φ.obj (Y i) :=
    HasColimit.mk ⟨_, isColimitCofanMkObjOfIsColimit Φ _ _ (coproductIsCoproduct Y)⟩
  let e := (PreservesCoproduct.iso Φ Y).symm
  have he : ∀ i, Sigma.ι (fun i => Φ.obj (Y i)) i ≫ e.hom = Φ.map (Sigma.ι Y i) := fun i =>
    ι_comp_sigmaComparison Φ Y i
  let mapΦ : (DirectSum ι fun i => (X ⟶ Y i)) →+ DirectSum ι fun i => (Φ.obj X ⟶ Φ.obj (Y i)) :=
    DirectSum.map fun i => Φ.mapAddHom
  let mapr : (DirectSum ι fun i => (Φ.obj X ⟶ Φ.obj (Y i))) →+ DirectSum ι fun i => (X ⟶ Y i) :=
    DirectSum.map fun i => ρ.r
  have hrΦ : ∀ a, mapr (mapΦ a) = a := fun a => by
    ext i
    simp [mapr, mapΦ, DirectSum.map_apply, ρ.r_map]
  have hmap : ∀ a, Φ.map (coproductComparison X Y a) =
      coproductComparison (Φ.obj X) (fun i => Φ.obj (Y i)) (mapΦ a) ≫ e.hom := by
    intro a
    induction a using DirectSum.induction_on with
    | zero => simp
    | of i f => simp [mapΦ, DirectSum.map_of, he]
    | add a b ha hb => simp [map_add, ha, hb, Preadditive.add_comp]
  have hr : ∀ b, ρ.r (coproductComparison (Φ.obj X) (fun i => Φ.obj (Y i)) b ≫ e.hom) =
      coproductComparison X Y (mapr b) := by
    intro b
    induction b using DirectSum.induction_on with
    | zero => simp
    | of i f => simp [mapr, DirectSum.map_of, he, ρ.r_comp_map]
    | add a b ha hb => simp [map_add, ha, hb, Preadditive.add_comp]
  constructor
  · intro a b hab
    have h₁ := congrArg Φ.map hab
    rw [hmap, hmap, cancel_mono] at h₁
    rw [← hrΦ a, ← hrΦ b, (hX ι _).1 h₁]
  · intro f
    obtain ⟨b, hb⟩ := (hX ι fun i => Φ.obj (Y i)).2 (Φ.map f ≫ e.inv)
    refine ⟨mapr b, ?_⟩
    rw [← hr, hb, Category.assoc, e.inv_hom_id, Category.comp_id, ρ.r_map]

end MapRetraction

omit [Preadditive C] [Preadditive D] in
/-- **Coproducts transfer along a comparison**: if `F' ⋙ Φ₂ ≅ Φ₁ ⋙ F`, where `Φ₁`, `F` and `Φ₂`
preserve colimits of shape `J` and `Φ₂` reflects isomorphisms, then `F'` preserves colimits of
shape `J`. -/
theorem preservesColimitsOfShape_of_comparison {C' : Type*} [Category C'] {D' : Type*}
    [Category D'] {J : Type*} [Category J] {F' : C' ⥤ D'} {Φ₂ : D' ⥤ D} {Φ₁ : C' ⥤ C}
    {F : C ⥤ D} (σ : F' ⋙ Φ₂ ≅ Φ₁ ⋙ F) [PreservesColimitsOfShape J Φ₁]
    [PreservesColimitsOfShape J F] [PreservesColimitsOfShape J Φ₂] [Φ₂.ReflectsIsomorphisms]
    [HasColimitsOfShape J D'] : PreservesColimitsOfShape J F' := by
  have : PreservesColimitsOfShape J (F' ⋙ Φ₂) := preservesColimitsOfShape_of_natIso σ.symm
  have : ReflectsColimitsOfShape J Φ₂ := reflectsColimitsOfShape_of_reflectsIsomorphisms
  exact preservesColimitsOfShape_of_reflects_of_preserves F' Φ₂

end DG
