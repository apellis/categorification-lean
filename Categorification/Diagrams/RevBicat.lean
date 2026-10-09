/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Bicategory.Basic
import Mathlib.Tactic.CategoryTheory.Bicategory.Basic

/-!
# The 1-cell dual of a bicategory, with the same 2-morphisms

For a bicategory `B`, `RevBicat B` has the objects of `B`, the 1-morphisms `a ⟶ b` are the
1-morphisms `b ⟶ a` of `B`, composition is reversed (`f ≫ g` in `RevBicat B` is `g ≫ f` in `B`),
and the 2-morphisms are literally those of `B` (the hom category `a ⟶ b` of `RevBicat B` *is* the
hom category `b ⟶ a` of `B`). This is Mathlib's `Bᵒᵖ` (`Mathlib.CategoryTheory.Bicategory.Opposites`)
without the wrapper around 2-morphisms, so that structures on the hom categories of `B` (additive,
linear, graded) are inherited definitionally.

It is used to read a presented 2-category (`StringDiagrams.Presentation.Bicat`, whose 1-morphisms
are words read from the left region to the right region) with the convention of Khovanov–Lauda and
Cautis–Lauda, where a 1-morphism goes from the region on the right of a diagram to the region on
its left.
-/

namespace Categorification

open CategoryTheory Bicategory

universe w v u

/-- The 1-cell dual of a bicategory, with the 2-morphisms of `B` unchanged. -/
@[ext]
structure RevBicat (B : Type u) where
  /-- The underlying object. -/
  as : B

namespace RevBicat

variable {B : Type u} [Bicategory.{w, v} B]

instance bicategory : Bicategory.{w, v} (RevBicat B) where
  Hom a b := b.as ⟶ a.as
  id a := 𝟙 a.as
  comp f g := g ≫ f
  homCategory a b := inferInstanceAs (Category (b.as ⟶ a.as))
  whiskerLeft f _ _ η := η ▷ f
  whiskerRight η h := h ◁ η
  associator f g h := (α_ h g f).symm
  leftUnitor f := ρ_ f
  rightUnitor f := λ_ f
  whiskerLeft_id f g := id_whiskerRight g f
  whiskerLeft_comp f _ _ _ η θ := comp_whiskerRight η θ f
  id_whiskerLeft η := whiskerRight_id η
  comp_whiskerLeft f g _ _ η := whiskerRight_comp η g f
  id_whiskerRight f g := whiskerLeft_id g f
  comp_whiskerRight η θ i := whiskerLeft_comp i η θ
  whiskerRight_id η := id_whiskerLeft η
  whiskerRight_comp η g h := comp_whiskerLeft h g η
  whisker_assoc f _ _ η h := by
    change h ◁ η ▷ f = (α_ h _ f).inv ≫ (h ◁ η) ▷ f ≫ (α_ h _ f).hom
    simp
  whisker_exchange η θ := (whisker_exchange θ η).symm
  pentagon f g h i := by
    change i ◁ (α_ h g f).inv ≫ (α_ i (h ≫ g) f).inv ≫ (α_ i h g).inv ▷ f =
      (α_ i h (g ≫ f)).inv ≫ (α_ (i ≫ h) g f).inv
    simp
  triangle f g := by
    change (α_ g (𝟙 _) f).inv ≫ (ρ_ g).hom ▷ f = g ◁ (λ_ f).hom
    simp

variable {a b c d : RevBicat B}

/-- A 1-morphism of `B` as a 1-morphism of `RevBicat B` in the opposite direction. -/
abbrev of {x y : B} (f : x ⟶ y) : (⟨y⟩ : RevBicat B) ⟶ ⟨x⟩ := f

theorem comp_def (f : a ⟶ b) (g : b ⟶ c) : f ≫ g = (g ≫ f : c.as ⟶ a.as) := rfl

theorem id_def (a : RevBicat B) : 𝟙 a = (𝟙 a.as : a.as ⟶ a.as) := rfl

theorem whiskerLeft_def (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) :
    f ◁ η = @Bicategory.whiskerRight B _ c.as b.as a.as g h η f := rfl

theorem whiskerRight_def {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) :
    η ▷ h = @Bicategory.whiskerLeft B _ c.as b.as a.as h f g η := rfl

theorem associator_hom_def (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (α_ f g h).hom = (@Bicategory.associator B _ d.as c.as b.as a.as h g f).inv := rfl

theorem associator_inv_def (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (α_ f g h).inv = (@Bicategory.associator B _ d.as c.as b.as a.as h g f).hom := rfl

theorem leftUnitor_hom_def (f : a ⟶ b) :
    (λ_ f).hom = (@Bicategory.rightUnitor B _ b.as a.as f).hom := rfl

theorem leftUnitor_inv_def (f : a ⟶ b) :
    (λ_ f).inv = (@Bicategory.rightUnitor B _ b.as a.as f).inv := rfl

theorem rightUnitor_hom_def (f : a ⟶ b) :
    (ρ_ f).hom = (@Bicategory.leftUnitor B _ b.as a.as f).hom := rfl

theorem rightUnitor_inv_def (f : a ⟶ b) :
    (ρ_ f).inv = (@Bicategory.leftUnitor B _ b.as a.as f).inv := rfl

end RevBicat

end Categorification
