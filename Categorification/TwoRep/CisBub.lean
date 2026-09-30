/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.LemAprime

/-!
# Endomorphisms of a 1-morphism induced by endomorphisms of an identity 1-morphism

CL's Lemma 3.14 (`lem:main`) writes endomorphisms of `E 1_n` as sums of "dots times bubbles",
where a *bubble* is an endomorphism `g : 1_{n+2} → 1_{n+2}⟨d⟩` of the identity 1-morphism placed
next to the strand `E 1_n`. For a 1-morphism `X : a ⟶ b` and `g : 𝟙 b ⟶ (𝟙 b)⟨d⟩` this is

`cisBub X g : X ⟶ X⟨d⟩ := (ρ_ X).inv ≫ (X ◁ g) ≫ (X ≫ 𝟙⟨d⟩ ≅ X⟨d⟩)`.

Its formal properties, under the two coherence mixins `ShiftInterchange` and `ShiftAssoc`:

* `cisBub_natural`: `η ≫ cisBub X' g = cisBub X g ≫ η⟨d⟩` for `η : X ⟶ X'` (interchange);
* `shWhiskerLeft_cisBub`: `F ◁ cisBub X g = cisBub (F ≫ X) g` as shifted 2-morphisms (associator
  coherence);
* `cisBub_eq_zero_iff`: for `X = 𝟙⟨s⟩`, `cisBub X g = 0` iff `g = 0`;
* linearity `cisBub_add`, `cisBub_smul`, `cisBub_zero`;
* `shWhiskerLeft_shPow`, `shWhiskerLeft_mk₀_id`: shifted left whiskering commutes with powers.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Module

universe w v u

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]

/-- The endomorphism of `X` of degree `d` induced by `g : 𝟙 ⟶ 𝟙⟨d⟩` ("a bubble next to `X`"). -/
def cisBub {a b : B} (X : a ⟶ b) {d : ℤ} (g : 𝟙 b ⟶ (𝟙 b)⟦d⟧) : X ⟶ X⟦d⟧ :=
  (ρ_ X).inv ≫ (X ◁ g) ≫ (compIdShiftIso X d).hom

section Linear

variable {a b : B} (X : a ⟶ b) {d : ℤ}

theorem cisBub_add (g g' : 𝟙 b ⟶ (𝟙 b)⟦d⟧) : cisBub X (g + g') = cisBub X g + cisBub X g' := by
  simp only [cisBub, whiskerLeft_add, Preadditive.add_comp, Preadditive.comp_add]

theorem cisBub_zero : cisBub X (0 : 𝟙 b ⟶ (𝟙 b)⟦d⟧) = 0 := by
  simp only [cisBub, whiskerLeft_zero', zero_comp, comp_zero]

variable (k : Type*) [Field k] [∀ a b : B, Linear k (a ⟶ b)] [GradedBicategory.IsLinear B k]

theorem cisBub_smul (c : k) (g : 𝟙 b ⟶ (𝟙 b)⟦d⟧) : cisBub X (c • g) = c • cisBub X g := by
  simp only [cisBub, whiskerLeft_smul, Linear.smul_comp, Linear.comp_smul]

end Linear

/-- `cisBub X g` as a shifted 2-morphism. -/
abbrev cisBubSh {a b : B} (X : a ⟶ b) {d : ℤ} (g : 𝟙 b ⟶ (𝟙 b)⟦d⟧) : ShiftedHom X X d :=
  cisBub X g

section Coherence

variable [GradedBicategory.ShiftInterchange B]

/-- **Naturality of bubbles**: `η ≫ cisBub X' g = cisBub X g ≫ η⟨d⟩`. -/
theorem cisBub_natural {a b : B} {X X' : a ⟶ b} (η : X ⟶ X') {d : ℤ} (g : 𝟙 b ⟶ (𝟙 b)⟦d⟧) :
    η ≫ cisBub X' g = cisBub X g ≫ η⟦d⟧' := by
  have hN := GradedBicategory.ShiftInterchange.whiskerLeftShiftIso_natural η (𝟙 b) d
  simp only [cisBub, compIdShiftIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc, ← reassoc_of% hN,
    ← Functor.map_comp, ← Functor.map_comp, rightUnitor_naturality]

/-- For `X = 𝟙⟨s⟩` (a shift of an identity), `cisBub X g = 0` forces `g = 0`. -/
theorem eq_zero_of_cisBub_eq_zero {b : B} (s : ℤ) {d : ℤ} (g : 𝟙 b ⟶ (𝟙 b)⟦d⟧)
    (h : cisBub ((𝟙 b)⟦s⟧) g = 0) : g = 0 := by
  have hN := GradedBicategory.ShiftInterchange.whiskerRightShiftIso_natural (𝟙 b) g s
  -- `𝟙⟨s⟩ ◁ g = 0`
  have h1 : (𝟙 b)⟦s⟧ ◁ g = 0 := by
    have := congrArg (fun φ => (ρ_ _).hom ≫ φ ≫ (compIdShiftIso _ _).inv) h
    simpa [cisBub] using this
  -- hence `(𝟙 ◁ g)⟨s⟩ = 0`, hence `𝟙 ◁ g = 0`
  have h2 : ((𝟙 b ◁ g)⟦s⟧' : ((𝟙 b) ≫ 𝟙 b)⟦s⟧ ⟶ ((𝟙 b) ≫ (𝟙 b)⟦d⟧)⟦s⟧) = 0 := by
    rw [← Category.id_comp ((𝟙 b ◁ g)⟦s⟧'), ← (whiskerRightShiftIso (𝟙 b) (𝟙 b) s).inv_hom_id,
      Category.assoc, hN, h1, zero_comp, comp_zero]
  have h3 : 𝟙 b ◁ g = 0 := (shiftFunctor _ s).map_injective (by rw [h2, Functor.map_zero])
  have := congrArg (fun φ => (λ_ _).inv ≫ φ ≫ (λ_ _).hom) h3
  simpa using this

variable [GradedBicategory.ShiftAssoc B]

omit [GradedBicategory.ShiftInterchange B] in
/-- **Bubbles and whiskering**: `F ◁ cisBub X g`, identified with a shifted 2-morphism of `F ≫ X`,
is `cisBub (F ≫ X) g`. -/
theorem shWhiskerLeft_cisBub {a b c : B} (F : a ⟶ b) (X : b ⟶ c) {d : ℤ} (g : 𝟙 c ⟶ (𝟙 c)⟦d⟧) :
    shWhiskerLeft F (cisBubSh X g) = cisBubSh (F ≫ X) g := by
  have hA := GradedBicategory.ShiftAssoc.assoc_shift F X (𝟙 c) d
  have hnat := whiskerLeftShiftIso_natural_right F (ρ_ X).hom d
  change F ◁ cisBub X g ≫ (whiskerLeftShiftIso F X d).hom = cisBub (F ≫ X) g
  simp only [cisBub, compIdShiftIso, Iso.trans_hom, Functor.mapIso_hom, Bicategory.whiskerLeft_comp,
    Category.assoc]
  rw [whiskerLeft_rightUnitor_inv, Category.assoc, ← associator_naturality_right_assoc,
    ← Iso.hom_inv_id_assoc (whiskerLeftShiftIso F (X ≫ 𝟙 c) d) (F ◁ (ρ_ X).hom⟦d⟧')]
  simp only [Category.assoc]
  rw [reassoc_of% hA, reassoc_of% hnat, ← Functor.map_comp_assoc, ← rightUnitor_comp,
    Iso.inv_hom_id, Category.comp_id]

end Coherence

/-! ## Shifted whiskering and powers -/

section Pow

variable {a b c : B} (F : a ⟶ b)

set_option backward.isDefEq.respectTransparency false in
/-- Shifted left whiskering fixes the identity in degree `0`. -/
theorem shWhiskerLeft_mk₀_id {g : b ⟶ c} (m₀ : ℤ) (h : m₀ = 0) :
    shWhiskerLeft F (ShiftedHom.mk₀ m₀ h (𝟙 g)) = ShiftedHom.mk₀ m₀ h (𝟙 (F ≫ g)) := by
  subst h
  change (F ◁ ShiftedHom.mk₀ (0 : ℤ) rfl (𝟙 g)) ≫ ((precomp c F).commShiftIso (0 : ℤ)).hom.app g =
    ShiftedHom.mk₀ (0 : ℤ) rfl (𝟙 (F ≫ g))
  rw [Functor.commShiftIso_zero, Functor.CommShift.isoZero_hom_app]
  simp only [ShiftedHom.mk₀, shiftFunctorZero', eqToIso_refl, Iso.refl_trans, Category.id_comp,
    precomp_map]
  rw [← Bicategory.whiskerLeft_comp_assoc, Iso.inv_hom_id_app]
  simp
  rfl

/-- Shifted left whiskering commutes with powers. -/
theorem shWhiskerLeft_shPow {g : b ⟶ c} {d : ℤ} (θ : ShiftedHom g g d) :
    ∀ i : ℕ, shWhiskerLeft F (shPow θ i) = shPow (shWhiskerLeft F θ) i
  | 0 => shWhiskerLeft_mk₀_id F _ _
  | i + 1 => by
    rw [shPow, shPow, shWhiskerLeft_comp, shWhiskerLeft_shPow θ i]

end Pow

end Categorification.TwoRep
