/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.CisBub

/-!
# Bubbles on the source side of a strand

The mirror of `CisBub.lean` for the bottom half (CL Lemma 3.14, eq. `eq:main2`): a bubble
`g : 1_n → 1_n⟨d⟩` is placed on the `1_n`-side of the strand `E 1_n`, i.e. on the *source* side
(Mathlib: `g ▷ X`). For `X : a ⟶ b` and `g : 𝟙 a ⟶ (𝟙 a)⟨d⟩`,

`cisBubR X g : X ⟶ X⟨d⟩ := (λ_ X).inv ≫ (g ▷ X) ≫ (𝟙⟨d⟩ ≫ X ≅ X⟨d⟩)`.

* `cisBubR_natural`: `η ≫ cisBubR X' g = cisBubR X g ≫ η⟨d⟩` (`ShiftInterchange`);
* `eq_zero_of_cisBubR_eq_zero`: for `X = 𝟙⟨s⟩`, `cisBubR X g = 0` forces `g = 0`;
* `shWhiskerRight_cisBubR`: `cisBubR X g ▷ Y = cisBubR (X ≫ Y) g` as shifted 2-morphisms; this needs
  the compatibility of the *right* whiskering shift isomorphisms with the associator, the mixin
  `GradedBicategory.ShiftAssocRight` introduced here (the mirror of `ShiftAssoc`);
* `shWhiskerRight_shPow`, `shWhiskerRight_mk₀_id`.
-/

noncomputable section

namespace Categorification.TwoRep

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Module

universe w v u

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]

/-- **Compatibility of the right whiskering shift isomorphisms with the associator**: the two
identifications `f⟨n⟩ ≫ (g ≫ h) ≅ ((f ≫ g) ≫ h)⟨n⟩` agree (the mirror of `ShiftAssoc`). -/
class GradedBicategory.ShiftAssocRight (B : Type u) [Bicategory.{w, v} B]
    [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B] :
    Prop where
  assoc_shift_right : ∀ {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (n : ℤ),
    (α_ (f⟦n⟧) g h).inv ≫ ((whiskerRightShiftIso f g n).hom ▷ h) ≫
        (whiskerRightShiftIso (f ≫ g) h n).hom =
      (whiskerRightShiftIso f (g ≫ h) n).hom ≫ ((α_ f g h).inv)⟦n⟧'

/-- Naturality of `f⟨n⟩ ≫ g ≅ (f ≫ g)⟨n⟩` in `f` (no coherence needed). -/
theorem whiskerRightShiftIso_natural_left {a b c : B} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c)
    (n : ℤ) : (η⟦n⟧' ▷ g) ≫ (whiskerRightShiftIso f' g n).hom =
      (whiskerRightShiftIso f g n).hom ≫ (η ▷ g)⟦n⟧' := by
  have := ((postcomp a g).commShiftIso n).hom.naturality η
  exact this

/-- The endomorphism of `X` of degree `d` induced by `g : 𝟙 ⟶ 𝟙⟨d⟩` on the source side. -/
def cisBubR {a b : B} (X : a ⟶ b) {d : ℤ} (g : 𝟙 a ⟶ (𝟙 a)⟦d⟧) : X ⟶ X⟦d⟧ :=
  (λ_ X).inv ≫ (g ▷ X) ≫ (idShiftCompIso X d).hom

section Linear

variable {a b : B} (X : a ⟶ b) {d : ℤ}

theorem cisBubR_add (g g' : 𝟙 a ⟶ (𝟙 a)⟦d⟧) : cisBubR X (g + g') = cisBubR X g + cisBubR X g' := by
  simp only [cisBubR, add_whiskerRight, Preadditive.add_comp, Preadditive.comp_add]

theorem cisBubR_zero : cisBubR X (0 : 𝟙 a ⟶ (𝟙 a)⟦d⟧) = 0 := by
  simp only [cisBubR, zero_whiskerRight', zero_comp, comp_zero]

variable (k : Type*) [Field k] [∀ a b : B, Linear k (a ⟶ b)] [GradedBicategory.IsLinear B k]

theorem cisBubR_smul (c : k) (g : 𝟙 a ⟶ (𝟙 a)⟦d⟧) : cisBubR X (c • g) = c • cisBubR X g := by
  simp only [cisBubR, smul_whiskerRight, Linear.smul_comp, Linear.comp_smul]

end Linear

/-- `cisBubR X g` as a shifted 2-morphism. -/
abbrev cisBubRSh {a b : B} (X : a ⟶ b) {d : ℤ} (g : 𝟙 a ⟶ (𝟙 a)⟦d⟧) : ShiftedHom X X d :=
  cisBubR X g

section Coherence

variable [GradedBicategory.ShiftInterchange B]

/-- **Naturality**: `η ≫ cisBubR X' g = cisBubR X g ≫ η⟨d⟩`. -/
theorem cisBubR_natural {a b : B} {X X' : a ⟶ b} (η : X ⟶ X') {d : ℤ} (g : 𝟙 a ⟶ (𝟙 a)⟦d⟧) :
    η ≫ cisBubR X' g = cisBubR X g ≫ η⟦d⟧' := by
  have hN := GradedBicategory.ShiftInterchange.whiskerRightShiftIso_natural (𝟙 a) η d
  simp only [cisBubR, idShiftCompIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc, ← reassoc_of% hN,
    ← Functor.map_comp, ← Functor.map_comp, leftUnitor_naturality]

/-- For `X = 𝟙⟨s⟩`, `cisBubR X g = 0` forces `g = 0`. -/
theorem eq_zero_of_cisBubR_eq_zero {a : B} (s : ℤ) {d : ℤ} (g : 𝟙 a ⟶ (𝟙 a)⟦d⟧)
    (h : cisBubR ((𝟙 a)⟦s⟧) g = 0) : g = 0 := by
  have hN := GradedBicategory.ShiftInterchange.whiskerLeftShiftIso_natural g (𝟙 a) s
  have h1 : g ▷ (𝟙 a)⟦s⟧ = 0 := by
    have := congrArg (fun φ => (λ_ _).hom ≫ φ ≫ (idShiftCompIso _ _).inv) h
    simpa [cisBubR] using this
  have h2 : ((g ▷ 𝟙 a)⟦s⟧' : ((𝟙 a) ≫ 𝟙 a)⟦s⟧ ⟶ ((𝟙 a)⟦d⟧ ≫ 𝟙 a)⟦s⟧) = 0 := by
    rw [← Category.id_comp ((g ▷ 𝟙 a)⟦s⟧'), ← (whiskerLeftShiftIso (𝟙 a) (𝟙 a) s).inv_hom_id,
      Category.assoc, hN, h1, zero_comp, comp_zero]
  have h3 : g ▷ 𝟙 a = 0 := (shiftFunctor _ s).map_injective (by rw [h2, Functor.map_zero])
  have := congrArg (fun φ => (ρ_ _).inv ≫ φ ≫ (ρ_ _).hom) h3
  simpa using this

omit [GradedBicategory.ShiftInterchange B] in
variable [GradedBicategory.ShiftAssocRight B] in
/-- **Bubbles and right whiskering**: `cisBubR X g ▷ Y`, identified with a shifted 2-morphism of
`X ≫ Y`, is `cisBubR (X ≫ Y) g`. -/
theorem shWhiskerRight_cisBubR {a b c : B} (X : a ⟶ b) (Y : b ⟶ c) {d : ℤ}
    (g : 𝟙 a ⟶ (𝟙 a)⟦d⟧) : shWhiskerRight (cisBubRSh X g) Y = cisBubRSh (X ≫ Y) g := by
  have hA := GradedBicategory.ShiftAssocRight.assoc_shift_right (𝟙 a) X Y d
  have hnat := whiskerRightShiftIso_natural_left (λ_ X).hom Y d
  change cisBubR X g ▷ Y ≫ (whiskerRightShiftIso X Y d).hom = cisBubR (X ≫ Y) g
  simp only [cisBubR, idShiftCompIso, Iso.trans_hom, Functor.mapIso_hom, comp_whiskerRight,
    Category.assoc]
  rw [leftUnitor_comp_inv, hnat,
    show g ▷ X ▷ Y = (α_ (𝟙 a) X Y).hom ≫ g ▷ (X ≫ Y) ≫ (α_ _ X Y).inv from by
      rw [Bicategory.whiskerRight_comp]; simp]
  simp only [Category.assoc]
  rw [reassoc_of% hA, ← Functor.map_comp, ← leftUnitor_comp]

end Coherence

/-! ## Shifted right whiskering and powers -/

section Pow

variable {a b c : B} (Y : b ⟶ c)

/-- Shifted right whiskering fixes the identity in degree `0`. -/
theorem shWhiskerRight_mk₀_id {f : a ⟶ b} (m₀ : ℤ) (h : m₀ = 0) :
    shWhiskerRight (ShiftedHom.mk₀ m₀ h (𝟙 f)) Y = ShiftedHom.mk₀ m₀ h (𝟙 (f ≫ Y)) := by
  subst h
  change (ShiftedHom.mk₀ (0 : ℤ) rfl (𝟙 f) ▷ Y) ≫ ((postcomp a Y).commShiftIso (0 : ℤ)).hom.app f =
    ShiftedHom.mk₀ (0 : ℤ) rfl (𝟙 (f ≫ Y))
  rw [Functor.commShiftIso_zero, Functor.CommShift.isoZero_hom_app]
  simp only [ShiftedHom.mk₀, shiftFunctorZero', eqToIso_refl, Iso.refl_trans, Category.id_comp,
    postcomp_map]
  rw [← comp_whiskerRight_assoc, Iso.inv_hom_id_app]
  simp
  rfl

/-- Shifted right whiskering commutes with powers. -/
theorem shWhiskerRight_shPow {f : a ⟶ b} {d : ℤ} (θ : ShiftedHom f f d) :
    ∀ i : ℕ, shWhiskerRight (shPow θ i) Y = shPow (shWhiskerRight θ Y) i
  | 0 => shWhiskerRight_mk₀_id Y _ _
  | i + 1 => by
    rw [shPow, shPow, shWhiskerRight_comp, shWhiskerRight_shPow θ i]

end Pow

end Categorification.TwoRep
