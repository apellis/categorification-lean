/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Mathlib.CategoryTheory.Preadditive.Basic
import Categorification.TwoRep.Zigzag

/-!
# The rightward crossing and the second adjunction at weights `0` and `-2`: formal part

Let `E_μ : μ → μ + 2` be 1-morphisms of a bicategory with (candidate) right adjoints `R_μ`, units
`η_μ : 𝟙 → R_μ E_μ`, counits `ε_μ : E_μ R_μ → 𝟙`, and 2-morphisms `τ_μ` on `E_{μ+2} E_μ` (the
crossing) and `x_μ` on `E_μ` (the dot). This is the data of a 2-representation of `sl₂` in the
sense of Rouquier, or of S. Cautis and A. D. Lauda, *Implicit structure in 2-representations of
quantum groups*, arXiv:1111.1431v3, Definition 1.2, with all gradings forgotten (the homogeneous
2-morphisms of all degrees of a graded 2-category form a bicategory, `GradedHomBicategory.lean`).
This file proves, by relation chasing in an arbitrary bicategory with preadditive Hom categories,
that the 1-morphism `R_μ` is also *left* adjoint to `E_μ` for `μ ∈ {0, -2}` as soon as Rouquier's
maps `ρ_{±2}` and `ρ_0` are invertible, as far as the zigzag identity for `E_μ` is concerned.
The argument is that of J. Brundan, *On the definition of Kac–Moody 2-category*,
arXiv:1501.00350v1 (Lemma 4.2 and Theorem 4.3), specialized to the weights `0` and `-2`, where
no bubbles occur; see also CL §3 and the README for why these two weights need a separate
argument in the proof of CL Proposition 3.9.

**Composition order.** As everywhere in this development, composition is written in Mathlib's
diagrammatic order: the composite written `E_λ E_{λ-2}` in the sources is `E₁ ≫ E₂` here
(`E₁ = E_{λ-2}`, `E₂ = E_λ`); a 2-morphism `X φ` of the sources (`φ` on the right-hand factor) is
`φ ▷ X`, and `φ X` is `X ◁ φ`.

## Main declarations

* `AdditiveWhiskering`: whiskering is additive (mixin for bicategories with preadditive Hom
  categories);
* `RightwardCrossing.sigma η₂ τ ε₁ : R₁ ≫ E₁ ⟶ E₂ ≫ R₂`: the rightward crossing
  `σ_λ : E_{λ-2} R_{λ-2} → R_λ E_λ` (Brundan (1.6); `λ` is the weight of the middle object);
* `pitchfork_cap`, `pitchfork_cup`: sliding a crossing through a counit or a unit (these use one
  zigzag identity of `E ⊣ R` only);
* `sigma_sigma`, `mixed_braid`: the composite of two rightward crossings, and the braid relation
  between two rightward crossings and an upward crossing (from the braid relation of `τ`);
* `tau_dot_tau_left`, `tau_dot_tau_right`: `τ x₁ τ = τ` and `τ x₂ τ = -τ` in the nilHecke algebra;
* `whiskerLeft_unit_eq`, `rightZigzag_zero`: weight `0`. If `σ_0` is invertible and
  `ρ_2 = (σ_2, ε, ε ∘ x)` is invertible, the last component `u₁` of `ρ_2⁻¹` and `ε ∘ σ_0⁻¹`
  satisfy the zigzag identity for `E_0`;
* `counit_whiskerRight_eq`, `rightZigzag_neg_two`: weight `-2`. If `σ_0` is invertible and
  `ρ_{-2} = (σ_{-2}, η, x ∘ η)` is invertible, `-σ_0⁻¹ ∘ η` and the last component `w₁` of
  `ρ_{-2}⁻¹` satisfy the zigzag identity for `E_{-2}`;
* `leftZigzag_idempotent_of_right_triangle`, `adjunctionOfRightTriangle`: the one-zigzag lemma.
  If `η`, `ε` satisfy the zigzag identity for the right adjoint `g`, the other zigzag is an
  idempotent endomorphism of `f`; if `End(f)` has no idempotents other than `0` and `1` and
  `g ≠ 0`, then `f ⊣ g`.
-/

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Bicategory

universe w v u

/-- **Whiskering is additive**: mixin for a bicategory whose Hom categories are preadditive. -/
class AdditiveWhiskering (C : Type u) [Bicategory.{w, v} C] [∀ a b : C, Preadditive (a ⟶ b)] :
    Prop where
  whiskerLeft_add : ∀ {a b c : C} (f : a ⟶ b) {g h : b ⟶ c} (η θ : g ⟶ h),
    f ◁ (η + θ) = f ◁ η + f ◁ θ
  add_whiskerRight : ∀ {a b c : C} {f g : a ⟶ b} (η θ : f ⟶ g) (h : b ⟶ c),
    (η + θ) ▷ h = η ▷ h + θ ▷ h

namespace AdditiveWhiskering

variable {C : Type u} [Bicategory.{w, v} C] [∀ a b : C, Preadditive (a ⟶ b)]
  [AdditiveWhiskering C] {a b c : C}

/-- Left whiskering as an additive map. -/
def whiskerLeftAddHom (f : a ⟶ b) (g h : b ⟶ c) : (g ⟶ h) →+ (f ≫ g ⟶ f ≫ h) :=
  AddMonoidHom.mk' (fun η => f ◁ η) (whiskerLeft_add f)

/-- Right whiskering as an additive map. -/
def whiskerRightAddHom (f g : a ⟶ b) (h : b ⟶ c) : (f ⟶ g) →+ (f ≫ h ⟶ g ≫ h) :=
  AddMonoidHom.mk' (fun η => η ▷ h) (fun η θ => add_whiskerRight η θ h)

theorem whiskerLeft_zero (f : a ⟶ b) (g h : b ⟶ c) : f ◁ (0 : g ⟶ h) = 0 :=
  map_zero (whiskerLeftAddHom f g h)

theorem zero_whiskerRight (f g : a ⟶ b) (h : b ⟶ c) : (0 : f ⟶ g) ▷ h = 0 :=
  map_zero (whiskerRightAddHom f g h)

theorem whiskerLeft_neg (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) : f ◁ (-η) = -(f ◁ η) :=
  map_neg (whiskerLeftAddHom f g h) η

theorem neg_whiskerRight {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) : (-η) ▷ h = -(η ▷ h) :=
  map_neg (whiskerRightAddHom f g h) η

end AdditiveWhiskering

namespace RightwardCrossing

/-! ## The nilHecke relations `τ x τ = ± τ` -/

section NilHecke

variable {D : Type*} [Category D] [Preadditive D] {X : D}

/-- `τ x₁ τ = τ` in the nilHecke algebra: if `τ² = 0` and `p τ - τ q = 1` (composition in
diagrammatic order) then `τ p τ = τ`. -/
theorem tau_dot_tau_left (t p q : X ⟶ X) (hsq : t ≫ t = 0) (hs : p ≫ t - t ≫ q = 𝟙 X) :
    t ≫ p ≫ t = t := by
  have h : p ≫ t = 𝟙 X + t ≫ q := by rw [← hs, sub_add_cancel]
  rw [h, Preadditive.comp_add, Category.comp_id, ← Category.assoc, hsq, Limits.zero_comp,
    add_zero]

/-- `τ x₂ τ = -τ` in the nilHecke algebra: if `τ² = 0` and `p τ - τ q = 1` then `τ q τ = -τ`. -/
theorem tau_dot_tau_right (t p q : X ⟶ X) (hsq : t ≫ t = 0) (hs : p ≫ t - t ≫ q = 𝟙 X) :
    t ≫ q ≫ t = -t := by
  have h : t ≫ q = p ≫ t - 𝟙 X := by rw [← hs, sub_sub_cancel]
  rw [← Category.assoc, h, Preadditive.sub_comp, Category.assoc, hsq, Limits.comp_zero,
    Category.id_comp, zero_sub]

end NilHecke

variable {C : Type u} [Bicategory.{w, v} C]

/-! ## The rightward crossing and the pitchfork relations -/

section Sigma

variable {a b c : C} {E₁ : a ⟶ b} {E₂ : b ⟶ c} {R₁ : b ⟶ a} {R₂ : c ⟶ b}

/-- **The rightward crossing** `σ_λ : E_{λ-2} R_{λ-2} → R_λ E_λ` (Brundan (1.6)): insert the unit
`η_λ` on the left, cross the two upward strands, and close with the counit `ε_{λ-2}` on the right.
In diagrammatic order, with `E₁ = E_{λ-2}`, `E₂ = E_λ`: a 2-morphism `R₁ ≫ E₁ ⟶ E₂ ≫ R₂`. -/
def sigma (η₂ : 𝟙 b ⟶ E₂ ≫ R₂) (τ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) (ε₁ : R₁ ≫ E₁ ⟶ 𝟙 b) :
    R₁ ≫ E₁ ⟶ E₂ ≫ R₂ :=
  𝟙 _ ⊗≫ (R₁ ≫ E₁) ◁ η₂ ⊗≫ R₁ ◁ τ ▷ R₂ ⊗≫ ε₁ ▷ (E₂ ≫ R₂) ⊗≫ 𝟙 _

theorem sigma_def (η₂ : 𝟙 b ⟶ E₂ ≫ R₂) (τ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) (ε₁ : R₁ ≫ E₁ ⟶ 𝟙 b) :
    sigma η₂ τ ε₁ = 𝟙 _ ⊗≫ (R₁ ≫ E₁) ◁ η₂ ⊗≫ R₁ ◁ τ ▷ R₂ ⊗≫ ε₁ ▷ (E₂ ≫ R₂) ⊗≫ 𝟙 _ :=
  rfl

/-- The rightward crossing with all associators and unitors written out. -/
theorem sigma_eq (η₂ : 𝟙 b ⟶ E₂ ≫ R₂) (τ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) (ε₁ : R₁ ≫ E₁ ⟶ 𝟙 b) :
    sigma η₂ τ ε₁ = (ρ_ (R₁ ≫ E₁)).inv ≫ (R₁ ≫ E₁) ◁ η₂ ≫ (α_ R₁ E₁ (E₂ ≫ R₂)).hom ≫
      R₁ ◁ (α_ E₁ E₂ R₂).inv ≫ R₁ ◁ τ ▷ R₂ ≫ R₁ ◁ (α_ E₁ E₂ R₂).hom ≫
      (α_ R₁ E₁ (E₂ ≫ R₂)).inv ≫ ε₁ ▷ (E₂ ≫ R₂) ≫ (λ_ (E₂ ≫ R₂)).hom := by
  rw [sigma_def]; bicategory

/-- **Pitchfork (cap)**: `(ε_μ E_μ) ∘ (E_μ σ_μ) = (E_μ ε_{μ-2}) ∘ (τ_{μ-2} R_{μ-2})`. Only the
zigzag identity of `E_μ` is used. -/
theorem pitchfork_cap (η₂ : 𝟙 b ⟶ E₂ ≫ R₂) (ε₂ : R₂ ≫ E₂ ⟶ 𝟙 c) (τ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂)
    (ε₁ : R₁ ≫ E₁ ⟶ 𝟙 b) (hZ : leftZigzag η₂ ε₂ = (λ_ E₂).hom ≫ (ρ_ E₂).inv) :
    sigma η₂ τ ε₁ ▷ E₂ ⊗≫ E₂ ◁ ε₂ = 𝟙 _ ⊗≫ R₁ ◁ τ ⊗≫ ε₁ ▷ E₂ ⊗≫ 𝟙 _ := by
  calc sigma η₂ τ ε₁ ▷ E₂ ⊗≫ E₂ ◁ ε₂
      = 𝟙 _ ⊗≫ (R₁ ≫ E₁) ◁ η₂ ▷ E₂ ⊗≫ R₁ ◁ τ ▷ R₂ ▷ E₂ ⊗≫
          (ε₁ ▷ (E₂ ≫ R₂ ≫ E₂) ≫ 𝟙 b ◁ E₂ ◁ ε₂) ⊗≫ 𝟙 _ := by
        rw [sigma_def]; bicategory
    _ = 𝟙 _ ⊗≫ (R₁ ≫ E₁) ◁ η₂ ▷ E₂ ⊗≫ R₁ ◁ (τ ▷ (R₂ ≫ E₂) ≫ (E₁ ≫ E₂) ◁ ε₂) ⊗≫
          ε₁ ▷ E₂ ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange]; bicategory
    _ = 𝟙 _ ⊗≫ (R₁ ≫ E₁) ◁ leftZigzag η₂ ε₂ ⊗≫ R₁ ◁ τ ⊗≫ ε₁ ▷ E₂ ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange, leftZigzag]; bicategory
    _ = 𝟙 _ ⊗≫ R₁ ◁ τ ⊗≫ ε₁ ▷ E₂ ⊗≫ 𝟙 _ := by
        rw [hZ]; bicategory

/-- **Pitchfork (cup)**: `(σ_{μ+2} E_μ) ∘ (E_μ η_μ) = (R_{μ+2} τ_μ) ∘ (η_{μ+2} E_μ)`. Only the
zigzag identity of `E_μ` is used. Here `E₁ = E_μ`, `E₂ = E_{μ+2}`. -/
theorem pitchfork_cup (η₁ : 𝟙 a ⟶ E₁ ≫ R₁) (ε₁ : R₁ ≫ E₁ ⟶ 𝟙 b) (η₂ : 𝟙 b ⟶ E₂ ≫ R₂)
    (τ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) (hZ : leftZigzag η₁ ε₁ = (λ_ E₁).hom ≫ (ρ_ E₁).inv) :
    η₁ ▷ E₁ ⊗≫ E₁ ◁ sigma η₂ τ ε₁ = 𝟙 _ ⊗≫ E₁ ◁ η₂ ⊗≫ τ ▷ R₂ ⊗≫ 𝟙 _ := by
  calc η₁ ▷ E₁ ⊗≫ E₁ ◁ sigma η₂ τ ε₁
      = 𝟙 _ ⊗≫ (η₁ ▷ (E₁ ≫ 𝟙 b) ≫ (E₁ ≫ R₁) ◁ E₁ ◁ η₂) ⊗≫ E₁ ◁ R₁ ◁ τ ▷ R₂ ⊗≫
          E₁ ◁ ε₁ ▷ (E₂ ≫ R₂) ⊗≫ 𝟙 _ := by
        rw [sigma_def]; bicategory
    _ = 𝟙 _ ⊗≫ E₁ ◁ η₂ ⊗≫ (η₁ ▷ ((E₁ ≫ E₂) ≫ R₂) ≫ (E₁ ≫ R₁) ◁ τ ▷ R₂) ⊗≫
          E₁ ◁ ε₁ ▷ (E₂ ≫ R₂) ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange]; bicategory
    _ = 𝟙 _ ⊗≫ E₁ ◁ η₂ ⊗≫ τ ▷ R₂ ⊗≫ leftZigzag η₁ ε₁ ▷ (E₂ ≫ R₂) ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange, leftZigzag]; bicategory
    _ = 𝟙 _ ⊗≫ E₁ ◁ η₂ ⊗≫ τ ▷ R₂ ⊗≫ 𝟙 _ := by
        rw [hZ]; bicategory

end Sigma

/-! ## Two rightward crossings -/

section Braid

variable {a b c d : C} {E₁ : a ⟶ b} {E₂ : b ⟶ c} {E₃ : c ⟶ d} {R₁ : b ⟶ a} {R₂ : c ⟶ b}
  {R₃ : d ⟶ c}

/-- **The composite of two rightward crossings** `(σ_{μ+2} E_μ) ∘ (E_μ σ_μ)`: insert the unit
`η_{μ+2}`, apply the two upward crossings on `E_{μ+2} E_μ E_{μ-2}` (first the one on the left
pair, then the one on the right pair), and close with the counit `ε_{μ-2}`. Here `E₁ = E_{μ-2}`,
`E₂ = E_μ`, `E₃ = E_{μ+2}`. -/
theorem sigma_sigma (η₂ : 𝟙 b ⟶ E₂ ≫ R₂) (ε₂ : R₂ ≫ E₂ ⟶ 𝟙 c) (τ₁₂ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂)
    (ε₁ : R₁ ≫ E₁ ⟶ 𝟙 b) (η₃ : 𝟙 c ⟶ E₃ ≫ R₃) (τ₂₃ : E₂ ≫ E₃ ⟶ E₂ ≫ E₃)
    (hZ : leftZigzag η₂ ε₂ = (λ_ E₂).hom ≫ (ρ_ E₂).inv) :
    sigma η₂ τ₁₂ ε₁ ▷ E₂ ⊗≫ E₂ ◁ sigma η₃ τ₂₃ ε₂ =
      𝟙 _ ⊗≫ (R₁ ≫ E₁ ≫ E₂) ◁ η₃ ⊗≫ R₁ ◁ E₁ ◁ τ₂₃ ▷ R₃ ⊗≫ R₁ ◁ τ₁₂ ▷ E₃ ▷ R₃ ⊗≫
        ε₁ ▷ (E₂ ≫ E₃ ≫ R₃) ⊗≫ 𝟙 _ := by
  calc sigma η₂ τ₁₂ ε₁ ▷ E₂ ⊗≫ E₂ ◁ sigma η₃ τ₂₃ ε₂
      = 𝟙 _ ⊗≫ ((sigma η₂ τ₁₂ ε₁ ▷ E₂) ▷ 𝟙 c ≫ ((E₂ ≫ R₂) ≫ E₂) ◁ η₃) ⊗≫
          E₂ ◁ R₂ ◁ τ₂₃ ▷ R₃ ⊗≫ E₂ ◁ ε₂ ▷ (E₃ ≫ R₃) ⊗≫ 𝟙 _ := by
        rw [sigma_def η₃ τ₂₃ ε₂]; bicategory
    _ = 𝟙 _ ⊗≫ ((R₁ ≫ E₁) ≫ E₂) ◁ η₃ ⊗≫
          (sigma η₂ τ₁₂ ε₁ ▷ ((E₂ ≫ E₃) ≫ R₃) ≫ (E₂ ≫ R₂) ◁ τ₂₃ ▷ R₃) ⊗≫
          E₂ ◁ ε₂ ▷ (E₃ ≫ R₃) ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange]; bicategory
    _ = 𝟙 _ ⊗≫ (R₁ ≫ E₁ ≫ E₂) ◁ η₃ ⊗≫ R₁ ◁ E₁ ◁ τ₂₃ ▷ R₃ ⊗≫
          (sigma η₂ τ₁₂ ε₁ ▷ E₂ ⊗≫ E₂ ◁ ε₂) ▷ (E₃ ≫ R₃) ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange]; bicategory
    _ = 𝟙 _ ⊗≫ (R₁ ≫ E₁ ≫ E₂) ◁ η₃ ⊗≫ R₁ ◁ E₁ ◁ τ₂₃ ▷ R₃ ⊗≫ R₁ ◁ τ₁₂ ▷ E₃ ▷ R₃ ⊗≫
          ε₁ ▷ (E₂ ≫ E₃ ≫ R₃) ⊗≫ 𝟙 _ := by
        rw [pitchfork_cap η₂ ε₂ τ₁₂ ε₁ hZ]; bicategory

/-- **The mixed braid relation** (Brundan (2.4) for equal colours):
`(σ_{μ+2} E_μ) ∘ (E_μ σ_μ) ∘ (τ_{μ-2} R_{μ-2}) = (R_{μ+2} τ_μ) ∘ (σ_{μ+2} E_μ) ∘ (E_μ σ_μ)`.
It follows from `sigma_sigma` and the braid relation `hB` for the upward crossings on
`E_{μ+2} E_μ E_{μ-2}`. -/
theorem mixed_braid (η₂ : 𝟙 b ⟶ E₂ ≫ R₂) (ε₂ : R₂ ≫ E₂ ⟶ 𝟙 c) (τ₁₂ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂)
    (ε₁ : R₁ ≫ E₁ ⟶ 𝟙 b) (η₃ : 𝟙 c ⟶ E₃ ≫ R₃) (τ₂₃ : E₂ ≫ E₃ ⟶ E₂ ≫ E₃)
    (hZ : leftZigzag η₂ ε₂ = (λ_ E₂).hom ≫ (ρ_ E₂).inv)
    (hB : E₁ ◁ τ₂₃ ≫ ((α_ E₁ E₂ E₃).inv ≫ τ₁₂ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom) ≫ E₁ ◁ τ₂₃ =
      ((α_ E₁ E₂ E₃).inv ≫ τ₁₂ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom) ≫ E₁ ◁ τ₂₃ ≫
        ((α_ E₁ E₂ E₃).inv ≫ τ₁₂ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom)) :
    𝟙 _ ⊗≫ R₁ ◁ τ₁₂ ⊗≫ (sigma η₂ τ₁₂ ε₁ ▷ E₂ ⊗≫ E₂ ◁ sigma η₃ τ₂₃ ε₂) =
      (sigma η₂ τ₁₂ ε₁ ▷ E₂ ⊗≫ E₂ ◁ sigma η₃ τ₂₃ ε₂) ⊗≫ τ₂₃ ▷ R₃ ⊗≫ 𝟙 _ := by
  have hB' : (E₁ ◁ τ₂₃ ⊗≫ τ₁₂ ▷ E₃ ⊗≫ E₁ ◁ τ₂₃ : E₁ ≫ E₂ ≫ E₃ ⟶ E₁ ≫ E₂ ≫ E₃) =
      𝟙 _ ⊗≫ τ₁₂ ▷ E₃ ⊗≫ E₁ ◁ τ₂₃ ⊗≫ τ₁₂ ▷ E₃ ⊗≫ 𝟙 _ := by
    calc (E₁ ◁ τ₂₃ ⊗≫ τ₁₂ ▷ E₃ ⊗≫ E₁ ◁ τ₂₃ : E₁ ≫ E₂ ≫ E₃ ⟶ E₁ ≫ E₂ ≫ E₃)
        = E₁ ◁ τ₂₃ ≫ ((α_ E₁ E₂ E₃).inv ≫ τ₁₂ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom) ≫ E₁ ◁ τ₂₃ := by
          bicategory
      _ = ((α_ E₁ E₂ E₃).inv ≫ τ₁₂ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom) ≫ E₁ ◁ τ₂₃ ≫
            ((α_ E₁ E₂ E₃).inv ≫ τ₁₂ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom) := hB
      _ = 𝟙 _ ⊗≫ τ₁₂ ▷ E₃ ⊗≫ E₁ ◁ τ₂₃ ⊗≫ τ₁₂ ▷ E₃ ⊗≫ 𝟙 _ := by
          bicategory
  calc 𝟙 _ ⊗≫ R₁ ◁ τ₁₂ ⊗≫ (sigma η₂ τ₁₂ ε₁ ▷ E₂ ⊗≫ E₂ ◁ sigma η₃ τ₂₃ ε₂)
      = 𝟙 _ ⊗≫ ((R₁ ◁ τ₁₂) ▷ 𝟙 c ≫ (R₁ ≫ E₁ ≫ E₂) ◁ η₃) ⊗≫ R₁ ◁ E₁ ◁ τ₂₃ ▷ R₃ ⊗≫
          R₁ ◁ τ₁₂ ▷ E₃ ▷ R₃ ⊗≫ ε₁ ▷ (E₂ ≫ E₃ ≫ R₃) ⊗≫ 𝟙 _ := by
        rw [sigma_sigma η₂ ε₂ τ₁₂ ε₁ η₃ τ₂₃ hZ]; bicategory
    _ = 𝟙 _ ⊗≫ (R₁ ≫ E₁ ≫ E₂) ◁ η₃ ⊗≫
          R₁ ◁ (𝟙 _ ⊗≫ τ₁₂ ▷ E₃ ⊗≫ E₁ ◁ τ₂₃ ⊗≫ τ₁₂ ▷ E₃ ⊗≫ 𝟙 _ :
            E₁ ≫ E₂ ≫ E₃ ⟶ E₁ ≫ E₂ ≫ E₃) ▷ R₃ ⊗≫
          ε₁ ▷ (E₂ ≫ E₃ ≫ R₃) ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange]; bicategory
    _ = 𝟙 _ ⊗≫ (R₁ ≫ E₁ ≫ E₂) ◁ η₃ ⊗≫
          R₁ ◁ (E₁ ◁ τ₂₃ ⊗≫ τ₁₂ ▷ E₃ ⊗≫ E₁ ◁ τ₂₃ : E₁ ≫ E₂ ≫ E₃ ⟶ E₁ ≫ E₂ ≫ E₃) ▷ R₃ ⊗≫
          ε₁ ▷ (E₂ ≫ E₃ ≫ R₃) ⊗≫ 𝟙 _ := by
        rw [hB']
    _ = 𝟙 _ ⊗≫ (R₁ ≫ E₁ ≫ E₂) ◁ η₃ ⊗≫ R₁ ◁ E₁ ◁ τ₂₃ ▷ R₃ ⊗≫ R₁ ◁ τ₁₂ ▷ E₃ ▷ R₃ ⊗≫
          ((R₁ ≫ E₁) ◁ τ₂₃ ▷ R₃ ≫ ε₁ ▷ ((E₂ ≫ E₃) ≫ R₃)) ⊗≫ 𝟙 _ := by
        bicategory
    _ = (sigma η₂ τ₁₂ ε₁ ▷ E₂ ⊗≫ E₂ ◁ sigma η₃ τ₂₃ ε₂) ⊗≫ τ₂₃ ▷ R₃ ⊗≫ 𝟙 _ := by
        rw [whisker_exchange, sigma_sigma η₂ ε₂ τ₁₂ ε₁ η₃ τ₂₃ hZ]; bicategory

end Braid

/-! ## Isomorphisms with a direct sum of three objects, without biproducts -/

section Sum₃

variable {D : Type*} [Category D] [Preadditive D] {X Y₁ Y₂ Y₃ : D}

/-- `(f₁, f₂, f₃) : X ⟶ Y₁ ⊕ Y₂ ⊕ Y₃` is an isomorphism: there are `gᵢ : Yᵢ ⟶ X` with
`∑ fᵢ ≫ gᵢ = 𝟙` and `gᵢ ≫ fⱼ = δᵢⱼ`. (Stated without biproducts, so that it makes sense in the
graded-Hom category of a category with shift, where the summands may carry different degrees.) -/
def IsIsoToSum₃ (f₁ : X ⟶ Y₁) (f₂ : X ⟶ Y₂) (f₃ : X ⟶ Y₃) : Prop :=
  ∃ (g₁ : Y₁ ⟶ X) (g₂ : Y₂ ⟶ X) (g₃ : Y₃ ⟶ X),
    f₁ ≫ g₁ + f₂ ≫ g₂ + f₃ ≫ g₃ = 𝟙 X ∧
    (g₁ ≫ f₁ = 𝟙 Y₁ ∧ g₁ ≫ f₂ = 0 ∧ g₁ ≫ f₃ = 0) ∧
    (g₂ ≫ f₁ = 0 ∧ g₂ ≫ f₂ = 𝟙 Y₂ ∧ g₂ ≫ f₃ = 0) ∧
    (g₃ ≫ f₁ = 0 ∧ g₃ ≫ f₂ = 0 ∧ g₃ ≫ f₃ = 𝟙 Y₃)

/-- `(g₁, g₂, g₃) : Y₁ ⊕ Y₂ ⊕ Y₃ ⟶ X` is an isomorphism: there are `fᵢ : X ⟶ Yᵢ` with
`∑ fᵢ ≫ gᵢ = 𝟙` and `gᵢ ≫ fⱼ = δᵢⱼ`. -/
def IsIsoFromSum₃ (g₁ : Y₁ ⟶ X) (g₂ : Y₂ ⟶ X) (g₃ : Y₃ ⟶ X) : Prop :=
  ∃ (f₁ : X ⟶ Y₁) (f₂ : X ⟶ Y₂) (f₃ : X ⟶ Y₃),
    f₁ ≫ g₁ + f₂ ≫ g₂ + f₃ ≫ g₃ = 𝟙 X ∧
    (g₁ ≫ f₁ = 𝟙 Y₁ ∧ g₁ ≫ f₂ = 0 ∧ g₁ ≫ f₃ = 0) ∧
    (g₂ ≫ f₁ = 0 ∧ g₂ ≫ f₂ = 𝟙 Y₂ ∧ g₂ ≫ f₃ = 0) ∧
    (g₃ ≫ f₁ = 0 ∧ g₃ ≫ f₂ = 0 ∧ g₃ ≫ f₃ = 𝟙 Y₃)

end Sum₃

/-! ## Detecting 2-morphisms after whiskering with a split family -/

section Split

variable [∀ a b : C, Preadditive (a ⟶ b)] [AdditiveWhiskering C] {a b c : C}

open AdditiveWhiskering

/-- If `(f₁, f₂, f₃) : X ⟶ Y₁ ⊕ Y₂ ⊕ Y₃` has a left inverse, a 2-morphism into `E ≫ X` is
determined by its composites with the `E ◁ fᵢ`. -/
theorem eq_of_comp_whiskerLeft_eq (E : a ⟶ b) {X Y₁ Y₂ Y₃ : b ⟶ c} {f₁ : X ⟶ Y₁} {f₂ : X ⟶ Y₂}
    {f₃ : X ⟶ Y₃} {g₁ : Y₁ ⟶ X} {g₂ : Y₂ ⟶ X} {g₃ : Y₃ ⟶ X}
    (hsum : f₁ ≫ g₁ + f₂ ≫ g₂ + f₃ ≫ g₃ = 𝟙 X) {P : a ⟶ c} {φ ψ : P ⟶ E ≫ X}
    (h₁ : φ ≫ E ◁ f₁ = ψ ≫ E ◁ f₁) (h₂ : φ ≫ E ◁ f₂ = ψ ≫ E ◁ f₂)
    (h₃ : φ ≫ E ◁ f₃ = ψ ≫ E ◁ f₃) : φ = ψ := by
  have key : ∀ χ : P ⟶ E ≫ X, χ =
      (χ ≫ E ◁ f₁) ≫ E ◁ g₁ + (χ ≫ E ◁ f₂) ≫ E ◁ g₂ + (χ ≫ E ◁ f₃) ≫ E ◁ g₃ := by
    intro χ
    calc χ = χ ≫ E ◁ (f₁ ≫ g₁ + f₂ ≫ g₂ + f₃ ≫ g₃) := by
          rw [hsum, Bicategory.whiskerLeft_id, Category.comp_id]
      _ = (χ ≫ E ◁ f₁) ≫ E ◁ g₁ + (χ ≫ E ◁ f₂) ≫ E ◁ g₂ + (χ ≫ E ◁ f₃) ≫ E ◁ g₃ := by
          simp only [whiskerLeft_add, Bicategory.whiskerLeft_comp, Preadditive.comp_add,
            Category.assoc]
  rw [key φ, key ψ, h₁, h₂, h₃]

/-- If `(f₁, f₂, f₃) : Y₁ ⊕ Y₂ ⊕ Y₃ ⟶ X` has a right inverse, a 2-morphism out of `X ≫ E` is
determined by its composites with the `fᵢ ▷ E`. -/
theorem eq_of_whiskerRight_comp_eq {X Y₁ Y₂ Y₃ : a ⟶ b} (E : b ⟶ c) {f₁ : Y₁ ⟶ X} {f₂ : Y₂ ⟶ X}
    {f₃ : Y₃ ⟶ X} {g₁ : X ⟶ Y₁} {g₂ : X ⟶ Y₂} {g₃ : X ⟶ Y₃}
    (hsum : g₁ ≫ f₁ + g₂ ≫ f₂ + g₃ ≫ f₃ = 𝟙 X) {P : a ⟶ c} {φ ψ : X ≫ E ⟶ P}
    (h₁ : f₁ ▷ E ≫ φ = f₁ ▷ E ≫ ψ) (h₂ : f₂ ▷ E ≫ φ = f₂ ▷ E ≫ ψ)
    (h₃ : f₃ ▷ E ≫ φ = f₃ ▷ E ≫ ψ) : φ = ψ := by
  have key : ∀ χ : X ≫ E ⟶ P, χ =
      g₁ ▷ E ≫ f₁ ▷ E ≫ χ + g₂ ▷ E ≫ f₂ ▷ E ≫ χ + g₃ ▷ E ≫ f₃ ▷ E ≫ χ := by
    intro χ
    calc χ = (g₁ ≫ f₁ + g₂ ≫ f₂ + g₃ ≫ f₃) ▷ E ≫ χ := by
          rw [hsum, Bicategory.id_whiskerRight, Category.id_comp]
      _ = g₁ ▷ E ≫ f₁ ▷ E ≫ χ + g₂ ▷ E ≫ f₂ ▷ E ≫ χ + g₃ ▷ E ≫ f₃ ▷ E ≫ χ := by
          simp only [add_whiskerRight, Bicategory.comp_whiskerRight, Preadditive.add_comp,
            Category.assoc]
  rw [key φ, key ψ, h₁, h₂, h₃]

end Split

/-! ## Weight `0`

`E₁ = E_{-2}`, `E₂ = E_0`, `E₃ = E_2`; `σ_0 = sigma η₂ τ₁₂ ε₁`, `σ_2 = sigma η₃ τ₂₃ ε₂`. -/

section WeightZero

variable [∀ a b : C, Preadditive (a ⟶ b)] [AdditiveWhiskering C]
  {a b c d : C} {E₁ : a ⟶ b} {E₂ : b ⟶ c} {E₃ : c ⟶ d} {R₁ : b ⟶ a} {R₂ : c ⟶ b} {R₃ : d ⟶ c}
  (η₂ : 𝟙 b ⟶ E₂ ≫ R₂) (ε₂ : R₂ ≫ E₂ ⟶ 𝟙 c) (τ₁₂ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) (ε₁ : R₁ ≫ E₁ ⟶ 𝟙 b)
  (η₃ : 𝟙 c ⟶ E₃ ≫ R₃) (τ₂₃ : E₂ ≫ E₃ ⟶ E₂ ≫ E₃)

open AdditiveWhiskering

omit [∀ a b : C, Preadditive (a ⟶ b)] [AdditiveWhiskering C] in
/-- The zigzag built from `η_0`, `σ_0⁻¹`, the crossing and `ε_{-2}` is the identity of `E_0`. -/
theorem unit_inv_cross_counit (hZ : leftZigzag η₂ ε₂ = (λ_ E₂).hom ≫ (ρ_ E₂).inv)
    {σi : E₂ ≫ R₂ ⟶ R₁ ≫ E₁} (hσi : σi ≫ sigma η₂ τ₁₂ ε₁ = 𝟙 _) :
    η₂ ▷ E₂ ⊗≫ σi ▷ E₂ ⊗≫ R₁ ◁ τ₁₂ ⊗≫ ε₁ ▷ E₂ = 𝟙 (𝟙 b ≫ E₂) := by
  calc η₂ ▷ E₂ ⊗≫ σi ▷ E₂ ⊗≫ R₁ ◁ τ₁₂ ⊗≫ ε₁ ▷ E₂
      = η₂ ▷ E₂ ⊗≫ σi ▷ E₂ ⊗≫
          (𝟙 _ ⊗≫ R₁ ◁ τ₁₂ ⊗≫ ε₁ ▷ E₂ ⊗≫ 𝟙 _ : (R₁ ≫ E₁) ≫ E₂ ⟶ E₂ ≫ 𝟙 c) ⊗≫ 𝟙 _ := by
        bicategory
    _ = η₂ ▷ E₂ ⊗≫ σi ▷ E₂ ⊗≫ (sigma η₂ τ₁₂ ε₁ ▷ E₂ ⊗≫ E₂ ◁ ε₂) ⊗≫ 𝟙 _ := by
        rw [pitchfork_cap η₂ ε₂ τ₁₂ ε₁ hZ]
    _ = η₂ ▷ E₂ ⊗≫ (σi ≫ sigma η₂ τ₁₂ ε₁) ▷ E₂ ⊗≫ E₂ ◁ ε₂ ⊗≫ 𝟙 _ := by
        bicategory
    _ = leftZigzag η₂ ε₂ ⊗≫ 𝟙 _ := by
        rw [hσi, leftZigzag]; bicategory
    _ = 𝟙 (𝟙 b ≫ E₂) := by
        rw [hZ]; bicategory

omit [∀ a b : C, Preadditive (a ⟶ b)] [AdditiveWhiskering C] in
/-- The candidate for `u₁ E_0`, tested against `(ε_0 ∘ y R_0) E_0` for an endomorphism `y` of
`E_0`. -/
theorem candidate_comp_counit (hZ : leftZigzag η₂ ε₂ = (λ_ E₂).hom ≫ (ρ_ E₂).inv)
    (σi : E₂ ≫ R₂ ⟶ R₁ ≫ E₁) (y : E₂ ⟶ E₂) :
    (𝟙 _ ⊗≫ η₂ ▷ E₂ ⊗≫ σi ▷ E₂ ⊗≫ R₁ ◁ τ₁₂ ⊗≫ sigma η₂ τ₁₂ ε₁ ▷ E₂ ⊗≫ 𝟙 _ :
        E₂ ≫ 𝟙 c ⟶ E₂ ≫ R₂ ≫ E₂) ≫ E₂ ◁ (R₂ ◁ y ≫ ε₂) =
      𝟙 _ ⊗≫ η₂ ▷ E₂ ⊗≫ σi ▷ E₂ ⊗≫ R₁ ◁ (τ₁₂ ≫ E₁ ◁ y ≫ τ₁₂) ⊗≫ ε₁ ▷ E₂ ⊗≫ 𝟙 _ := by
  calc (𝟙 _ ⊗≫ η₂ ▷ E₂ ⊗≫ σi ▷ E₂ ⊗≫ R₁ ◁ τ₁₂ ⊗≫ sigma η₂ τ₁₂ ε₁ ▷ E₂ ⊗≫ 𝟙 _ :
        E₂ ≫ 𝟙 c ⟶ E₂ ≫ R₂ ≫ E₂) ≫ E₂ ◁ (R₂ ◁ y ≫ ε₂)
      = 𝟙 _ ⊗≫ η₂ ▷ E₂ ⊗≫ σi ▷ E₂ ⊗≫ R₁ ◁ τ₁₂ ⊗≫
          (sigma η₂ τ₁₂ ε₁ ▷ E₂ ≫ (E₂ ≫ R₂) ◁ y) ⊗≫ E₂ ◁ ε₂ := by
        bicategory
    _ = 𝟙 _ ⊗≫ η₂ ▷ E₂ ⊗≫ σi ▷ E₂ ⊗≫ R₁ ◁ (τ₁₂ ≫ E₁ ◁ y) ⊗≫
          (sigma η₂ τ₁₂ ε₁ ▷ E₂ ⊗≫ E₂ ◁ ε₂) := by
        rw [← whisker_exchange]; bicategory
    _ = 𝟙 _ ⊗≫ η₂ ▷ E₂ ⊗≫ σi ▷ E₂ ⊗≫ R₁ ◁ (τ₁₂ ≫ E₁ ◁ y ≫ τ₁₂) ⊗≫ ε₁ ▷ E₂ ⊗≫ 𝟙 _ := by
        rw [pitchfork_cap η₂ ε₂ τ₁₂ ε₁ hZ]; bicategory

/-- **The unit at weight `0`, whiskered by `E_0`** (Brundan, proof of (4.4), at `h = 0`): if
`σ_0` is invertible and `(s, u₀, u₁)` is inverse to `ρ_2 = (σ_2, ε_0, ε_0 ∘ x R_0)`, then
`u₁ E_0 = (E_0 σ_0) ∘ (τ_{-2} R_{-2}) ∘ (E_0 σ_0⁻¹) ∘ (E_0 η_0)`. -/
theorem whiskerLeft_unit_eq (hZ : leftZigzag η₂ ε₂ = (λ_ E₂).hom ≫ (ρ_ E₂).inv)
    (hτ₁₂ : τ₁₂ ≫ τ₁₂ = 0) (hτ₂₃ : τ₂₃ ≫ τ₂₃ = 0) (x₁ : E₁ ⟶ E₁) (x₂ : E₂ ⟶ E₂)
    (hNH : E₁ ◁ x₂ ≫ τ₁₂ - τ₁₂ ≫ x₁ ▷ E₂ = 𝟙 _)
    (hB : E₁ ◁ τ₂₃ ≫ ((α_ E₁ E₂ E₃).inv ≫ τ₁₂ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom) ≫ E₁ ◁ τ₂₃ =
      ((α_ E₁ E₂ E₃).inv ≫ τ₁₂ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom) ≫ E₁ ◁ τ₂₃ ≫
        ((α_ E₁ E₂ E₃).inv ≫ τ₁₂ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom))
    {σi : E₂ ≫ R₂ ⟶ R₁ ≫ E₁} (hσi : σi ≫ sigma η₂ τ₁₂ ε₁ = 𝟙 _)
    {s : E₃ ≫ R₃ ⟶ R₂ ≫ E₂} {u₀ u₁ : 𝟙 c ⟶ R₂ ≫ E₂}
    (hsum : sigma η₃ τ₂₃ ε₂ ≫ s + ε₂ ≫ u₀ + (R₂ ◁ x₂ ≫ ε₂) ≫ u₁ = 𝟙 _)
    (hu₁ : u₁ ≫ sigma η₃ τ₂₃ ε₂ = 0) (hu₂ : u₁ ≫ ε₂ = 0) (hu₃ : u₁ ≫ R₂ ◁ x₂ ≫ ε₂ = 𝟙 _) :
    E₂ ◁ u₁ =
      𝟙 _ ⊗≫ η₂ ▷ E₂ ⊗≫ σi ▷ E₂ ⊗≫ R₁ ◁ τ₁₂ ⊗≫ sigma η₂ τ₁₂ ε₁ ▷ E₂ ⊗≫ 𝟙 _ := by
  refine eq_of_comp_whiskerLeft_eq E₂ hsum ?_ ?_ ?_
  · -- the component `σ_2 E_0`
    rw [← Bicategory.whiskerLeft_comp, hu₁, whiskerLeft_zero]
    symm
    calc (𝟙 _ ⊗≫ η₂ ▷ E₂ ⊗≫ σi ▷ E₂ ⊗≫ R₁ ◁ τ₁₂ ⊗≫ sigma η₂ τ₁₂ ε₁ ▷ E₂ ⊗≫ 𝟙 _ :
          E₂ ≫ 𝟙 c ⟶ E₂ ≫ R₂ ≫ E₂) ≫ E₂ ◁ sigma η₃ τ₂₃ ε₂
        = 𝟙 _ ⊗≫ η₂ ▷ E₂ ⊗≫ σi ▷ E₂ ⊗≫
            (𝟙 _ ⊗≫ R₁ ◁ τ₁₂ ⊗≫ (sigma η₂ τ₁₂ ε₁ ▷ E₂ ⊗≫ E₂ ◁ sigma η₃ τ₂₃ ε₂) :
              (R₁ ≫ E₁) ≫ E₂ ⟶ E₂ ≫ E₃ ≫ R₃) := by
          bicategory
      _ = 𝟙 _ ⊗≫ η₂ ▷ E₂ ⊗≫ σi ▷ E₂ ⊗≫
            ((sigma η₂ τ₁₂ ε₁ ▷ E₂ ⊗≫ E₂ ◁ sigma η₃ τ₂₃ ε₂) ⊗≫ τ₂₃ ▷ R₃ ⊗≫ 𝟙 _ :
              (R₁ ≫ E₁) ≫ E₂ ⟶ E₂ ≫ E₃ ≫ R₃) := by
          rw [mixed_braid η₂ ε₂ τ₁₂ ε₁ η₃ τ₂₃ hZ hB]
      _ = 𝟙 _ ⊗≫ η₂ ▷ E₂ ⊗≫ (σi ≫ sigma η₂ τ₁₂ ε₁) ▷ E₂ ⊗≫ E₂ ◁ sigma η₃ τ₂₃ ε₂ ⊗≫
            τ₂₃ ▷ R₃ ⊗≫ 𝟙 _ := by
          bicategory
      _ = 𝟙 _ ⊗≫ (η₂ ▷ E₂ ⊗≫ E₂ ◁ sigma η₃ τ₂₃ ε₂) ⊗≫ τ₂₃ ▷ R₃ ⊗≫ 𝟙 _ := by
          rw [hσi]; bicategory
      _ = 𝟙 _ ⊗≫ E₂ ◁ η₃ ⊗≫ (τ₂₃ ≫ τ₂₃) ▷ R₃ ⊗≫ 𝟙 _ := by
          rw [pitchfork_cup η₂ ε₂ η₃ τ₂₃ hZ]; bicategory
      _ = 0 := by
          simp only [hτ₂₃, zero_whiskerRight, bicategoricalComp, Limits.zero_comp,
            Limits.comp_zero]
  · -- the component `ε_0 E_0`
    rw [← Bicategory.whiskerLeft_comp, hu₂, whiskerLeft_zero]
    symm
    have h := candidate_comp_counit η₂ ε₂ τ₁₂ ε₁ hZ σi (𝟙 E₂)
    rw [Bicategory.whiskerLeft_id, Category.id_comp] at h
    rw [h]
    simp only [Bicategory.whiskerLeft_id, Category.id_comp, hτ₁₂, whiskerLeft_zero,
      bicategoricalComp, Limits.zero_comp, Limits.comp_zero]
  · -- the component `(ε_0 ∘ x R_0) E_0`
    rw [← Bicategory.whiskerLeft_comp, hu₃, Bicategory.whiskerLeft_id]
    symm
    rw [candidate_comp_counit η₂ ε₂ τ₁₂ ε₁ hZ σi x₂, tau_dot_tau_left _ _ _ hτ₁₂ hNH]
    calc 𝟙 _ ⊗≫ η₂ ▷ E₂ ⊗≫ σi ▷ E₂ ⊗≫ R₁ ◁ τ₁₂ ⊗≫ ε₁ ▷ E₂ ⊗≫ 𝟙 _
        = 𝟙 _ ⊗≫ (η₂ ▷ E₂ ⊗≫ σi ▷ E₂ ⊗≫ R₁ ◁ τ₁₂ ⊗≫ ε₁ ▷ E₂) ⊗≫ 𝟙 _ := by
          bicategory
      _ = 𝟙 (E₂ ≫ 𝟙 c) := by
          rw [unit_inv_cross_counit η₂ ε₂ τ₁₂ ε₁ hZ hσi]; bicategory

/-- **The zigzag identity for `E_0`** (Brundan Theorem 4.3 at weight `0`): if `σ_0` is invertible
and `(s, u₀, u₁)` is inverse to `ρ_2 = (σ_2, ε_0, ε_0 ∘ x R_0)`, then the unit `u₁ : 𝟙 ⟶ E_0 R_0`
and the counit `ε_{-2} ∘ σ_0⁻¹ : R_0 E_0 ⟶ 𝟙` satisfy `(E_0 ε') ∘ (η' E_0) = 1`. Besides the
invertibility hypotheses, only the zigzag identity for `E_0`, `τ² = 0`, one dot-slide relation
and the braid relation are used. -/
theorem rightZigzag_zero (hZ : leftZigzag η₂ ε₂ = (λ_ E₂).hom ≫ (ρ_ E₂).inv)
    (hτ₁₂ : τ₁₂ ≫ τ₁₂ = 0) (hτ₂₃ : τ₂₃ ≫ τ₂₃ = 0) (x₁ : E₁ ⟶ E₁) (x₂ : E₂ ⟶ E₂)
    (hNH : E₁ ◁ x₂ ≫ τ₁₂ - τ₁₂ ≫ x₁ ▷ E₂ = 𝟙 _)
    (hB : E₁ ◁ τ₂₃ ≫ ((α_ E₁ E₂ E₃).inv ≫ τ₁₂ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom) ≫ E₁ ◁ τ₂₃ =
      ((α_ E₁ E₂ E₃).inv ≫ τ₁₂ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom) ≫ E₁ ◁ τ₂₃ ≫
        ((α_ E₁ E₂ E₃).inv ≫ τ₁₂ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom))
    {σi : E₂ ≫ R₂ ⟶ R₁ ≫ E₁} (hσ : sigma η₂ τ₁₂ ε₁ ≫ σi = 𝟙 _)
    (hσi : σi ≫ sigma η₂ τ₁₂ ε₁ = 𝟙 _)
    {s : E₃ ≫ R₃ ⟶ R₂ ≫ E₂} {u₀ u₁ : 𝟙 c ⟶ R₂ ≫ E₂}
    (hsum : sigma η₃ τ₂₃ ε₂ ≫ s + ε₂ ≫ u₀ + (R₂ ◁ x₂ ≫ ε₂) ≫ u₁ = 𝟙 _)
    (hu₁ : u₁ ≫ sigma η₃ τ₂₃ ε₂ = 0) (hu₂ : u₁ ≫ ε₂ = 0) (hu₃ : u₁ ≫ R₂ ◁ x₂ ≫ ε₂ = 𝟙 _) :
    rightZigzag u₁ (σi ≫ ε₁) = (ρ_ E₂).hom ≫ (λ_ E₂).inv := by
  calc rightZigzag u₁ (σi ≫ ε₁)
      = (𝟙 _ ⊗≫ η₂ ▷ E₂ ⊗≫ σi ▷ E₂ ⊗≫ R₁ ◁ τ₁₂ ⊗≫ sigma η₂ τ₁₂ ε₁ ▷ E₂ ⊗≫ 𝟙 _ :
          E₂ ≫ 𝟙 c ⟶ E₂ ≫ R₂ ≫ E₂) ⊗≫ (σi ≫ ε₁) ▷ E₂ := by
        rw [rightZigzag, whiskerLeft_unit_eq η₂ ε₂ τ₁₂ ε₁ η₃ τ₂₃ hZ hτ₁₂ hτ₂₃ x₁ x₂ hNH hB hσi
          hsum hu₁ hu₂ hu₃]
    _ = 𝟙 _ ⊗≫ η₂ ▷ E₂ ⊗≫ σi ▷ E₂ ⊗≫ R₁ ◁ τ₁₂ ⊗≫ (sigma η₂ τ₁₂ ε₁ ≫ σi) ▷ E₂ ⊗≫
          ε₁ ▷ E₂ := by
        bicategory
    _ = 𝟙 _ ⊗≫ (η₂ ▷ E₂ ⊗≫ σi ▷ E₂ ⊗≫ R₁ ◁ τ₁₂ ⊗≫ ε₁ ▷ E₂) := by
        rw [hσ]; bicategory
    _ = (ρ_ E₂).hom ≫ (λ_ E₂).inv := by
        rw [unit_inv_cross_counit η₂ ε₂ τ₁₂ ε₁ hZ hσi]; bicategory

end WeightZero

/-! ## Weight `-2`

`E₁ = E_{-4}`, `E₂ = E_{-2}`, `E₃ = E_0`; `σ_{-2} = sigma η₂ τ₁₂ ε₁`, `σ_0 = sigma η₃ τ₂₃ ε₂`. -/

section WeightNegTwo

variable [∀ a b : C, Preadditive (a ⟶ b)] [AdditiveWhiskering C]
  {a b c d : C} {E₁ : a ⟶ b} {E₂ : b ⟶ c} {E₃ : c ⟶ d} {R₁ : b ⟶ a} {R₂ : c ⟶ b} {R₃ : d ⟶ c}
  (η₂ : 𝟙 b ⟶ E₂ ≫ R₂) (ε₂ : R₂ ≫ E₂ ⟶ 𝟙 c) (τ₁₂ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) (ε₁ : R₁ ≫ E₁ ⟶ 𝟙 b)
  (η₃ : 𝟙 c ⟶ E₃ ≫ R₃) (τ₂₃ : E₂ ≫ E₃ ⟶ E₂ ≫ E₃)

open AdditiveWhiskering

omit [∀ a b : C, Preadditive (a ⟶ b)] [AdditiveWhiskering C] in
/-- The zigzag built from `η_0`, the crossing, `σ_0⁻¹` and `ε_{-2}` is the identity of
`E_{-2}`. -/
theorem unit_cross_inv_counit (hZ : leftZigzag η₂ ε₂ = (λ_ E₂).hom ≫ (ρ_ E₂).inv)
    {σi : E₃ ≫ R₃ ⟶ R₂ ≫ E₂} (hσ : sigma η₃ τ₂₃ ε₂ ≫ σi = 𝟙 _) :
    E₂ ◁ η₃ ⊗≫ τ₂₃ ▷ R₃ ⊗≫ E₂ ◁ σi ⊗≫ E₂ ◁ ε₂ = 𝟙 (E₂ ≫ 𝟙 c) := by
  calc E₂ ◁ η₃ ⊗≫ τ₂₃ ▷ R₃ ⊗≫ E₂ ◁ σi ⊗≫ E₂ ◁ ε₂
      = 𝟙 _ ⊗≫ (𝟙 _ ⊗≫ E₂ ◁ η₃ ⊗≫ τ₂₃ ▷ R₃ ⊗≫ 𝟙 _ : 𝟙 b ≫ E₂ ⟶ E₂ ≫ E₃ ≫ R₃) ⊗≫
          E₂ ◁ σi ⊗≫ E₂ ◁ ε₂ := by
        bicategory
    _ = 𝟙 _ ⊗≫ (η₂ ▷ E₂ ⊗≫ E₂ ◁ sigma η₃ τ₂₃ ε₂) ⊗≫ E₂ ◁ σi ⊗≫ E₂ ◁ ε₂ := by
        rw [pitchfork_cup η₂ ε₂ η₃ τ₂₃ hZ]
    _ = 𝟙 _ ⊗≫ η₂ ▷ E₂ ⊗≫ E₂ ◁ (sigma η₃ τ₂₃ ε₂ ≫ σi) ⊗≫ E₂ ◁ ε₂ := by
        bicategory
    _ = 𝟙 _ ⊗≫ leftZigzag η₂ ε₂ := by
        rw [hσ, leftZigzag]; bicategory
    _ = 𝟙 (E₂ ≫ 𝟙 c) := by
        rw [hZ]; bicategory

omit [∀ a b : C, Preadditive (a ⟶ b)] [AdditiveWhiskering C] in
/-- The candidate for `-E_{-2} w₁`, tested against `E_{-2} (R_{-2} y ∘ η_{-2})` for an
endomorphism `y` of `E_{-2}`. -/
theorem unit_comp_candidate (hZ : leftZigzag η₂ ε₂ = (λ_ E₂).hom ≫ (ρ_ E₂).inv)
    (σi : E₃ ≫ R₃ ⟶ R₂ ≫ E₂) (y : E₂ ⟶ E₂) :
    (η₂ ≫ y ▷ R₂) ▷ E₂ ≫
        (𝟙 _ ⊗≫ E₂ ◁ sigma η₃ τ₂₃ ε₂ ⊗≫ τ₂₃ ▷ R₃ ⊗≫ E₂ ◁ σi ⊗≫ E₂ ◁ ε₂ ⊗≫ 𝟙 _ :
          (E₂ ≫ R₂) ≫ E₂ ⟶ 𝟙 b ≫ E₂) =
      𝟙 _ ⊗≫ E₂ ◁ η₃ ⊗≫ (τ₂₃ ≫ y ▷ E₃ ≫ τ₂₃) ▷ R₃ ⊗≫ E₂ ◁ σi ⊗≫ E₂ ◁ ε₂ ⊗≫ 𝟙 _ := by
  calc (η₂ ≫ y ▷ R₂) ▷ E₂ ≫
        (𝟙 _ ⊗≫ E₂ ◁ sigma η₃ τ₂₃ ε₂ ⊗≫ τ₂₃ ▷ R₃ ⊗≫ E₂ ◁ σi ⊗≫ E₂ ◁ ε₂ ⊗≫ 𝟙 _ :
          (E₂ ≫ R₂) ≫ E₂ ⟶ 𝟙 b ≫ E₂)
      = η₂ ▷ E₂ ⊗≫ (y ▷ (R₂ ≫ E₂) ≫ E₂ ◁ sigma η₃ τ₂₃ ε₂) ⊗≫ τ₂₃ ▷ R₃ ⊗≫ E₂ ◁ σi ⊗≫
          E₂ ◁ ε₂ ⊗≫ 𝟙 _ := by
        bicategory
    _ = 𝟙 _ ⊗≫ (η₂ ▷ E₂ ⊗≫ E₂ ◁ sigma η₃ τ₂₃ ε₂) ⊗≫ (y ▷ E₃ ≫ τ₂₃) ▷ R₃ ⊗≫ E₂ ◁ σi ⊗≫
          E₂ ◁ ε₂ ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange]; bicategory
    _ = 𝟙 _ ⊗≫ E₂ ◁ η₃ ⊗≫ (τ₂₃ ≫ y ▷ E₃ ≫ τ₂₃) ▷ R₃ ⊗≫ E₂ ◁ σi ⊗≫ E₂ ◁ ε₂ ⊗≫ 𝟙 _ := by
        rw [pitchfork_cup η₂ ε₂ η₃ τ₂₃ hZ]; bicategory

/-- **The counit at weight `-2`, whiskered by `E_{-2}`** (Brundan (4.5) at `h = -2`): if `σ_0` is
invertible and `(t, w₀, w₁)` is inverse to `ρ_{-2} = (σ_{-2}, η_{-2}, R_{-2} x ∘ η_{-2})`, then
`E_{-2} w₁ = -(ε_{-2} E_{-2}) ∘ (σ_0⁻¹ E_{-2}) ∘ (R_0 τ_{-2}) ∘ (σ_0 E_{-2})`. -/
theorem counit_whiskerRight_eq (hZ : leftZigzag η₂ ε₂ = (λ_ E₂).hom ≫ (ρ_ E₂).inv)
    (hτ₁₂ : τ₁₂ ≫ τ₁₂ = 0) (hτ₂₃ : τ₂₃ ≫ τ₂₃ = 0) (x₂ : E₂ ⟶ E₂) (x₃ : E₃ ⟶ E₃)
    (hNH : E₂ ◁ x₃ ≫ τ₂₃ - τ₂₃ ≫ x₂ ▷ E₃ = 𝟙 _)
    (hB : E₁ ◁ τ₂₃ ≫ ((α_ E₁ E₂ E₃).inv ≫ τ₁₂ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom) ≫ E₁ ◁ τ₂₃ =
      ((α_ E₁ E₂ E₃).inv ≫ τ₁₂ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom) ≫ E₁ ◁ τ₂₃ ≫
        ((α_ E₁ E₂ E₃).inv ≫ τ₁₂ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom))
    {σi : E₃ ≫ R₃ ⟶ R₂ ≫ E₂} (hσ : sigma η₃ τ₂₃ ε₂ ≫ σi = 𝟙 _)
    {t : E₂ ≫ R₂ ⟶ R₁ ≫ E₁} {w₀ w₁ : E₂ ≫ R₂ ⟶ 𝟙 b}
    (hsum : t ≫ sigma η₂ τ₁₂ ε₁ + w₀ ≫ η₂ + w₁ ≫ η₂ ≫ x₂ ▷ R₂ = 𝟙 _)
    (hw₁ : sigma η₂ τ₁₂ ε₁ ≫ w₁ = 0) (hw₂ : η₂ ≫ w₁ = 0) (hw₃ : (η₂ ≫ x₂ ▷ R₂) ≫ w₁ = 𝟙 _) :
    w₁ ▷ E₂ =
      -(𝟙 _ ⊗≫ E₂ ◁ sigma η₃ τ₂₃ ε₂ ⊗≫ τ₂₃ ▷ R₃ ⊗≫ E₂ ◁ σi ⊗≫ E₂ ◁ ε₂ ⊗≫ 𝟙 _ :
        (E₂ ≫ R₂) ≫ E₂ ⟶ 𝟙 b ≫ E₂) := by
  refine eq_of_whiskerRight_comp_eq E₂ hsum ?_ ?_ ?_
  · -- the component `E_{-2} σ_{-2}`
    rw [← Bicategory.comp_whiskerRight, hw₁, zero_whiskerRight, Preadditive.comp_neg,
      eq_comm, neg_eq_zero]
    calc sigma η₂ τ₁₂ ε₁ ▷ E₂ ≫
          (𝟙 _ ⊗≫ E₂ ◁ sigma η₃ τ₂₃ ε₂ ⊗≫ τ₂₃ ▷ R₃ ⊗≫ E₂ ◁ σi ⊗≫ E₂ ◁ ε₂ ⊗≫ 𝟙 _ :
            (E₂ ≫ R₂) ≫ E₂ ⟶ 𝟙 b ≫ E₂)
        = 𝟙 _ ⊗≫ ((sigma η₂ τ₁₂ ε₁ ▷ E₂ ⊗≫ E₂ ◁ sigma η₃ τ₂₃ ε₂) ⊗≫ τ₂₃ ▷ R₃ ⊗≫ 𝟙 _ :
            (R₁ ≫ E₁) ≫ E₂ ⟶ E₂ ≫ E₃ ≫ R₃) ⊗≫ E₂ ◁ σi ⊗≫ E₂ ◁ ε₂ ⊗≫ 𝟙 _ := by
          bicategory
      _ = 𝟙 _ ⊗≫ (𝟙 _ ⊗≫ R₁ ◁ τ₁₂ ⊗≫ (sigma η₂ τ₁₂ ε₁ ▷ E₂ ⊗≫ E₂ ◁ sigma η₃ τ₂₃ ε₂) :
            (R₁ ≫ E₁) ≫ E₂ ⟶ E₂ ≫ E₃ ≫ R₃) ⊗≫ E₂ ◁ σi ⊗≫ E₂ ◁ ε₂ ⊗≫ 𝟙 _ := by
          rw [mixed_braid η₂ ε₂ τ₁₂ ε₁ η₃ τ₂₃ hZ hB]
      _ = 𝟙 _ ⊗≫ R₁ ◁ τ₁₂ ⊗≫ sigma η₂ τ₁₂ ε₁ ▷ E₂ ⊗≫ E₂ ◁ (sigma η₃ τ₂₃ ε₂ ≫ σi) ⊗≫
            E₂ ◁ ε₂ ⊗≫ 𝟙 _ := by
          bicategory
      _ = 𝟙 _ ⊗≫ R₁ ◁ τ₁₂ ⊗≫ (sigma η₂ τ₁₂ ε₁ ▷ E₂ ⊗≫ E₂ ◁ ε₂) ⊗≫ 𝟙 _ := by
          rw [hσ]; bicategory
      _ = 𝟙 _ ⊗≫ R₁ ◁ (τ₁₂ ≫ τ₁₂) ⊗≫ ε₁ ▷ E₂ ⊗≫ 𝟙 _ := by
          rw [pitchfork_cap η₂ ε₂ τ₁₂ ε₁ hZ]; bicategory
      _ = 0 := by
          simp only [hτ₁₂, whiskerLeft_zero, bicategoricalComp, Limits.zero_comp,
            Limits.comp_zero]
  · -- the component `E_{-2} η_{-2}`
    rw [← Bicategory.comp_whiskerRight, hw₂, zero_whiskerRight, Preadditive.comp_neg,
      eq_comm, neg_eq_zero]
    have h := unit_comp_candidate η₂ ε₂ η₃ τ₂₃ hZ σi (𝟙 E₂)
    rw [Bicategory.id_whiskerRight, Category.comp_id] at h
    rw [h]
    simp only [Bicategory.id_whiskerRight, Category.id_comp, hτ₂₃, zero_whiskerRight,
      bicategoricalComp, Limits.zero_comp, Limits.comp_zero]
  · -- the component `E_{-2} (R_{-2} x ∘ η_{-2})`
    rw [← Bicategory.comp_whiskerRight, hw₃, Bicategory.id_whiskerRight, Preadditive.comp_neg,
      unit_comp_candidate η₂ ε₂ η₃ τ₂₃ hZ σi x₂, tau_dot_tau_right _ _ _ hτ₂₃ hNH]
    have h : (𝟙 _ ⊗≫ E₂ ◁ η₃ ⊗≫ τ₂₃ ▷ R₃ ⊗≫ E₂ ◁ σi ⊗≫ E₂ ◁ ε₂ ⊗≫ 𝟙 _ :
        𝟙 b ≫ E₂ ⟶ 𝟙 b ≫ E₂) = 𝟙 _ := by
      calc (𝟙 _ ⊗≫ E₂ ◁ η₃ ⊗≫ τ₂₃ ▷ R₃ ⊗≫ E₂ ◁ σi ⊗≫ E₂ ◁ ε₂ ⊗≫ 𝟙 _ :
            𝟙 b ≫ E₂ ⟶ 𝟙 b ≫ E₂)
          = 𝟙 _ ⊗≫ (E₂ ◁ η₃ ⊗≫ τ₂₃ ▷ R₃ ⊗≫ E₂ ◁ σi ⊗≫ E₂ ◁ ε₂) ⊗≫ 𝟙 _ := by
            bicategory
        _ = 𝟙 _ := by
            rw [unit_cross_inv_counit η₂ ε₂ η₃ τ₂₃ hZ hσ]; bicategory
    have h' : (𝟙 _ ⊗≫ E₂ ◁ η₃ ⊗≫ (-τ₂₃) ▷ R₃ ⊗≫ E₂ ◁ σi ⊗≫ E₂ ◁ ε₂ ⊗≫ 𝟙 _ :
        𝟙 b ≫ E₂ ⟶ 𝟙 b ≫ E₂) =
        -(𝟙 _ ⊗≫ E₂ ◁ η₃ ⊗≫ τ₂₃ ▷ R₃ ⊗≫ E₂ ◁ σi ⊗≫ E₂ ◁ ε₂ ⊗≫ 𝟙 _ :
          𝟙 b ≫ E₂ ⟶ 𝟙 b ≫ E₂) := by
      simp only [bicategoricalComp, neg_whiskerRight, Preadditive.neg_comp,
        Preadditive.comp_neg]
    rw [h', h, neg_neg]

/-- **The zigzag identity for `E_{-2}`** (Brundan Theorem 4.3 at weight `-2`): if `σ_0` is
invertible and `(t, w₀, w₁)` is inverse to `ρ_{-2} = (σ_{-2}, η_{-2}, R_{-2} x ∘ η_{-2})`, then
the unit `-σ_0⁻¹ ∘ η_0 : 𝟙 ⟶ E_{-2} R_{-2}` and the counit `w₁ : R_{-2} E_{-2} ⟶ 𝟙` satisfy
`(E_{-2} ε') ∘ (η' E_{-2}) = 1`. -/
theorem rightZigzag_neg_two (hZ : leftZigzag η₂ ε₂ = (λ_ E₂).hom ≫ (ρ_ E₂).inv)
    (hτ₁₂ : τ₁₂ ≫ τ₁₂ = 0) (hτ₂₃ : τ₂₃ ≫ τ₂₃ = 0) (x₂ : E₂ ⟶ E₂) (x₃ : E₃ ⟶ E₃)
    (hNH : E₂ ◁ x₃ ≫ τ₂₃ - τ₂₃ ≫ x₂ ▷ E₃ = 𝟙 _)
    (hB : E₁ ◁ τ₂₃ ≫ ((α_ E₁ E₂ E₃).inv ≫ τ₁₂ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom) ≫ E₁ ◁ τ₂₃ =
      ((α_ E₁ E₂ E₃).inv ≫ τ₁₂ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom) ≫ E₁ ◁ τ₂₃ ≫
        ((α_ E₁ E₂ E₃).inv ≫ τ₁₂ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom))
    {σi : E₃ ≫ R₃ ⟶ R₂ ≫ E₂} (hσ : sigma η₃ τ₂₃ ε₂ ≫ σi = 𝟙 _)
    (hσi : σi ≫ sigma η₃ τ₂₃ ε₂ = 𝟙 _)
    {t : E₂ ≫ R₂ ⟶ R₁ ≫ E₁} {w₀ w₁ : E₂ ≫ R₂ ⟶ 𝟙 b}
    (hsum : t ≫ sigma η₂ τ₁₂ ε₁ + w₀ ≫ η₂ + w₁ ≫ η₂ ≫ x₂ ▷ R₂ = 𝟙 _)
    (hw₁ : sigma η₂ τ₁₂ ε₁ ≫ w₁ = 0) (hw₂ : η₂ ≫ w₁ = 0) (hw₃ : (η₂ ≫ x₂ ▷ R₂) ≫ w₁ = 𝟙 _) :
    rightZigzag (-(η₃ ≫ σi)) w₁ = (ρ_ E₂).hom ≫ (λ_ E₂).inv := by
  calc rightZigzag (-(η₃ ≫ σi)) w₁
      = E₂ ◁ (η₃ ≫ σi) ⊗≫
          (𝟙 _ ⊗≫ E₂ ◁ sigma η₃ τ₂₃ ε₂ ⊗≫ τ₂₃ ▷ R₃ ⊗≫ E₂ ◁ σi ⊗≫ E₂ ◁ ε₂ ⊗≫ 𝟙 _ :
            (E₂ ≫ R₂) ≫ E₂ ⟶ 𝟙 b ≫ E₂) := by
        rw [rightZigzag, counit_whiskerRight_eq η₂ ε₂ τ₁₂ ε₁ η₃ τ₂₃ hZ hτ₁₂ hτ₂₃ x₂ x₃ hNH hB hσ
          hsum hw₁ hw₂ hw₃]
        simp only [bicategoricalComp, whiskerLeft_neg, Preadditive.neg_comp,
          Preadditive.comp_neg, neg_neg]
    _ = E₂ ◁ η₃ ⊗≫ E₂ ◁ (σi ≫ sigma η₃ τ₂₃ ε₂) ⊗≫ τ₂₃ ▷ R₃ ⊗≫ E₂ ◁ σi ⊗≫ E₂ ◁ ε₂ ⊗≫ 𝟙 _ := by
        bicategory
    _ = (E₂ ◁ η₃ ⊗≫ τ₂₃ ▷ R₃ ⊗≫ E₂ ◁ σi ⊗≫ E₂ ◁ ε₂) ⊗≫ 𝟙 _ := by
        rw [hσi]; bicategory
    _ = (ρ_ E₂).hom ≫ (λ_ E₂).inv := by
        rw [unit_cross_inv_counit η₂ ε₂ η₃ τ₂₃ hZ hσ]; bicategory

end WeightNegTwo

/-! ## The one-zigzag lemma -/

section OneZigzag

variable {a b : C} {f : a ⟶ b} {g : b ⟶ a}

/-- The zigzag of the right adjoint does not change when the left adjoint is replaced by an
isomorphic 1-morphism. -/
theorem rightZigzag_comp_iso {f' : a ⟶ b} (η : 𝟙 a ⟶ f ≫ g) (ε : g ≫ f ⟶ 𝟙 b) (θ : f' ≅ f) :
    rightZigzag (η ≫ θ.inv ▷ g) (g ◁ θ.hom ≫ ε) = rightZigzag η ε := by
  calc rightZigzag (η ≫ θ.inv ▷ g) (g ◁ θ.hom ≫ ε)
      = g ◁ η ⊗≫ g ◁ (θ.inv ≫ θ.hom) ▷ g ⊗≫ ε ▷ g := by
        rw [rightZigzag]; bicategory
    _ = rightZigzag η ε := by
        rw [Iso.inv_hom_id, rightZigzag]; bicategory

/-- If `η`, `ε` satisfy the zigzag identity for `g`, the zigzag for `f` is idempotent. (The
mirror image of Mathlib's `rightZigzag_idempotent_of_left_triangle`.) -/
theorem leftZigzag_idempotent_of_right_triangle (η : 𝟙 a ⟶ f ≫ g) (ε : g ≫ f ⟶ 𝟙 b)
    (h : rightZigzag η ε = (ρ_ _).hom ≫ (λ_ _).inv) :
    leftZigzag η ε ⊗≫ leftZigzag η ε = leftZigzag η ε := by
  dsimp only [leftZigzag]
  calc
    _ = η ▷ f ⊗≫ ((𝟙 a ◁ f ◁ ε) ≫ η ▷ (f ≫ 𝟙 b)) ⊗≫ f ◁ ε := by
      bicategory
    _ = 𝟙 _ ⊗≫ (𝟙 a ◁ η ≫ η ▷ (f ≫ g)) ▷ f ⊗≫ f ◁ ((g ≫ f) ◁ ε ≫ ε ▷ 𝟙 b) ⊗≫ 𝟙 _ := by
      rw [whisker_exchange]; bicategory
    _ = η ▷ f ⊗≫ f ◁ rightZigzag η ε ▷ f ⊗≫ f ◁ ε := by
      rw [whisker_exchange, whisker_exchange, rightZigzag]; bicategory
    _ = η ▷ f ⊗≫ f ◁ ε := by
      rw [h]; bicategory

/-- If `η`, `ε` satisfy the zigzag identity for `g`, the counit absorbs the zigzag of `f`. -/
theorem whiskerLeft_leftZigzag_comp_counit (η : 𝟙 a ⟶ f ≫ g) (ε : g ≫ f ⟶ 𝟙 b)
    (h : rightZigzag η ε = (ρ_ _).hom ≫ (λ_ _).inv) :
    g ◁ leftZigzag η ε ⊗≫ ε = 𝟙 _ ⊗≫ ε := by
  calc g ◁ leftZigzag η ε ⊗≫ ε
      = 𝟙 _ ⊗≫ g ◁ η ▷ f ⊗≫ ((g ≫ f) ◁ ε ≫ ε ▷ 𝟙 b) ⊗≫ 𝟙 _ := by
        rw [leftZigzag]; bicategory
    _ = 𝟙 _ ⊗≫ rightZigzag η ε ▷ f ⊗≫ ε := by
        rw [whisker_exchange, rightZigzag]; bicategory
    _ = 𝟙 _ ⊗≫ ε := by
        rw [h]; bicategory

variable [∀ a b : C, Preadditive (a ⟶ b)] [AdditiveWhiskering C]

open AdditiveWhiskering

/-- **The one-zigzag lemma.** Let `η : 𝟙 ⟶ f ≫ g` and `ε : g ≫ f ⟶ 𝟙` satisfy the zigzag
identity for `g`. If the only idempotent endomorphisms of `f` are `0` and `1`, and `g` is not
zero, then `η` and `ε` are the unit and counit of an adjunction `f ⊣ g`. -/
def adjunctionOfRightTriangle (η : 𝟙 a ⟶ f ≫ g) (ε : g ≫ f ⟶ 𝟙 b)
    (h : rightZigzag η ε = (ρ_ _).hom ≫ (λ_ _).inv)
    (hloc : ∀ e : f ⟶ f, e ≫ e = e → e = 0 ∨ e = 𝟙 f) (hg : 𝟙 g ≠ 0) : f ⊣ g where
  unit := η
  counit := ε
  right_triangle := h
  left_triangle := by
    have hz : leftZigzag η ε = (λ_ f).hom ≫ ((λ_ f).inv ≫ leftZigzag η ε ≫ (ρ_ f).hom) ≫
        (ρ_ f).inv := by
      simp
    have he : ((λ_ f).inv ≫ leftZigzag η ε ≫ (ρ_ f).hom) ≫
        ((λ_ f).inv ≫ leftZigzag η ε ≫ (ρ_ f).hom) =
        (λ_ f).inv ≫ leftZigzag η ε ≫ (ρ_ f).hom := by
      calc ((λ_ f).inv ≫ leftZigzag η ε ≫ (ρ_ f).hom) ≫
            ((λ_ f).inv ≫ leftZigzag η ε ≫ (ρ_ f).hom)
          = (λ_ f).inv ≫ (leftZigzag η ε ⊗≫ leftZigzag η ε) ≫ (ρ_ f).hom := by
            simp [bicategoricalComp]
        _ = (λ_ f).inv ≫ leftZigzag η ε ≫ (ρ_ f).hom := by
            rw [leftZigzag_idempotent_of_right_triangle η ε h]
    rcases hloc _ he with h0 | h1
    · exfalso
      apply hg
      have hz0 : leftZigzag η ε = 0 := by
        rw [hz, h0, Limits.zero_comp, Limits.comp_zero]
      have hε : ε = 0 := by
        have h1 := whiskerLeft_leftZigzag_comp_counit η ε h
        rw [hz0, whiskerLeft_zero] at h1
        have h2 : (𝟙 _ ⊗≫ ε : g ≫ 𝟙 a ≫ f ⟶ 𝟙 b) = 0 := by
          rw [← h1]
          simp only [bicategoricalComp, Limits.zero_comp]
        calc ε = 𝟙 _ ⊗≫ (𝟙 _ ⊗≫ ε : g ≫ 𝟙 a ≫ f ⟶ 𝟙 b) := by bicategory
          _ = 0 := by rw [h2]; simp only [bicategoricalComp, Limits.comp_zero]
      have h3 : (ρ_ g).hom ≫ (λ_ g).inv = 0 := by
        rw [← h, rightZigzag, hε, zero_whiskerRight]
        simp only [bicategoricalComp, Limits.comp_zero]
      calc 𝟙 g = (ρ_ g).inv ≫ ((ρ_ g).hom ≫ (λ_ g).inv) ≫ (λ_ g).hom := by simp
        _ = 0 := by rw [h3, Limits.zero_comp, Limits.comp_zero]
    · rw [hz, h1, Category.id_comp]

end OneZigzag

end RightwardCrossing

end Categorification.TwoRep
