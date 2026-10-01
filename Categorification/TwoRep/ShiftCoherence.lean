/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.MateSh

/-!
# Shift coherence of a graded bicategory

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, §2.1.2 (`sec:categories`): in a graded additive 2-category "the composition maps
`Hom(A, B) × Hom(B, C) → Hom(A, C)` form graded additive `k`-linear functors". In a strict
2-category whose shift is a degree shift this means `X⟨a⟩ Y = (X Y)⟨a⟩ = X Y⟨a⟩` on the nose, and
homogeneous 2-morphisms of arbitrary degrees can be composed horizontally and vertically subject to
the (sign-free) axioms of a 2-category. For a bicategory with shift functors on its Hom categories
(`GradedBicategory`, `Basic.lean`) the same statement is a list of compatibilities between the
whiskering shift isomorphisms `whiskerLeftShiftIso : f ≫ g⟦n⟧ ≅ (f ≫ g)⟦n⟧` and
`whiskerRightShiftIso : f⟦n⟧ ≫ g ≅ (f ≫ g)⟦n⟧` and the structure isomorphisms of the bicategory.
These were introduced one at a time, where first needed:

* `GradedBicategory.ShiftInterchange` (`ShiftInterchange.lean`): the two whiskering shift
  isomorphisms are natural in the other variable and commute with each other;
* `GradedBicategory.ShiftAssoc` (`LemAprime.lean`), `GradedBicategory.ShiftAssocMid`
  (`MateSh.lean`), `GradedBicategory.ShiftAssocRight` (`CisBubRight.lean`): compatibility with the
  associator, with the shift on the right, middle and left factor of a triple composite;
* `GradedBicategory.ShiftUnitor` (`MateSh.lean`): compatibility with the unitors.

`GradedBicategory.ShiftCoherence B` is their conjunction, **shift coherence**. It packages the explicit coherence hypotheses needed for a future graded-Hom bicategory
construction; that construction is not asserted here. No boundedness or adjunction hypothesis
is used in this infrastructure. The boundedness assumption for the Prop. 3.9 route remains an
extra hypothesis, not part of the printed theorem; the unrestricted problem is separate.

This file also restates the associator and unitor compatibilities as identities between shifted
2-morphisms: the whiskering axioms of a bicategory (`id_whiskerLeft`, `comp_whiskerLeft`,
`whiskerRight_id`, `whiskerRight_comp`, `whisker_assoc`) for shifted 2-morphisms.

## Main declarations

* `GradedBicategory.ShiftCoherence`;
* `shWhiskerLeft_mk₀`, `shWhiskerRight_mk₀`: whiskering a 2-morphism of degree `0`;
* `shWhiskerLeft_of_id`, `shWhiskerLeft_of_comp`, `shWhiskerRight_of_id`,
  `shWhiskerRight_of_comp`, `shWhisker_assoc`: the whiskering axioms for shifted 2-morphisms.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory

universe w v u

/-- **Shift coherence** of a graded bicategory (CL §2.1.2: the composition functors are graded):
the whiskering shift isomorphisms `f ≫ g⟦n⟧ ≅ (f ≫ g)⟦n⟧` and `f⟦n⟧ ≫ g ≅ (f ≫ g)⟦n⟧` are natural
in the other variable, commute with each other (`ShiftInterchange`), and are compatible with the
associators (`ShiftAssoc`, `ShiftAssocMid`, `ShiftAssocRight`) and the unitors (`ShiftUnitor`).
This bundles existing coherence assumptions, without assuming biadjointness or boundedness. -/
class GradedBicategory.ShiftCoherence (B : Type u) [Bicategory.{w, v} B]
    [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B] : Prop
    extends GradedBicategory.ShiftInterchange B, GradedBicategory.ShiftAssoc B,
      GradedBicategory.ShiftAssocMid B, GradedBicategory.ShiftAssocRight B,
      GradedBicategory.ShiftUnitor B

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]

section Degree0

variable {a b c : B}

/-- Left whiskering of a 2-morphism of degree `0`. -/
theorem shWhiskerLeft_mk₀ (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) :
    shWhiskerLeft f (ShiftedHom.mk₀ (0 : ℤ) rfl η) = ShiftedHom.mk₀ (0 : ℤ) rfl (f ◁ η) :=
  ShiftedHom.map_mk₀ (0 : ℤ) rfl η (precomp c f)

/-- Right whiskering of a 2-morphism of degree `0`. -/
theorem shWhiskerRight_mk₀ {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) :
    shWhiskerRight (ShiftedHom.mk₀ (0 : ℤ) rfl η) h = ShiftedHom.mk₀ (0 : ℤ) rfl (η ▷ h) :=
  ShiftedHom.map_mk₀ (0 : ℤ) rfl η (postcomp a h)

end Degree0

section Unitors

variable [GradedBicategory.ShiftUnitor B] {a b : B}

/-- `𝟙 ◁ η = λ ≫ η ≫ λ⁻¹` for a shifted 2-morphism `η`. -/
theorem shWhiskerLeft_of_id {f g : a ⟶ b} {n : ℤ} (η : ShiftedHom f g n) :
    shWhiskerLeft (𝟙 a) η = (ShiftedHom.mk₀ (0 : ℤ) rfl (λ_ f).hom).comp
      (η.comp (ShiftedHom.mk₀ (0 : ℤ) rfl (λ_ g).inv) (zero_add n)) (add_zero n) := by
  rw [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀, shWhiskerLeft_eq]
  have h := GradedBicategory.ShiftUnitor.leftUnitor_shift g n
  rw [← cancel_mono (((λ_ g).hom)⟦n⟧'), Category.assoc, h]
  simp

/-- `η ▷ 𝟙 = ρ ≫ η ≫ ρ⁻¹` for a shifted 2-morphism `η`. -/
theorem shWhiskerRight_of_id {f g : a ⟶ b} {n : ℤ} (η : ShiftedHom f g n) :
    shWhiskerRight η (𝟙 b) = (ShiftedHom.mk₀ (0 : ℤ) rfl (ρ_ f).hom).comp
      (η.comp (ShiftedHom.mk₀ (0 : ℤ) rfl (ρ_ g).inv) (zero_add n)) (add_zero n) := by
  rw [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀, shWhiskerRight_eq]
  have h := GradedBicategory.ShiftUnitor.rightUnitor_shift g n
  rw [← cancel_mono (((ρ_ g).hom)⟦n⟧'), Category.assoc, h]
  simp

end Unitors

section Associators

variable {a b c d : B}

/-- `(f ≫ g) ◁ η = α ≫ f ◁ g ◁ η ≫ α⁻¹` for a shifted 2-morphism `η`. -/
theorem shWhiskerLeft_of_comp [GradedBicategory.ShiftAssoc B] (f : a ⟶ b) (g : b ⟶ c)
    {h h' : c ⟶ d} {n : ℤ} (η : ShiftedHom h h' n) :
    shWhiskerLeft (f ≫ g) η = (ShiftedHom.mk₀ (0 : ℤ) rfl (α_ f g h).hom).comp
      ((shWhiskerLeft f (shWhiskerLeft g η)).comp
        (ShiftedHom.mk₀ (0 : ℤ) rfl (α_ f g h').inv) (zero_add n)) (add_zero n) := by
  rw [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀]
  simp only [shWhiskerLeft_eq]
  have h₁ := GradedBicategory.ShiftAssoc.assoc_shift f g h' n
  rw [← cancel_mono (((α_ f g h').hom)⟦n⟧')]
  simp only [Category.assoc, Iso.map_inv_hom_id, Category.comp_id]
  rw [← h₁]
  simp

/-- `η ▷ (g ≫ h) = α⁻¹ ≫ η ▷ g ▷ h ≫ α` for a shifted 2-morphism `η`. -/
theorem shWhiskerRight_of_comp [GradedBicategory.ShiftAssocRight B] {f f' : a ⟶ b} {n : ℤ}
    (η : ShiftedHom f f' n) (g : b ⟶ c) (h : c ⟶ d) :
    shWhiskerRight η (g ≫ h) = (ShiftedHom.mk₀ (0 : ℤ) rfl (α_ f g h).inv).comp
      ((shWhiskerRight (shWhiskerRight η g) h).comp
        (ShiftedHom.mk₀ (0 : ℤ) rfl (α_ f' g h).hom) (zero_add n)) (add_zero n) := by
  rw [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀]
  simp only [shWhiskerRight_eq]
  have h₁ := GradedBicategory.ShiftAssocRight.assoc_shift_right f' g h n
  rw [← cancel_mono (((α_ f' g h).inv)⟦n⟧')]
  simp only [Category.assoc, Iso.map_hom_inv_id, Category.comp_id]
  rw [← h₁]
  simp

/-- `(f ◁ η) ▷ h = α ≫ f ◁ (η ▷ h) ≫ α⁻¹` for a shifted 2-morphism `η`. -/
theorem shWhisker_assoc [GradedBicategory.ShiftAssocMid B] (f : a ⟶ b) {g g' : b ⟶ c} {n : ℤ}
    (η : ShiftedHom g g' n) (h : c ⟶ d) :
    shWhiskerRight (shWhiskerLeft f η) h = (ShiftedHom.mk₀ (0 : ℤ) rfl (α_ f g h).hom).comp
      ((shWhiskerLeft f (shWhiskerRight η h)).comp
        (ShiftedHom.mk₀ (0 : ℤ) rfl (α_ f g' h).inv) (zero_add n)) (add_zero n) := by
  rw [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀]
  simp only [shWhiskerLeft_eq, shWhiskerRight_eq]
  have h₁ := GradedBicategory.ShiftAssocMid.assoc_shift_mid f g' h n
  rw [← cancel_mono (((α_ f g' h).hom)⟦n⟧')]
  simp only [comp_whiskerRight, Category.assoc, Iso.map_inv_hom_id, Category.comp_id]
  rw [← h₁]
  simp

end Associators

end Categorification.TwoRep
