/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.ModelQStrongSl2

/-!
# Mixed-label KLR relations in the model of a `Q`-strong 2-representation

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, Definition 1.2 (4) and §2.3: for the model of
`Categorification.TwoRep.ModelQStrong` (normalized dots `r_i⁻¹ x`), the KLR relations on upward
strands that do not involve the polynomials `Q_{ij}` are killed, each read with its own outer
regions:

* the dot slides through a crossing of differently labelled strands (CL (2.12); KL III
  Definition 3.1, relations of `R(ν)`): `killed_klr_slideLNe`, `killed_klr_slideRNe`;
* the braid relation (CL (2.13)) for all bottom labels `c d e` except `c = e ≠ d`:
  `killed_klr_braid_gen` (for `c = d = e` this is also `killed_klr_braid`).

The relations are first proved in the graded-Hom bicategory (`crossQ_dot_slide_left`,
`crossQ_dot_slide_right`, `crossQ_braid`). In the braid diagrams the intermediate words carry
regions that are equal but not syntactically equal (`λ + α_c + α_e` read in two orders), so the
images of consecutive layers are separated by transports; the normal-form lemmas
`chain3_keyZ2`, `chain3_keyZ12` absorb these into images of free 2-morphisms, and
`crossQ_braid_cast` is the braid relation with the corresponding transports.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory

universe w v u u₁

section Mid

open StringDiagrams Diagrams.BicatInterp

variable {S : Signature} {D : Type*} [Bicategory D] (M : Model S D) {a b c d : FB S}

/-- **Three layers in normal form**, with transports between the first and the second and
between the second and the third layer (fully reassociated). -/
theorem chain3_key_mid {W₀ W₁ W₂ W₃ P Q₁ P₂ Q₂ P₃ Q : a ⟶ d}
    {p₁ : a ⟶ b} {q₁ : c ⟶ d} {x₁ y₁ : b ⟶ c} (τ₁ : p₁ ≫ (x₁ ≫ q₁) ≅ W₀)
    (τ₁' : p₁ ≫ (y₁ ≫ q₁) ≅ W₁) (g₁ : M.lift.map x₁ ⟶ M.lift.map y₁)
    {b₂ c₂ : FB S} {p₂ : a ⟶ b₂} {q₂ : c₂ ⟶ d} {x₂ y₂ : b₂ ⟶ c₂} (τ₂ : p₂ ≫ (x₂ ≫ q₂) ≅ W₁)
    (τ₂' : p₂ ≫ (y₂ ≫ q₂) ≅ W₂) (g₂ : M.lift.map x₂ ⟶ M.lift.map y₂)
    {b₃ c₃ : FB S} {p₃ : a ⟶ b₃} {q₃ : c₃ ⟶ d} {x₃ y₃ : b₃ ⟶ c₃} (τ₃ : p₃ ≫ (x₃ ≫ q₃) ≅ W₂)
    (τ₃' : p₃ ≫ (y₃ ≫ q₃) ≅ W₃) (g₃ : M.lift.map x₃ ⟶ M.lift.map y₃)
    (A₁ : P ⟶ p₁ ≫ (x₁ ≫ q₁)) (B₁ : p₁ ≫ (y₁ ≫ q₁) ⟶ Q₁) (E₁ : Q₁ ⟶ P₂)
    (A₂ : P₂ ⟶ p₂ ≫ (x₂ ≫ q₂)) (B₂ : p₂ ≫ (y₂ ≫ q₂) ⟶ Q₂) (E₂ : Q₂ ⟶ P₃)
    (A₃ : P₃ ⟶ p₃ ≫ (x₃ ≫ q₃)) (B₃ : p₃ ≫ (y₃ ≫ q₃) ⟶ Q)
    (X : P ⟶ W₀) (Y : W₃ ⟶ Q) :
    M.lift.map₂ A₁ ≫ midK M p₁ q₁ g₁ ≫ M.lift.map₂ B₁ ≫ M.lift.map₂ E₁ ≫
        M.lift.map₂ A₂ ≫ midK M p₂ q₂ g₂ ≫ M.lift.map₂ B₂ ≫ M.lift.map₂ E₂ ≫
          M.lift.map₂ A₃ ≫ midK M p₃ q₃ g₃ ≫ M.lift.map₂ B₃ =
      M.lift.map₂ X ≫ layerAt M τ₁ τ₁' g₁ ≫ layerAt M τ₂ τ₂' g₂ ≫ layerAt M τ₃ τ₃' g₃ ≫
        M.lift.map₂ Y := by
  have h := chain3_key M τ₁ τ₁' g₁ τ₂ τ₂' g₂ τ₃ τ₃' g₃ (𝟙 _) A₁ B₁ E₁ A₂ B₂ E₂ A₃ B₃ (𝟙 _) X Y
  simp only [PrelaxFunctor.map₂_id, Category.id_comp, Category.comp_id, Category.assoc] at h
  exact h

/-- `chain3_key_mid` with a transport only between the first and the second layer. -/
theorem chain3_key_mid1 {W₀ W₁ W₂ W₃ P Q₁ P₂ Q₂ Q : a ⟶ d}
    {p₁ : a ⟶ b} {q₁ : c ⟶ d} {x₁ y₁ : b ⟶ c} (τ₁ : p₁ ≫ (x₁ ≫ q₁) ≅ W₀)
    (τ₁' : p₁ ≫ (y₁ ≫ q₁) ≅ W₁) (g₁ : M.lift.map x₁ ⟶ M.lift.map y₁)
    {b₂ c₂ : FB S} {p₂ : a ⟶ b₂} {q₂ : c₂ ⟶ d} {x₂ y₂ : b₂ ⟶ c₂} (τ₂ : p₂ ≫ (x₂ ≫ q₂) ≅ W₁)
    (τ₂' : p₂ ≫ (y₂ ≫ q₂) ≅ W₂) (g₂ : M.lift.map x₂ ⟶ M.lift.map y₂)
    {b₃ c₃ : FB S} {p₃ : a ⟶ b₃} {q₃ : c₃ ⟶ d} {x₃ y₃ : b₃ ⟶ c₃} (τ₃ : p₃ ≫ (x₃ ≫ q₃) ≅ W₂)
    (τ₃' : p₃ ≫ (y₃ ≫ q₃) ≅ W₃) (g₃ : M.lift.map x₃ ⟶ M.lift.map y₃)
    (A₁ : P ⟶ p₁ ≫ (x₁ ≫ q₁)) (B₁ : p₁ ≫ (y₁ ≫ q₁) ⟶ Q₁) (E₁ : Q₁ ⟶ P₂)
    (A₂ : P₂ ⟶ p₂ ≫ (x₂ ≫ q₂)) (B₂ : p₂ ≫ (y₂ ≫ q₂) ⟶ Q₂)
    (A₃ : Q₂ ⟶ p₃ ≫ (x₃ ≫ q₃)) (B₃ : p₃ ≫ (y₃ ≫ q₃) ⟶ Q)
    (X : P ⟶ W₀) (Y : W₃ ⟶ Q) :
    M.lift.map₂ A₁ ≫ midK M p₁ q₁ g₁ ≫ M.lift.map₂ B₁ ≫ M.lift.map₂ E₁ ≫
        M.lift.map₂ A₂ ≫ midK M p₂ q₂ g₂ ≫ M.lift.map₂ B₂ ≫
          M.lift.map₂ A₃ ≫ midK M p₃ q₃ g₃ ≫ M.lift.map₂ B₃ =
      M.lift.map₂ X ≫ layerAt M τ₁ τ₁' g₁ ≫ layerAt M τ₂ τ₂' g₂ ≫ layerAt M τ₃ τ₃' g₃ ≫
        M.lift.map₂ Y := by
  have h := chain3_key_mid M τ₁ τ₁' g₁ τ₂ τ₂' g₂ τ₃ τ₃' g₃ A₁ B₁ E₁ A₂ B₂ (𝟙 _) A₃ B₃ X Y
  simp only [PrelaxFunctor.map₂_id, Category.id_comp] at h
  exact h

/-- `chain3_key_mid` with a transport only between the second and the third layer. -/
theorem chain3_key_mid2 {W₀ W₁ W₂ W₃ P Q₁ Q₂ P₃ Q : a ⟶ d}
    {p₁ : a ⟶ b} {q₁ : c ⟶ d} {x₁ y₁ : b ⟶ c} (τ₁ : p₁ ≫ (x₁ ≫ q₁) ≅ W₀)
    (τ₁' : p₁ ≫ (y₁ ≫ q₁) ≅ W₁) (g₁ : M.lift.map x₁ ⟶ M.lift.map y₁)
    {b₂ c₂ : FB S} {p₂ : a ⟶ b₂} {q₂ : c₂ ⟶ d} {x₂ y₂ : b₂ ⟶ c₂} (τ₂ : p₂ ≫ (x₂ ≫ q₂) ≅ W₁)
    (τ₂' : p₂ ≫ (y₂ ≫ q₂) ≅ W₂) (g₂ : M.lift.map x₂ ⟶ M.lift.map y₂)
    {b₃ c₃ : FB S} {p₃ : a ⟶ b₃} {q₃ : c₃ ⟶ d} {x₃ y₃ : b₃ ⟶ c₃} (τ₃ : p₃ ≫ (x₃ ≫ q₃) ≅ W₂)
    (τ₃' : p₃ ≫ (y₃ ≫ q₃) ≅ W₃) (g₃ : M.lift.map x₃ ⟶ M.lift.map y₃)
    (A₁ : P ⟶ p₁ ≫ (x₁ ≫ q₁)) (B₁ : p₁ ≫ (y₁ ≫ q₁) ⟶ Q₁)
    (A₂ : Q₁ ⟶ p₂ ≫ (x₂ ≫ q₂)) (B₂ : p₂ ≫ (y₂ ≫ q₂) ⟶ Q₂) (E₂ : Q₂ ⟶ P₃)
    (A₃ : P₃ ⟶ p₃ ≫ (x₃ ≫ q₃)) (B₃ : p₃ ≫ (y₃ ≫ q₃) ⟶ Q)
    (X : P ⟶ W₀) (Y : W₃ ⟶ Q) :
    M.lift.map₂ A₁ ≫ midK M p₁ q₁ g₁ ≫ M.lift.map₂ B₁ ≫
        M.lift.map₂ A₂ ≫ midK M p₂ q₂ g₂ ≫ M.lift.map₂ B₂ ≫ M.lift.map₂ E₂ ≫
          M.lift.map₂ A₃ ≫ midK M p₃ q₃ g₃ ≫ M.lift.map₂ B₃ =
      M.lift.map₂ X ≫ layerAt M τ₁ τ₁' g₁ ≫ layerAt M τ₂ τ₂' g₂ ≫ layerAt M τ₃ τ₃' g₃ ≫
        M.lift.map₂ Y := by
  have h := chain3_key_mid M τ₁ τ₁' g₁ τ₂ τ₂' g₂ τ₃ τ₃' g₃ A₁ B₁ (𝟙 _) A₂ B₂ E₂ A₃ B₃ X Y
  simp only [PrelaxFunctor.map₂_id, Category.id_comp] at h
  exact h

/-- **Three layers in normal form**, with a transport between the second and the third layer,
which becomes the image `Z` of a free 2-morphism between the normal forms. -/
theorem chain3_keyZ2 {W₀ W₁ W₂ W₂' W₃ P Q₁ Q₂ P₃ Q : a ⟶ d}
    {p₁ : a ⟶ b} {q₁ : c ⟶ d} {x₁ y₁ : b ⟶ c} (τ₁ : p₁ ≫ (x₁ ≫ q₁) ≅ W₀)
    (τ₁' : p₁ ≫ (y₁ ≫ q₁) ≅ W₁) (g₁ : M.lift.map x₁ ⟶ M.lift.map y₁)
    {b₂ c₂ : FB S} {p₂ : a ⟶ b₂} {q₂ : c₂ ⟶ d} {x₂ y₂ : b₂ ⟶ c₂} (τ₂ : p₂ ≫ (x₂ ≫ q₂) ≅ W₁)
    (τ₂' : p₂ ≫ (y₂ ≫ q₂) ≅ W₂) (g₂ : M.lift.map x₂ ⟶ M.lift.map y₂)
    {b₃ c₃ : FB S} {p₃ : a ⟶ b₃} {q₃ : c₃ ⟶ d} {x₃ y₃ : b₃ ⟶ c₃} (τ₃ : p₃ ≫ (x₃ ≫ q₃) ≅ W₂')
    (τ₃' : p₃ ≫ (y₃ ≫ q₃) ≅ W₃) (g₃ : M.lift.map x₃ ⟶ M.lift.map y₃)
    (A₁ : P ⟶ p₁ ≫ (x₁ ≫ q₁)) (B₁ : p₁ ≫ (y₁ ≫ q₁) ⟶ Q₁)
    (A₂ : Q₁ ⟶ p₂ ≫ (x₂ ≫ q₂)) (B₂ : p₂ ≫ (y₂ ≫ q₂) ⟶ Q₂) (E₂ : Q₂ ⟶ P₃)
    (A₃ : P₃ ⟶ p₃ ≫ (x₃ ≫ q₃)) (B₃ : p₃ ≫ (y₃ ≫ q₃) ⟶ Q)
    (X : P ⟶ W₀) (Z : W₂ ⟶ W₂') (Y : W₃ ⟶ Q) :
    M.lift.map₂ A₁ ≫ midK M p₁ q₁ g₁ ≫ M.lift.map₂ B₁ ≫
        M.lift.map₂ A₂ ≫ midK M p₂ q₂ g₂ ≫ M.lift.map₂ B₂ ≫ M.lift.map₂ E₂ ≫
          M.lift.map₂ A₃ ≫ midK M p₃ q₃ g₃ ≫ M.lift.map₂ B₃ =
      M.lift.map₂ X ≫ layerAt M τ₁ τ₁' g₁ ≫ layerAt M τ₂ τ₂' g₂ ≫ M.lift.map₂ Z ≫
        layerAt M τ₃ τ₃' g₃ ≫ M.lift.map₂ Y := by
  calc _ = M.lift.map₂ A₁ ≫ midK M p₁ q₁ g₁ ≫ M.lift.map₂ (B₁ ≫ A₂) ≫
        midK M p₂ q₂ g₂ ≫ M.lift.map₂ (B₂ ≫ E₂ ≫ A₃) ≫ midK M p₃ q₃ g₃ ≫
          M.lift.map₂ B₃ := by
          simp only [PrelaxFunctor.map₂_comp, Category.assoc]
    _ = M.lift.map₂ (X ≫ τ₁.inv) ≫ midK M p₁ q₁ g₁ ≫ M.lift.map₂ (τ₁'.hom ≫ τ₂.inv) ≫
        midK M p₂ q₂ g₂ ≫ M.lift.map₂ (τ₂'.hom ≫ Z ≫ τ₃.inv) ≫ midK M p₃ q₃ g₃ ≫
          M.lift.map₂ (τ₃'.hom ≫ Y) := by
          rw [lift_map₂_eq M A₁ (X ≫ τ₁.inv),
            lift_map₂_eq M (B₁ ≫ A₂) (τ₁'.hom ≫ τ₂.inv),
            lift_map₂_eq M (B₂ ≫ E₂ ≫ A₃) (τ₂'.hom ≫ Z ≫ τ₃.inv),
            lift_map₂_eq M B₃ (τ₃'.hom ≫ Y)]
    _ = _ := by simp only [layerAt, PrelaxFunctor.map₂_comp, Category.assoc]

/-- **Three layers in normal form**, with transports between consecutive layers (becoming `Z₁`
and `Z₂`). -/
theorem chain3_keyZ12 {W₀ W₁ W₁' W₂ W₂' W₃ P Q₁ P₂ Q₂ P₃ Q : a ⟶ d}
    {p₁ : a ⟶ b} {q₁ : c ⟶ d} {x₁ y₁ : b ⟶ c} (τ₁ : p₁ ≫ (x₁ ≫ q₁) ≅ W₀)
    (τ₁' : p₁ ≫ (y₁ ≫ q₁) ≅ W₁) (g₁ : M.lift.map x₁ ⟶ M.lift.map y₁)
    {b₂ c₂ : FB S} {p₂ : a ⟶ b₂} {q₂ : c₂ ⟶ d} {x₂ y₂ : b₂ ⟶ c₂} (τ₂ : p₂ ≫ (x₂ ≫ q₂) ≅ W₁')
    (τ₂' : p₂ ≫ (y₂ ≫ q₂) ≅ W₂) (g₂ : M.lift.map x₂ ⟶ M.lift.map y₂)
    {b₃ c₃ : FB S} {p₃ : a ⟶ b₃} {q₃ : c₃ ⟶ d} {x₃ y₃ : b₃ ⟶ c₃} (τ₃ : p₃ ≫ (x₃ ≫ q₃) ≅ W₂')
    (τ₃' : p₃ ≫ (y₃ ≫ q₃) ≅ W₃) (g₃ : M.lift.map x₃ ⟶ M.lift.map y₃)
    (A₁ : P ⟶ p₁ ≫ (x₁ ≫ q₁)) (B₁ : p₁ ≫ (y₁ ≫ q₁) ⟶ Q₁) (E₁ : Q₁ ⟶ P₂)
    (A₂ : P₂ ⟶ p₂ ≫ (x₂ ≫ q₂)) (B₂ : p₂ ≫ (y₂ ≫ q₂) ⟶ Q₂) (E₂ : Q₂ ⟶ P₃)
    (A₃ : P₃ ⟶ p₃ ≫ (x₃ ≫ q₃)) (B₃ : p₃ ≫ (y₃ ≫ q₃) ⟶ Q)
    (X : P ⟶ W₀) (Z₁ : W₁ ⟶ W₁') (Z₂ : W₂ ⟶ W₂') (Y : W₃ ⟶ Q) :
    M.lift.map₂ A₁ ≫ midK M p₁ q₁ g₁ ≫ M.lift.map₂ B₁ ≫ M.lift.map₂ E₁ ≫
        M.lift.map₂ A₂ ≫ midK M p₂ q₂ g₂ ≫ M.lift.map₂ B₂ ≫ M.lift.map₂ E₂ ≫
          M.lift.map₂ A₃ ≫ midK M p₃ q₃ g₃ ≫ M.lift.map₂ B₃ =
      M.lift.map₂ X ≫ layerAt M τ₁ τ₁' g₁ ≫ M.lift.map₂ Z₁ ≫ layerAt M τ₂ τ₂' g₂ ≫
        M.lift.map₂ Z₂ ≫ layerAt M τ₃ τ₃' g₃ ≫ M.lift.map₂ Y := by
  calc _ = M.lift.map₂ A₁ ≫ midK M p₁ q₁ g₁ ≫ M.lift.map₂ (B₁ ≫ E₁ ≫ A₂) ≫
        midK M p₂ q₂ g₂ ≫ M.lift.map₂ (B₂ ≫ E₂ ≫ A₃) ≫ midK M p₃ q₃ g₃ ≫
          M.lift.map₂ B₃ := by
          simp only [PrelaxFunctor.map₂_comp, Category.assoc]
    _ = M.lift.map₂ (X ≫ τ₁.inv) ≫ midK M p₁ q₁ g₁ ≫ M.lift.map₂ (τ₁'.hom ≫ Z₁ ≫ τ₂.inv) ≫
        midK M p₂ q₂ g₂ ≫ M.lift.map₂ (τ₂'.hom ≫ Z₂ ≫ τ₃.inv) ≫ midK M p₃ q₃ g₃ ≫
          M.lift.map₂ (τ₃'.hom ≫ Y) := by
          rw [lift_map₂_eq M A₁ (X ≫ τ₁.inv),
            lift_map₂_eq M (B₁ ≫ E₁ ≫ A₂) (τ₁'.hom ≫ Z₁ ≫ τ₂.inv),
            lift_map₂_eq M (B₂ ≫ E₂ ≫ A₃) (τ₂'.hom ≫ Z₂ ≫ τ₃.inv),
            lift_map₂_eq M B₃ (τ₃'.hom ≫ Y)]
    _ = _ := by simp only [layerAt, PrelaxFunctor.map₂_comp, Category.assoc]

end Mid

section Model

open GradedHomBicat
open QuantumGroup UDot KL3.Diagram StringDiagrams Diagrams.BicatInterp
open KrullSchmidtCat (HomFinite)

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [GradedBicategory.ShiftCoherence B] [GradedBicategory.IsLinear B k]
  [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)]
  {I : Type*} {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {Q : I → I → MvPolynomial (Fin 2) k}

namespace QStrong

/-! ## The relations in the graded-Hom bicategory -/

section Gr

variable (S : QStrong B C RD k Q)

/-- CL (2.12), for `i ≠ j`: the (normalized) dot on the `j`-strand slides through `τ_{ij}`. -/
theorem crossQ_dot_slide_right (i j : I) (hij : i ≠ j) {l n m n' : X} (h₁ : l + RD.iX j = n)
    (h₂ : n + RD.iX i = m) (h₃ : l + RD.iX i = n') (h₄ : n' + RD.iX j = m) :
    S.dotQ j h₁ ▷ S.Eg i h₂ ≫ S.crossQ i j h₁ h₂ h₃ h₄ =
      S.crossQ i j h₁ h₂ h₃ h₄ ≫ S.Eg i h₃ ◁ S.dotQ j h₄ := by
  have h := congrArg (of₂ (C.dot j j - C.dot i j)) (S.klr.dot_slide_right i j hij h₁ h₂ h₃ h₄)
  rw [← of₂_comp_of₂, ← of₂_comp_of₂, ← whiskerLeft_of₂, ← of₂_whiskerRight] at h
  simp only [dotQ, crossQ, GradedHomBicat.whiskerLeft_smul, GradedHomBicat.smul_whiskerRight,
    Linear.smul_comp, Linear.comp_smul]
  rw [h]

/-- CL (2.12), for `i ≠ j`: the (normalized) dot on the `i`-strand slides through `τ_{ij}`. -/
theorem crossQ_dot_slide_left (i j : I) (hij : i ≠ j) {l n m n' : X} (h₁ : l + RD.iX j = n)
    (h₂ : n + RD.iX i = m) (h₃ : l + RD.iX i = n') (h₄ : n' + RD.iX j = m) :
    S.Eg j h₁ ◁ S.dotQ i h₂ ≫ S.crossQ i j h₁ h₂ h₃ h₄ =
      S.crossQ i j h₁ h₂ h₃ h₄ ≫ S.dotQ i h₃ ▷ S.Eg j h₄ := by
  have h := congrArg (of₂ (C.dot i i - C.dot i j)) (S.klr.dot_slide_left i j hij h₁ h₂ h₃ h₄)
  rw [← of₂_comp_of₂, ← of₂_comp_of₂, ← whiskerLeft_of₂, ← of₂_whiskerRight] at h
  simp only [dotQ, crossQ, GradedHomBicat.whiskerLeft_smul, GradedHomBicat.smul_whiskerRight,
    Linear.smul_comp, Linear.comp_smul]
  rw [h]

/-- CL (2.13): the braid relation for the crossings of a `Q`-strong 2-representation, unless
`i = c` and `(α_i, α_j) < 0` (bottom labels `i j c`). -/
theorem crossQ_braid (i j c : I) (hb : ¬ (i = c ∧ C.dot i j < 0))
    {l w₁ w₂ w₃ w₄ w₅ w₆ m : X} (e1 : l + RD.iX c = w₁) (e2 : w₁ + RD.iX j = w₂)
    (e3 : w₂ + RD.iX i = m) (e4 : w₁ + RD.iX i = w₃) (e5 : w₃ + RD.iX j = m)
    (e6 : l + RD.iX i = w₄) (e7 : w₄ + RD.iX c = w₃) (e8 : w₄ + RD.iX j = w₅)
    (e9 : w₅ + RD.iX c = m) (e10 : l + RD.iX j = w₆) (e11 : w₆ + RD.iX c = w₂)
    (e12 : w₆ + RD.iX i = w₅) :
    S.Eg c e1 ◁ S.crossQ i j e2 e3 e4 e5 ≫
        ((α_ (S.Eg c e1) (S.Eg i e4) (S.Eg j e5)).inv ≫ S.crossQ i c e1 e4 e6 e7 ▷ S.Eg j e5 ≫
          (α_ (S.Eg i e6) (S.Eg c e7) (S.Eg j e5)).hom) ≫
        S.Eg i e6 ◁ S.crossQ j c e7 e5 e8 e9 =
      ((α_ (S.Eg c e1) (S.Eg j e2) (S.Eg i e3)).inv ≫ S.crossQ j c e1 e2 e10 e11 ▷ S.Eg i e3 ≫
          (α_ (S.Eg j e10) (S.Eg c e11) (S.Eg i e3)).hom) ≫
        S.Eg j e10 ◁ S.crossQ i c e11 e3 e12 e9 ≫
        ((α_ (S.Eg j e10) (S.Eg i e12) (S.Eg c e9)).inv ≫ S.crossQ i j e10 e12 e6 e8 ▷ S.Eg c e9 ≫
          (α_ (S.Eg i e6) (S.Eg j e8) (S.Eg c e9)).hom) := by
  have h := congrArg (of₂ (-(C.dot i j + C.dot i c + C.dot j c)))
    (S.klr.braid i j c hb e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12)
  simp only [KLRGens.braidLRL, KLRGens.braidRLR, KLRGens.crossL, KLRGens.crossR] at h
  simp only [← of₂_comp_of₂, Category.assoc] at h
  simp only [crossQ, whiskerLeft_of₂, of₂_whiskerRight, associator_hom_eq, associator_inv_eq,
    incl₂_eq_of₂, Category.assoc]
  exact h

/-- The braid relation (CL (2.13), bottom labels `c d e`) in the form produced by the
interpretation of the braid diagrams: the intermediate weights `w₂'`, `w₃'`, `w₅'` are equal to
`w₂`, `w₃`, `w₅` but not syntactically, and are related by transports. -/
theorem crossQ_braid_cast (c d e : I) (hb : ¬ (c = e ∧ C.dot c d < 0))
    {l w₁ w₂ w₂' w₃ w₃' w₄ w₅ w₅' w₆ m : X}
    (e1 : l + RD.iX e = w₁) (e2 : w₁ + RD.iX d = w₂) (e3 : w₂ + RD.iX c = m)
    (e4 : w₁ + RD.iX c = w₃) (e5 : w₃ + RD.iX d = m) (e6 : l + RD.iX c = w₄)
    (e7 : w₄ + RD.iX e = w₃) (e8 : w₄ + RD.iX d = w₅) (e9 : w₅ + RD.iX e = m)
    (e10 : l + RD.iX d = w₆) (e11 : w₆ + RD.iX e = w₂) (e12 : w₆ + RD.iX c = w₅)
    (e7' : w₄ + RD.iX e = w₃') (e5' : w₃' + RD.iX d = m) (e11' : w₆ + RD.iX e = w₂')
    (e3' : w₂' + RD.iX c = m) (e12' : w₆ + RD.iX c = w₅') (e9' : w₅' + RD.iX e = m)
    (hw₂ : w₂' = w₂) (hw₃ : w₃' = w₃) (hw₅ : w₅' = w₅)
    (p₁ : (S.Eg c e6 ≫ S.Eg e e7) ≫ S.Eg d e5 = (S.Eg c e6 ≫ S.Eg e e7') ≫ S.Eg d e5')
    (p₂ : (S.Eg d e10 ≫ S.Eg e e11) ≫ S.Eg c e3 = (S.Eg d e10 ≫ S.Eg e e11') ≫ S.Eg c e3')
    (p₃ : (S.Eg d e10 ≫ S.Eg c e12') ≫ S.Eg e e9' = (S.Eg d e10 ≫ S.Eg c e12) ≫ S.Eg e e9) :
    ((α_ (S.Eg e e1) (S.Eg d e2) (S.Eg c e3)).hom ≫ S.Eg e e1 ◁ S.crossQ c d e2 e3 e4 e5 ≫
        (α_ (S.Eg e e1) (S.Eg c e4) (S.Eg d e5)).inv) ≫
      S.crossQ c e e1 e4 e6 e7 ▷ S.Eg d e5 ≫ eqToHom p₁ ≫
        ((α_ (S.Eg c e6) (S.Eg e e7') (S.Eg d e5')).hom ≫
          S.Eg c e6 ◁ S.crossQ d e e7' e5' e8 e9 ≫ (α_ (S.Eg c e6) (S.Eg d e8) (S.Eg e e9)).inv) =
    S.crossQ d e e1 e2 e10 e11 ▷ S.Eg c e3 ≫ eqToHom p₂ ≫
      ((α_ (S.Eg d e10) (S.Eg e e11') (S.Eg c e3')).hom ≫
        S.Eg d e10 ◁ S.crossQ c e e11' e3' e12' e9' ≫
          (α_ (S.Eg d e10) (S.Eg c e12') (S.Eg e e9')).inv) ≫
        eqToHom p₃ ≫ S.crossQ c d e10 e12 e6 e8 ▷ S.Eg e e9 := by
  subst hw₂ hw₃ hw₅
  simp only [eqToHom_refl, Category.id_comp]
  have h := S.crossQ_braid c d e hb e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12
  apply (cancel_epi (α_ (S.Eg e e1) (S.Eg d e2) (S.Eg c e3)).inv).1
  apply (cancel_mono (α_ (S.Eg c e6) (S.Eg d e8) (S.Eg e e9)).hom).1
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id] at h ⊢
  exact h

end Gr


/-! ## The relations on upward strands -/

section Up

variable {S : QStrong B C RD k Q} (Sc : CL.CLScalars C k)

attribute [local irreducible] KL3.Diagram.sh

theorem sig0_colourSrc_g (c : Col I X) :
    (sig0 RD).colourSrc c = sh RD c.l + c.r := rfl

theorem sig0_colourTgt_g (c : Col I X) : (sig0 RD).colourTgt c = c.r := rfl

theorem sig0_dom_dot_g (c : Col I X) : (sig0 RD).dom (.dot c) = [c] := rfl

theorem sig0_cod_dot_g (c : Col I X) : (sig0 RD).cod (.dot c) = [c] := rfl

theorem sig0_dom_cross_g (e : Bool) (i j : I) (ν : X) :
    (sig0 RD).dom (.cross e i j ν) = wd RD ν [(e, i), (e, j)] := rfl

theorem sig0_cod_cross_g (e : Bool) (i j : I) (ν : X) :
    (sig0 RD).cod (.cross e i j ν) = wd RD ν [(e, j), (e, i)] := rfl

theorem upDiag_X2_D0_g (c d : I) (μ : X) :
    upDiag RD μ (KLR.Diagram.X2 c d ≫ KLR.Diagram.D0 d c) =
      mkD RD μ [([], .cross true c d, []), ([], .dot (up d), [up c])]
        ⟨rfl, rfl, rfl⟩ := by
  rfl

theorem upDiag_D1_X2_g (c d : I) (μ : X) :
    upDiag RD μ (KLR.Diagram.D1 c d ≫ KLR.Diagram.X2 c d) =
      mkD RD μ [([up c], .dot (up d), []), ([], .cross true c d, [])]
        ⟨rfl, rfl, rfl⟩ := by
  rfl

set_option maxHeartbeats 2000000 in
/-- The dot slide `τ (x on the left strand) = (x on the right strand) τ` for differently labelled
strands. -/
theorem klr_slideLNe (c d : I) (h : c ≠ d) (μ : X) :
    (interp (genImg (S := S) Sc) (KL3.Diagram.wt RD μ [up c, up d] : X) μ).functor.map
        (upDiag RD μ (KLR.Diagram.X2 c d ≫ KLR.Diagram.D0 d c)) -
      (interp (genImg (S := S) Sc) (KL3.Diagram.wt RD μ [up c, up d] : X) μ).functor.map
        (upDiag RD μ (KLR.Diagram.D1 c d ≫ KLR.Diagram.X2 c d)) = 0 := by
  rw [upDiag_X2_D0_g, upDiag_D1_X2_g]
  have hc : Cond (S := psig RD) (KL3.Diagram.wt RD μ [up c, up d] : X) μ
      (ob RD μ [up c, up d]) := ⟨⟨rfl, rfl, trivial⟩, rfl, rfl⟩
  have hc' : Cond (S := psig RD) (KL3.Diagram.wt RD μ [up c, up d] : X) μ
      (ob RD μ [up d, up c]) :=
    ⟨⟨@add_left_comm X _ _ _ _, rfl, trivial⟩, rfl, @add_left_comm X _ _ _ _⟩
  apply (cancel_epi (eqToHom (objI_pos _ _ hc).symm)).1
  apply (cancel_mono (eqToHom (objI_pos _ _ hc'))).1
  set_option backward.isDefEq.respectTransparency false in
  simp only [Limits.comp_zero, Limits.zero_comp, Preadditive.sub_comp, Preadditive.comp_sub]
  set_option backward.isDefEq.respectTransparency false in
  simp only [Interpretation.functor_map, mkD, Diagram.layers_mk, layList_cons, layList_nil,
    Interpretation.mapChain]
  set_option backward.isDefEq.respectTransparency false in
  simp only [lay, Shape.gen, wd_cons, wd_nil, wt_cons, wt_nil, List.nil_append,
    List.cons_append, Shape.dom]
  rw [layerI_pos _ _ _ _ ?c1]
  try rw [layerI_pos _ _ _ _ ?c2]
  try rw [layerI_pos _ _ _ _ ?c3]
  try rw [layerI_pos _ _ _ _ ?c4]
  all_goals try (refine ⟨?_, ?_, ?_⟩ <;>
      simp [Signature.ok, Signature.endR, Layer.dom, sig0_colourSrc_g, sig0_colourTgt_g,
        sig0_dom_cross_g, sig0_dom_dot_g, add_left_comm])
  set_option backward.isDefEq.respectTransparency false in
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl, Category.comp_id,
    Category.id_comp]
  unfold coreC core
  dsimp only [Signature.endR, psig_colourTgt, psig_colourSrc, Signature.pivotal_dom_gen,
    Signature.pivotal_cod_gen, Signature.pivotal_left_gen, Signature.pivotal_right_gen,
    sig0_dom_cross_g, sig0_cod_cross_g, sig0_dom_dot_g, sig0_cod_dot_g, wd_cons, wd_nil, wt_cons,
    wt_nil, sig0_colourTgt_g, sig0_colourSrc_g]
  rw [chain2_key' S.model ?t1 ?t1' _ ?t2 ?t2' _ _ _ _ _ (𝟙 _) (𝟙 _),
    chain2_key' S.model ?t3 ?t3' _ ?t4 ?t4' _ _ _ _ _ (𝟙 _) (𝟙 _)]
  case t1 => exact (λ_ _) ≪≫ (ρ_ _)
  case t1' => exact (λ_ _) ≪≫ (ρ_ _)
  case t2 => exact whiskerLeftIso _ (ρ_ _)
  case t2' => exact whiskerLeftIso _ (ρ_ _)
  case t3 => exact λ_ _
  case t3' => exact λ_ _
  case t4 => exact (λ_ _) ≪≫ (ρ_ _)
  case t4' => exact (λ_ _) ≪≫ (ρ_ _)
  erw [layerAt_whole, layerAt_right, layerAt_left]
  set_option backward.isDefEq.respectTransparency false in
  simp only [PrelaxFunctor.map₂_id, Category.id_comp, Category.comp_id]
  exact sub_eq_zero.2 (S.crossQ_dot_slide_right c d h _ _ _ _).symm

theorem upDiag_D0_X2_g (c d : I) (μ : X) :
    upDiag RD μ (KLR.Diagram.D0 c d ≫ KLR.Diagram.X2 c d) =
      mkD RD μ [([], .dot (up c), [up d]), ([], .cross true c d, [])]
        ⟨rfl, rfl, rfl⟩ := by
  rfl

theorem upDiag_X2_D1_g (c d : I) (μ : X) :
    upDiag RD μ (KLR.Diagram.X2 c d ≫ KLR.Diagram.D1 d c) =
      mkD RD μ [([], .cross true c d, []), ([up d], .dot (up c), [])]
        ⟨rfl, rfl, rfl⟩ := by
  rfl

set_option maxHeartbeats 2000000 in
/-- The dot slide `(x on the left strand) τ = τ (x on the right strand)` for differently labelled
strands. -/
theorem klr_slideRNe (c d : I) (h : c ≠ d) (μ : X) :
    (interp (genImg (S := S) Sc) (KL3.Diagram.wt RD μ [up c, up d] : X) μ).functor.map
        (upDiag RD μ (KLR.Diagram.D0 c d ≫ KLR.Diagram.X2 c d)) -
      (interp (genImg (S := S) Sc) (KL3.Diagram.wt RD μ [up c, up d] : X) μ).functor.map
        (upDiag RD μ (KLR.Diagram.X2 c d ≫ KLR.Diagram.D1 d c)) = 0 := by
  rw [upDiag_D0_X2_g, upDiag_X2_D1_g]
  have hc : Cond (S := psig RD) (KL3.Diagram.wt RD μ [up c, up d] : X) μ
      (ob RD μ [up c, up d]) := ⟨⟨rfl, rfl, trivial⟩, rfl, rfl⟩
  have hc' : Cond (S := psig RD) (KL3.Diagram.wt RD μ [up c, up d] : X) μ
      (ob RD μ [up d, up c]) :=
    ⟨⟨@add_left_comm X _ _ _ _, rfl, trivial⟩, rfl, @add_left_comm X _ _ _ _⟩
  apply (cancel_epi (eqToHom (objI_pos _ _ hc).symm)).1
  apply (cancel_mono (eqToHom (objI_pos _ _ hc'))).1
  set_option backward.isDefEq.respectTransparency false in
  simp only [Limits.comp_zero, Limits.zero_comp, Preadditive.sub_comp, Preadditive.comp_sub]
  set_option backward.isDefEq.respectTransparency false in
  simp only [Interpretation.functor_map, mkD, Diagram.layers_mk, layList_cons, layList_nil,
    Interpretation.mapChain]
  set_option backward.isDefEq.respectTransparency false in
  simp only [lay, Shape.gen, wd_cons, wd_nil, wt_cons, wt_nil, List.nil_append,
    List.cons_append, Shape.dom]
  rw [layerI_pos _ _ _ _ ?c1]
  try rw [layerI_pos _ _ _ _ ?c2]
  try rw [layerI_pos _ _ _ _ ?c3]
  try rw [layerI_pos _ _ _ _ ?c4]
  all_goals try (refine ⟨?_, ?_, ?_⟩ <;>
      simp [Signature.ok, Signature.endR, Layer.dom, sig0_colourSrc_g, sig0_colourTgt_g,
        sig0_dom_cross_g, sig0_dom_dot_g, add_left_comm])
  set_option backward.isDefEq.respectTransparency false in
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl, Category.comp_id,
    Category.id_comp]
  unfold coreC core
  dsimp only [Signature.endR, psig_colourTgt, psig_colourSrc, Signature.pivotal_dom_gen,
    Signature.pivotal_cod_gen, Signature.pivotal_left_gen, Signature.pivotal_right_gen,
    sig0_dom_cross_g, sig0_cod_cross_g, sig0_dom_dot_g, sig0_cod_dot_g, wd_cons, wd_nil, wt_cons,
    wt_nil, sig0_colourTgt_g, sig0_colourSrc_g]
  rw [chain2_key' S.model ?t1 ?t1' _ ?t2 ?t2' _ _ _ _ _ (𝟙 _) (𝟙 _),
    chain2_key' S.model ?t3 ?t3' _ ?t4 ?t4' _ _ _ _ _ (𝟙 _) (𝟙 _)]
  case t1 => exact whiskerLeftIso _ (ρ_ _)
  case t1' => exact whiskerLeftIso _ (ρ_ _)
  case t2 => exact (λ_ _) ≪≫ (ρ_ _)
  case t2' => exact (λ_ _) ≪≫ (ρ_ _)
  case t3 => exact (λ_ _) ≪≫ (ρ_ _)
  case t3' => exact (λ_ _) ≪≫ (ρ_ _)
  case t4 => exact λ_ _
  case t4' => exact λ_ _
  erw [layerAt_whole, layerAt_right, layerAt_left]
  set_option backward.isDefEq.respectTransparency false in
  simp only [PrelaxFunctor.map₂_id, Category.id_comp, Category.comp_id]
  exact sub_eq_zero.2 (S.crossQ_dot_slide_left c d h _ _ _ _)

theorem upDiag_braidL_g (c d e : I) (μ : X) :
    upDiag RD μ (KLR.Diagram.braidL c d e) =
      mkD RD μ [([], .cross true c d, [up e]), ([up d], .cross true c e, []),
        ([], .cross true d e, [up c])] ⟨rfl, rfl, rfl, rfl⟩ := by
  rfl

theorem upDiag_braidR_g (c d e : I) (μ : X) :
    upDiag RD μ (KLR.Diagram.braidR c d e) =
      mkD RD μ [([up c], .cross true d e, []), ([], .cross true c e, [up d]),
        ([up e], .cross true c d, [])] ⟨rfl, rfl, rfl, rfl⟩ := by
  rfl

set_option maxHeartbeats 10000000 in
/-- The braid relation on three upward strands with bottom labels `c d e`, unless `c = e` and
`(α_c, α_d) < 0` (the hypothesis of CL (2.13)). -/
theorem klr_braid_gen' (c d e : I) (hb' : ¬ (c = e ∧ C.dot c d < 0)) (μ : X) :
    (interp (genImg (S := S) Sc) (KL3.Diagram.wt RD μ [up c, up d, up e] : X) μ).functor.map
        (upDiag RD μ (KLR.Diagram.braidL c d e)) -
      (interp (genImg (S := S) Sc) (KL3.Diagram.wt RD μ [up c, up d, up e] : X) μ).functor.map
        (upDiag RD μ (KLR.Diagram.braidR c d e)) = 0 := by
  rw [upDiag_braidL_g, upDiag_braidR_g]
  have hc : Cond (S := psig RD) (KL3.Diagram.wt RD μ [up c, up d, up e] : X) μ
      (ob RD μ [up c, up d, up e]) := ⟨⟨rfl, rfl, rfl, trivial⟩, rfl, rfl⟩
  have hc' : Cond (S := psig RD) (KL3.Diagram.wt RD μ [up c, up d, up e] : X) μ
      (ob RD μ [up e, up d, up c]) := by
    refine ⟨⟨?_, rfl, rfl, trivial⟩, rfl, ?_⟩ <;>
      change sh RD (up e) + (sh RD (up d) + (sh RD (up c) + μ)) =
        sh RD (up c) + (sh RD (up d) + (sh RD (up e) + μ)) <;> abel
  apply (cancel_epi (eqToHom (objI_pos _ _ hc).symm)).1
  apply (cancel_mono (eqToHom (objI_pos _ _ hc'))).1
  set_option backward.isDefEq.respectTransparency false in
  simp only [Limits.comp_zero, Limits.zero_comp, Preadditive.sub_comp, Preadditive.comp_sub]
  set_option backward.isDefEq.respectTransparency false in
  simp only [Interpretation.functor_map, mkD, Diagram.layers_mk, layList_cons, layList_nil,
    Interpretation.mapChain]
  set_option backward.isDefEq.respectTransparency false in
  simp only [lay, Shape.gen, wd_cons, wd_nil, wt_cons, wt_nil, List.nil_append,
    List.cons_append, Shape.dom]
  dsimp only [up] at *
  generalize_proofs
  generalize h1 :
      sh RD ((true, d) : Letter I) + (sh RD ((true, c) : Letter I) +
        (sh RD ((true, e) : Letter I) + μ)) = x1 at *
  obtain rfl :
      x1 = sh RD ((true, c) : Letter I) + (sh RD ((true, d) : Letter I) +
        (sh RD ((true, e) : Letter I) + μ)) := by
    rw [← h1]; abel
  generalize h2 :
      sh RD ((true, d) : Letter I) + (sh RD ((true, e) : Letter I) +
        (sh RD ((true, c) : Letter I) + μ)) = x2 at *
  obtain rfl :
      x2 = sh RD ((true, c) : Letter I) + (sh RD ((true, d) : Letter I) +
        (sh RD ((true, e) : Letter I) + μ)) := by
    rw [← h2]; abel
  generalize h3 :
      sh RD ((true, e) : Letter I) + (sh RD ((true, d) : Letter I) +
        (sh RD ((true, c) : Letter I) + μ)) = x3 at *
  obtain rfl :
      x3 = sh RD ((true, c) : Letter I) + (sh RD ((true, d) : Letter I) +
        (sh RD ((true, e) : Letter I) + μ)) := by
    rw [← h3]; abel
  generalize h4 :
      sh RD ((true, c) : Letter I) + (sh RD ((true, e) : Letter I) +
        (sh RD ((true, d) : Letter I) + μ)) = x4 at *
  obtain rfl :
      x4 = sh RD ((true, c) : Letter I) + (sh RD ((true, d) : Letter I) +
        (sh RD ((true, e) : Letter I) + μ)) := by
    rw [← h4]; abel
  generalize h5 :
      sh RD ((true, e) : Letter I) + (sh RD ((true, c) : Letter I) +
        (sh RD ((true, d) : Letter I) + μ)) = x5 at *
  obtain rfl :
      x5 = sh RD ((true, c) : Letter I) + (sh RD ((true, d) : Letter I) +
        (sh RD ((true, e) : Letter I) + μ)) := by
    rw [← h5]; abel
  generalize h6 : sh RD ((true, e) : Letter I) + (sh RD ((true, d) : Letter I) + μ) = x6 at *
  obtain rfl :
      x6 = sh RD ((true, d) : Letter I) + (sh RD ((true, e) : Letter I) + μ) := by
    rw [← h6]; abel
  generalize h7 : sh RD ((true, e) : Letter I) + (sh RD ((true, c) : Letter I) + μ) = x7 at *
  obtain rfl :
      x7 = sh RD ((true, c) : Letter I) + (sh RD ((true, e) : Letter I) + μ) := by
    rw [← h7]; abel
  generalize h8 : sh RD ((true, c) : Letter I) + (sh RD ((true, d) : Letter I) + μ) = x8 at *
  obtain rfl :
      x8 = sh RD ((true, d) : Letter I) + (sh RD ((true, c) : Letter I) + μ) := by
    rw [← h8]; abel
  rw [layerI_pos _ _ _ _ ?c1]
  try rw [layerI_pos _ _ _ _ ?c2]
  try rw [layerI_pos _ _ _ _ ?c3]
  try rw [layerI_pos _ _ _ _ ?c4]
  try rw [layerI_pos _ _ _ _ ?c5]
  try rw [layerI_pos _ _ _ _ ?c6]
  all_goals try (refine ⟨?_, ?_, ?_⟩ <;>
      simp [Signature.ok, Signature.endR, Layer.dom, sig0_colourSrc_g, sig0_colourTgt_g,
        sig0_dom_cross_g] <;> (try constructor) <;> abel)
  set_option backward.isDefEq.respectTransparency false in
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl, Category.comp_id,
    Category.id_comp]
  unfold coreC core
  dsimp only [Signature.endR, psig_colourTgt, psig_colourSrc, Signature.pivotal_dom_gen,
    Signature.pivotal_cod_gen, Signature.pivotal_left_gen, Signature.pivotal_right_gen,
    sig0_dom_cross_g, sig0_cod_cross_g, wd_cons, wd_nil, wt_cons,
    wt_nil, sig0_colourTgt_g, sig0_colourSrc_g]
  simp only [Category.assoc]
  set_option backward.isDefEq.respectTransparency false in
  rw [eqToHom_word ?w0 _]
  set_option backward.isDefEq.respectTransparency false in
  rw [eqToHom_word ?w1 _]
  set_option backward.isDefEq.respectTransparency false in
  rw [eqToHom_word ?w2 _]
  case w0 | w1 | w2 =>
    simp [Layer.cod, Layer.dom, sig0_cod_cross_g, sig0_dom_cross_g, add_left_comm]
  rw [chain3_keyZ2 S.model ?t1 ?t1' _ ?t2 ?t2' _ ?t3 ?t3' _ _ _ _ _ _ _ _ (𝟙 _) (eqToHom ?z1)
      (𝟙 _),
    chain3_keyZ12 S.model ?t4 ?t4' _ ?t5 ?t5' _ ?t6 ?t6' _ _ _ _ _ _ _ _ _ (𝟙 _) (eqToHom ?z2)
      (eqToHom ?z3) (𝟙 _)]
  case t1 | t1' | t3 | t3' | t5 | t5' =>
    exact whiskerLeftIso _ (ρ_ _) ≪≫ (α_ _ _ _).symm
  case t2 | t2' | t4 | t4' | t6 | t6' => exact λ_ _
  case z1 =>
    generalize_proofs
    generalize hx : sh RD ((true, e) : Letter I) + (sh RD ((true, c) : Letter I) + μ) = x at *
    obtain rfl :
        x = sh RD ((true, c) : Letter I) + (sh RD ((true, e) : Letter I) + μ) := by
      rw [← hx]; abel
    rfl
  case z2 =>
    generalize_proofs
    generalize hx : sh RD ((true, e) : Letter I) + (sh RD ((true, d) : Letter I) + μ) = x at *
    obtain rfl :
        x = sh RD ((true, d) : Letter I) + (sh RD ((true, e) : Letter I) + μ) := by
      rw [← hx]; abel
    rfl
  case z3 =>
    generalize_proofs
    generalize hx : sh RD ((true, c) : Letter I) + (sh RD ((true, d) : Letter I) + μ) = x at *
    obtain rfl :
        x = sh RD ((true, d) : Letter I) + (sh RD ((true, c) : Letter I) + μ) := by
      rw [← hx]; abel
    rfl
  repeat erw [layerAt_right_assoc]
  repeat erw [layerAt_left]
  simp only [lift_map₂_eqToHom, PrelaxFunctor.map₂_id, Category.id_comp, Category.comp_id]
  exact sub_eq_zero.2 (S.crossQ_braid_cast c d e hb' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (add_left_comm _ _ _) (add_left_comm _ _ _) (add_left_comm _ _ _) _ _ _)

/-- The braid relation on three upward strands with bottom labels `c d e`, unless `c = e ≠ d`. -/
theorem klr_braid_gen (c d e : I) (hb : ¬ (c = e ∧ c ≠ d)) (μ : X) :
    (interp (genImg (S := S) Sc) (KL3.Diagram.wt RD μ [up c, up d, up e] : X) μ).functor.map
        (upDiag RD μ (KLR.Diagram.braidL c d e)) -
      (interp (genImg (S := S) Sc) (KL3.Diagram.wt RD μ [up c, up d, up e] : X) μ).functor.map
        (upDiag RD μ (KLR.Diagram.braidR c d e)) = 0 := by
  refine klr_braid_gen' (S := S) Sc c d e ?_ μ
  rintro ⟨rfl, hcd⟩
  refine hb ⟨rfl, fun h' => ?_⟩
  subst h'
  exact absurd hcd (not_lt.2 (C.dot_self_pos c).le)


/-! ### The relations, read with their own outer regions -/

theorem killed_klr_slideLNe (c d : I) (h : c ≠ d) (μ : X) :
    (freeLift k (interp (genImg (S := S) Sc) (Rel.dom (.klr μ (.slideLNe c d h) : Rel RD)).start
      (Rel.dom (.klr μ (.slideLNe c d h) : Rel RD)).endR).functor).map
        (relation k (.klr μ (.slideLNe c d h) : Rel RD)) = 0 := by
  set_option backward.isDefEq.respectTransparency false in
  rw [relation, KLR.Diagram.relation, upLin_sub, upLin_of, upLin_of, Functor.map_sub,
    freeLift_map_of, freeLift_map_of]
  exact klr_slideLNe (S := S) Sc c d h μ

theorem killed_klr_slideRNe (c d : I) (h : c ≠ d) (μ : X) :
    (freeLift k (interp (genImg (S := S) Sc) (Rel.dom (.klr μ (.slideRNe c d h) : Rel RD)).start
      (Rel.dom (.klr μ (.slideRNe c d h) : Rel RD)).endR).functor).map
        (relation k (.klr μ (.slideRNe c d h) : Rel RD)) = 0 := by
  set_option backward.isDefEq.respectTransparency false in
  rw [relation, KLR.Diagram.relation, upLin_sub, upLin_of, upLin_of, Functor.map_sub,
    freeLift_map_of, freeLift_map_of]
  exact klr_slideRNe (S := S) Sc c d h μ

theorem killed_klr_braid_gen (c d e : I) (h : ¬ (c = e ∧ c ≠ d)) (μ : X) :
    (freeLift k (interp (genImg (S := S) Sc) (Rel.dom (.klr μ (.braid c d e h) : Rel RD)).start
      (Rel.dom (.klr μ (.braid c d e h) : Rel RD)).endR).functor).map
        (relation k (.klr μ (.braid c d e h) : Rel RD)) = 0 := by
  set_option backward.isDefEq.respectTransparency false in
  rw [relation, KLR.Diagram.relation, upLin_sub, upLin_of, upLin_of, Functor.map_sub,
    freeLift_map_of, freeLift_map_of]
  exact klr_braid_gen (S := S) Sc c d e h μ

end Up

end QStrong

end Model

end Categorification.TwoRep
