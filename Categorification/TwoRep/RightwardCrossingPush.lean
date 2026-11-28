/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RightwardCrossing
import Categorification.Diagrams.BicatInterpPush
import Mathlib.CategoryTheory.Category.Cat

/-!
# The rightward crossing under strict pseudofunctors, and in `Cat`

Brundan, arXiv:1501.00350v1, (1.6): the rightward crossing `σ = (η₂ on the left) · τ · ε₁`
(`RightwardCrossing.sigma`).

* `sp_map₂_sigma`: a strict pseudofunctor sends the rightward crossing built from `η₂`, `τ`,
  `ε₁` to the rightward crossing built from their images, up to the equalities `map_comp` and
  `map_id` of the 1-morphisms (`sp_map₂_sigma_mapAdjunction` for the unit and counit of
  adjunctions).
* `Cat.sigma_toNatTrans_app`: in `Cat`, the rightward crossing at an object `X` is
  `η₂ (E₁ R₁ X) ≫ R₂ (τ (R₁ X)) ≫ R₂ (E₂ (ε₁ X))`.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory Bicategory Categorification.Diagrams.BicatInterp

universe w₁ w₂ w₃ w₄ v₂ v₃

section Strict

variable {C' : Type w₃} [Bicategory.{w₄, v₃} C'] {C : Type w₁} [Bicategory.{w₂, v₂} C]
  {a b c : C'} {E₁ : a ⟶ b} {E₂ : b ⟶ c} {R₁ : b ⟶ a} {R₂ : c ⟶ b}

/-- **A pseudofunctor preserves the rightward crossing**: the rightward crossing built from the
images of `η₂`, `τ`, `ε₁` is the image of the rightward crossing, conjugated by the
compositors. -/
theorem sigma_map (F : Pseudofunctor C' C) (η₂ : 𝟙 b ⟶ E₂ ≫ R₂) (τ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂)
    (ε₁ : R₁ ≫ E₁ ⟶ 𝟙 b) :
    RightwardCrossing.sigma ((F.mapId b).inv ≫ F.map₂ η₂ ≫ (F.mapComp E₂ R₂).hom)
        ((F.mapComp E₁ E₂).inv ≫ F.map₂ τ ≫ (F.mapComp E₁ E₂).hom)
        ((F.mapComp R₁ E₁).inv ≫ F.map₂ ε₁ ≫ (F.mapId b).hom) =
      (F.mapComp R₁ E₁).inv ≫ F.map₂ (RightwardCrossing.sigma η₂ τ ε₁) ≫
        (F.mapComp E₂ R₂).hom := by
  have hs : ∀ {Z : F.obj b ⟶ F.obj b} (h : F.map R₁ ≫ F.map E₁ ≫ F.map (𝟙 b) ⟶ Z),
      (F.mapComp R₁ E₁).inv ≫ (ρ_ (F.map (R₁ ≫ E₁))).inv ≫
        F.map (R₁ ≫ E₁) ◁ (F.mapId b).inv ≫ (F.mapComp R₁ E₁).hom ▷ F.map (𝟙 b) ≫
          (α_ (F.map R₁) (F.map E₁) (F.map (𝟙 b))).hom ≫ h =
      (ρ_ (F.map R₁ ≫ F.map E₁)).inv ≫ (α_ (F.map R₁) (F.map E₁) (𝟙 (F.obj b))).hom ≫
        F.map R₁ ◁ F.map E₁ ◁ (F.mapId b).inv ≫ h := by
    intro Z h
    rw [whisker_exchange_assoc, ← rightUnitor_inv_naturality_assoc, Iso.inv_hom_id_assoc,
      associator_naturality_right_assoc]
  have he : (α_ (F.map (𝟙 b)) (F.map E₂) (F.map R₂)).hom ≫ F.map (𝟙 b) ◁ (F.mapComp E₂ R₂).inv ≫
        (F.mapId b).hom ▷ F.map (E₂ ≫ R₂) ≫ (λ_ (F.map (E₂ ≫ R₂))).hom ≫
          (F.mapComp E₂ R₂).hom =
      (F.mapId b).hom ▷ F.map E₂ ▷ F.map R₂ ≫ (α_ (𝟙 (F.obj b)) (F.map E₂) (F.map R₂)).hom ≫
        (λ_ (F.map E₂ ≫ F.map R₂)).hom := by
    rw [whisker_exchange_assoc, leftUnitor_naturality_assoc, Iso.inv_hom_id, Category.comp_id,
      ← associator_naturality_left_assoc]
  simp [RightwardCrossing.sigma_def, bicategoricalComp, F.map₂_iso_inv]
  rw [hs, he]

variable (Φ : StrictPseudofunctor C' C)

/-- **A strict pseudofunctor preserves the rightward crossing**, up to the equalities of the
images of composites. -/
theorem sp_map₂_sigma (η₂ : 𝟙 b ⟶ E₂ ≫ R₂) (τ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) (ε₁ : R₁ ≫ E₁ ⟶ 𝟙 b) :
    Φ.map₂ (RightwardCrossing.sigma η₂ τ ε₁) =
      eqToHom (Φ.map_comp R₁ E₁) ≫
        RightwardCrossing.sigma
          (eqToHom (Φ.map_id b).symm ≫ Φ.map₂ η₂ ≫ eqToHom (Φ.map_comp E₂ R₂))
          (eqToHom (Φ.map_comp E₁ E₂).symm ≫ Φ.map₂ τ ≫ eqToHom (Φ.map_comp E₁ E₂))
          (eqToHom (Φ.map_comp R₁ E₁).symm ≫ Φ.map₂ ε₁ ≫ eqToHom (Φ.map_id b)) ≫
        eqToHom (Φ.map_comp E₂ R₂).symm := by
  have h := sigma_map Φ.toPseudofunctor η₂ τ ε₁
  have e₁ := Φ.mapId_eq_eqToIso b
  have e₂ := Φ.mapComp_eq_eqToIso R₁ E₁
  have e₃ := Φ.mapComp_eq_eqToIso E₂ R₂
  have e₄ := Φ.mapComp_eq_eqToIso E₁ E₂
  change RightwardCrossing.sigma ((Φ.mapId b).inv ≫ Φ.map₂ η₂ ≫ (Φ.mapComp E₂ R₂).hom)
      ((Φ.mapComp E₁ E₂).inv ≫ Φ.map₂ τ ≫ (Φ.mapComp E₁ E₂).hom)
      ((Φ.mapComp R₁ E₁).inv ≫ Φ.map₂ ε₁ ≫ (Φ.mapId b).hom) =
    (Φ.mapComp R₁ E₁).inv ≫ Φ.map₂ (RightwardCrossing.sigma η₂ τ ε₁) ≫
      (Φ.mapComp E₂ R₂).hom at h
  rw [e₁, e₂, e₃, e₄] at h
  simp only [eqToIso.hom, eqToIso.inv] at h
  rw [h]
  simp

/-- `sp_map₂_sigma` for the unit and counit of adjunctions. -/
theorem sp_map₂_sigma_mapAdjunction (adj₁ : E₁ ⊣ R₁) (adj₂ : E₂ ⊣ R₂)
    (τ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) :
    Φ.map₂ (RightwardCrossing.sigma adj₂.unit τ adj₁.counit) =
      eqToHom (Φ.map_comp R₁ E₁) ≫
        RightwardCrossing.sigma (Φ.mapAdjunction adj₂).unit
          (eqToHom (Φ.map_comp E₁ E₂).symm ≫ Φ.map₂ τ ≫ eqToHom (Φ.map_comp E₁ E₂))
          (Φ.mapAdjunction adj₁).counit ≫
        eqToHom (Φ.map_comp E₂ R₂).symm := by
  rw [sp_map₂_sigma, StrictPseudofunctor.mapAdjunction_unit',
    StrictPseudofunctor.mapAdjunction_counit']

end Strict

section Cat

universe v u

/-- **The rightward crossing in `Cat`**, at an object. -/
theorem Cat.sigma_toNatTrans_app {A B D : Cat.{v, u}} {E₁ : A ⟶ B} {R₁ : B ⟶ A}
    {E₂ : B ⟶ D} {R₂ : D ⟶ B} (η₂ : 𝟙 B ⟶ E₂ ≫ R₂) (τ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂)
    (ε₁ : R₁ ≫ E₁ ⟶ 𝟙 B) (X : B) :
    (RightwardCrossing.sigma η₂ τ ε₁).toNatTrans.app X =
      η₂.toNatTrans.app (E₁.toFunctor.obj (R₁.toFunctor.obj X)) ≫
        R₂.toFunctor.map (τ.toNatTrans.app (R₁.toFunctor.obj X)) ≫
          R₂.toFunctor.map (E₂.toFunctor.map (ε₁.toNatTrans.app X)) := by
  rw [RightwardCrossing.sigma_eq]
  simp

end Cat

end Categorification.TwoRep
