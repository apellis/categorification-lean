/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.BicatInterpPush
import Mathlib.CategoryTheory.Bicategory.Adjunction.Mate
import Mathlib.CategoryTheory.Bicategory.EqToHom

/-!
# Strict pseudofunctors, adjunctions and mates

A strict pseudofunctor `Φ : C' → C` carries an adjunction `l ⊣ r` to an adjunction
`Φ l ⊣ Φ r` (Mathlib's `StrictPseudofunctor.mapAdjunction`). This file records that it commutes
with mates (`sp_map₂_conjugateEquiv_symm`) and with composites of adjunctions
(`sp_mapAdjunction_comp_heq`), up to the identifications `Φ (f ≫ g) = Φ f ≫ Φ g`.
-/

noncomputable section

namespace Categorification.Diagrams.BicatInterp

open CategoryTheory Bicategory

universe w₁ w₂ w₃ w₄ v₂ v₃

variable {C' : Type w₃} [Bicategory.{w₄, v₃} C'] {C : Type w₁} [Bicategory.{w₂, v₂} C]
  (Φ : StrictPseudofunctor C' C)

/-- **Mates commute with a strict pseudofunctor.** -/
theorem sp_map₂_conjugateEquiv_symm {a b : C'} {l₁ l₂ : a ⟶ b} {r₁ r₂ : b ⟶ a}
    (adj₁ : l₁ ⊣ r₁) (adj₂ : l₂ ⊣ r₂) (x : r₁ ⟶ r₂) :
    Φ.map₂ ((conjugateEquiv adj₁ adj₂).symm x) =
      (conjugateEquiv (Φ.mapAdjunction adj₁) (Φ.mapAdjunction adj₂)).symm (Φ.map₂ x) := by
  rw [conjugateEquiv_symm_apply', conjugateEquiv_symm_apply',
    StrictPseudofunctor.mapAdjunction_unit', StrictPseudofunctor.mapAdjunction_counit']
  simp only [PrelaxFunctor.map₂_comp, sp_map₂_leftUnitor_inv, sp_map₂_whiskerRight,
    sp_map₂_associator_hom, sp_map₂_whiskerLeft, sp_map₂_rightUnitor_hom, comp_whiskerRight,
    whiskerLeft_comp, eqToHom_whiskerRight, whiskerLeft_eqToHom, Category.assoc,
    eqToHom_trans_assoc, eqToHom_trans]
  simp

theorem compUnit_eq {a b c : C'} {f₁ : a ⟶ b} {g₁ : b ⟶ a} {f₂ : b ⟶ c} {g₂ : c ⟶ b}
    (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) :
    Adjunction.compUnit adj₁ adj₂ = adj₁.unit ≫ f₁ ◁ (λ_ g₁).inv ≫ f₁ ◁ adj₂.unit ▷ g₁ ≫
      (α_ f₁ (f₂ ≫ g₂) g₁).inv ≫ (α_ f₁ f₂ g₂).inv ▷ g₁ ≫ (α_ (f₁ ≫ f₂) g₂ g₁).hom := by
  simp only [Adjunction.compUnit]
  bicategory

theorem compCounit_eq {a b c : C'} {f₁ : a ⟶ b} {g₁ : b ⟶ a} {f₂ : b ⟶ c} {g₂ : c ⟶ b}
    (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) :
    Adjunction.compCounit adj₁ adj₂ = (α_ g₂ g₁ (f₁ ≫ f₂)).hom ≫ g₂ ◁ (α_ g₁ f₁ f₂).inv ≫
      g₂ ◁ adj₁.counit ▷ f₂ ≫ g₂ ◁ (λ_ f₂).hom ≫ adj₂.counit := by
  simp only [Adjunction.compCounit]
  bicategory

theorem adjunction_heq_of {a b : C} {l l' : a ⟶ b} {r r' : b ⟶ a} (A : l ⊣ r) (A' : l' ⊣ r')
    (hl : l = l') (hr : r = r') (hu : A.unit = A'.unit ≫ eqToHom (by rw [hl, hr]))
    (hc : A.counit = eqToHom (by rw [hl, hr]) ≫ A'.counit) : A ≍ A' := by
  subst hl hr
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at hu hc
  exact heq_of_eq (Adjunction.ext hu hc)

/-- **Composites of adjunctions commute with a strict pseudofunctor.** -/
theorem sp_mapAdjunction_comp_heq {a b c : C'} {f₁ : a ⟶ b} {g₁ : b ⟶ a} {f₂ : b ⟶ c}
    {g₂ : c ⟶ b} (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) :
    Φ.mapAdjunction (adj₁.comp adj₂) ≍ (Φ.mapAdjunction adj₁).comp (Φ.mapAdjunction adj₂) := by
  refine adjunction_heq_of _ _ (Φ.map_comp _ _) (Φ.map_comp _ _) ?_ ?_
  · rw [StrictPseudofunctor.mapAdjunction_unit']
    simp only [Bicategory.Adjunction.comp]
    rw [compUnit_eq adj₁ adj₂, compUnit_eq (Φ.mapAdjunction adj₁) (Φ.mapAdjunction adj₂),
      StrictPseudofunctor.mapAdjunction_unit', StrictPseudofunctor.mapAdjunction_unit']
    simp only [PrelaxFunctor.map₂_comp, sp_map₂_whiskerRight,
      sp_map₂_associator_hom, sp_map₂_associator_inv, sp_map₂_whiskerLeft,
      sp_map₂_leftUnitor_inv, comp_whiskerRight, whiskerLeft_comp, eqToHom_whiskerRight,
      whiskerLeft_eqToHom, Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
    rw [associator_inv_congr (f := Φ.map f₁) rfl (Φ.map_comp f₂ g₂) rfl,
      associator_hom_congr (Φ.map_comp f₁ f₂) rfl rfl]
    simp
  · rw [StrictPseudofunctor.mapAdjunction_counit']
    simp only [Bicategory.Adjunction.comp]
    rw [compCounit_eq adj₁ adj₂,
      compCounit_eq (Φ.mapAdjunction adj₁) (Φ.mapAdjunction adj₂),
      StrictPseudofunctor.mapAdjunction_counit', StrictPseudofunctor.mapAdjunction_counit']
    simp only [PrelaxFunctor.map₂_comp, sp_map₂_whiskerRight,
      sp_map₂_associator_hom, sp_map₂_associator_inv, sp_map₂_whiskerLeft,
      sp_map₂_leftUnitor_hom, comp_whiskerRight, whiskerLeft_comp, eqToHom_whiskerRight,
      whiskerLeft_eqToHom, Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
    rw [associator_hom_congr (f := Φ.map g₂) (g := Φ.map g₁) rfl rfl (Φ.map_comp f₁ f₂)]
    simp

end Categorification.Diagrams.BicatInterp
