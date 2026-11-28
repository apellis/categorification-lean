/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AdjointTwo
import Categorification.WeightedKLR.Rigidity.CupCapProp721DerivedPaste

/-!
# Conjugate isomorphisms of pasted squares, and conjugates commuting with shifts

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21. The isomorphisms `𝔈_i 𝕋 ≅ 𝕋 𝔈_i` and `𝔉_i 𝕋 ≅ 𝕋 𝔉_i` are conjugates of the
isomorphisms `𝕂 𝔉_i ≅ 𝔉_i 𝕂` and `𝕂 𝔈_i ≅ 𝔈_i 𝕂` (`CupCap.rightAdjointCommIso`). For the
crossings one needs the composites `𝔈_i²`, `𝔉_i²`: the conjugate of a pasted square, along the
composite adjunctions, is the pasting of the conjugates (`CupCap.rightAdjointCommIso_squarePaste`).

For the quantum trace, which contains a homological shift, a 2-morphism has to commute with the
shift. The conjugate of a 2-morphism commuting with the shift, along two adjunctions compatible
with the shift, commutes with the shift (`CupCap.conjugateEquiv_commShift`).

## Main results

* `CupCap.rightAdjointCommIso_squarePaste`.
* `CupCap.conjugateEquiv_eq_whisker`, `CupCap.conjugateEquiv_commShift`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open CategoryTheory

section Paste

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

variable {A₁ : Type u₁} {A₂ : Type u₂} {A₃ : Type u₃} {B₁ : Type u₄} {B₂ : Type u₅}
  {B₃ : Type u₆} [Category.{v₁} A₁] [Category.{v₂} A₂] [Category.{v₃} A₃]
  [Category.{v₄} B₁] [Category.{v₅} B₂] [Category.{v₆} B₃]
  {K₁ : A₁ ⥤ B₁} {T₁ : B₁ ⥤ A₁} {K₂ : A₂ ⥤ B₂} {T₂ : B₂ ⥤ A₂} {K₃ : A₃ ⥤ B₃} {T₃ : B₃ ⥤ A₃}
  {EA : A₁ ⥤ A₂} {FA : A₂ ⥤ A₁} {EB : B₁ ⥤ B₂} {FB : B₂ ⥤ B₁}
  {EA' : A₂ ⥤ A₃} {FA' : A₃ ⥤ A₂} {EB' : B₂ ⥤ B₃} {FB' : B₃ ⥤ B₂}

/-- **The conjugate of a pasted square is the pasting of the conjugates**: for squares
`c₁ : K₁ ⋙ E_B ≅ E_A ⋙ K₂` and `c₂ : K₂ ⋙ E_B' ≅ E_A' ⋙ K₃`, the conjugate, along the composite
adjunctions `E_A ⋙ E_A' ⊣ F_A' ⋙ F_A` and `E_B ⋙ E_B' ⊣ F_B' ⋙ F_B`, of the pasted square is
the pasting of the two conjugate isomorphisms. -/
theorem rightAdjointCommIso_squarePaste (adj₁ : K₁ ⊣ T₁) (adj₂ : K₂ ⊣ T₂) (adj₃ : K₃ ⊣ T₃)
    (adjA : EA ⊣ FA) (adjB : EB ⊣ FB) (adjA' : EA' ⊣ FA') (adjB' : EB' ⊣ FB')
    (c₁ : K₁ ⋙ EB ≅ EA ⋙ K₂) (c₂ : K₂ ⋙ EB' ≅ EA' ⋙ K₃) :
    rightAdjointCommIso adj₁ adj₃ (adjA.comp adjA') (adjB.comp adjB')
        (squarePaste c₂.symm c₁.symm).symm =
      squarePaste (rightAdjointCommIso adj₁ adj₂ adjA adjB c₁)
        (rightAdjointCommIso adj₂ adj₃ adjA' adjB' c₂) := by
  have key : ∀ {W : A₂} {X' : B₂} (y : B₃) (g : EB'.obj X' ⟶ y) (z : W ⟶ T₂.obj X'),
      adjA'.unit.app W ≫ FA'.map (adj₃.unit.app (EA'.obj W) ≫
        T₃.map (c₂.inv.app W ≫ EB'.map (K₂.map z ≫ adj₂.counit.app X') ≫ g)) =
      z ≫ adjA'.unit.app _ ≫ FA'.map (adj₃.unit.app _ ≫
        T₃.map (c₂.inv.app _ ≫ EB'.map (adj₂.counit.app X') ≫ g)) := by
    intro W X' y g z
    rw [← adjA'.unit_naturality_assoc]
    simp only [← Functor.map_comp]
    congr 1
    have h1 := adj₃.unit.naturality (EA'.map z)
    have h2 := c₂.inv.naturality z
    simp only [Functor.id_map, Functor.comp_map] at h1 h2
    rw [reassoc_of% h1]
    congr 1
    simp only [← Functor.map_comp]
    congr 1
    rw [reassoc_of% h2]
    simp only [Functor.map_comp, Category.assoc]
  ext x
  simp only [rightAdjointCommIso, squarePaste, conjugateIsoEquiv_apply_hom, Iso.symm_hom,
    conjugateEquiv_apply_app, Iso.trans_hom, NatTrans.comp_app, Iso.symm_inv,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Adjunction.comp_unit_app, Adjunction.comp_counit_app, Functor.comp_obj, Functor.comp_map,
    Category.id_comp, Category.comp_id, Category.assoc, Functor.map_comp]
  congr 1
  simp only [← Functor.map_comp]
  congr 1
  let h : K₂.obj (EA.obj (T₁.obj (FB.obj (FB'.obj x)))) ⟶ FB'.obj x :=
    c₁.inv.app _ ≫ EB.map (adj₁.counit.app _) ≫ adjB.counit.app _
  have hz : K₂.map (adj₂.unit.app _ ≫ T₂.map h) ≫ adj₂.counit.app _ = h := by simp
  have := key x (adjB'.counit.app x) (adj₂.unit.app _ ≫ T₂.map h)
  rw [hz] at this
  simp only [h, Functor.map_comp, Category.assoc] at this ⊢
  exact this
end Paste

section Shift

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}

/-- The conjugate `α^∨ : R₁ ⟶ R₂` of `α : L₂ ⟶ L₁` along `L₁ ⊣ R₁`, `L₂ ⊣ R₂`, written as a
composite of whiskerings of the unit of `L₂ ⊣ R₂`, `α` and the counit of `L₁ ⊣ R₁`. -/
theorem conjugateEquiv_eq_whisker (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁) :
    conjugateEquiv adj₁ adj₂ α =
      R₁.rightUnitor.inv ≫ Functor.whiskerLeft R₁ adj₂.unit ≫
        Functor.whiskerLeft R₁ (Functor.whiskerRight α R₂) ≫ (Functor.associator R₁ L₁ R₂).inv ≫
          Functor.whiskerRight adj₁.counit R₂ ≫ R₂.leftUnitor.hom := by
  ext x
  simp [conjugateEquiv_apply_app]

variable (A : Type*) [AddMonoid A] [HasShift C A] [HasShift D A] [L₁.CommShift A]
  [L₂.CommShift A] [R₁.CommShift A] [R₂.CommShift A]

/-- **The conjugate of a 2-morphism commuting with the shift commutes with the shift**, when
both adjunctions are compatible with the shifts. -/
theorem conjugateEquiv_commShift (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) [adj₁.CommShift A]
    [adj₂.CommShift A] (α : L₂ ⟶ L₁) [NatTrans.CommShift α A] :
    NatTrans.CommShift (conjugateEquiv adj₁ adj₂ α) A := by
  rw [conjugateEquiv_eq_whisker]
  infer_instance

end Shift

end Categorification.Stendhal.CupCap
