/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721Adjoint

/-!
# The conjugate isomorphisms and 2-morphisms

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21. The isomorphisms `𝔉 𝕋 ≅ 𝕋 𝔉` and `𝔈 𝕋 ≅ 𝕋 𝔈` are conjugates (mates) of
isomorphisms `𝕂 𝔈 ≅ 𝔈 𝕂` and `𝕂 𝔉 ≅ 𝔉 𝕂` (`CupCap.rightAdjointCommIso`). This file shows that
taking conjugates preserves the compatibility with 2-morphisms: if `c` carries `β` to `α`, then
the conjugate isomorphism carries the conjugate of `β` to the conjugate of `α`
(`CupCap.rightAdjointCommIso_whisker`). With the homological shift, the same holds when the
conjugate of `α` commutes with the shift (`CupCap.rightAdjointShiftCommIso_whisker`).

## Main results

* `CupCap.rightAdjointCommIso_whisker`.
* `CupCap.rightAdjointShiftCommIso_whisker`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {A₁ : Type u₁} {A₂ : Type u₂} {B₁ : Type u₃} {B₂ : Type u₄}
  [Category.{v₁} A₁] [Category.{v₂} A₂] [Category.{v₃} B₁] [Category.{v₄} B₂]
  {K₁ : A₁ ⥤ B₁} {T₁ : B₁ ⥤ A₁} {K₂ : A₂ ⥤ B₂} {T₂ : B₂ ⥤ A₂}
  {EA EA' : A₁ ⥤ A₂} {FA FA' : A₂ ⥤ A₁} {EB EB' : B₁ ⥤ B₂} {FB FB' : B₂ ⥤ B₁}

/-- **The conjugate isomorphism carries conjugate 2-morphisms to conjugate 2-morphisms**: if
`(β ∘ K₁) ≫ c' = c ≫ (K₂ ∘ α)` for `α : E_A ⟶ E_A'`, `β : E_B ⟶ E_B'`, then the conjugate
isomorphisms `F_B ⋙ T₁ ≅ T₂ ⋙ F_A` satisfy `(T₁ ∘ β^∨) ≫ c^∨ = c'^∨ ≫ (α^∨ ∘ T₂)`, where `^∨`
is the conjugate along the adjunctions `E ⊣ F`. -/
theorem rightAdjointCommIso_whisker (adj₁ : K₁ ⊣ T₁) (adj₂ : K₂ ⊣ T₂) (adjA : EA ⊣ FA)
    (adjB : EB ⊣ FB) (adjA' : EA' ⊣ FA') (adjB' : EB' ⊣ FB') (c : K₁ ⋙ EB ≅ EA ⋙ K₂)
    (c' : K₁ ⋙ EB' ≅ EA' ⋙ K₂) {α : EA ⟶ EA'} {β : EB ⟶ EB'}
    (h : Functor.whiskerLeft K₁ β ≫ c'.hom = c.hom ≫ Functor.whiskerRight α K₂) :
    Functor.whiskerRight (conjugateEquiv adjB' adjB β) T₁ ≫
        (rightAdjointCommIso adj₁ adj₂ adjA adjB c).hom =
      (rightAdjointCommIso adj₁ adj₂ adjA' adjB' c').hom ≫
        Functor.whiskerLeft T₂ (conjugateEquiv adjA' adjA α) := by
  have h' : c.inv ≫ Functor.whiskerLeft K₁ β = Functor.whiskerRight α K₂ ≫ c'.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  simp only [rightAdjointCommIso, conjugateIsoEquiv_apply_hom, Iso.symm_hom]
  rw [← conjugateEquiv_whiskerLeft adjB' adjB adj₁ β, conjugateEquiv_comp, h',
    ← conjugateEquiv_whiskerRight adjA' adjA adj₂ α, conjugateEquiv_comp]

/-- **With the homological shift**: if moreover the conjugate `α^∨ : F_A' ⟶ F_A` commutes with
the shift, the shifted conjugate isomorphisms carry `β^∨` to `α^∨`. -/
theorem rightAdjointShiftCommIso_whisker [HasShift A₁ ℤ] [HasShift A₂ ℤ] [FA.CommShift ℤ]
    [FA'.CommShift ℤ] (adj₁ : K₁ ⊣ T₁) (adj₂ : K₂ ⊣ T₂) (adjA : EA ⊣ FA)
    (adjB : EB ⊣ FB) (adjA' : EA' ⊣ FA') (adjB' : EB' ⊣ FB') (c : K₁ ⋙ EB ≅ EA ⋙ K₂)
    (c' : K₁ ⋙ EB' ≅ EA' ⋙ K₂) {α : EA ⟶ EA'} {β : EB ⟶ EB'}
    (hα : NatTrans.CommShift (conjugateEquiv adjA' adjA α) ℤ)
    (h : Functor.whiskerLeft K₁ β ≫ c'.hom = c.hom ≫ Functor.whiskerRight α K₂) (n : ℤ) :
    Functor.whiskerRight (conjugateEquiv adjB' adjB β) (T₁ ⋙ shiftFunctor A₁ n) ≫
        (rightAdjointShiftCommIso adj₁ adj₂ adjA adjB c n).hom =
      (rightAdjointShiftCommIso adj₁ adj₂ adjA' adjB' c' n).hom ≫
        Functor.whiskerLeft (T₂ ⋙ shiftFunctor A₂ n) (conjugateEquiv adjA' adjA α) := by
  have := hα
  have key := rightAdjointCommIso_whisker adj₁ adj₂ adjA adjB adjA' adjB' c c' h
  ext x
  have k' := congrArg (fun t => NatTrans.app t x) key
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at k'
  simp only [rightAdjointShiftCommIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.comp_map, Category.comp_id, Category.id_comp]
  rw [← Functor.map_comp_assoc, k', Functor.map_comp, Category.assoc, Category.assoc]
  congr 1
  have hs := NatTrans.app_shift (conjugateEquiv adjA' adjA α) n (T₂.obj x)
  erw [hs]
  simp only [Iso.inv_hom_id_app_assoc]

end Categorification.Stendhal.CupCap
