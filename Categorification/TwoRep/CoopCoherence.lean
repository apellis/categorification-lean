/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.Coop
import Categorification.TwoRep.ShiftCoherence

/-!
# Shift coherence of the bidual of a graded bicategory

The compatibilities of the whiskering shift isomorphisms `f ≫ g⟨n⟩ ≅ (f ≫ g)⟨n⟩` and
`f⟨n⟩ ≫ g ≅ (f ≫ g)⟨n⟩` with the associator and the unitors (the mixins
`GradedBicategory.ShiftAssoc`, `ShiftAssocRight`, `ShiftAssocMid`, `ShiftUnitor`; S. Cautis,
A. D. Lauda, arXiv:1111.1431v3, §2.1.2: the composition functors of a graded 2-category are
graded) pass to the bidual `Coop B`. Since the bidual exchanges left and right whiskering
(`Coop.whiskerLeftShiftIso_hom_unop`, `Coop.whiskerRightShiftIso_hom_unop`), `ShiftAssoc` and
`ShiftAssocRight` are exchanged, while `ShiftAssocMid` and `ShiftUnitor` are self-dual. (The
instance for `ShiftInterchange` is in `Coop.lean`.) Hence shift coherence
(`GradedBicategory.ShiftCoherence`) passes to the bidual.

## Main declarations

* `Coop.shiftAssoc`, `Coop.shiftAssocRight`, `Coop.shiftAssocMid`, `Coop.shiftUnitor`;
* `Coop.shiftCoherence`.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Opposite
open Pretriangulated Pretriangulated.Opposite

universe w v u

/-- Isomorphisms with equal `hom` have equal `inv`. -/
theorem Iso.inv_eq_of_hom_eq {C : Type*} [Category C] {X Y : C} {e₁ e₂ : X ≅ Y}
    (h : e₁.hom = e₂.hom) : e₁.inv = e₂.inv :=
  congrArg Iso.inv (Iso.ext h)

namespace Coop

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]

/-- The bidual exchanges `ShiftAssocRight` and `ShiftAssoc`. -/
instance shiftAssoc [GradedBicategory.ShiftAssocRight B] : GradedBicategory.ShiftAssoc (Coop B) where
  assoc_shift {a b c d} f g h n := by
    apply Quiver.Hom.unop_inj
    have hK := GradedBicategory.ShiftAssocRight.assoc_shift_right h.unop g.unop f.unop (-n)
    have hinv := Iso.inv_eq_of_hom_eq
      (e₁ := (α_ (h.unop⟦-n⟧) g.unop f.unop).symm ≪≫
        whiskerRightIso (whiskerRightShiftIso h.unop g.unop (-n)) f.unop ≪≫
        whiskerRightShiftIso (h.unop ≫ g.unop) f.unop (-n))
      (e₂ := whiskerRightShiftIso h.unop (g.unop ≫ f.unop) (-n) ≪≫
        (shiftFunctor _ (-n)).mapIso (α_ h.unop g.unop f.unop).symm)
      (by simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
          exact hK)
    simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv,
      Category.assoc] at hinv
    rw [unop_comp₂, unop_comp₂, unop_comp₂, unop_shift_map₂, whiskerLeftShiftIso_hom_unop,
      whiskerLeftShiftIso_hom_unop, unop_whiskerLeft, whiskerLeftShiftIso_hom_unop,
      associator_hom_unop, associator_hom_unop]
    exact (Category.assoc _ _ _).trans hinv

/-- The bidual exchanges `ShiftAssoc` and `ShiftAssocRight`. -/
instance shiftAssocRight [GradedBicategory.ShiftAssoc B] :
    GradedBicategory.ShiftAssocRight (Coop B) where
  assoc_shift_right {a b c d} f g h n := by
    apply Quiver.Hom.unop_inj
    have hK := GradedBicategory.ShiftAssoc.assoc_shift h.unop g.unop f.unop (-n)
    have hinv := Iso.inv_eq_of_hom_eq
      (e₁ := α_ h.unop g.unop (f.unop⟦-n⟧) ≪≫
        whiskerLeftIso h.unop (whiskerLeftShiftIso g.unop f.unop (-n)) ≪≫
        whiskerLeftShiftIso h.unop (g.unop ≫ f.unop) (-n))
      (e₂ := whiskerLeftShiftIso (h.unop ≫ g.unop) f.unop (-n) ≪≫
        (shiftFunctor _ (-n)).mapIso (α_ h.unop g.unop f.unop))
      (by simp only [Iso.trans_hom, Functor.mapIso_hom]
          exact hK)
    simp only [Iso.trans_inv, Functor.mapIso_inv, Category.assoc] at hinv
    rw [unop_comp₂, unop_comp₂, unop_comp₂, unop_shift_map₂, whiskerRightShiftIso_hom_unop,
      whiskerRightShiftIso_hom_unop, unop_whiskerRight, whiskerRightShiftIso_hom_unop,
      associator_inv_unop, associator_inv_unop]
    exact (Category.assoc _ _ _).trans hinv

/-- `ShiftAssocMid` is self-dual. -/
instance shiftAssocMid [GradedBicategory.ShiftAssocMid B] :
    GradedBicategory.ShiftAssocMid (Coop B) where
  assoc_shift_mid {a b c d} f g h n := by
    apply Quiver.Hom.unop_inj
    have hK := GradedBicategory.ShiftAssocMid.assoc_shift_mid h.unop g.unop f.unop (-n)
    -- `i₁`, `i₂`: the two composite shift isomorphisms; `hK` says `α' ≫ i₂ = i₁ ≫ α⟨-n⟩`
    have key : (whiskerRightIso (whiskerLeftShiftIso h.unop g.unop (-n)) f.unop ≪≫
          whiskerRightShiftIso (h.unop ≫ g.unop) f.unop (-n)).inv ≫
          (α_ h.unop (g.unop⟦-n⟧) f.unop).hom =
        ((α_ h.unop g.unop f.unop).hom)⟦-n⟧' ≫
          (whiskerLeftIso h.unop (whiskerRightShiftIso g.unop f.unop (-n)) ≪≫
            whiskerLeftShiftIso h.unop (g.unop ≫ f.unop) (-n)).inv := by
      rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
      simp only [Iso.trans_hom, Category.assoc]
      exact hK
    simp only [Iso.trans_inv, Category.assoc] at key
    rw [unop_comp₂, unop_comp₂, unop_comp₂, unop_comp₂, unop_shift_map₂,
      whiskerLeftShiftIso_hom_unop, whiskerRightShiftIso_hom_unop, unop_whiskerLeft,
      unop_whiskerRight, whiskerRightShiftIso_hom_unop, whiskerLeftShiftIso_hom_unop,
      associator_hom_unop, associator_hom_unop]
    exact (Category.assoc _ _ _).trans
      (key.trans (Category.assoc (obj := (ofCoop d ⟶ ofCoop a)) _ _ _).symm)

/-- `ShiftUnitor` is self-dual (the bidual exchanges the left and right unitors). -/
instance shiftUnitor [GradedBicategory.ShiftUnitor B] : GradedBicategory.ShiftUnitor (Coop B) where
  leftUnitor_shift {a b} g n := by
    apply Quiver.Hom.unop_inj
    have hK := GradedBicategory.ShiftUnitor.rightUnitor_shift g.unop (-n)
    have hinv := Iso.inv_eq_of_hom_eq
      (e₁ := whiskerRightShiftIso g.unop (𝟙 (ofCoop a)) (-n) ≪≫
        (shiftFunctor _ (-n)).mapIso (ρ_ g.unop))
      (e₂ := ρ_ (g.unop⟦-n⟧))
      (by simp only [Iso.trans_hom]
          exact hK)
    simp only [Iso.trans_inv] at hinv
    rw [unop_comp₂, unop_shift_map₂, whiskerLeftShiftIso_hom_unop, leftUnitor_hom_unop,
      leftUnitor_hom_unop]
    exact hinv
  rightUnitor_shift {a b} f n := by
    apply Quiver.Hom.unop_inj
    have hK := GradedBicategory.ShiftUnitor.leftUnitor_shift f.unop (-n)
    have hinv := Iso.inv_eq_of_hom_eq
      (e₁ := whiskerLeftShiftIso (𝟙 (ofCoop b)) f.unop (-n) ≪≫
        (shiftFunctor _ (-n)).mapIso (λ_ f.unop))
      (e₂ := λ_ (f.unop⟦-n⟧))
      (by simp only [Iso.trans_hom]
          exact hK)
    simp only [Iso.trans_inv] at hinv
    rw [unop_comp₂, unop_shift_map₂, whiskerRightShiftIso_hom_unop, rightUnitor_hom_unop,
      rightUnitor_hom_unop]
    exact hinv

/-- **Shift coherence passes to the bidual.** -/
instance shiftCoherence [GradedBicategory.ShiftCoherence B] :
    GradedBicategory.ShiftCoherence (Coop B) where
  toShiftInterchange := inferInstance
  toShiftAssoc := inferInstance
  toShiftAssocMid := inferInstance
  toShiftAssocRight := inferInstance
  toShiftUnitor := inferInstance

end Coop

end Categorification.TwoRep
