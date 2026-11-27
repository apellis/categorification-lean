/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.CategoryTheory.HomCongr
import Mathlib.Algebra.Group.Int.Defs

/-!
# Bijectivity of a functor on morphisms between shifts

For a functor `F` commuting with shifts, bijectivity of `F` on the morphisms `X ⟶ Y⟦d⟧` for all
`d` gives bijectivity on all morphisms `X⟦n⟧ ⟶ Y⟦m⟧` (`map_bijective_shift_shift`). This is the
reduction, in Webster, arXiv:1309.3796v3, proof of Theorem 6.15, of the full faithfulness of the
braiding on shifted generators to `Hom` and the higher `Ext` between them.
-/

namespace Categorification

open CategoryTheory

variable {C D : Type*} [Category C] [Category D] (F : C ⥤ D)

/-- Bijectivity on morphisms is invariant under isomorphisms of source and target. -/
theorem map_bijective_of_iso {A A' B B' : C} (eA : A ≅ A') (eB : B ≅ B')
    (h : Function.Bijective (F.map : (A ⟶ B) → (F.obj A ⟶ F.obj B))) :
    Function.Bijective (F.map : (A' ⟶ B') → (F.obj A' ⟶ F.obj B')) := by
  have e : (F.map : (A' ⟶ B') → _) =
      (Iso.homCongr (F.mapIso eA) (F.mapIso eB)) ∘ F.map ∘ (Iso.homCongr eA.symm eB.symm) := by
    funext g
    simp only [Function.comp_apply, Iso.homCongr_apply, Functor.mapIso_inv, Functor.mapIso_hom,
      Iso.symm_inv, Iso.symm_hom, ← F.map_comp, Category.assoc, Iso.inv_hom_id,
      Iso.inv_hom_id_assoc, Category.comp_id]
  rw [e]
  exact ((Iso.homCongr (F.mapIso eA) (F.mapIso eB)).bijective.comp h).comp
    (Iso.homCongr eA.symm eB.symm).bijective

/-- A functor is bijective on morphisms between objects with no nonzero morphisms on either
side. -/
theorem map_bijective_of_forall_eq {A B : C} (h₁ : ∀ f g : A ⟶ B, f = g)
    (h₂ : ∀ f g : F.obj A ⟶ F.obj B, f = g) (a : A ⟶ B) :
    Function.Bijective (F.map : (A ⟶ B) → (F.obj A ⟶ F.obj B)) :=
  ⟨fun f g _ => h₁ f g, fun g => ⟨a, h₂ _ g⟩⟩

variable [HasShift C ℤ] [HasShift D ℤ] [F.CommShift ℤ]

/-- Bijectivity on `A ⟶ B` gives bijectivity on `A⟦n⟧ ⟶ B⟦n⟧`. -/
theorem map_bijective_shift {A B : C} (n : ℤ)
    (h : Function.Bijective (F.map : (A ⟶ B) → (F.obj A ⟶ F.obj B))) :
    Function.Bijective (F.map : (A⟦n⟧ ⟶ B⟦n⟧) → (F.obj (A⟦n⟧) ⟶ F.obj (B⟦n⟧))) := by
  rw [← Function.Bijective.of_comp_iff _ ⟨(shiftFunctor C n).map_injective, (shiftFunctor C n).map_surjective⟩]
  have e : (F.map ∘ (shiftFunctor C n).map : (A ⟶ B) → _) =
      (Iso.homCongr ((F.commShiftIso n).app A).symm ((F.commShiftIso n).app B).symm) ∘
        (shiftFunctor D n).map ∘ F.map := by
    funext f
    simp only [Function.comp_apply, Iso.homCongr_apply, Iso.symm_inv, Iso.symm_hom, Iso.app_hom,
      Iso.app_inv]
    rw [← Category.assoc, ← Functor.commShiftIso_hom_naturality, Category.assoc,
      Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  rw [e]
  exact ((Iso.homCongr ((F.commShiftIso n).app A).symm
    ((F.commShiftIso n).app B).symm).bijective.comp ⟨(shiftFunctor D n).map_injective, (shiftFunctor D n).map_surjective⟩).comp h

/-- **Bijectivity on all shifts from bijectivity into shifts of the target**: if `F` is bijective
on `X ⟶ Y⟦d⟧` for every `d`, it is bijective on `X⟦n⟧ ⟶ Y⟦m⟧` for all `n`, `m`. -/
theorem map_bijective_shift_shift {X Y : C}
    (h : ∀ d : ℤ, Function.Bijective (F.map : (X ⟶ Y⟦d⟧) → (F.obj X ⟶ F.obj (Y⟦d⟧))))
    (n m : ℤ) :
    Function.Bijective (F.map : (X⟦n⟧ ⟶ Y⟦m⟧) → (F.obj (X⟦n⟧) ⟶ F.obj (Y⟦m⟧))) :=
  map_bijective_of_iso F (Iso.refl _) ((shiftFunctorAdd' C (m - n) n m (by omega)).app Y).symm
    (map_bijective_shift F n (h (m - n)))

omit [HasShift D ℤ] [F.CommShift ℤ] in
/-- Bijectivity on `X ⟶ Y` is bijectivity on `X ⟶ Y⟦0⟧`. -/
theorem map_bijective_shift_zero {X Y : C}
    (h : Function.Bijective (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y))) :
    Function.Bijective (F.map : (X ⟶ Y⟦(0 : ℤ)⟧) → (F.obj X ⟶ F.obj (Y⟦(0 : ℤ)⟧))) :=
  map_bijective_of_iso F (Iso.refl _) ((shiftFunctorZero C ℤ).app Y).symm h

end Categorification
