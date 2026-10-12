/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.KLR.CyclotomicMixedMate.BicategoricalSquare
import Categorification.TwoRep.SidewaysCrossing

/-!
# AdditiveMateFormula

Component formulas for mates in the bicategory of additive categories.
The four objects and both adjunctions are arbitrary.
-/

noncomputable section
open CategoryTheory Categorification.TwoRep
namespace PrivateAdditiveMate
universe v u
open CategoryTheory.Bicategory
variable {A B C D : AdditiveCat.{v, u}}
  {L : A ⟶ B} {R : B ⟶ A} {L' : C ⟶ D} {R' : D ⟶ C}
  (adj : CategoryTheory.Adjunction L.obj R.obj)
  (adj' : CategoryTheory.Adjunction L'.obj R'.obj)
  {G : A ⟶ C} {H : B ⟶ D} (α : G ≫ L' ⟶ L ≫ H)

theorem mate_app (M : B) :
    (mateEquiv (AdditiveCat.ofAdjunction adj) (AdditiveCat.ofAdjunction adj') α).hom.app M =
      adj'.unit.app (G.obj.obj (R.obj.obj M)) ≫
        R'.obj.map (α.hom.app (R.obj.obj M)) ≫
          R'.obj.map (H.obj.map (adj.counit.app M)) := by
  rw [mateEquiv_eq_comp]
  change 𝟙 _ ≫ adj'.unit.app (G.obj.obj (R.obj.obj M)) ≫ 𝟙 _ ≫ 𝟙 _ ≫
    R'.obj.map (α.hom.app (R.obj.obj M)) ≫ 𝟙 _ ≫ 𝟙 _ ≫
      R'.obj.map (H.obj.map (adj.counit.app M)) ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]

theorem mate_app_homEquiv (M : B) :
    (mateEquiv (AdditiveCat.ofAdjunction adj) (AdditiveCat.ofAdjunction adj') α).hom.app M =
      adj'.homEquiv _ _ (α.hom.app (R.obj.obj M) ≫ H.obj.map (adj.counit.app M)) := by
  rw [mate_app, CategoryTheory.Adjunction.homEquiv_apply]
  exact congrArg (fun t => adj'.unit.app (G.obj.obj (R.obj.obj M)) ≫ t)
    (R'.obj.map_comp (α.hom.app (R.obj.obj M)) (H.obj.map (adj.counit.app M))).symm

end PrivateAdditiveMate
