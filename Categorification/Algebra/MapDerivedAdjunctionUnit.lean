/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.MapDerivedNatTrans
import Categorification.TwoRep.RouqSl2

/-!
# Units and counits of derived adjunctions, and derived explicit inverses

For an adjunction `F ⊣ G` of exact functors between abelian categories, the unit and counit of
the induced adjunction on derived categories (`Adjunction.mapDerivedCategory`) are the derived
unit and counit, conjugated by `Functor.mapDerivedCategoryIdIso` and
`Functor.mapDerivedCategoryCompIso` (`Adjunction.mapDerivedCategory_unit_eq`,
`Adjunction.mapDerivedCategory_counit_eq`).

An explicit inverse of `(f, g 0, …, g (n-1))` in a category of exact functors (`TwoRep.SumInvTo`,
`TwoRep.SumInvFrom`; Brundan, arXiv:1501.00350v1, (1.8), (1.9)) passes to derived categories
(`TwoRep.SumInvTo.mapDerivedCategory`, `TwoRep.SumInvFrom.mapDerivedCategory`). These are the
inputs for lifting Rouquier's local data from module categories to derived categories.
-/

noncomputable section

namespace CategoryTheory

open Category Limits

universe w₁ w₂

variable {C₁ : Type*} [Category* C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type*} [Category* C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]

namespace Adjunction

variable {F : C₁ ⥤ C₂} {G : C₂ ⥤ C₁} [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- **The derived unit** is the derived functor of the unit, up to the identifications of the
derived identity and of the derived composite. -/
theorem mapDerivedCategory_unit_eq (adj : F ⊣ G) :
    adj.mapDerivedCategory.unit = (Functor.mapDerivedCategoryIdIso C₁).inv ≫
      adj.unit.mapDerivedCategory ≫ (Functor.mapDerivedCategoryCompIso F G).inv := by
  rw [← cancel_epi (Functor.mapDerivedCategoryIdIso C₁).hom, Iso.hom_inv_id_assoc,
    ← cancel_mono (Functor.mapDerivedCategoryCompIso F G).hom, assoc, assoc,
    Iso.inv_hom_id, comp_id]
  refine NatTrans.derivedCategory_ext fun X => ?_
  simp only [NatTrans.comp_app, mapDerivedCategory_unit_app,
    Functor.mapDerivedCategoryIdIso_hom_app, Functor.mapDerivedCategoryCompIso_hom_app_Q_obj,
    NatTrans.mapDerivedCategory_app_Q_obj, assoc]
  rw [← Functor.map_comp_assoc G.mapDerivedCategory, Iso.inv_hom_id_app]
  have h1 : G.mapDerivedCategory.map
      (𝟙 ((F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).obj X)) = 𝟙 _ :=
    G.mapDerivedCategory.map_id _
  rw [h1]
  erw [Category.id_comp, Iso.inv_hom_id_app_assoc]
  congr 1
  simp only [← Functor.map_comp_assoc]
  congr 2
  ext n
  simp

/-- **The derived counit** is the derived functor of the counit, up to the identifications of
the derived composite and of the derived identity. -/
theorem mapDerivedCategory_counit_eq (adj : F ⊣ G) :
    adj.mapDerivedCategory.counit = (Functor.mapDerivedCategoryCompIso G F).hom ≫
      adj.counit.mapDerivedCategory ≫ (Functor.mapDerivedCategoryIdIso C₂).hom := by
  refine NatTrans.derivedCategory_ext fun X => ?_
  simp only [NatTrans.comp_app, mapDerivedCategory_counit_app,
    Functor.mapDerivedCategoryIdIso_hom_app, Functor.mapDerivedCategoryCompIso_hom_app_Q_obj,
    NatTrans.mapDerivedCategory_app_Q_obj, assoc, Iso.inv_hom_id_app_assoc]
  congr 2
  simp only [← Functor.map_comp]
  congr 1
  ext n
  simp

end Adjunction

namespace NatTrans

variable {F G : C₁ ⥤ C₂} [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

theorem mapDerivedCategory_sum {ι : Type*} (s : Finset ι) (σ : ι → (F ⟶ G)) :
    (∑ m ∈ s, σ m).mapDerivedCategory = ∑ m ∈ s, (σ m).mapDerivedCategory := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, mapDerivedCategory_add, ih]

end NatTrans

end CategoryTheory

namespace Categorification.TwoRep

open CategoryTheory Limits

universe w₁ w₂

variable {C₁ : Type*} [Category* C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type*} [Category* C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  {F G H : C₁ ⥤ C₂} [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H] {n : ℕ}

/-- **An explicit inverse of exact functors passes to derived categories.** -/
def SumInvTo.mapDerivedCategory {f : F ⟶ G} {g : ℕ → (F ⟶ H)} (S : SumInvTo f g n) :
    SumInvTo f.mapDerivedCategory (fun m => (g m).mapDerivedCategory) n where
  f' := S.f'.mapDerivedCategory
  g' m := (S.g' m).mapDerivedCategory
  total := by
    simp only [← NatTrans.mapDerivedCategory_comp, ← NatTrans.mapDerivedCategory_sum,
      ← NatTrans.mapDerivedCategory_add, S.total, NatTrans.mapDerivedCategory_id]
  ff := by rw [← NatTrans.mapDerivedCategory_comp, S.ff, NatTrans.mapDerivedCategory_id]
  fg m hm := by
    rw [← NatTrans.mapDerivedCategory_comp, S.fg m hm, NatTrans.mapDerivedCategory_zero]
  gf m hm := by
    rw [← NatTrans.mapDerivedCategory_comp, S.gf m hm, NatTrans.mapDerivedCategory_zero]
  gg m m' hm hm' := by
    rw [← NatTrans.mapDerivedCategory_comp, S.gg m m' hm hm']
    split_ifs
    · exact NatTrans.mapDerivedCategory_id
    · exact NatTrans.mapDerivedCategory_zero

/-- **An explicit inverse out of a sum of exact functors passes to derived categories.** -/
def SumInvFrom.mapDerivedCategory {f : G ⟶ F} {g : ℕ → (H ⟶ F)} (S : SumInvFrom f g n) :
    SumInvFrom f.mapDerivedCategory (fun m => (g m).mapDerivedCategory) n where
  f' := S.f'.mapDerivedCategory
  g' m := (S.g' m).mapDerivedCategory
  total := by
    simp only [← NatTrans.mapDerivedCategory_comp, ← NatTrans.mapDerivedCategory_sum,
      ← NatTrans.mapDerivedCategory_add, S.total, NatTrans.mapDerivedCategory_id]
  ff := by rw [← NatTrans.mapDerivedCategory_comp, S.ff, NatTrans.mapDerivedCategory_id]
  fg m hm := by
    rw [← NatTrans.mapDerivedCategory_comp, S.fg m hm, NatTrans.mapDerivedCategory_zero]
  gf m hm := by
    rw [← NatTrans.mapDerivedCategory_comp, S.gf m hm, NatTrans.mapDerivedCategory_zero]
  gg m m' hm hm' := by
    rw [← NatTrans.mapDerivedCategory_comp, S.gg m m' hm hm']
    split_ifs
    · exact NatTrans.mapDerivedCategory_id
    · exact NatTrans.mapDerivedCategory_zero

end Categorification.TwoRep
