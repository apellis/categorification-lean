/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DG.Category.Derived.KProjective
import Mathlib.CategoryTheory.Shift.Adjunction
import Mathlib.CategoryTheory.Triangulated.Adjunction

set_option backward.isDefEq.respectTransparency false

/-!
# K-projective resolutions of dg modules over a dg category as a left adjoint

For a dg category `C`, the K-projective resolution functor `D(C) ⥤ K(C)` (the inverse of
`DG.CatModule.DerivedCategory.kProjectiveEquivalence` followed by the inclusion) is left
adjoint to the localization `Qh : K(C) ⥤ D(C)`, compatibly with the shifts. The counit
`p(Qh Y) ⟶ Y` is the resolution map. This is the dg-category form of
`Categorification.resolutionAdjunction`; it is used for the composites of graded braiding
functors (Webster, arXiv:1309.3796v3, Lemma 6.12).
-/

open CategoryTheory DG DG.CatModule DG.CatModule.DerivedCategory

universe w'' w v u

noncomputable section

namespace Categorification.CatModuleResolution

variable (C : Type u) [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  [DGCategory C] [HasDerivedCategory.{w'', max u v w} C]

set_option hygiene false in
local notation "K" => CatModule.HomotopyCategory.subcategoryKProjective.{max u v w} C
set_option hygiene false in
local notation "E" => CatModule.DerivedCategory.kProjectiveEquivalence.{w'', max u v w} C

instance kProjectiveEquivalence_functor_commShift : (E).functor.CommShift ℤ :=
  inferInstanceAs (((K).ι ⋙ Qh).CommShift ℤ)

instance kProjectiveEquivalence_inverse_commShift : (E).inverse.CommShift ℤ :=
  (E).commShiftInverse ℤ

instance kProjectiveEquivalence_commShift : (E).CommShift ℤ :=
  (E).commShift_of_functor ℤ

instance kProjectiveEquivalence_inverse_isTriangulated : (E).inverse.IsTriangulated := by
  let : (E).functor.IsTriangulated := inferInstanceAs (((K).ι ⋙ Qh).IsTriangulated)
  let : (E).IsTriangulated := Equivalence.IsTriangulated.mk' _ inferInstance
  infer_instance

/-- The K-projective resolution functor `D(C) ⥤ K(C)`. -/
abbrev resolutionFunctor :
    DerivedCategory.{w''} C ⥤ CatModule.HomotopyCategory.{max u v w} C :=
  (E).inverse ⋙ (K).ι

/-- The hom-set bijection `Hom_K(p X, Y) ≃ Hom_D(X, Qh Y)`. -/
def resolutionHomEquiv (X : DerivedCategory.{w''} C)
    (Y : CatModule.HomotopyCategory.{max u v w} C) :
    ((resolutionFunctor.{w''} C).obj X ⟶ Y) ≃ (X ⟶ Qh.obj Y) :=
  (Equiv.ofBijective _ (ObjectProperty.leftOrthogonal.map_bijective_of_isTriangulated
    ((E).inverse.obj X).property Qh Y)).trans
    (((E).counitIso.app X).homCongr (Iso.refl _))

theorem resolutionHomEquiv_apply {X : DerivedCategory.{w''} C}
    {Y : CatModule.HomotopyCategory.{max u v w} C}
    (f : (resolutionFunctor.{w''} C).obj X ⟶ Y) :
    resolutionHomEquiv.{w''} C X Y f = (E).counitIso.inv.app X ≫ Qh.map f := by
  change _ ≫ Qh.map f ≫ 𝟙 _ = _
  rw [Category.comp_id]
  rfl

/-- **K-projective resolution is left adjoint to `Qh`.** -/
def resolutionAdjunction :
    resolutionFunctor.{w''} C ⊣ (Qh : CatModule.HomotopyCategory.{max u v w} C ⥤ _) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := resolutionHomEquiv.{w''} C
      homEquiv_naturality_left_symm := by
        intro X' X Y f g
        rw [Equiv.symm_apply_eq]
        obtain ⟨h, rfl⟩ := (resolutionHomEquiv.{w''} C X Y).surjective g
        rw [Equiv.symm_apply_apply, resolutionHomEquiv_apply, resolutionHomEquiv_apply,
          Functor.map_comp, ← Category.assoc, ← Category.assoc]
        congr 1
        exact (E).counitIso.inv.naturality f
      homEquiv_naturality_right := by
        intro X Y Y' f g
        rw [resolutionHomEquiv_apply, resolutionHomEquiv_apply, Functor.map_comp,
          Category.assoc] }

@[simp]
theorem resolutionAdjunction_unit_app (X : DerivedCategory.{w''} C) :
    (resolutionAdjunction.{w''} C).unit.app X = (E).counitIso.inv.app X := by
  change resolutionHomEquiv.{w''} C X _ (𝟙 _) = _
  rw [resolutionHomEquiv_apply]
  exact (congrArg (_ ≫ ·) (Qh.map_id _)).trans (Category.comp_id _)

/-- `Qh` of the counit (the resolution map) is the counit of the K-projective equivalence. -/
theorem Qh_map_resolutionAdjunction_counit_app (Y : CatModule.HomotopyCategory.{max u v w} C) :
    Qh.map ((resolutionAdjunction.{w''} C).counit.app Y) = (E).counitIso.hom.app (Qh.obj Y) := by
  have h' : resolutionHomEquiv.{w''} C _ Y ((resolutionAdjunction.{w''} C).counit.app Y) =
      𝟙 _ :=
    (resolutionHomEquiv.{w''} C _ Y).apply_symm_apply (𝟙 _)
  rw [resolutionHomEquiv_apply] at h'
  rw [← cancel_epi ((E).counitIso.inv.app (Qh.obj Y)), h', Iso.inv_hom_id_app]
  rfl

instance resolutionAdjunction_commShift : (resolutionAdjunction.{w''} C).CommShift ℤ :=
  Adjunction.CommShift.mk' _ _ ⟨fun a => by
    ext X
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      resolutionAdjunction_unit_app, Functor.commShiftIso_comp_hom_app]
    have h := NatTrans.shift_app_comm (E).counitIso.inv a X
    simp only [Functor.comp_obj, Functor.id_obj, Functor.commShiftIso_comp_hom_app] at h
    have h2 := Functor.commShiftIso_comp_hom_app (K).ι Qh a ((E).inverse.obj X)
    rw [h]
    congr 1
    exact (congrArg (_ ≫ ·) h2).trans (by rw [Functor.map_comp, Category.assoc]; rfl)⟩

/-- The resolution map `p(Qh Y) ⟶ Y` becomes invertible in the derived category. -/
instance isIso_Qh_map_resolutionAdjunction_counit_app
    (Y : CatModule.HomotopyCategory.{max u v w} C) :
    IsIso (Qh.map ((resolutionAdjunction.{w''} C).counit.app Y)) := by
  rw [Qh_map_resolutionAdjunction_counit_app]
  infer_instance

end Categorification.CatModuleResolution
