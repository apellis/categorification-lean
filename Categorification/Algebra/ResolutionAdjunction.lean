/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DerivedTensorTriangulated
import Mathlib.CategoryTheory.Shift.Adjunction

set_option backward.isDefEq.respectTransparency false

/-!
# K-projective resolutions as a left adjoint

For a dg ring `B`, the K-projective resolution functor `D(B) ⥤ K(B)` (the inverse of
`DG.DerivedCategory.kProjectiveEquivalence` followed by the inclusion) is left adjoint to the
localization `Qh : K(B) ⥤ D(B)`, compatibly with the shifts. The counit `p(Qh Y) ⟶ Y` is the
resolution map.
-/

open CategoryTheory DG DG.DerivedCategory

universe w u

noncomputable section

namespace Categorification

variable (B : Type u) [Ring B] [DGAddCommGroup B] [DGRing B] [HasDerivedCategory.{w, u} B]

instance kProjectiveEquivalence_functor_commShift' :
    (kProjectiveEquivalence.{w} B).functor.CommShift ℤ :=
  inferInstanceAs ((kProjectiveFunctor.{w} B).CommShift ℤ)

noncomputable instance kProjectiveEquivalence_inverse_commShift' :
    (kProjectiveEquivalence.{w} B).inverse.CommShift ℤ :=
  (kProjectiveEquivalence.{w} B).commShiftInverse ℤ

instance kProjectiveEquivalence_commShift' : (kProjectiveEquivalence.{w} B).CommShift ℤ :=
  (kProjectiveEquivalence.{w} B).commShift_of_functor ℤ

instance kProjectiveEquivalence_inverse_isTriangulated' :
    (kProjectiveEquivalence.{w} B).inverse.IsTriangulated := by
  let : (kProjectiveEquivalence.{w} B).functor.IsTriangulated :=
    inferInstanceAs ((kProjectiveFunctor.{w} B).IsTriangulated)
  let : (kProjectiveEquivalence.{w} B).IsTriangulated :=
    Equivalence.IsTriangulated.mk' _ inferInstance
  infer_instance

/-- The K-projective resolution functor `D(B) ⥤ K(B)`. -/
abbrev resolutionFunctor : DerivedCategory.{w, u} B ⥤ DG.HomotopyCategory.{u} B :=
  (kProjectiveEquivalence.{w} B).inverse ⋙ (DG.HomotopyCategory.subcategoryKProjective.{u} B).ι

instance resolutionFunctor_isTriangulated : (resolutionFunctor.{w} B).IsTriangulated :=
  inferInstance

/-- The hom-set bijection `Hom_K(p X, Y) ≃ Hom_D(X, Qh Y)`. -/
def resolutionHomEquiv (X : DerivedCategory.{w, u} B) (Y : DG.HomotopyCategory.{u} B) :
    ((resolutionFunctor.{w} B).obj X ⟶ Y) ≃ (X ⟶ Qh.obj Y) :=
  (Equiv.ofBijective _ (ObjectProperty.leftOrthogonal.map_bijective_of_isTriangulated
    ((kProjectiveEquivalence.{w} B).inverse.obj X).property Qh Y)).trans
    (((kProjectiveEquivalence.{w} B).counitIso.app X).homCongr (Iso.refl _))

theorem resolutionHomEquiv_apply {X : DerivedCategory.{w, u} B} {Y : DG.HomotopyCategory.{u} B}
    (f : (resolutionFunctor.{w} B).obj X ⟶ Y) :
    resolutionHomEquiv.{w} B X Y f =
      (kProjectiveEquivalence.{w} B).counitIso.inv.app X ≫ Qh.map f := by
  change _ ≫ Qh.map f ≫ 𝟙 _ = _
  rw [Category.comp_id]
  rfl

/-- **K-projective resolution is left adjoint to `Qh`.** -/
def resolutionAdjunction : resolutionFunctor.{w} B ⊣ (Qh : DG.HomotopyCategory.{u} B ⥤ _) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := resolutionHomEquiv.{w} B
      homEquiv_naturality_left_symm := by
        intro X' X Y f g
        rw [Equiv.symm_apply_eq]
        obtain ⟨h, rfl⟩ := (resolutionHomEquiv.{w} B X Y).surjective g
        rw [Equiv.symm_apply_apply, resolutionHomEquiv_apply, resolutionHomEquiv_apply,
          Functor.map_comp, ← Category.assoc, ← Category.assoc]
        congr 1
        exact (kProjectiveEquivalence.{w} B).counitIso.inv.naturality f
      homEquiv_naturality_right := by
        intro X Y Y' f g
        rw [resolutionHomEquiv_apply, resolutionHomEquiv_apply, Functor.map_comp,
          Category.assoc] }

@[simp]
theorem resolutionAdjunction_unit_app (X : DerivedCategory.{w, u} B) :
    (resolutionAdjunction.{w} B).unit.app X =
      (kProjectiveEquivalence.{w} B).counitIso.inv.app X := by
  change resolutionHomEquiv.{w} B X _ (𝟙 _) = _
  rw [resolutionHomEquiv_apply]
  exact (congrArg (_ ≫ ·) (Qh.map_id _)).trans (Category.comp_id _)

/-- `Qh` of the counit (the resolution map) is the counit of the K-projective equivalence. -/
theorem Qh_map_resolutionAdjunction_counit_app (Y : DG.HomotopyCategory.{u} B) :
    Qh.map ((resolutionAdjunction.{w} B).counit.app Y) =
      (kProjectiveEquivalence.{w} B).counitIso.hom.app (Qh.obj Y) := by
  have h' : resolutionHomEquiv.{w} B _ Y ((resolutionAdjunction.{w} B).counit.app Y) = 𝟙 _ :=
    (resolutionHomEquiv.{w} B _ Y).apply_symm_apply (𝟙 _)
  rw [resolutionHomEquiv_apply] at h'
  rw [← cancel_epi ((kProjectiveEquivalence.{w} B).counitIso.inv.app (Qh.obj Y)), h',
    Iso.inv_hom_id_app]
  rfl

instance resolutionAdjunction_commShift : (resolutionAdjunction.{w} B).CommShift ℤ :=
  Adjunction.CommShift.mk' _ _ ⟨fun a => by
    ext X
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      resolutionAdjunction_unit_app, Functor.commShiftIso_comp_hom_app]
    have h := NatTrans.shift_app_comm (kProjectiveEquivalence.{w} B).counitIso.inv a X
    simp only [Functor.comp_obj, Functor.id_obj, Functor.commShiftIso_comp_hom_app] at h
    have h2 := Functor.commShiftIso_comp_hom_app (HomotopyCategory.subcategoryKProjective.{u} B).ι
      Qh a ((kProjectiveEquivalence.{w} B).inverse.obj X)
    rw [h]
    congr 1
    exact (congrArg (_ ≫ ·) h2).trans (by rw [Functor.map_comp, Category.assoc]; rfl)⟩

end Categorification
