/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DiagramWeightRingEquiv
import DG.Bigraded.Derived

/-!
# Equivalence of derived diagram-weight categories under ring relabelling

Weight-preserving mutually inverse ring maps give mutually inverse
restriction functors. This transports the evaluation from the reversed
red order in Webster, arXiv:1309.3796v2, §7.1.
-/
noncomputable section
namespace Categorification
open CategoryTheory DG CatModule
open scoped DG.DegreeZero
universe u v
variable {A B : Type u} [Ring A] [Ring B] [InternalGrading A] [InternalGrading B]
  [BigradedDGRing A] [BigradedDGRing B] (e : A ≃+* B)
  (he : ∀ {j : ℤ} (a : A), e a ∈ wgrading j ↔ a ∈ wgrading j)

include he in
omit [BigradedDGRing A] [BigradedDGRing B] in
private theorem inverseWeight {j : ℤ} (b : B) : e.symm b ∈ wgrading j ↔ b ∈ wgrading j := by
  simpa only [e.apply_symm_apply] using (he (e.symm b)).symm

local notation "F" => weightFunctorOfRingEquiv e he
local notation "G" => weightFunctorOfRingEquiv e.symm (inverseWeight e he)

private def forwardInverse : F ⋙ G ≅ 𝟭 (WeightCategory A) :=
  NatIso.ofComponents (fun _ => WeightCategory.isoOfEq rfl) (fun f => by
    apply WeightCategory.hom_ext
    change _ * _ = _ * _
    simp [WeightCategory.isoOfEq]
    exact e.symm_apply_apply f.val)

private def inverseForward : G ⋙ F ≅ 𝟭 (WeightCategory B) :=
  NatIso.ofComponents (fun _ => WeightCategory.isoOfEq rfl) (fun f => by
    apply WeightCategory.hom_ext
    change _ * _ = _ * _
    simp [WeightCategory.isoOfEq]
    exact e.apply_symm_apply f.val)

private def homotopyEquiv :
    CatModule.HomotopyCategory.{v} (WeightCategory B) ≌ CatModule.HomotopyCategory.{v} (WeightCategory A) := by
  let hA := CatModule.HomotopyCategory.precompNatIso (forwardInverse e he)
    (fun _ => WeightCategory.mem_grading_zero_of_val_eq_one _ rfl) (fun _ => WeightCategory.d_eq_zero_of_val_eq_one _ rfl)
    (fun _ => WeightCategory.mem_grading_zero_of_val_eq_one _ rfl) (fun _ => WeightCategory.d_eq_zero_of_val_eq_one _ rfl)
  let hB := CatModule.HomotopyCategory.precompNatIso (inverseForward e he)
    (fun _ => WeightCategory.mem_grading_zero_of_val_eq_one _ rfl) (fun _ => WeightCategory.d_eq_zero_of_val_eq_one _ rfl)
    (fun _ => WeightCategory.mem_grading_zero_of_val_eq_one _ rfl) (fun _ => WeightCategory.d_eq_zero_of_val_eq_one _ rfl)
  exact CategoryTheory.Equivalence.mk (CatModule.HomotopyCategory.precomp F) (CatModule.HomotopyCategory.precomp G)
    ((CatModule.HomotopyCategory.precompIdIso _).symm ≪≫ hB.symm ≪≫ CatModule.HomotopyCategory.precompCompIso G F)
    ((CatModule.HomotopyCategory.precompCompIso F G).symm ≪≫ hA ≪≫ CatModule.HomotopyCategory.precompIdIso _)

/-- Restriction along a homogeneous ring equivalence preserves K-projectivity
of dg modules over the weight category. -/
theorem isKProjective_precomp_weightRingEquiv {P : CatModule.{v} (WeightCategory B)} (hP : IsKProjective P) :
    IsKProjective ((CatModule.precomp F).obj P) := by
  let H := homotopyEquiv.{u,v} e he
  let Q := CatModule.HomotopyCategory.quotient.{v} (WeightCategory B)
  let K := CatModule.HomotopyCategory.subcategoryKProjective.{v} (WeightCategory A)
  let Acyc := CatModule.HomotopyCategory.subcategoryAcyclic.{v} (WeightCategory B)
  have hk := (CatModule.HomotopyCategory.quotient_obj_mem_subcategoryKProjective_iff P).mpr hP
  have ac {Y : CatModule.HomotopyCategory.{v} (WeightCategory A)}
      (hY : CatModule.HomotopyCategory.subcategoryAcyclic _ Y) : Acyc (H.inverse.obj Y) := by
    obtain ⟨N,rfl⟩ := CatModule.HomotopyCategory.quotient_obj_surjective Y
    have hN := (CatModule.HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff N).mp hY
    exact Acyc.prop_of_iso ((CatModule.HomotopyCategory.precompFactors G).app N).symm
      ((CatModule.HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff _).mpr (hN.precomp _))
  apply (CatModule.HomotopyCategory.quotient_obj_mem_subcategoryKProjective_iff _).mp
  apply K.prop_of_iso ((CatModule.HomotopyCategory.precompFactors F).app P)
  change K (H.functor.obj (Q.obj P))
  intro Y f hY
  have h₁ := hk (H.unitIso.hom.app _ ≫ H.inverse.map f) (ac hY)
  apply H.inverse.map_injective
  rw [Functor.map_zero]
  exact (cancel_epi (H.unitIso.hom.app _)).mp (h₁.trans (by simp))

variable [CatModule.HasDerivedCategory.{v,u} (WeightCategory A)]
  [CatModule.HasDerivedCategory.{v,u} (WeightCategory B)]

/-- Restriction along a homogeneous ring equivalence is an equivalence of
weight-module derived categories. -/
def weightRingEquivDerivedRestriction :
    CatModule.DerivedCategory.{v,u} (WeightCategory B) ≌ CatModule.DerivedCategory.{v,u} (WeightCategory A) := by
  let hA := CatModule.DerivedCategory.restrictNatIso (forwardInverse e he)
    (fun _ => WeightCategory.mem_grading_zero_of_val_eq_one _ rfl) (fun _ => WeightCategory.d_eq_zero_of_val_eq_one _ rfl)
    (fun _ => WeightCategory.mem_grading_zero_of_val_eq_one _ rfl) (fun _ => WeightCategory.d_eq_zero_of_val_eq_one _ rfl)
  let hB := CatModule.DerivedCategory.restrictNatIso (inverseForward e he)
    (fun _ => WeightCategory.mem_grading_zero_of_val_eq_one _ rfl) (fun _ => WeightCategory.d_eq_zero_of_val_eq_one _ rfl)
    (fun _ => WeightCategory.mem_grading_zero_of_val_eq_one _ rfl) (fun _ => WeightCategory.d_eq_zero_of_val_eq_one _ rfl)
  exact CategoryTheory.Equivalence.mk (CatModule.DerivedCategory.restrict F) (CatModule.DerivedCategory.restrict G)
    ((CatModule.DerivedCategory.restrictIdIso _).symm ≪≫ hB.symm ≪≫ CatModule.DerivedCategory.restrictCompIso G F)
    ((CatModule.DerivedCategory.restrictCompIso F G).symm ≪≫ hA ≪≫ CatModule.DerivedCategory.restrictIdIso _)
end Categorification
