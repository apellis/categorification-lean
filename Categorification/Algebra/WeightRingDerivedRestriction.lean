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
