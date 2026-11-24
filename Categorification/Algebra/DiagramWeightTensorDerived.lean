/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DiagramWeightTensorCone
import Mathlib.CategoryTheory.Triangulated.Adjunction

/-!
# The triangulated diagram derived tensor

Transfer the cone comparison through the K-projective equivalence to
the derived category. Vanishing at a weight and cohomological degree
then propagates through finite iterated extensions.
-/

noncomputable section
namespace Categorification

open CategoryTheory Limits Pretriangulated DG DGOpposite
open scoped DG.DegreeZero CatModule

universe u

variable {B : Type u} [Ring B] [InternalGrading B] [BigradedDGRing B]
local notation "C" => WeightCategory B

open MulOpposite

variable {A P : Type u} [Ring A] [InternalGrading A] [BigradedDGRing A]
  [AddCommGroup P] [Module A P] [Module Bᵐᵒᵖ P] [SMulCommClass A Bᵐᵒᵖ P]
  (G : ℤ → AddSubgroup P)
  (hl : ∀ {i j : ℤ} {a : A} {x : P}, a ∈ wgrading i → x ∈ G j → a • x ∈ G (i+j))
  (hr : ∀ {i j : ℤ} {b : B} {x : P}, b ∈ wgrading i → x ∈ G j → MulOpposite.op b • x ∈ G (j+i))

local notation "D" => diagramWeightBimodule G hl hr


universe v

variable [CatModule.HasDerivedCategory.{v,u} (WeightCategory A)]
  [CatModule.HasDerivedCategory.{v,u} (WeightCategory B)]

/-- Shifts commute with the diagram tensor computed on K-projective models. -/
noncomputable instance diagramWeightDerivedTensor_commShift :
    (diagramWeightDerivedTensor G hl hr).CommShift ℤ := by
  let K := CatModule.HomotopyCategory.subcategoryKProjective.{u} (WeightCategory B)
  let E := CatModule.DerivedCategory.kProjectiveEquivalence (WeightCategory B)
  letI : E.functor.CommShift ℤ := by
    change (K.ι ⋙ CatModule.DerivedCategory.Qh).CommShift ℤ
    infer_instance
  letI : E.inverse.CommShift ℤ := E.commShiftInverse ℤ
  change (E.inverse ⋙ K.ι ⋙ diagramWeightTensorHomotopy G hl hr ⋙
    CatModule.DerivedCategory.Qh).CommShift ℤ
  infer_instance

/-- The diagram derived tensor is triangulated without a projectivity hypothesis
on the coefficient. -/
instance diagramWeightDerivedTensor_isTriangulated :
    (diagramWeightDerivedTensor G hl hr).IsTriangulated := by
  let K := CatModule.HomotopyCategory.subcategoryKProjective.{u} (WeightCategory B)
  let E := CatModule.DerivedCategory.kProjectiveEquivalence (WeightCategory B)
  let : E.functor.CommShift ℤ := by
    change (K.ι ⋙ CatModule.DerivedCategory.Qh).CommShift ℤ
    infer_instance
  let : E.inverse.CommShift ℤ := E.commShiftInverse ℤ
  let : E.CommShift ℤ := E.commShift_of_functor ℤ
  let : E.functor.IsTriangulated := by
    change (K.ι ⋙ CatModule.DerivedCategory.Qh).IsTriangulated
    infer_instance
  let : E.IsTriangulated := Equivalence.IsTriangulated.mk' E inferInstance
  change (E.inverse ⋙ K.ι ⋙ diagramWeightTensorHomotopy G hl hr ⋙
    CatModule.DerivedCategory.Qh).IsTriangulated
  infer_instance

/-- Vanishing at an output weight and cohomological degree extends from the
pieces of a finite iterated extension to the resulting module. -/
theorem diagramWeightDerivedTensor_cohomology_isZero_of_extensions
    (X : WeightCategory A) (n : ℤ)
    (P : ObjectProperty (CatModule.DerivedCategory.{v,u} (WeightCategory B)))
    (hP : ∀ Z, P Z → IsZero ((CatModule.DerivedCategory.cohomologyFunctor X n).obj
      ((diagramWeightDerivedTensor G hl hr).obj Z)))
    (m : ℕ) {Z : CatModule.DerivedCategory.{v,u} (WeightCategory B)}
    (hZ : P.extensionProductIter m Z) :
    IsZero ((CatModule.DerivedCategory.cohomologyFunctor X n).obj
      ((diagramWeightDerivedTensor G hl hr).obj Z)) := by
  let F := diagramWeightDerivedTensor G hl hr ⋙ CatModule.DerivedCategory.cohomologyFunctor X n
  induction m generalizing Z with
  | zero => exact hP Z hZ
  | succ m ih =>
    rw [ObjectProperty.extensionProductIter_succ] at hZ
    obtain ⟨Y, W, f, g, h, ht, hy, hw⟩ := hZ
    have hY : IsZero (F.obj Y) := hP Y hy
    have hW : IsZero (F.obj W) := ih hw
    have he := F.map_distinguished_exact (Triangle.mk f g h) ht
    exact he.isZero_X₂ (hY.eq_of_src _ _) (hW.eq_of_tgt _ _)

end Categorification
