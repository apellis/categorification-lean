/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DerivedTensor
import DG.Homotopy.OrdinaryBimoduleTensorTriangulated
import Mathlib.CategoryTheory.Triangulated.Adjunction

/-!
# Triangulated derived tensor for ordinary bimodules

The degree-zero ordinary bimodule tensor structure on the homotopy category
extends along the K-projective equivalence to the derived category.
-/

open CategoryTheory DG
open scoped DG.DegreeZero

noncomputable section

namespace Categorification

universe w u

variable (A B M : Type u) [Ring A] [Ring B] [AddCommGroup M] [Module A M]
  [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]

local instance : Fact (∀ m : InDegreeZero M, m ∈ grading 0) :=
  ⟨fun _ => (InDegreeZero.mem_grading_iff (M := M)).mpr (Or.inl rfl)⟩

open DG.DerivedCategory

variable [HasDerivedCategory.{w, u} A] [HasDerivedCategory.{w, u} B]

noncomputable local instance kProjectiveInverse_commShift :
    (kProjectiveEquivalence.{w} B).inverse.CommShift ℤ := by
  letI : (kProjectiveEquivalence.{w} B).functor.CommShift ℤ :=
    inferInstanceAs ((kProjectiveFunctor.{w} B).CommShift ℤ)
  exact (kProjectiveEquivalence.{w} B).commShiftInverse ℤ

local instance kProjectiveInverse_isTriangulated :
    (kProjectiveEquivalence.{w} B).inverse.IsTriangulated := by
  let : (kProjectiveEquivalence.{w} B).functor.CommShift ℤ :=
    inferInstanceAs ((kProjectiveFunctor.{w} B).CommShift ℤ)
  let : (kProjectiveEquivalence.{w} B).functor.IsTriangulated :=
    inferInstanceAs ((kProjectiveFunctor.{w} B).IsTriangulated)
  let : (kProjectiveEquivalence.{w} B).CommShift ℤ :=
    (kProjectiveEquivalence.{w} B).commShift_of_functor ℤ
  let : (kProjectiveEquivalence.{w} B).IsTriangulated :=
    Equivalence.IsTriangulated.mk' _ inferInstance
  infer_instance

noncomputable instance derivedTensor_commShift :
    (Categorification.derivedTensor.{w} A B M).CommShift ℤ := by
  unfold Categorification.derivedTensor
  infer_instance

instance derivedTensor_isTriangulated :
    (Categorification.derivedTensor.{w} A B M).IsTriangulated := by
  unfold Categorification.derivedTensor
  infer_instance

variable (C C' N : Type u) [Ring C] [Ring C'] [AddCommGroup N]
    [Module C N] [Module C'ᵐᵒᵖ N] [SMulCommClass C C'ᵐᵒᵖ N]
    [HasDerivedCategory.{w, u} Cᵐᵒᵖ] [HasDerivedCategory.{w, u} C'ᵐᵒᵖ]

noncomputable instance derivedRightTensor_commShift :
    (derivedRightTensor.{w} C C' N).CommShift ℤ := by
  unfold derivedRightTensor
  infer_instance

instance derivedRightTensor_isTriangulated :
    (derivedRightTensor.{w} C C' N).IsTriangulated := by
  unfold derivedRightTensor
  infer_instance

end Categorification
