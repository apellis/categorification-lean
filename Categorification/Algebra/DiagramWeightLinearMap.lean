/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DiagramWeightBimodule

/-!
# Homogeneous linear maps of diagram weight modules

A weight-preserving linear map restricts to a dg module map on the
left weight components. It can be applied to grading-preserving
quotient maps and shifted inclusions in pointwise exact sequences.
-/

noncomputable section

namespace Categorification

open CategoryTheory DG MulOpposite
open scoped DG.DegreeZero

universe u

variable {A C M N : Type u} [Ring A] [Ring C]
  [InternalGrading A] [InternalGrading C] [BigradedDGRing A] [BigradedDGRing C]
  [AddCommGroup M] [Module A M] [Module Cᵐᵒᵖ M] [SMulCommClass A Cᵐᵒᵖ M]
  [AddCommGroup N] [Module A N] [Module Cᵐᵒᵖ N] [SMulCommClass A Cᵐᵒᵖ N]
  (G : ℤ → AddSubgroup M) (H : ℤ → AddSubgroup N)
  (hgL : ∀ {i j : ℤ} {a : A} {x : M}, a ∈ wgrading i → x ∈ G j → a • x ∈ G (i+j))
  (hgR : ∀ {i j : ℤ} {c : C} {x : M}, c ∈ wgrading i → x ∈ G j → op c • x ∈ G (j+i))
  (hhL : ∀ {i j : ℤ} {a : A} {x : N}, a ∈ wgrading i → x ∈ H j → a • x ∈ H (i+j))
  (hhR : ∀ {i j : ℤ} {c : C} {x : N}, c ∈ wgrading i → x ∈ H j → op c • x ∈ H (j+i))
  (Z : WeightCategory C) (f : M →ₗ[A] N)
  (hf : ∀ {i : ℤ} {x : M}, x ∈ G i → f x ∈ H i)

private def homogeneousWeightAddHom (X : WeightCategory A) :
    InDegreeZero (G (X.as - Z.as)) →+ InDegreeZero (H (X.as - Z.as)) where
  toFun x := ⟨f x.val, hf x.property⟩
  map_zero' := Subtype.ext (map_zero f)
  map_add' x y := Subtype.ext (map_add f x.val y.val)

/-- A homogeneous linear map induces a map of the left weight modules at a fixed right weight. -/
def diagramWeightLeftLinearMap :
    (diagramWeightBimodule G hgL hgR).left Z ⟶ (diagramWeightBimodule H hhL hhR).left Z where
  app X := homogeneousWeightAddHom G H Z f hf X
  map_mem' {X i x} hx := by
    rcases (InDegreeZero.mem_grading_iff (M := G (X.as - Z.as))).mp hx with rfl | h
    · exact InDegreeZero.mem_grading_zero _
    · let g := homogeneousWeightAddHom G H Z f hf X
      exact (InDegreeZero.mem_grading_iff (M := H (X.as - Z.as))).mpr
        (Or.inr ((congrArg g h).trans (map_zero g)))
  map_d' {X} x := by
    let g := homogeneousWeightAddHom G H Z f hf X
    exact (congrArg g (InDegreeZero.d_apply (G (X.as - Z.as)) x)).trans (map_zero g)
  map_smul' a x := Subtype.ext (map_smul f a.val x.val)

end Categorification
