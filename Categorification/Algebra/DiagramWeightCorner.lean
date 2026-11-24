/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DiagramWeightBimodule
import Categorification.Algebra.CornerBimodule
import Categorification.Algebra.Graded.RightTwist
import Categorification.WeightedKLR.GradedK0.Grading

/-!
# Derived graded right tensor with rectangular corners

The coefficient between two degree-zero idempotents inherits an internal
degree by restriction. The derived right tensor uses the opposite corner
rings, with the action on the rectangular corner given by multiplication.
-/

noncomputable section

namespace Categorification

open CategoryTheory DG DirectSum MulOpposite Categorification.Graded
open scoped DG.DegreeZero

universe u v

variable {k : Type*} {A : Type u} [Field k] [Ring A] [Algebra k A]
  (G : ℤ → Submodule k A) [GradedAlgebra G]
  {e e' : A} (he : IsIdempotentElem e) (he' : IsIdempotentElem e')

/-- The homogeneous pieces of the rectangular corner between two idempotents. -/
def diagramCornerWeight (j : ℤ) : AddSubgroup (cornerBimodule e e') :=
  (G j).toAddSubgroup.comap (cornerBimodule e e').subtype

variable (he0 : e ∈ G 0) (he'0 : e' ∈ G 0)

local notation "L" => Graded.cornerGrading G he
local notation "R" => Graded.cornerGrading G he'

private def unopUnopRingHom {S : Type*} [Ring S] : Sᵐᵒᵖᵐᵒᵖ →+* S where
  toFun a := a.unop.unop
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

attribute [local instance] cornerBimodule.instModuleLeft cornerBimodule.instModuleRight

private instance (h : IsIdempotentElem e) :
    Module h.Cornerᵐᵒᵖᵐᵒᵖ (cornerBimodule e e') :=
  Module.compHom _ unopUnopRingHom

private instance (h : IsIdempotentElem e) (h' : IsIdempotentElem e') :
    SMulCommClass h'.Cornerᵐᵒᵖ h.Cornerᵐᵒᵖᵐᵒᵖ (cornerBimodule e e') where
  smul_comm a b x := Subtype.ext (show (b.unop.unop.val * x.val) * a.unop.val =
    b.unop.unop.val * (x.val * a.unop.val) from mul_assoc _ _ _)

/-- Derived right tensor with a rectangular corner, retaining internal weight. -/
def diagramCornerWeightDerivedRightTensor :
    letI := Graded.cornerGradedAlgebra G he he0
    letI := Graded.cornerGradedAlgebra G he' he'0
    letI := gradedAlgebraInternalGrading (oppositeGrade L)
    letI := gradedAlgebraInternalGrading (oppositeGrade R)
    letI := gradedAlgebraBigradedDGRing (oppositeGrade L)
    letI := gradedAlgebraBigradedDGRing (oppositeGrade R)
    [CatModule.HasDerivedCategory.{v,u} (WeightCategory he.Cornerᵐᵒᵖ)] →
    [CatModule.HasDerivedCategory.{v,u} (WeightCategory he'.Cornerᵐᵒᵖ)] →
    CatModule.DerivedCategory.{v,u} (WeightCategory he.Cornerᵐᵒᵖ) ⥤
      CatModule.DerivedCategory.{v,u} (WeightCategory he'.Cornerᵐᵒᵖ) := by
  letI := Graded.cornerGradedAlgebra G he he0
  letI := Graded.cornerGradedAlgebra G he' he'0
  letI := gradedAlgebraInternalGrading (oppositeGrade L)
  letI := gradedAlgebraInternalGrading (oppositeGrade R)
  letI := gradedAlgebraBigradedDGRing (oppositeGrade L)
  letI := gradedAlgebraBigradedDGRing (oppositeGrade R)
  intro hL hR
  exact diagramWeightDerivedTensor (A := he'.Cornerᵐᵒᵖ) (B := he.Cornerᵐᵒᵖ)
    (diagramCornerWeight G)
    (fun {i j a x} ha hx => by
      have hm : x.val * a.unop.val ∈ G (j + i) := SetLike.GradedMul.mul_mem (A := G)
        hx (show a.unop.val ∈ G i from ha)
      rw [add_comm j i] at hm
      change (a • x : cornerBimodule e e').val ∈ G (i + j)
      rw [cornerBimodule.coe_smul_right he']
      exact hm)
    (fun {i j b x} hb hx => by
      have hm : b.unop.val * x.val ∈ G (i + j) := SetLike.GradedMul.mul_mem (A := G)
        (show b.unop.val ∈ G i from hb) hx
      rw [add_comm i j] at hm
      change (op b • x : cornerBimodule e e').val ∈ G (j + i)
      exact hm)

end Categorification
