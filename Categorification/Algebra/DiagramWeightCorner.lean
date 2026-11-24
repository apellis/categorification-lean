/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DiagramWeightCoend
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

private theorem rightCornerLeft {i j : ℤ} {a : he'.Cornerᵐᵒᵖ}
    {x : cornerBimodule e e'} (ha : a.unop.val ∈ G i) (hx : x ∈ diagramCornerWeight G j) :
    a • x ∈ diagramCornerWeight G (i + j) := by
  have hm : x.val * a.unop.val ∈ G (j + i) := SetLike.GradedMul.mul_mem (A := G) hx ha
  rw [add_comm j i] at hm
  change (a • x : cornerBimodule e e').val ∈ G (i + j)
  rw [cornerBimodule.coe_smul_right he']
  exact hm

private theorem rightCornerRight {i j : ℤ} {b : he.Cornerᵐᵒᵖ}
    {x : cornerBimodule e e'} (hb : b.unop.val ∈ G i) (hx : x ∈ diagramCornerWeight G j) :
    op b • x ∈ diagramCornerWeight G (j + i) := by
  have hm : b.unop.val * x.val ∈ G (i + j) := SetLike.GradedMul.mul_mem (A := G) hb hx
  rw [add_comm i j] at hm
  exact hm

/-- The graded weight bimodule for right tensor by the rectangular corner. -/
def diagramCornerWeightRightBimodule :
    letI := Graded.cornerGradedAlgebra G he he0
    letI := Graded.cornerGradedAlgebra G he' he'0
    letI := gradedAlgebraInternalGrading (oppositeGrade L)
    letI := gradedAlgebraInternalGrading (oppositeGrade R)
    letI := gradedAlgebraBigradedDGRing (oppositeGrade L)
    letI := gradedAlgebraBigradedDGRing (oppositeGrade R)
    CatBimodule (WeightCategory he'.Cornerᵐᵒᵖ) (WeightCategory he.Cornerᵐᵒᵖ) := by
  letI := Graded.cornerGradedAlgebra G he he0
  letI := Graded.cornerGradedAlgebra G he' he'0
  letI := gradedAlgebraInternalGrading (oppositeGrade L)
  letI := gradedAlgebraInternalGrading (oppositeGrade R)
  letI := gradedAlgebraBigradedDGRing (oppositeGrade L)
  letI := gradedAlgebraBigradedDGRing (oppositeGrade R)
  exact diagramWeightBimodule (A := he'.Cornerᵐᵒᵖ) (B := he.Cornerᵐᵒᵖ)
    (diagramCornerWeight G)
    (rightCornerLeft G (e := e) he') (rightCornerRight G (e' := e') he)

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
    (rightCornerLeft G (e := e) he') (rightCornerRight G (e' := e') he)

section Composition

variable {g : A} (hg : IsIdempotentElem g) (hg0 : g ∈ G 0)

local notation "S" => Graded.cornerGrading G hg

private def cornerRightProduct : cornerBimodule e' g →+ cornerBimodule e e' →+ cornerBimodule e g where
  toFun x :=
    { toFun y := ⟨y.val * x.val, mem_cornerBimodule.mpr
        ⟨by rw [← mul_assoc, (mem_cornerBimodule.mp y.property).1],
          by rw [mul_assoc, (mem_cornerBimodule.mp x.property).2]⟩⟩
      map_zero' := Subtype.ext (zero_mul x.val)
      map_add' := fun y z => Subtype.ext (add_mul y.val z.val x.val) }
  map_zero' := AddMonoidHom.ext fun y => Subtype.ext (mul_zero y.val)
  map_add' x z := AddMonoidHom.ext fun y => Subtype.ext (mul_add y.val x.val z.val)

private theorem cornerRightProduct_mem {i j : ℤ} {x : cornerBimodule e' g}
    {y : cornerBimodule e e'} (hx : x ∈ diagramCornerWeight G i)
    (hy : y ∈ diagramCornerWeight G j) :
    cornerRightProduct x y ∈ diagramCornerWeight G (i + j) := by
  have hm : y.val * x.val ∈ G (j + i) := SetLike.GradedMul.mul_mem (A := G) hy hx
  rw [add_comm j i] at hm
  exact hm

/-- Composition of two rectangular coefficients descends to the tensor
over the intermediate weight category. -/
def diagramCornerWeightRightCoendProduct :
    letI := Graded.cornerGradedAlgebra G he he0
    letI := Graded.cornerGradedAlgebra G he' he'0
    letI := Graded.cornerGradedAlgebra G hg hg0
    letI := gradedAlgebraInternalGrading (oppositeGrade L)
    letI := gradedAlgebraInternalGrading (oppositeGrade R)
    letI := gradedAlgebraInternalGrading (oppositeGrade S)
    letI := gradedAlgebraBigradedDGRing (oppositeGrade L)
    letI := gradedAlgebraBigradedDGRing (oppositeGrade R)
    letI := gradedAlgebraBigradedDGRing (oppositeGrade S)
    (X : WeightCategory hg.Cornerᵐᵒᵖ) → (Z : WeightCategory he.Cornerᵐᵒᵖ) →
      CatTensorProduct ((diagramCornerWeightRightBimodule G he' hg he'0 hg0).right X)
        ((diagramCornerWeightRightBimodule G he he' he0 he'0).left Z) →+
          InDegreeZero (diagramCornerWeight (e := e) (e' := g) G (X.as - Z.as)) := by
  letI := Graded.cornerGradedAlgebra G he he0
  letI := Graded.cornerGradedAlgebra G he' he'0
  letI := Graded.cornerGradedAlgebra G hg hg0
  letI := gradedAlgebraInternalGrading (oppositeGrade L)
  letI := gradedAlgebraInternalGrading (oppositeGrade R)
  letI := gradedAlgebraInternalGrading (oppositeGrade S)
  letI := gradedAlgebraBigradedDGRing (oppositeGrade L)
  letI := gradedAlgebraBigradedDGRing (oppositeGrade R)
  letI := gradedAlgebraBigradedDGRing (oppositeGrade S)
  intro X Z
  exact diagramWeightCoendProduct
    (A := hg.Cornerᵐᵒᵖ) (B := he'.Cornerᵐᵒᵖ) (C := he.Cornerᵐᵒᵖ)
    (diagramCornerWeight G) (diagramCornerWeight G) (diagramCornerWeight G)
    (rightCornerLeft G (e := e') hg) (rightCornerRight G (e' := g) he')
    (rightCornerLeft G (e := e) he') (rightCornerRight G (e' := e') he)
    cornerRightProduct (cornerRightProduct_mem G)
    (fun b x y => Subtype.ext (by
      change y.val * (op b • x : cornerBimodule e' g).val =
        (b • y : cornerBimodule e e').val * x.val
      rw [cornerBimodule.coe_smul_right he']
      exact (mul_assoc _ _ _).symm)) X Z

/-- The coend map is ordinary diagram multiplication on a pure tensor. -/
theorem diagramCornerWeightRightCoendProduct_tmul :
    letI := Graded.cornerGradedAlgebra G he he0
    letI := Graded.cornerGradedAlgebra G he' he'0
    letI := Graded.cornerGradedAlgebra G hg hg0
    letI := gradedAlgebraInternalGrading (oppositeGrade L)
    letI := gradedAlgebraInternalGrading (oppositeGrade R)
    letI := gradedAlgebraInternalGrading (oppositeGrade S)
    letI := gradedAlgebraBigradedDGRing (oppositeGrade L)
    letI := gradedAlgebraBigradedDGRing (oppositeGrade R)
    letI := gradedAlgebraBigradedDGRing (oppositeGrade S)
    ∀ (X : WeightCategory hg.Cornerᵐᵒᵖ) (Y : WeightCategory he'.Cornerᵐᵒᵖ)
      (Z : WeightCategory he.Cornerᵐᵒᵖ)
      (x : (diagramCornerWeightRightBimodule G he' hg he'0 hg0).obj X Y)
      (y : (diagramCornerWeightRightBimodule G he he' he0 he'0).obj Y Z),
      (diagramCornerWeightRightCoendProduct G he he' he0 he'0 hg hg0 X Z
        (CatTensorProduct.tmul Y x y)).val.val = y.val.val * x.val.val := by
  let := Graded.cornerGradedAlgebra G he he0
  let := Graded.cornerGradedAlgebra G he' he'0
  let := Graded.cornerGradedAlgebra G hg hg0
  let := gradedAlgebraInternalGrading (oppositeGrade L)
  let := gradedAlgebraInternalGrading (oppositeGrade R)
  let := gradedAlgebraInternalGrading (oppositeGrade S)
  let := gradedAlgebraBigradedDGRing (oppositeGrade L)
  let := gradedAlgebraBigradedDGRing (oppositeGrade R)
  let := gradedAlgebraBigradedDGRing (oppositeGrade S)
  intro X Y Z x y
  exact congrArg Subtype.val (diagramWeightCoendProduct_tmul
    (A := hg.Cornerᵐᵒᵖ) (B := he'.Cornerᵐᵒᵖ) (C := he.Cornerᵐᵒᵖ)
    (diagramCornerWeight G) (diagramCornerWeight G) (diagramCornerWeight G)
    (rightCornerLeft G (e := e') hg) (rightCornerRight G (e' := g) he')
    (rightCornerLeft G (e := e) he') (rightCornerRight G (e' := e') he)
    cornerRightProduct (cornerRightProduct_mem G) _ X Z Y x y)

end Composition

end Categorification
