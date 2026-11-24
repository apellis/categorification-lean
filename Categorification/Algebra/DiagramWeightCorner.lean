/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DiagramWeightCoendSurjectivity
import Categorification.Algebra.DiagramWeightOrdinaryTensor
import Categorification.Algebra.DiagramWeightCoendNaturality
import Categorification.Algebra.CornerTensorCutLift
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

/-- The rectangular coefficient product in the right-module order. -/
def cornerRightProduct : cornerBimodule e' g →+ cornerBimodule e e' →+ cornerBimodule e g where
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

/-- The right-module coend product is onto when ordinary products span the
target and each corner is the direct sum of its homogeneous pieces. -/
theorem diagramCornerWeightRightCoendProduct_surjective
    (h₁ : IsInternal (diagramCornerWeight (e := e') (e' := g) G))
    (h₂ : IsInternal (diagramCornerWeight (e := e) (e' := e') G))
    (h₃ : IsInternal (diagramCornerWeight (e := e) (e' := g) G))
    (hspan : AddSubgroup.closure
      (Set.range fun z : cornerBimodule e' g × cornerBimodule e e' =>
        cornerRightProduct z.1 z.2) = ⊤) :
    letI := Graded.cornerGradedAlgebra G he he0
    letI := Graded.cornerGradedAlgebra G he' he'0
    letI := Graded.cornerGradedAlgebra G hg hg0
    letI := gradedAlgebraInternalGrading (oppositeGrade L)
    letI := gradedAlgebraInternalGrading (oppositeGrade R)
    letI := gradedAlgebraInternalGrading (oppositeGrade S)
    letI := gradedAlgebraBigradedDGRing (oppositeGrade L)
    letI := gradedAlgebraBigradedDGRing (oppositeGrade R)
    letI := gradedAlgebraBigradedDGRing (oppositeGrade S)
    ∀ (X : WeightCategory hg.Cornerᵐᵒᵖ) (Z : WeightCategory he.Cornerᵐᵒᵖ),
      Function.Surjective (diagramCornerWeightRightCoendProduct G he he' he0 he'0 hg hg0 X Z) := by
  let := Graded.cornerGradedAlgebra G he he0
  let := Graded.cornerGradedAlgebra G he' he'0
  let := Graded.cornerGradedAlgebra G hg hg0
  let := gradedAlgebraInternalGrading (oppositeGrade L)
  let := gradedAlgebraInternalGrading (oppositeGrade R)
  let := gradedAlgebraInternalGrading (oppositeGrade S)
  let := gradedAlgebraBigradedDGRing (oppositeGrade L)
  let := gradedAlgebraBigradedDGRing (oppositeGrade R)
  let := gradedAlgebraBigradedDGRing (oppositeGrade S)
  let := h₁.chooseDecomposition
  let := h₂.chooseDecomposition
  let := h₃.chooseDecomposition
  intro X Z
  exact diagramWeightCoendProduct_surjective
    (A := hg.Cornerᵐᵒᵖ) (B := he'.Cornerᵐᵒᵖ) (C := he.Cornerᵐᵒᵖ)
    (diagramCornerWeight G) (diagramCornerWeight G) (diagramCornerWeight G)
    (rightCornerLeft G (e := e') hg) (rightCornerRight G (e' := g) he')
    (rightCornerLeft G (e := e) he') (rightCornerRight G (e' := e') he)
    cornerRightProduct (cornerRightProduct_mem G) _ X Z hspan

end Composition

/-- The left-module family of a rectangular right weight bimodule. -/
def diagramCornerWeightRightFamily :
    letI := Graded.cornerGradedAlgebra G he he0
    letI := Graded.cornerGradedAlgebra G he' he'0
    letI := gradedAlgebraInternalGrading (oppositeGrade L)
    letI := gradedAlgebraInternalGrading (oppositeGrade R)
    letI := gradedAlgebraBigradedDGRing (oppositeGrade L)
    letI := gradedAlgebraBigradedDGRing (oppositeGrade R)
    (WeightCategory he.Cornerᵐᵒᵖ)ᵒᵖ ⥤ CatModule (WeightCategory he'.Cornerᵐᵒᵖ) := by
  letI := Graded.cornerGradedAlgebra G he he0
  letI := Graded.cornerGradedAlgebra G he' he'0
  letI := gradedAlgebraInternalGrading (oppositeGrade L)
  letI := gradedAlgebraInternalGrading (oppositeGrade R)
  letI := gradedAlgebraBigradedDGRing (oppositeGrade L)
  letI := gradedAlgebraBigradedDGRing (oppositeGrade R)
  exact diagramWeightLeftFunctor (diagramCornerWeight G)
    (rightCornerLeft G (e := e) he') (rightCornerRight G (e' := e') he)

section OrdinaryComparison

open CornerEndomorphism

variable {k : Type*} {A : Type u} [Field k] [Ring A] [Algebra k A]
  (G : ℤ → Submodule k A) [GradedAlgebra G]
  {e₂ e₁ e₀ : A} (h₂ : IsIdempotentElem e₂) (h₁ : IsIdempotentElem e₁) (h₀ : IsIdempotentElem e₀)
  (he₂ : e₂ ∈ G 0) (he₁ : e₁ ∈ G 0) (he₀ : e₀ ∈ G 0)

local notation "OW" h:arg => Graded.oppositeGrade (Graded.cornerGrading G h)
local notation "D₁" => diagramCornerWeightRightBimodule G h₁ h₀ he₁ he₀
local notation "D₂" => diagramCornerWeightRightBimodule G h₂ h₁ he₂ he₁

/-- Forget weights on the tensor coend of two rectangular coefficients. -/
def diagramCornerWeightRightToOrdinary :
    letI := Graded.cornerGradedAlgebra G h₂ he₂
    letI := Graded.cornerGradedAlgebra G h₁ he₁
    letI := Graded.cornerGradedAlgebra G h₀ he₀
    letI := gradedAlgebraInternalGrading (OW h₂)
    letI := gradedAlgebraInternalGrading (OW h₁)
    letI := gradedAlgebraInternalGrading (OW h₀)
    letI := gradedAlgebraBigradedDGRing (OW h₂)
    letI := gradedAlgebraBigradedDGRing (OW h₁)
    letI := gradedAlgebraBigradedDGRing (OW h₀)
    (X : WeightCategory h₀.Cornerᵐᵒᵖ) → (Z : WeightCategory h₂.Cornerᵐᵒᵖ) →
      CatTensorProduct ((D₁).right X) ((D₂).left Z) →+ CornerTensor k A e₂ e₁ e₀ := by
  letI := Graded.cornerGradedAlgebra G h₂ he₂
  letI := Graded.cornerGradedAlgebra G h₁ he₁
  letI := Graded.cornerGradedAlgebra G h₀ he₀
  letI := gradedAlgebraInternalGrading (OW h₂)
  letI := gradedAlgebraInternalGrading (OW h₁)
  letI := gradedAlgebraInternalGrading (OW h₀)
  letI := gradedAlgebraBigradedDGRing (OW h₂)
  letI := gradedAlgebraBigradedDGRing (OW h₁)
  letI := gradedAlgebraBigradedDGRing (OW h₀)
  intro X Z
  let F (Y : WeightCategory h₁.Cornerᵐᵒᵖ) :
      ((D₁).right X).obj (DG.DGOpposite.op Y) →+
        ((D₂).left Z).obj Y →+ CornerTensor k A e₂ e₁ e₀ :=
    { toFun := fun x =>
        { toFun := fun y => CornerTensor.tmul y.val.val x.val.val
          map_zero' := by
            change (CornerTensor.tmul 0 x.val.val : CornerTensor k A e₂ e₁ e₀) = 0
            rw [CornerTensor.tmul_def, TensorProduct.zero_tmul, map_zero]
          map_add' := fun y y' => CornerTensor.tmul_add_left _ _ _ }
      map_zero' := AddMonoidHom.ext fun y => by
        change (CornerTensor.tmul y.val.val 0 : CornerTensor k A e₂ e₁ e₀) = 0
        rw [CornerTensor.tmul_def, TensorProduct.tmul_zero, map_zero]
      map_add' := fun x x' => AddMonoidHom.ext fun y => CornerTensor.tmul_add_right _ _ _ }
  refine CatTensorProduct.lift F ?_
  intro Y Y' f x y
  rw [CatBimodule.right_ract]
  have hc : e₁ * f.val.unop.val * e₁ = f.val.unop.val := by
    rw [corner_mul_left h₁, corner_mul_right h₁]
  exact (CornerTensor.tmul_balance_of hc y.val.val x.val.val).symm

local notation "G₁" => diagramCornerWeight (e := e₁) (e' := e₀) G
local notation "G₂" => diagramCornerWeight (e := e₂) (e' := e₁) G

/-- Cut an ordinary tensor and slice its homogeneous terms into the weight coend. -/
def diagramCornerWeightRightSlice
    (d₁ : IsInternal G₁) (d₂ : IsInternal G₂) :
    letI := Graded.cornerGradedAlgebra G h₂ he₂
    letI := Graded.cornerGradedAlgebra G h₁ he₁
    letI := Graded.cornerGradedAlgebra G h₀ he₀
    letI := gradedAlgebraInternalGrading (OW h₂)
    letI := gradedAlgebraInternalGrading (OW h₁)
    letI := gradedAlgebraInternalGrading (OW h₀)
    letI := gradedAlgebraBigradedDGRing (OW h₂)
    letI := gradedAlgebraBigradedDGRing (OW h₁)
    letI := gradedAlgebraBigradedDGRing (OW h₀)
    (X : WeightCategory h₀.Cornerᵐᵒᵖ) → (Z : WeightCategory h₂.Cornerᵐᵒᵖ) →
      CornerTensor k A e₂ e₁ e₀ →+ CatTensorProduct ((D₁).right X) ((D₂).left Z) := by
  letI := Graded.cornerGradedAlgebra G h₂ he₂
  letI := Graded.cornerGradedAlgebra G h₁ he₁
  letI := Graded.cornerGradedAlgebra G h₀ he₀
  letI := gradedAlgebraInternalGrading (OW h₂)
  letI := gradedAlgebraInternalGrading (OW h₁)
  letI := gradedAlgebraInternalGrading (OW h₀)
  letI := gradedAlgebraBigradedDGRing (OW h₂)
  letI := gradedAlgebraBigradedDGRing (OW h₁)
  letI := gradedAlgebraBigradedDGRing (OW h₀)
  letI := d₁.chooseDecomposition
  letI := d₂.chooseDecomposition
  intro X Z
  exact cornerTensorCutLift (k := k) h₂ h₁ h₀
    (diagramWeightTensorSlice (A := h₀.Cornerᵐᵒᵖ) (B := h₁.Cornerᵐᵒᵖ) (C := h₂.Cornerᵐᵒᵖ)
      G₁ G₂ (rightCornerLeft G (e := e₁) h₀) (rightCornerRight G (e' := e₀) h₁)
      (rightCornerLeft G (e := e₂) h₁) (rightCornerRight G (e' := e₁) h₂) X Z)
    (fun b x y => diagramWeightTensorSlice_balanced
      (A := h₀.Cornerᵐᵒᵖ) (B := h₁.Cornerᵐᵒᵖ) (C := h₂.Cornerᵐᵒᵖ)
      G₁ G₂ (rightCornerLeft G (e := e₁) h₀) (rightCornerRight G (e' := e₀) h₁)
      (rightCornerLeft G (e := e₂) h₁) (rightCornerRight G (e' := e₁) h₂)
      X Z (op b) x y)

/-- Ordinary slicing is a left inverse to the forgetful map on the field corner tensor. -/
theorem diagramCornerWeightRightSlice_leftInverse
    (d₁ : IsInternal G₁) (d₂ : IsInternal G₂) :
    letI := Graded.cornerGradedAlgebra G h₂ he₂
    letI := Graded.cornerGradedAlgebra G h₁ he₁
    letI := Graded.cornerGradedAlgebra G h₀ he₀
    letI := gradedAlgebraInternalGrading (OW h₂)
    letI := gradedAlgebraInternalGrading (OW h₁)
    letI := gradedAlgebraInternalGrading (OW h₀)
    letI := gradedAlgebraBigradedDGRing (OW h₂)
    letI := gradedAlgebraBigradedDGRing (OW h₁)
    letI := gradedAlgebraBigradedDGRing (OW h₀)
    ∀ (X : WeightCategory h₀.Cornerᵐᵒᵖ) (Z : WeightCategory h₂.Cornerᵐᵒᵖ),
      Function.LeftInverse
        (diagramCornerWeightRightSlice G h₂ h₁ h₀ he₂ he₁ he₀ d₁ d₂ X Z)
        (diagramCornerWeightRightToOrdinary G h₂ h₁ h₀ he₂ he₁ he₀ X Z) := by
  let := Graded.cornerGradedAlgebra G h₂ he₂
  let := Graded.cornerGradedAlgebra G h₁ he₁
  let := Graded.cornerGradedAlgebra G h₀ he₀
  let := gradedAlgebraInternalGrading (OW h₂)
  let := gradedAlgebraInternalGrading (OW h₁)
  let := gradedAlgebraInternalGrading (OW h₀)
  let := gradedAlgebraBigradedDGRing (OW h₂)
  let := gradedAlgebraBigradedDGRing (OW h₁)
  let := gradedAlgebraBigradedDGRing (OW h₀)
  let := d₁.chooseDecomposition
  let := d₂.chooseDecomposition
  intro X Z t
  let f := diagramCornerWeightRightToOrdinary G h₂ h₁ h₀ he₂ he₁ he₀ X Z
  let g := diagramCornerWeightRightSlice G h₂ h₁ h₀ he₂ he₁ he₀ d₁ d₂ X Z
  change g (f t) = t
  induction t using CatTensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul Y x y =>
    have hf : f (CatTensorProduct.tmul Y x y) = CornerTensor.tmul y.val.val x.val.val := by
      dsimp only [f, diagramCornerWeightRightToOrdinary]
      apply CatTensorProduct.lift_tmul
      intro S S' a v w
      rw [CatBimodule.right_ract]
      have hc : e₁ * a.val.unop.val * e₁ = a.val.unop.val := by
        rw [corner_mul_left h₁, corner_mul_right h₁]
      exact (CornerTensor.tmul_balance_of hc w.val.val v.val.val).symm
    rw [hf]
    exact (cornerTensorCutLift_tmul (k := k) h₂ h₁ h₀ _ _ y.val x.val).trans
      (diagramWeightTensorSlice_tmul
        (A := h₀.Cornerᵐᵒᵖ) (B := h₁.Cornerᵐᵒᵖ) (C := h₂.Cornerᵐᵒᵖ)
        G₁ G₂ (rightCornerLeft G (e := e₁) h₀) (rightCornerRight G (e' := e₀) h₁)
        (rightCornerLeft G (e := e₂) h₁) (rightCornerRight G (e' := e₁) h₂) X Z Y x y)
  | add t t' ht ht' => rw [map_add, map_add, ht, ht']

/-- Injectivity of ordinary multiplication implies injectivity of the weight coend multiplication. -/
theorem diagramCornerWeightRightCoendProduct_injective
    (d₁ : IsInternal G₁) (d₂ : IsInternal G₂)
    (hOrd : Function.Injective (CornerTensor.mult (k := k) h₂ h₁ h₀)) :
    letI := Graded.cornerGradedAlgebra G h₂ he₂
    letI := Graded.cornerGradedAlgebra G h₁ he₁
    letI := Graded.cornerGradedAlgebra G h₀ he₀
    letI := gradedAlgebraInternalGrading (OW h₂)
    letI := gradedAlgebraInternalGrading (OW h₁)
    letI := gradedAlgebraInternalGrading (OW h₀)
    letI := gradedAlgebraBigradedDGRing (OW h₂)
    letI := gradedAlgebraBigradedDGRing (OW h₁)
    letI := gradedAlgebraBigradedDGRing (OW h₀)
    ∀ (X : WeightCategory h₀.Cornerᵐᵒᵖ) (Z : WeightCategory h₂.Cornerᵐᵒᵖ),
      Function.Injective (diagramCornerWeightRightCoendProduct G h₂ h₁ he₂ he₁ h₀ he₀ X Z) := by
  let := Graded.cornerGradedAlgebra G h₂ he₂
  let := Graded.cornerGradedAlgebra G h₁ he₁
  let := Graded.cornerGradedAlgebra G h₀ he₀
  let := gradedAlgebraInternalGrading (OW h₂)
  let := gradedAlgebraInternalGrading (OW h₁)
  let := gradedAlgebraInternalGrading (OW h₀)
  let := gradedAlgebraBigradedDGRing (OW h₂)
  let := gradedAlgebraBigradedDGRing (OW h₁)
  let := gradedAlgebraBigradedDGRing (OW h₀)
  intro X Z
  let f := diagramCornerWeightRightToOrdinary G h₂ h₁ h₀ he₂ he₁ he₀ X Z
  let g := diagramCornerWeightRightCoendProduct G h₂ h₁ he₂ he₁ h₀ he₀ X Z
  let m := CornerTensor.mult (k := k) h₂ h₁ h₀
  have hf : Function.Injective f :=
    (diagramCornerWeightRightSlice_leftInverse G h₂ h₁ h₀ he₂ he₁ he₀ d₁ d₂ X Z).injective
  have hmul (t : CatTensorProduct ((D₁).right X) ((D₂).left Z)) :
      m (f t) = (g t).val.val := by
    induction t using CatTensorProduct.induction_on with
    | zero => simp only [map_zero]; rfl
    | tmul Y x y =>
      have ht : f (CatTensorProduct.tmul Y x y) = CornerTensor.tmul y.val.val x.val.val := by
        dsimp only [f, diagramCornerWeightRightToOrdinary]
        apply CatTensorProduct.lift_tmul
        intro S S' a v w
        rw [CatBimodule.right_ract]
        have hc : e₁ * a.val.unop.val * e₁ = a.val.unop.val := by
          rw [corner_mul_left h₁, corner_mul_right h₁]
        exact (CornerTensor.tmul_balance_of hc w.val.val v.val.val).symm
      have hg : (g (CatTensorProduct.tmul Y x y)).val.val = y.val.val * x.val.val :=
        diagramCornerWeightRightCoendProduct_tmul G h₂ h₁ he₂ he₁ h₀ he₀ X Y Z x y
      rw [ht, hg]
      change CornerTensor.mult (k := k) h₂ h₁ h₀ (CornerTensor.tmul y.val.val x.val.val) = _
      have hx := mem_cornerBimodule.mp x.val.property
      have hy := mem_cornerBimodule.mp y.val.property
      rw [CornerTensor.mult_tmul, hy.1, hy.2, mul_assoc, hx.2]
    | add t t' ht ht' =>
      rw [map_add, map_add, ht, ht', map_add]
      rfl
  intro t t' h
  apply hf
  apply hOrd
  exact (hmul t).trans ((congrArg (fun z => z.val.val) h).trans (hmul t').symm)

local notation "G₃" => diagramCornerWeight (e := e₂) (e' := e₀) G

/-- The pointwise right coend equivalence is natural in its source weight. -/
def diagramCornerWeightRightCoendNatIso :
    letI := Graded.cornerGradedAlgebra G h₂ he₂
    letI := Graded.cornerGradedAlgebra G h₁ he₁
    letI := Graded.cornerGradedAlgebra G h₀ he₀
    letI := gradedAlgebraInternalGrading (OW h₂)
    letI := gradedAlgebraInternalGrading (OW h₁)
    letI := gradedAlgebraInternalGrading (OW h₀)
    letI := gradedAlgebraBigradedDGRing (OW h₂)
    letI := gradedAlgebraBigradedDGRing (OW h₁)
    letI := gradedAlgebraBigradedDGRing (OW h₀)
    (∀ (X : WeightCategory h₀.Cornerᵐᵒᵖ) (Z : WeightCategory h₂.Cornerᵐᵒᵖ),
      Function.Bijective (diagramCornerWeightRightCoendProduct G h₂ h₁ he₂ he₁ h₀ he₀ X Z)) →
    (diagramCornerWeightRightFamily G h₂ h₁ he₂ he₁ ⋙ (D₁).tensorFunctor ≅
      diagramCornerWeightRightFamily G h₂ h₀ he₂ he₀) := by
  letI := Graded.cornerGradedAlgebra G h₂ he₂
  letI := Graded.cornerGradedAlgebra G h₁ he₁
  letI := Graded.cornerGradedAlgebra G h₀ he₀
  letI := gradedAlgebraInternalGrading (OW h₂)
  letI := gradedAlgebraInternalGrading (OW h₁)
  letI := gradedAlgebraInternalGrading (OW h₀)
  letI := gradedAlgebraBigradedDGRing (OW h₂)
  letI := gradedAlgebraBigradedDGRing (OW h₁)
  letI := gradedAlgebraBigradedDGRing (OW h₀)
  intro hbij
  exact diagramWeightCoendProductNatIso
    (A := h₀.Cornerᵐᵒᵖ) (B := h₁.Cornerᵐᵒᵖ) (C := h₂.Cornerᵐᵒᵖ)
    G₁ G₂ G₃ (rightCornerLeft G (e := e₁) h₀) (rightCornerRight G (e' := e₀) h₁)
    (rightCornerLeft G (e := e₂) h₁) (rightCornerRight G (e' := e₁) h₂)
    cornerRightProduct (cornerRightProduct_mem G)
    (fun b x y => Subtype.ext (by
      change y.val * (op b • x : cornerBimodule e₁ e₀).val =
        (b • y : cornerBimodule e₂ e₁).val * x.val
      rw [cornerBimodule.coe_smul_right h₁]
      exact (mul_assoc _ _ _).symm))
    (rightCornerLeft G (e := e₂) h₀) (rightCornerRight G (e' := e₀) h₂)
    (fun a x y => Subtype.ext (by
      change y.val * (a • x : cornerBimodule e₁ e₀).val =
        (a • cornerRightProduct x y : cornerBimodule e₂ e₀).val
      rw [cornerBimodule.coe_smul_right h₀, cornerBimodule.coe_smul_right h₀]
      exact (mul_assoc _ _ _).symm))
    (fun c x y => Subtype.ext (show (c.unop.val * y.val) * x.val =
      c.unop.val * (y.val * x.val) from mul_assoc _ _ _)) hbij

end OrdinaryComparison

end Categorification
