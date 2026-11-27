/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DiagramWeightForgetDerived
import Categorification.WeightedKLR.RedStrands.BraidingAuxiliaryDerived
import Categorification.WeightedKLR.RedStrands.BraidingWeightDecomposition

/-!
# Forgetting the weights of the graded braiding functors

For a graded algebra and two degree-zero idempotents `e`, `e'`, the derived right tensor with
the rectangular corner `e A e'` in its internal grading
(`Categorification.diagramCornerWeightDerivedRightTensor`) becomes the ungraded derived right
tensor `- ⊗ᴸ_{eAe} eAe'` after forgetting the weights
(`Categorification.diagramCornerWeightForgetDerivedIso`).

For the braided Stendhal algebras this compares the graded braiding functors of B. Webster,
*Knot invariants and higher representation theory*, arXiv:1309.3796v3, Definition 6.6, with
the ungraded ones: forgetting the weights after the graded functor `𝔅_w` (in the auxiliary
grading) is the ungraded `𝔅_w` after forgetting the weights
(`Categorification.Stendhal.BraidedStendhalAlgebra.auxiliaryGradedBraidingFunctorForgetIso`).
-/

noncomputable section

namespace Categorification

open CategoryTheory DG DirectSum MulOpposite Categorification.Graded
open scoped DG.DegreeZero

universe u v w

section Corner

variable {k : Type*} {A : Type u} [Field k] [Ring A] [Algebra k A]
  (G : ℤ → Submodule k A) [GradedAlgebra G]
  {e e' : A} (he : IsIdempotentElem e) (he' : IsIdempotentElem e')
  (he0 : e ∈ G 0) (he'0 : e' ∈ G 0)

local notation "L" => Graded.cornerGrading G he
local notation "R" => Graded.cornerGrading G he'

attribute [local instance] cornerBimodule.instModuleLeft cornerBimodule.instModuleRight

private theorem cornerWeight_left_mem {i j : ℤ} {a : he'.Cornerᵐᵒᵖ}
    {x : cornerBimodule e e'} (ha : a.unop.val ∈ G i) (hx : x ∈ diagramCornerWeight G j) :
    a • x ∈ diagramCornerWeight G (i + j) := by
  have hm : x.val * a.unop.val ∈ G (j + i) := SetLike.GradedMul.mul_mem (A := G) hx ha
  rw [add_comm j i] at hm
  change (a • x : cornerBimodule e e').val ∈ G (i + j)
  rw [cornerBimodule.coe_smul_right he']
  exact hm

private theorem cornerWeight_right_mem {i j : ℤ} {b : he.Cornerᵐᵒᵖ}
    {x : cornerBimodule e e'} (hb : b.unop.val ∈ G i) (hx : x ∈ diagramCornerWeight G j) :
    op b • x ∈ diagramCornerWeight G (j + i) := by
  have hm : b.unop.val * x.val ∈ G (i + j) := SetLike.GradedMul.mul_mem (A := G) hb hx
  rw [add_comm i j] at hm
  exact hm

/-- **Forgetting the weights of a graded corner tensor**: the derived right tensor with the
rectangular corner in its internal grading, followed by forgetting the weights, is the
ungraded derived right tensor with the corner after forgetting the weights. -/
def diagramCornerWeightForgetDerivedIso :
    letI := Graded.cornerGradedAlgebra G he he0
    letI := Graded.cornerGradedAlgebra G he' he'0
    letI := gradedAlgebraInternalGrading (oppositeGrade L)
    letI := gradedAlgebraInternalGrading (oppositeGrade R)
    letI := gradedAlgebraBigradedDGRing (oppositeGrade L)
    letI := gradedAlgebraBigradedDGRing (oppositeGrade R)
    [CatModule.HasDerivedCategory.{v,u} (WeightCategory he.Cornerᵐᵒᵖ)] →
    [CatModule.HasDerivedCategory.{v,u} (WeightCategory he'.Cornerᵐᵒᵖ)] →
    [DG.HasDerivedCategory.{w,u} he.Cornerᵐᵒᵖ] → [DG.HasDerivedCategory.{w,u} he'.Cornerᵐᵒᵖ] →
    (diagramCornerWeightDerivedRightTensor G he he' he0 he'0 ⋙
        CatModule.weightForgetDerived he'.Cornerᵐᵒᵖ ≅
      CatModule.weightForgetDerived he.Cornerᵐᵒᵖ ⋙
        derivedRightTensor.{w} he.Corner he'.Corner (cornerBimodule e e')) := by
  letI := Graded.cornerGradedAlgebra G he he0
  letI := Graded.cornerGradedAlgebra G he' he'0
  letI := gradedAlgebraInternalGrading (oppositeGrade L)
  letI := gradedAlgebraInternalGrading (oppositeGrade R)
  letI := gradedAlgebraBigradedDGRing (oppositeGrade L)
  letI := gradedAlgebraBigradedDGRing (oppositeGrade R)
  letI := (diagramCornerWeight_isInternal G he0 he'0).chooseDecomposition
  intro _ _ _ _
  exact diagramWeightForgetDerivedIso (A := he'.Cornerᵐᵒᵖ) (B := he.Cornerᵐᵒᵖ)
    (diagramCornerWeight G) (cornerWeight_left_mem G he') (cornerWeight_right_mem G he)

end Corner

end Categorification

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR DG CategoryTheory
open scoped DG.DegreeZero

universe u v w

variable {I : Type*} {k : Type u} [DecidableEq I] [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
  (G : KLR.GradingDatum (stendhalQ Q Λ))

local notation "V" => violAuxiliaryGrade (ν := ν) G
local notation "hE" => isIdempotentElem_violMk_redProj k Q Λ ν
local notation "S" => fun κ => Graded.oppositeGrade (Graded.cornerGrading V (hE κ))

/-- **The graded braiding functors forget to the ungraded ones** (Webster, arXiv:1309.3796v3,
Definition 6.6): forgetting the weights after the graded `𝔅_w` (auxiliary grading) is the
ungraded `𝔅_w = - ⊗ᴸ B(κ', κ)` after forgetting the weights. -/
def auxiliaryGradedBraidingFunctorForgetIso (κ' κ : List (Fin ℓ)) :
    letI := Graded.cornerGradedAlgebra V (hE κ')
      (redProj_mem_violAuxiliaryGrade G κ')
    letI := Graded.cornerGradedAlgebra V (hE κ)
      (redProj_mem_violAuxiliaryGrade G κ)
    letI := gradedAlgebraInternalGrading (S κ')
    letI := gradedAlgebraInternalGrading (S κ)
    letI := gradedAlgebraBigradedDGRing (S κ')
    letI := gradedAlgebraBigradedDGRing (S κ)
    [CatModule.HasDerivedCategory.{v,_} (WeightCategory (hE κ').Cornerᵐᵒᵖ)] →
    [CatModule.HasDerivedCategory.{v,_} (WeightCategory (hE κ).Cornerᵐᵒᵖ)] →
    [DG.HasDerivedCategory.{w} (hE κ').Cornerᵐᵒᵖ] → [DG.HasDerivedCategory.{w} (hE κ).Cornerᵐᵒᵖ] →
    (auxiliaryGradedBraidingFunctor G κ' κ ⋙ CatModule.weightForgetDerived (hE κ).Cornerᵐᵒᵖ ≅
      CatModule.weightForgetDerived (hE κ').Cornerᵐᵒᵖ ⋙ braidingFunctor.{w} k Q Λ ν κ' κ) := by
  letI := Graded.cornerGradedAlgebra V (hE κ')
    (redProj_mem_violAuxiliaryGrade G κ')
  letI := Graded.cornerGradedAlgebra V (hE κ)
    (redProj_mem_violAuxiliaryGrade G κ)
  letI := gradedAlgebraInternalGrading (S κ')
  letI := gradedAlgebraInternalGrading (S κ)
  letI := gradedAlgebraBigradedDGRing (S κ')
  letI := gradedAlgebraBigradedDGRing (S κ)
  intro _ _ _ _
  exact diagramCornerWeightForgetDerivedIso V (hE κ') (hE κ)
    (redProj_mem_violAuxiliaryGrade G κ') (redProj_mem_violAuxiliaryGrade G κ)

end Categorification.Stendhal.BraidedStendhalAlgebra
