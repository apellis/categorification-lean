/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DiagramWeightEquivalence
import Categorification.WeightedKLR.RedStrands.BraidingForgetDerived

/-!
# The graded braiding functors are equivalences

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
Theorem 6.15, for the graded braiding functors of Definition 6.6: every graded braiding functor
`𝔅(κ', κ)` between red orders, the derived right tensor with the braided Stendhal bimodule
retaining its auxiliary grading, is an equivalence of derived categories of dg modules over the
weight categories (`isEquivalence_auxiliaryGradedBraidingFunctor`).

The ungraded functors are equivalences (`isEquivalence_braidingFunctor`), and a graded derived
corner tensor is an equivalence when the ungraded one is
(`Categorification.isEquivalence_diagramCornerWeightDerivedRightTensor`, from
`Categorification.isEquivalence_diagramWeightDerivedTensor`). Route hypotheses: those of the
ungraded theorem, namely the injectivity hypothesis of Lemma 6.8 inside
`RowFigureFiveHypotheses`, at the Khovanov–Lauda scalars.
-/

noncomputable section

namespace Categorification

open CategoryTheory DG MulOpposite Categorification.Graded
open scoped DG.DegreeZero

universe u w

/-- An equivalence between preadditive categories with binary products preserves compact
objects. -/
theorem isCompact_obj_of_isEquivalence {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] [Preadditive 𝒞]
    [Preadditive 𝒟] (F : 𝒞 ⥤ 𝒟) (hA : F.Additive) (hE : F.IsEquivalence) {X : 𝒞}
    (hX : IsCompact.{w} X) : IsCompact.{w} (F.obj X) :=
  have : F.asEquivalence.functor.Additive := hA
  hX.map_of_equivalence F.asEquivalence

section Corner

variable {k : Type*} {A : Type u} [Field k] [Ring A] [Algebra k A]
  (G : ℤ → Submodule k A) [GradedAlgebra G]
  {e e' : A} (he : IsIdempotentElem e) (he' : IsIdempotentElem e')
  (he0 : e ∈ G 0) (he'0 : e' ∈ G 0)

local notation "L" => Graded.cornerGrading G he
local notation "R" => Graded.cornerGrading G he'

attribute [local instance] cornerBimodule.instModuleLeft cornerBimodule.instModuleRight

private theorem cornerWeight_left_mem' {i j : ℤ} {a : he'.Cornerᵐᵒᵖ}
    {x : cornerBimodule e e'} (ha : a.unop.val ∈ G i) (hx : x ∈ diagramCornerWeight G j) :
    a • x ∈ diagramCornerWeight G (i + j) := by
  have hm : x.val * a.unop.val ∈ G (j + i) := SetLike.GradedMul.mul_mem (A := G) hx ha
  rw [add_comm j i] at hm
  change (a • x : cornerBimodule e e').val ∈ G (i + j)
  rw [cornerBimodule.coe_smul_right he']
  exact hm

private theorem cornerWeight_right_mem' {i j : ℤ} {b : he.Cornerᵐᵒᵖ}
    {x : cornerBimodule e e'} (hb : b.unop.val ∈ G i) (hx : x ∈ diagramCornerWeight G j) :
    op b • x ∈ diagramCornerWeight G (j + i) := by
  have hm : b.unop.val * x.val ∈ G (i + j) := SetLike.GradedMul.mul_mem (A := G) hb hx
  rw [add_comm i j] at hm
  exact hm

/-- **A graded derived corner tensor is an equivalence when the ungraded one is**: if
`- ⊗ᴸ_{eAe} eAe'` is an equivalence, so is its graded form on dg modules over the weight
categories. -/
theorem isEquivalence_diagramCornerWeightDerivedRightTensor :
    letI := Graded.cornerGradedAlgebra G he he0
    letI := Graded.cornerGradedAlgebra G he' he'0
    letI := gradedAlgebraInternalGrading (oppositeGrade L)
    letI := gradedAlgebraInternalGrading (oppositeGrade R)
    letI := gradedAlgebraBigradedDGRing (oppositeGrade L)
    letI := gradedAlgebraBigradedDGRing (oppositeGrade R)
    [CatModule.HasDerivedCategory.{u,u} (WeightCategory he.Cornerᵐᵒᵖ)] →
    [CatModule.HasDerivedCategory.{u,u} (WeightCategory he'.Cornerᵐᵒᵖ)] →
    [DG.HasDerivedCategory.{w,u} he.Cornerᵐᵒᵖ] → [DG.HasDerivedCategory.{w,u} he'.Cornerᵐᵒᵖ] →
    (derivedRightTensor.{w} he.Corner he'.Corner (cornerBimodule e e')).IsEquivalence →
    (diagramCornerWeightDerivedRightTensor G he he' he0 he'0).IsEquivalence := by
  let := Graded.cornerGradedAlgebra G he he0
  let := Graded.cornerGradedAlgebra G he' he'0
  let := gradedAlgebraInternalGrading (oppositeGrade L)
  let := gradedAlgebraInternalGrading (oppositeGrade R)
  let := gradedAlgebraBigradedDGRing (oppositeGrade L)
  let := gradedAlgebraBigradedDGRing (oppositeGrade R)
  let := (diagramCornerWeight_isInternal G he0 he'0).chooseDecomposition
  intro _ _ _ _ h
  have : (derivedTensor.{w} he'.Cornerᵐᵒᵖ he.Cornerᵐᵒᵖ (cornerBimodule e e')).IsEquivalence := h
  exact isEquivalence_diagramWeightDerivedTensor (A := he'.Cornerᵐᵒᵖ) (B := he.Cornerᵐᵒᵖ)
    (diagramCornerWeight G) (cornerWeight_left_mem' G he') (cornerWeight_right_mem' G he)

/-- The graded derived corner tensor is additive. -/
theorem diagramCornerWeightDerivedRightTensor_additive :
    letI := Graded.cornerGradedAlgebra G he he0
    letI := Graded.cornerGradedAlgebra G he' he'0
    letI := gradedAlgebraInternalGrading (oppositeGrade L)
    letI := gradedAlgebraInternalGrading (oppositeGrade R)
    letI := gradedAlgebraBigradedDGRing (oppositeGrade L)
    letI := gradedAlgebraBigradedDGRing (oppositeGrade R)
    [CatModule.HasDerivedCategory.{u,u} (WeightCategory he.Cornerᵐᵒᵖ)] →
    [CatModule.HasDerivedCategory.{u,u} (WeightCategory he'.Cornerᵐᵒᵖ)] →
    (diagramCornerWeightDerivedRightTensor G he he' he0 he'0).Additive := by
  let := Graded.cornerGradedAlgebra G he he0
  let := Graded.cornerGradedAlgebra G he' he'0
  let := gradedAlgebraInternalGrading (oppositeGrade L)
  let := gradedAlgebraInternalGrading (oppositeGrade R)
  let := gradedAlgebraBigradedDGRing (oppositeGrade L)
  let := gradedAlgebraBigradedDGRing (oppositeGrade R)
  intro _ _
  exact diagramWeightDerivedTensor_additive (A := he'.Cornerᵐᵒᵖ) (B := he.Cornerᵐᵒᵖ)
    (diagramCornerWeight G) (cornerWeight_left_mem' G he') (cornerWeight_right_mem' G he)

end Corner

end Categorification

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR DG CategoryTheory
open scoped DG.DegreeZero

universe w

variable {I : Type u} {k : Type u} [DecidableEq I] [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
  (G : KLR.GradingDatum (stendhalQ Q Λ))

local notation "V" => violAuxiliaryGrade (ν := ν) G
local notation "hE" => isIdempotentElem_violMk_redProj k Q Λ ν
local notation "S" => fun κ => Graded.oppositeGrade (Graded.cornerGrading V (hE κ))

/-- The graded braiding functors are additive. -/
theorem auxiliaryGradedBraidingFunctor_additive (κ' κ : List (Fin ℓ)) :
    letI := Graded.cornerGradedAlgebra V (hE κ')
      (redProj_mem_violAuxiliaryGrade G κ')
    letI := Graded.cornerGradedAlgebra V (hE κ)
      (redProj_mem_violAuxiliaryGrade G κ)
    letI := gradedAlgebraInternalGrading (S κ')
    letI := gradedAlgebraInternalGrading (S κ)
    letI := gradedAlgebraBigradedDGRing (S κ')
    letI := gradedAlgebraBigradedDGRing (S κ)
    [CatModule.HasDerivedCategory.{u,u} (WeightCategory (hE κ').Cornerᵐᵒᵖ)] →
    [CatModule.HasDerivedCategory.{u,u} (WeightCategory (hE κ).Cornerᵐᵒᵖ)] →
    Functor.Additive
      (C := CatModule.DerivedCategory.{u,u} (WeightCategory (hE κ').Cornerᵐᵒᵖ))
      (D := CatModule.DerivedCategory.{u,u} (WeightCategory (hE κ).Cornerᵐᵒᵖ))
      (auxiliaryGradedBraidingFunctor G κ' κ) := by
  let := Graded.cornerGradedAlgebra V (hE κ') (redProj_mem_violAuxiliaryGrade G κ')
  let := Graded.cornerGradedAlgebra V (hE κ) (redProj_mem_violAuxiliaryGrade G κ)
  let := gradedAlgebraInternalGrading (S κ')
  let := gradedAlgebraInternalGrading (S κ)
  let := gradedAlgebraBigradedDGRing (S κ')
  let := gradedAlgebraBigradedDGRing (S κ)
  intro _ _
  exact diagramCornerWeightDerivedRightTensor_additive V (hE κ') (hE κ)
    (redProj_mem_violAuxiliaryGrade G κ') (redProj_mem_violAuxiliaryGrade G κ)

/-- **A graded braiding functor is an equivalence when the ungraded one is** (Webster,
arXiv:1309.3796v3, Definition 6.6 and Theorem 6.15): if `𝔅(κ', κ) = - ⊗ᴸ B(κ', κ)` is an
equivalence, so is the graded `𝔅(κ', κ)` in the auxiliary grading. -/
theorem isEquivalence_auxiliaryGradedBraidingFunctor_of_isEquivalence (κ' κ : List (Fin ℓ)) :
    letI := Graded.cornerGradedAlgebra V (hE κ')
      (redProj_mem_violAuxiliaryGrade G κ')
    letI := Graded.cornerGradedAlgebra V (hE κ)
      (redProj_mem_violAuxiliaryGrade G κ)
    letI := gradedAlgebraInternalGrading (S κ')
    letI := gradedAlgebraInternalGrading (S κ)
    letI := gradedAlgebraBigradedDGRing (S κ')
    letI := gradedAlgebraBigradedDGRing (S κ)
    [CatModule.HasDerivedCategory.{u,u} (WeightCategory (hE κ').Cornerᵐᵒᵖ)] →
    [CatModule.HasDerivedCategory.{u,u} (WeightCategory (hE κ).Cornerᵐᵒᵖ)] →
    [DG.HasDerivedCategory.{w} (hE κ').Cornerᵐᵒᵖ] → [DG.HasDerivedCategory.{w} (hE κ).Cornerᵐᵒᵖ] →
    (braidingFunctor.{w} k Q Λ ν κ' κ).IsEquivalence →
    Functor.IsEquivalence
      (C := CatModule.DerivedCategory.{u,u} (WeightCategory (hE κ').Cornerᵐᵒᵖ))
      (D := CatModule.DerivedCategory.{u,u} (WeightCategory (hE κ).Cornerᵐᵒᵖ))
      (auxiliaryGradedBraidingFunctor G κ' κ) := by
  let := Graded.cornerGradedAlgebra V (hE κ') (redProj_mem_violAuxiliaryGrade G κ')
  let := Graded.cornerGradedAlgebra V (hE κ) (redProj_mem_violAuxiliaryGrade G κ)
  let := gradedAlgebraInternalGrading (S κ')
  let := gradedAlgebraInternalGrading (S κ)
  let := gradedAlgebraBigradedDGRing (S κ')
  let := gradedAlgebraBigradedDGRing (S κ)
  intro _ _ _ _ h
  exact isEquivalence_diagramCornerWeightDerivedRightTensor V (hE κ') (hE κ)
    (redProj_mem_violAuxiliaryGrade G κ') (redProj_mem_violAuxiliaryGrade G κ) h

end Categorification.Stendhal.BraidedStendhalAlgebra
