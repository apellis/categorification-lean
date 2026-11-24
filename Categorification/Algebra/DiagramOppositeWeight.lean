/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DiagramBigrading
import Categorification.Algebra.Graded.RightTwist
import DG.Category.Opposite
import DG.Category.Weight

/-!
# Opposite weight categories of graded diagram algebras

For Webster, arXiv:1309.3796v2, Lemma 6.11, this comparison identifies the
weight category of the opposite corner with the dg opposite weight category.
The map on objects negates internal weights and the map on morphisms takes
the opposite of the same homogeneous algebra element.
-/

noncomputable section

namespace Categorification

open CategoryTheory DG
open scoped DG.DegreeZero

universe u
variable {k : Type*} {A : Type u} [Field k] [Ring A] [Algebra k A]
    (G : ℤ → Submodule k A) [GradedAlgebra G]

/-- Negating weights identifies the dg opposite weight category with the
weight category of the graded opposite algebra. -/
def oppositeWeightFunctor :
    letI := gradedAlgebraInternalGrading G
    letI := gradedAlgebraBigradedDGRing G
    letI := gradedAlgebraInternalGrading (Graded.oppositeGrade G)
    letI := gradedAlgebraBigradedDGRing (Graded.oppositeGrade G)
    DGOpposite (WeightCategory A) ⥤ WeightCategory Aᵐᵒᵖ := by
  letI := gradedAlgebraInternalGrading G
  letI := gradedAlgebraBigradedDGRing G
  letI := gradedAlgebraInternalGrading (Graded.oppositeGrade G)
  letI := gradedAlgebraBigradedDGRing (Graded.oppositeGrade G)
  have weightHom_degreeZero {X Y : WeightCategory A} (f : X ⟶ Y) :
      f ∈ grading (0 : ℤ) :=
    WeightCategory.mem_grading_iff.mpr (mem_degreeZeroGrading_zero _ f.val)
  exact {
    obj X := ⟨-X.unop.as⟩
    map {X Y} f := ⟨MulOpposite.op (DGOpposite.homUnop f).val, by
      change (DGOpposite.homUnop f).val ∈ G (-Y.unop.as - -X.unop.as)
      rw [show -Y.unop.as - -X.unop.as = X.unop.as - Y.unop.as by omega]
      exact (DGOpposite.homUnop f).property⟩
    map_id _ := rfl
    map_comp {X Y Z} f g := by
      apply WeightCategory.hom_ext
      have hf : f ∈ grading (0 : ℤ) := weightHom_degreeZero (DGOpposite.homUnop f)
      have hg : g ∈ grading (0 : ℤ) := weightHom_degreeZero (DGOpposite.homUnop g)
      rw [DGOpposite.homUnop_comp_of_mem hf hg, zero_mul, koszulSign_zero, one_smul]
      rfl
  }

/-- The opposite weight functor is fully faithful. -/
def oppositeWeightFullyFaithful :
    letI := gradedAlgebraInternalGrading G
    letI := gradedAlgebraBigradedDGRing G
    letI := gradedAlgebraInternalGrading (Graded.oppositeGrade G)
    letI := gradedAlgebraBigradedDGRing (Graded.oppositeGrade G)
    (oppositeWeightFunctor G).FullyFaithful := by
  letI := gradedAlgebraInternalGrading G
  letI := gradedAlgebraBigradedDGRing G
  letI := gradedAlgebraInternalGrading (Graded.oppositeGrade G)
  letI := gradedAlgebraBigradedDGRing (Graded.oppositeGrade G)
  exact {
    preimage {X Y} f := DGOpposite.homOp ⟨f.val.unop, by
      change f.val.unop ∈ G (X.unop.as - Y.unop.as)
      have hf : f.val.unop ∈ G (-Y.unop.as - -X.unop.as) := f.property
      rw [show X.unop.as - Y.unop.as = -Y.unop.as - -X.unop.as by omega]
      exact hf⟩
    map_preimage f := WeightCategory.hom_ext rfl
    preimage_map f := rfl
  }

/-- The opposite weight functor reaches every weight. -/
theorem oppositeWeightFunctor_surjective :
    letI := gradedAlgebraInternalGrading G
    letI := gradedAlgebraBigradedDGRing G
    letI := gradedAlgebraInternalGrading (Graded.oppositeGrade G)
    letI := gradedAlgebraBigradedDGRing (Graded.oppositeGrade G)
    Function.Surjective (oppositeWeightFunctor G).obj := by
  intro Y
  exact ⟨DGOpposite.op ⟨-Y.as⟩, WeightCategory.ext (neg_neg _)⟩

/-- Negating weights is injective on objects as well. -/
theorem oppositeWeightFunctor_bijective :
    letI := gradedAlgebraInternalGrading G
    letI := gradedAlgebraBigradedDGRing G
    letI := gradedAlgebraInternalGrading (Graded.oppositeGrade G)
    letI := gradedAlgebraBigradedDGRing (Graded.oppositeGrade G)
    Function.Bijective (oppositeWeightFunctor G).obj := by
  refine ⟨?_, oppositeWeightFunctor_surjective G⟩
  intro X Y h
  cases X with
  | op X =>
    cases Y with
    | op Y =>
      have he := congrArg WeightCategory.as h
      change -X.as = -Y.as at he
      exact congrArg DGOpposite.op (WeightCategory.ext (neg_injective he))

/-- The opposite weight comparison is additive. -/
theorem oppositeWeightFunctor_additive :
    letI := gradedAlgebraInternalGrading G
    letI := gradedAlgebraBigradedDGRing G
    letI := gradedAlgebraInternalGrading (Graded.oppositeGrade G)
    letI := gradedAlgebraBigradedDGRing (Graded.oppositeGrade G)
    (oppositeWeightFunctor G).Additive := by
  let _ := gradedAlgebraInternalGrading G
  let _ := gradedAlgebraBigradedDGRing G
  let _ := gradedAlgebraInternalGrading (Graded.oppositeGrade G)
  let _ := gradedAlgebraBigradedDGRing (Graded.oppositeGrade G)
  exact ⟨by intros; exact WeightCategory.hom_ext rfl⟩

/-- The opposite weight comparison preserves the hom complexes. -/
theorem oppositeWeightFunctor_isDGFunctor :
    letI := gradedAlgebraInternalGrading G
    letI := gradedAlgebraBigradedDGRing G
    letI := gradedAlgebraInternalGrading (Graded.oppositeGrade G)
    letI := gradedAlgebraBigradedDGRing (Graded.oppositeGrade G)
    letI := oppositeWeightFunctor_additive G
    (oppositeWeightFunctor G).IsDGFunctor := by
  let _ := gradedAlgebraInternalGrading G
  let _ := gradedAlgebraBigradedDGRing G
  let _ := gradedAlgebraInternalGrading (Graded.oppositeGrade G)
  let _ := gradedAlgebraBigradedDGRing (Graded.oppositeGrade G)
  let _ := oppositeWeightFunctor_additive G
  refine ⟨?_, ?_⟩
  · intro X Y n f hf
    have h : (DGOpposite.homUnop f).val ∈ grading n :=
      WeightCategory.mem_grading_iff.mp (DGOpposite.mem_grading_iff.mp hf)
    apply WeightCategory.mem_grading_iff.mpr
    change MulOpposite.op (DGOpposite.homUnop f).val ∈ grading n
    rcases DegreeZero.mem_grading_iff.mp h with rfl | h
    · exact mem_degreeZeroGrading_zero _ _
    · rw [h]
      exact zero_mem _
  · intros
    exact WeightCategory.hom_ext rfl

end Categorification
