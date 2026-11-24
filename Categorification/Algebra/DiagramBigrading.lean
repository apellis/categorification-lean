/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DerivedTensor
import DG.Bigraded.Basic

/-!
# Diagram gradings as internal dg gradings

A ring in cohomological degree zero can retain a separate internal
diagram grading. This is used for the derived functors of Webster,
arXiv:1309.3796v2, Definition 7.4.
-/

noncomputable section

namespace Categorification

open CategoryTheory DG DirectSum
open scoped DG.DegreeZero

variable {R : Type*} [Ring R] (G : ℤ → AddSubgroup R) [DirectSum.Decomposition G]

/-- A graded algebra regarded as a dg algebra concentrated in cohomological degree zero. -/
@[instance_reducible]
def gradedRingInternalGrading : InternalGrading R where
  wgrading := G
  isHomogeneous_grading' := by
    intro n j x hx
    rcases (InDegreeZero.ring_mem_grading_iff (R := R)).mp hx with hn | hx
    · exact (InDegreeZero.ring_mem_grading_iff (R := R)).mpr (Or.inl hn)
    · rw [hx, DirectSum.decompose_zero, DirectSum.zero_apply, ZeroMemClass.coe_zero]
      exact zero_mem _
  d_mem_wgrading' := fun {_ _} _ => by rw [InDegreeZero.ring_d_apply]; exact zero_mem _

/-- The internal multiplication agrees with the given ring grading. -/
theorem gradedRingBigradedDGRing [SetLike.GradedMonoid G] :
    letI := gradedRingInternalGrading G
    BigradedDGRing R :=
  letI := gradedRingInternalGrading G
  { one_mem := SetLike.GradedOne.one_mem (A := G)
    mul_mem := fun i j x y ha hb => by
      change x * y ∈ G (i + j)
      exact SetLike.GradedMul.mul_mem (A := G) ha hb }

end Categorification

namespace Categorification

open DG DirectSum
open scoped DG.DegreeZero

variable {k A : Type*} [CommRing k] [Ring A] [Algebra k A]
  (G : ℤ → Submodule k A) [GradedAlgebra G]

local notation "wG" => fun j => Submodule.toAddSubgroup (G j)

@[instance_reducible]
private def additiveDecomposition : Decomposition wG where
  decompose' := Decomposition.decompose' (ℳ := G)
  left_inv := Decomposition.left_inv (ℳ := G)
  right_inv := Decomposition.right_inv (ℳ := G)

/-- Regard the algebra grading as the internal grading of a degree-zero dg algebra. -/
@[instance_reducible]
def gradedAlgebraInternalGrading : InternalGrading A :=
  letI := additiveDecomposition G
  gradedRingInternalGrading wG

theorem gradedAlgebraBigradedDGRing :
    letI := gradedAlgebraInternalGrading G
    BigradedDGRing A := by
  let := additiveDecomposition G
  let : SetLike.GradedMonoid wG :=
    { one_mem := show (1 : A) ∈ G 0 from SetLike.GradedOne.one_mem
      mul_mem := fun i j a b ha hb =>
        show a*b ∈ G (i+j) from SetLike.GradedMul.mul_mem (A := G) ha hb }
  exact gradedRingBigradedDGRing wG

end Categorification

namespace Categorification

open DG DirectSum
open scoped DG.DegreeZero

variable (k : Type*) [CommRing k]

/-- The field has internal grading concentrated in degree zero. -/
@[instance_reducible]
def scalarInternalGrading : InternalGrading k :=
  gradedRingInternalGrading (grading (M := k))

theorem scalarBigradedDGRing :
    letI := scalarInternalGrading k
    BigradedDGRing k :=
  gradedRingBigradedDGRing (grading (M := k))

end Categorification
