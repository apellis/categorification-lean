/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.GradedMiddleScalarRepresentables
import DG.Category.Derived.TensorInduction

/-!
# The clockwise fundamental circle with the ST quantum trace

In Webster, arXiv:1309.3796v2, Proposition 7.13 gives the quantum trace as
derived tensor with the left simple. The orientation rules of §8.1 assign
the coevaluation to a clockwise cup and the quantum trace to a clockwise cap.
For the self-dual fundamental weight of type A₁ the left coefficient is the
scalar character at the middle cut. Its diagram bimodule and its derived
tensor give the following computation on the scalar weight category.
-/

noncomputable section
namespace Categorification.Stendhal.FundamentalCorner
open CategoryTheory CategoryTheory.Limits DG CatModule MulOpposite Coevaluation
open scoped DG.DegreeZero
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
local notation "T" => TensorProductAlgebra ℚ Q wt ({()} : Multiset Unit)
local notation "G" => Graded.oppositeGrade (tensorProductGrade grading ({()} : Multiset Unit))
local instance : InternalGrading Tᵐᵒᵖ := gradedAlgebraInternalGrading G
local instance : BigradedDGRing Tᵐᵒᵖ := gradedAlgebraBigradedDGRing G
local instance : InternalGrading ℚ := scalarInternalGrading ℚ
local instance : BigradedDGRing ℚ := scalarBigradedDGRing ℚ
local notation "Fχ" => WeightCategory.mapFunctor gradedMiddleCharacter gradedMiddleCharacter_mem_weight
local notation "line" j:arg => CatModule.DerivedCategory.Q.obj (representable (⟨j⟩ : WeightCategory ℚ))

/-- The bimodule of the left middle coefficient used by the ST quantum trace. -/
def fundamentalTraceCoefficient : CatBimodule (WeightCategory ℚ) (WeightCategory Tᵐᵒᵖ) :=
  CatBimodule.ofFunctor Fχ

/-- Each equal-weight fiber is a copy of the scalars. -/
def fundamentalTraceCoefficient_line (j : ℤ) :
    fundamentalTraceCoefficient.obj ⟨j⟩ ⟨j⟩ ≃+ ℚ where
  toFun x := x.val
  invFun x := ⟨x, (InDegreeZero.ring_mem_grading_iff (R := ℚ)).mpr (Or.inl (sub_self j))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- Every fiber away from the diagonal of the two weights is zero. -/
theorem fundamentalTraceCoefficient_off_diagonal (i j : ℤ) (h : j ≠ i) :
    Subsingleton (fundamentalTraceCoefficient.obj ⟨j⟩ ⟨i⟩) := by
  refine ⟨fun x y => Subtype.ext ?_⟩
  have hz (z : fundamentalTraceCoefficient.obj ⟨j⟩ ⟨i⟩) : z.val = 0 :=
    ((InDegreeZero.ring_mem_grading_iff (R := ℚ)).mp z.property).resolve_left (sub_ne_zero.mpr h)
  exact (hz x).trans (hz y).symm

/-- The diagram action on the trace coefficient is the middle-cut character. -/
theorem fundamentalTraceCoefficient_action {i j : WeightCategory Tᵐᵒᵖ} {k : WeightCategory ℚ}
    (a : i ⟶ j) (z : fundamentalTraceCoefficient.obj k j) :
    ((fundamentalTraceCoefficient.ract a) z).val = z.val * middleCharacter a.val.unop := rfl

universe v
variable [CatModule.HasDerivedCategory.{v,0} (WeightCategory ℚ)]
  [CatModule.HasDerivedCategory.{v,0} (WeightCategory Tᵐᵒᵖ)]

/-- The clockwise cap of Proposition 7.13, taken as a derived tensor product. -/
def gradedFundamentalQuantumTrace :=
  CatModule.DerivedCategory.derivedTensor fundamentalTraceCoefficient (CatBimodule.isKProjective_ofFunctor_left Fχ)

/-- Tensoring with the left character agrees with extension along its weight functor. -/
def gradedFundamentalQuantumTraceIso : gradedFundamentalQuantumTrace ≅ gradedMiddleCap :=
  CatModule.DerivedCategory.derivedTensorOfFunctorIso Fχ

/-- A clockwise fundamental circle on the scalar generator has exactly two
scalar summands, in internal/cohomological bidegrees (−1,1) and (1,−1). -/
def gradedFundamentalClockwiseCircleIso :
    (gradedMiddleCup ⋙ gradedFundamentalQuantumTrace).obj (line 0) ≅
      (line (-1))⟦(-1 : ℤ)⟧ ⊞ (line 1)⟦(1 : ℤ)⟧ :=
  gradedFundamentalQuantumTraceIso.app _ ≪≫ gradedMiddleCupCap_fieldIso

/-- The clockwise calculation on any shifted scalar representable. -/
def gradedFundamentalClockwiseCircle_shiftedIso (j n : ℤ) :
    (gradedMiddleCup ⋙ gradedFundamentalQuantumTrace).obj ((line j)⟦n⟧) ≅
      (line (j-1))⟦n-1⟧ ⊞ (line (j+1))⟦n+1⟧ :=
  gradedFundamentalQuantumTraceIso.app _ ≪≫ gradedMiddleCupCap_shiftedScalarIso j n

end Categorification.Stendhal.FundamentalCorner
