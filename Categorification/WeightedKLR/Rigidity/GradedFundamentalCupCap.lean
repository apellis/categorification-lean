/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DiagramBigrading
import Categorification.Algebra.Graded.RightTwist
import Categorification.WeightedKLR.Rigidity.GradedCharacterCupCap
import Categorification.WeightedKLR.Rigidity.FundamentalCoevaluation
import Categorification.WeightedKLR.RedStrands.FundamentalCornerEuler

/-!
# Internally graded terminal-character cup and cap

For two fundamental type A₁ weights over the rationals, the terminal
character gives a graded cup and cap model. The cup has diagram shift
one and cohomological shift minus one. In Webster, arXiv:1309.3796v2,
Proposition 7.5 uses the middle loading `κ = (0, 1)`.
-/

noncomputable section

namespace Categorification.Stendhal.FundamentalCorner

open CategoryTheory DG MulOpposite Coevaluation
open scoped DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

local notation "T" => TensorProductAlgebra ℚ Q wt ({()} : Multiset Unit)
local notation "G" => Graded.oppositeGrade (tensorProductGrade grading ({()} : Multiset Unit))

private theorem terminalCharacter_homogeneous {j : ℤ} (hj : j ≠ 0) {a : T}
    (ha : a ∈ tensorProductGrade grading ({()} : Multiset Unit) j) :
    terminalCharacter a = 0 := by
  unfold terminalCharacter
  exact FirstWeight.boundaryCharacter_eq_zero_of_ne_grade Q wt grading
    (by intro r; simp [wt]) terminal terminal_ordered (by unfold IsViolated; decide +kernel) hj ha

local instance : InternalGrading Tᵐᵒᵖ := gradedAlgebraInternalGrading G
local instance : BigradedDGRing Tᵐᵒᵖ := gradedAlgebraBigradedDGRing G
local instance : InternalGrading ℚ := scalarInternalGrading ℚ
local instance : BigradedDGRing ℚ := scalarBigradedDGRing ℚ

/-- The terminal coefficient character as a map of degree-zero dg rings. -/
def gradedTerminalCharacter : Tᵐᵒᵖ →ᵈᵍ+* ℚ :=
  oppositeScalarCharacter terminalCharacter.toRingHom

@[simp] theorem gradedTerminalCharacter_op (a : T) :
    gradedTerminalCharacter (op a) = terminalCharacter a := rfl

/-- The fundamental character respects the internal diagram grading. -/
theorem gradedTerminalCharacter_mem_weight {j : ℤ} {a : Tᵐᵒᵖ}
    (ha : a ∈ wgrading j) : gradedTerminalCharacter a ∈ wgrading j :=
  oppositeScalarCharacter_mem_weight terminalCharacter.toRingHom (fun hj hz => terminalCharacter_homogeneous hj hz) ha

universe v

variable [CatModule.HasDerivedCategory.{v,0} (WeightCategory ℚ)]
  [CatModule.HasDerivedCategory.{v,0} (WeightCategory Tᵐᵒᵖ)]

/-- The terminal-character cup over ℚ for two type A₁ fundamental weights.
The internal shift is one and the cohomological shift is minus one. -/
def gradedFundamentalCup :
    CatModule.DerivedCategory.{v,0} (WeightCategory ℚ) ⥤
      CatModule.DerivedCategory.{v,0} (WeightCategory Tᵐᵒᵖ) :=
  shiftedCharacterCup gradedTerminalCharacter gradedTerminalCharacter_mem_weight 1 (-1)

/-- The internally graded cap with the terminal coefficient in type A₁. -/
def gradedFundamentalCap :
    CatModule.DerivedCategory.{v,0} (WeightCategory Tᵐᵒᵖ) ⥤
      CatModule.DerivedCategory.{v,0} (WeightCategory ℚ) :=
  characterCap gradedTerminalCharacter gradedTerminalCharacter_mem_weight


end Categorification.Stendhal.FundamentalCorner
