/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoMiddleWeightRecurrence

import Categorification.WeightedKLR.RedStrands.LabelTwoMiddleSupportedResolution

/-!
# Internal weights of the periodic label-two middle tensor

Webster, arXiv:1309.3796v2, §8.2, Proposition 8.4. The reflected
coefficient kills the higher support in the middle standard's graded
resolution. The companion triangles then identify consecutive negative
cohomology groups at weights differing by two.
-/

noncomputable section

namespace Categorification.Stendhal.LabelTwo

open CategoryTheory DG
open scoped DG.DegreeZero
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe v
variable (k : Type) [Field k]

local notation "ν₂" => (({()} : Multiset Unit) + {()})
local notation "A₂" => TensorProductAlgebra k (parameter k) weights ν₂
local notation "𝒜₂" => middleTensorGrade k (labelTwoGradingDatum k)

local instance middlePeriodicInternalGrading : InternalGrading A₂ := gradedAlgebraInternalGrading 𝒜₂
local instance middlePeriodicDGGrading : BigradedDGRing A₂ := gradedAlgebraBigradedDGRing 𝒜₂
local instance middlePeriodicScalarGrading : InternalGrading k := scalarInternalGrading k
local instance middlePeriodicScalarDGGrading : BigradedDGRing k := scalarBigradedDGRing k

variable [CatModule.HasDerivedCategory.{v,0} (WeightCategory
  (TensorProductAlgebra k (parameter k) weights (({()} : Multiset Unit) + {()})))]
  [CatModule.HasDerivedCategory.{v,0} (WeightCategory k)]

local notation "F" => middleReflectedWeightDerivedTensor k
local notation "Q" => CatModule.DerivedCategory.Q
local notation "H" => CatModule.DerivedCategory.cohomologyFunctor

/-- The companion of the sum quotient gives one step of the middle
recurrence, lowering the output internal weight by two. -/
def middleSumWeightTensorStepIso (X : WeightCategory k) (n : ℤ)
    (hn : n ≠ 0) (hn' : n + 1 ≠ 0) :
    (H X n).obj ((F).obj ((Q).obj (middleSumWeightModule k 0))) ≅
    (H ((WeightCategory.shiftFunctor k (-2)).obj X) (n + 1)).obj
      ((F).obj ((Q).obj (middleDifferenceWeightModule k 0))) :=
  middleSumWeightShiftIso k F X n
      (middleStandardWeight_cohomology_isZero k X n hn)
      (middleStandardWeight_cohomology_isZero k X (n + 1) hn') ≪≫
    middleDifferenceWeightTensorCohomologyShiftIso k 2 X (n + 1)

/-- The difference quotient gives the other step of the middle
recurrence with the same internal weight decrease. -/
def middleDifferenceWeightTensorStepIso (X : WeightCategory k) (n : ℤ)
    (hn : n ≠ 0) (hn' : n + 1 ≠ 0) :
    (H X n).obj ((F).obj ((Q).obj (middleDifferenceWeightModule k 0))) ≅
    (H ((WeightCategory.shiftFunctor k (-2)).obj X) (n + 1)).obj
      ((F).obj ((Q).obj (middleSumWeightModule k 0))) :=
  middleDifferenceWeightShiftIso k F X n
      (middleStandardWeight_cohomology_isZero k X n hn)
      (middleStandardWeight_cohomology_isZero k X (n + 1) hn') ≪≫
    middleSumWeightTensorCohomologyShiftIso k 2 X (n + 1)

/-- On the negative tail, two middle companion steps increase the
cohomological index by two and lower the output internal weight by four. -/
def middleSumWeightTensorPeriodIso (X : WeightCategory k) (n : ℤ) (hn : n ≤ -3) :
    (H X n).obj ((F).obj ((Q).obj (middleSumWeightModule k 0))) ≅
    (H ((WeightCategory.shiftFunctor k (-4)).obj X) (n + 2)).obj
      ((F).obj ((Q).obj (middleSumWeightModule k 0))) := by
  let X' := (WeightCategory.shiftFunctor k (-2)).obj X
  have he : (WeightCategory.shiftFunctor k (-2)).obj X' =
      (WeightCategory.shiftFunctor k (-4)).obj X := by
    exact congrArg (fun a : ℤ => (⟨a⟩ : WeightCategory k))
      (show X.as + (-2 : ℤ) + (-2 : ℤ) = X.as + (-4 : ℤ) by omega)
  have hd : n + 1 + 1 = n + 2 := by omega
  let S := (F).obj ((Q).obj (middleSumWeightModule k 0))
  have hIndex : (H ((WeightCategory.shiftFunctor k (-2)).obj X') (n + 1 + 1)).obj S =
      (H ((WeightCategory.shiftFunctor k (-4)).obj X) (n + 2)).obj S := by
    rw [he, hd]
  exact middleSumWeightTensorStepIso k X n (by omega) (by omega) ≪≫
    middleDifferenceWeightTensorStepIso k X' (n + 1) (by omega) (by omega) ≪≫
    eqToIso hIndex

end Categorification.Stendhal.LabelTwo
