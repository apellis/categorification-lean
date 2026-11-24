/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DiagramWeightCohomologyShift
import Categorification.WeightedKLR.RedStrands.LabelTwoMiddleWeightTriangles

/-!
# The actual label-two middle weight recurrence

A triangulated functor applied to the two actual companion triangles
has the expected connecting isomorphisms when its middle standard
cohomology vanishes. The target retains the internal shift by two.
-/

noncomputable section

set_option maxHeartbeats 1800000
set_option maxRecDepth 2048

namespace Categorification.Stendhal.LabelTwo

open KLR CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated DG
open scoped DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable (k : Type) [Field k]

local notation "ν₂" => (({()} : Multiset Unit) + {()})
local notation "A₂" => TensorProductAlgebra k (parameter k) weights ν₂
local notation "𝒜₂" => middleTensorGrade k (labelTwoGradingDatum k)

local instance : InternalGrading A₂ := gradedAlgebraInternalGrading 𝒜₂
local instance : BigradedDGRing A₂ := gradedAlgebraBigradedDGRing 𝒜₂

universe v

variable [CatModule.HasDerivedCategory.{v,0} (WeightCategory
  (TensorProductAlgebra k (parameter k) weights (({()} : Multiset Unit) + {()})))]
  {C : Type} [Category C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  [DGCategory C] [CatModule.HasDerivedCategory.{v,0} C]

variable (F : CatModule.DerivedCategory.{v,0} (WeightCategory
      (TensorProductAlgebra k (parameter k) weights (({()} : Multiset Unit) + {()}))) ⥤
    CatModule.DerivedCategory.{v,0} C)
  [F.CommShift ℤ] [F.IsTriangulated]

local notation "L₂" => CatModule.DerivedCategory.Q (C := WeightCategory A₂)
local notation "H₀" => CatModule.DerivedCategory.cohomologyFunctor

/-- Vanishing of the actual standard's cohomology at the specified weight and degree. -/
abbrev middleWeightStandardIsZero (X : C) (n : ℤ) : Prop :=
  IsZero ((H₀ X n).obj (F.obj ((L₂).obj (middleStandardWeightModule k))))

variable (X : C) (n : ℤ)
  (h₀ : middleWeightStandardIsZero k F X n)
  (h₁ : middleWeightStandardIsZero k F X (n + 1))

/-- The sum quotient's cohomology shifts to the difference quotient with its
actual internal shift by two. -/
def middleSumWeightShiftIso :
    (H₀ X n).obj (F.obj ((L₂).obj (middleSumWeightModule k 0))) ≅
      (H₀ X (n + 1)).obj (F.obj ((L₂).obj (middleDifferenceWeightModule k 2))) := by
  let δ := Classical.choose (middleSumWeight_distinguished k)
  let T := Triangle.mk ((L₂).map (middleSumWeightCompanion k))
    ((L₂).map (middleSumWeightAugmentation k)) δ
  have hT : T ∈ distTriang _ := Classical.choose_spec (middleSumWeight_distinguished k)
  exact weightCohomologyShiftIso X (F.mapTriangle.obj T) (F.map_distinguished T hT) n h₀ h₁

/-- The difference quotient's cohomology shifts to the sum quotient with its
actual internal shift by two. -/
def middleDifferenceWeightShiftIso :
    (H₀ X n).obj (F.obj ((L₂).obj (middleDifferenceWeightModule k 0))) ≅
      (H₀ X (n + 1)).obj (F.obj ((L₂).obj (middleSumWeightModule k 2))) := by
  let δ := Classical.choose (middleDifferenceWeight_distinguished k)
  let T := Triangle.mk ((L₂).map (middleDifferenceWeightCompanion k))
    ((L₂).map (middleDifferenceWeightAugmentation k)) δ
  have hT : T ∈ distTriang _ := Classical.choose_spec (middleDifferenceWeight_distinguished k)
  exact weightCohomologyShiftIso X (F.mapTriangle.obj T) (F.map_distinguished T hT) n h₀ h₁

/-- If the standard's cohomology vanishes, that of the sum quotient is the
kernel of the next shifted companion map. -/
def middleSumWeightKernelIso :
    (H₀ X n).obj (F.obj ((L₂).obj (middleSumWeightModule k 0))) ≅
      kernel ((H₀ X (n + 1)).map (F.map ((L₂).map (middleSumWeightCompanion k)))) := by
  let δ := Classical.choose (middleSumWeight_distinguished k)
  let T := Triangle.mk ((L₂).map (middleSumWeightCompanion k))
    ((L₂).map (middleSumWeightAugmentation k)) δ
  have hT : T ∈ distTriang _ := Classical.choose_spec (middleSumWeight_distinguished k)
  exact weightCohomologyShiftKernelIso X (F.mapTriangle.obj T) (F.map_distinguished T hT) n h₀

/-- If the standard's cohomology vanishes, that of the difference quotient is
the kernel of the other shifted companion map. -/
def middleDifferenceWeightKernelIso :
    (H₀ X n).obj (F.obj ((L₂).obj (middleDifferenceWeightModule k 0))) ≅
      kernel ((H₀ X (n + 1)).map (F.map ((L₂).map (middleDifferenceWeightCompanion k)))) := by
  let δ := Classical.choose (middleDifferenceWeight_distinguished k)
  let T := Triangle.mk ((L₂).map (middleDifferenceWeightCompanion k))
    ((L₂).map (middleDifferenceWeightAugmentation k)) δ
  have hT : T ∈ distTriang _ := Classical.choose_spec (middleDifferenceWeight_distinguished k)
  exact weightCohomologyShiftKernelIso X (F.mapTriangle.obj T) (F.map_distinguished T hT) n h₀

end Categorification.Stendhal.LabelTwo
