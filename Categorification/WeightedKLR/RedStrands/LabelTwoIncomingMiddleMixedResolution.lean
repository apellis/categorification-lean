/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoIncomingMiddleMixed
import Categorification.WeightedKLR.RedStrands.LabelTwoMiddleSupportedResolution

/-!
# Vanishing of the incoming exterior and middle-standard mixed tensor
-/

namespace Categorification.Stendhal.LabelTwo

open CategoryTheory.Limits DG KLR
open scoped DG.DegreeZero

noncomputable section

universe w

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable (k : Type) [Field k] [DG.HasDerivedCategory.{w,0} k]
  [DG.HasDerivedCategory.{w,0} (TensorProductAlgebra k (parameter k)
    weights (({()} : Multiset Unit) + {()}))]

/-- The incoming exterior coefficient and the middle standard have zero
ambient derived tensor homology in every degree. -/
theorem incomingMiddleStandardHomology_isZero (n : ℤ) :
    IsZero (incomingMiddleStandardHomology k n) := by
  obtain ⟨R,hR⟩ := exists_middleStandard_supportedResolution k
  exact incomingMiddleStandardHomology_isZero_of_support k R hR n

end
end Categorification.Stendhal.LabelTwo
