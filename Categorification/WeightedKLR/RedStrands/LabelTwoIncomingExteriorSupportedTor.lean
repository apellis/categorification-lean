/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoIncomingExteriorAcyclic
import Categorification.WeightedKLR.RedStrands.LabelTwoMiddleSupportedResolution

noncomputable section

namespace Categorification.Stendhal.LabelTwo

open CategoryTheory.Limits DG
open scoped DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe w
variable (k : Type) [Field k]
variable [HasDerivedCategory.{w,0}
  (TensorProductAlgebra k (parameter k) (fun (_ : Fin 2) => Finsupp.single () 2)
    (Multiset.replicate 2 ()))]
  [HasDerivedCategory.{w,0} k]

private theorem incoming_ordered : IsRedOrdered labelTwoExteriorRightLoading := by
  unfold IsRedOrdered
  decide +kernel

/-- The ambient diagonal derived tensor of the actual divided incoming exterior
term has no homology in nonzero cohomological degree. -/
theorem incomingExteriorAmbientHomology_isZero (n : ℤ) (hn : n ≠ 0) :
    IsZero (incomingExteriorAmbientHomology k n) := by
  obtain ⟨R,hR⟩ := exists_loadingStandard_supportedResolution k
    ⟨labelTwoExteriorRightLoading,incoming_ordered⟩
  exact incomingExteriorAmbientHomology_isZero_of_support k R hR n hn

end Categorification.Stendhal.LabelTwo
