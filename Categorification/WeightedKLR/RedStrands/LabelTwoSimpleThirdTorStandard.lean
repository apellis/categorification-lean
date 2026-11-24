/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoSimpleThirdTor
import Categorification.WeightedKLR.RedStrands.LabelTwoMiddleSupportedResolution

/-!
# The label-two third Tor vanishing with the actual middle resolution
-/

namespace Categorification.Stendhal.LabelTwo

open CategoryTheory CategoryTheory.Limits DG DG.DerivedCategory
open scoped DG.DegreeZero

noncomputable section

universe w
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable (k : Type) [Field k] [NeZero (2 : k)] [HasDerivedCategory.{w,0} k]
  [HasDerivedCategory.{w,0} (TensorProductAlgebra k (parameter k)
    (fun (_ : Fin 2) => Finsupp.single () 2) (Multiset.replicate 2 ()))]

local notation "T" => TensorProductAlgebra k (parameter k) weights (({()} : Multiset Unit) + {()})
local notation "TRaw" => TensorProductAlgebra k (parameter k)
  (fun (_ : Fin 2) => Finsupp.single () 2) (Multiset.replicate 2 ())
local notation "L" => labelTwoExteriorCokernel (parameter k)

local instance thirdTorStandardNormalizedDerived : HasDerivedCategory.{w,0} T :=
  inferInstanceAs (HasDerivedCategory.{w,0} TRaw)

/-- The third ambient self Tor of the actual reflected simple vanishes when two is invertible. -/
theorem labelTwoSimpleAmbientTorThree_isZero :
    IsZero (reflectedAmbientHomology k L L (-3)) :=
  labelTwoSimpleTorThree_isZero_of_middleAcyclic k (middleAmbientAcyclic k (-1) (by decide))

end
end Categorification.Stendhal.LabelTwo
