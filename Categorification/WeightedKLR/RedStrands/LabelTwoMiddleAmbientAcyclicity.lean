/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoMiddleSupport
import Categorification.WeightedKLR.RedStrands.OppositeStandardTor

/-!
# Ambient acyclicity at the label-two middle standard

In Webster §8.2, the reflected dot-sum coefficient kills every strictly higher
loading. A supported projective resolution therefore computes the ambient
derived tensor with the middle standard in degree zero.
-/

noncomputable section

namespace Categorification.Stendhal.LabelTwo

open KLR CategoryTheory CategoryTheory.Limits DG DG.DerivedCategory MulOpposite
open scoped DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe w

variable (k : Type) [Field k]
local notation "blackWeight" => (({()} : Multiset Unit) + {()})
local notation "Ambient" => TensorProductAlgebra k (parameter k) weights blackWeight
local notation "S" => Standard k
local notation "N" => rightMiddleDotSumQuotient k
local notation "Label" => {s : Seq (stendhalWeight 2 blackWeight) // IsRedOrdered s}

variable [HasDerivedCategory.{w, 0}
  (TensorProductAlgebra k (parameter k) weights (({()} : Multiset Unit) + {()}))] [HasDerivedCategory.{w, 0} ℤ]

/-- Ambient standard resolution with higher loading support makes the diagrammatic
middle standard acyclic for tensoring with the reflected middle coefficient. -/
theorem middleStandard_derivedTensorHomology_isZero_of_higher_support
    (P : ProjectiveResolution (ModuleCat.of Ambient S))
    (hs : ∀ j : ℕ, ∃ (J : Type) (label : J → Label)
      (inc : ∀ i, lIdeal (seqIdem (parameter k) weights (label i).1 (label i).2) →ₗ[Ambient]
        P.complex.X (j + 1)),
      (∀ i, StendhalLT loading (label i).1) ∧ ∀ x : P.complex.X (j + 1),
        x ∈ Submodule.span Ambient {y | ∃ i z, inc i z = y})
    (n : ℤ) (hn : n ≠ 0) :
    IsZero ((homologyFunctor (A := ℤ) ℤ n).obj
      ((derivedTensor ℤ Ambient (N : Type)).obj
        (Q.obj (DGModuleCat.of Ambient (InDegreeZero S))))) := by
  exact isZero_derivedTensorHomology_of_projectiveResolution_loading_support P
    (fun i : Label => seqIdem (parameter k) weights i.1 i.2)
    (fun i => StendhalLT loading i.1)
    (fun i => seqIdem_mul_self (parameter k) weights i.1 i.2)
    hs (fun i hi => rightMiddleDotSumQuotient_kills_higher k i.1 i.2 hi) n hn

end Categorification.Stendhal.LabelTwo
