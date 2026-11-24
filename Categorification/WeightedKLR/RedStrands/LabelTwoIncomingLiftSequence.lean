/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoIncomingLiftCut
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The short exact sequence of the incoming preimage
-/

namespace Categorification.Stendhal.LabelTwo

open KLR CategoryTheory

noncomputable section

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable (k : Type) [Field k]
local notation "T" => TensorProductAlgebra k (parameter k) weights (({()} : Multiset Unit) + {()})
local notation "S" => Standard k
local notation "J" => incomingLiftSubmodule k
local notation "U" => LinearMap.range (diagramPlus k)
local notation "V" => LinearMap.range (normalizedIncoming k)
local notation "q" => Submodule.mkQ (LinearMap.range (diagramPlus k))

/-- The cokernel of the incoming crossing in the middle dot-sum quotient. -/
abbrev IncomingMiddleCokernel := (StandardDotSumQuotient k) ⧸ V

private def incomingMiddleQuotient : S →ₗ[T] IncomingMiddleCokernel k :=
  (V).mkQ.comp q

private theorem incomingMiddleQuotient_surjective :
    Function.Surjective (incomingMiddleQuotient k) :=
  (V).mkQ_surjective.comp (U).mkQ_surjective

private theorem incomingMiddleQuotient_exact :
    Function.Exact (J).subtype (incomingMiddleQuotient k) := by
  apply LinearMap.exact_iff.mpr
  rw [incomingMiddleQuotient, LinearMap.ker_comp, Submodule.ker_mkQ, Submodule.range_subtype]
  rfl

/-- The actual incoming preimage, unquotiented middle standard, and incoming
cokernel form a short exact sequence of diagram modules. -/
def incomingLiftShortComplex : ShortComplex (ModuleCat T) :=
  ShortComplex.mk (ModuleCat.ofHom (J).subtype)
    (ModuleCat.ofHom (incomingMiddleQuotient k)) (by
      apply ModuleCat.hom_ext
      exact LinearMap.ext fun z => (incomingMiddleQuotient_exact k z.val).2 ⟨z,rfl⟩)

/-- Exactness of the actual preimage sequence. -/
theorem incomingLiftShortComplex_shortExact : (incomingLiftShortComplex k).ShortExact := by
  let C := incomingLiftShortComplex k
  have : Mono C.f := (ModuleCat.mono_iff_injective C.f).mpr Subtype.val_injective
  have : Epi C.g := (ModuleCat.epi_iff_surjective C.g).mpr (incomingMiddleQuotient_surjective k)
  constructor
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact C).mpr (incomingMiddleQuotient_exact k)

end
end Categorification.Stendhal.LabelTwo
