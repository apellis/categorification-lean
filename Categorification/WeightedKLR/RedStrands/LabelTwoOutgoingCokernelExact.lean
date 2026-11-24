/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoIncomingLiftSequence
import Categorification.WeightedKLR.RedStrands.LabelTwoExteriorCokernelGrade
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The final short exact sequence of the label-two exterior complex

The cokernel of the incoming crossing embeds into the exterior
projective by the outgoing differential. The quotient is the final
simple augmentation.
-/

namespace Categorification.Stendhal.LabelTwo

open KLR CategoryTheory

noncomputable section

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
variable (k : Type) [Field k]
local notation "T" => TensorProductAlgebra k (parameter k) weights (({()} : Multiset Unit) + {()})
local notation "V" => LinearMap.range (normalizedIncoming k)
local notation "K" => IncomingMiddleCokernel k
private abbrev projector : T := labelTwoLeftExteriorProjector (parameter k)
local notation "P" => lIdeal (projector k)
local notation "L" => labelTwoExteriorCokernel (parameter k)
local notation "TRaw" => TensorProductAlgebra k (parameter k)
  (fun (_ : Fin 2) => Finsupp.single () 2) (Multiset.replicate 2 ())
local instance : Module T L := inferInstanceAs (Module TRaw L)
private abbrev aug : P →ₗ[T] L := labelTwoExteriorAugmentation (parameter k)

/-- The outgoing differential descends to the cokernel of the incoming differential. -/
def incomingCokernelToExterior : K →ₗ[T] P :=
  (V).liftQ (normalizedOutgoing k) fun z hz => (labelTwoNormalizedCrossings_exact k z).2 hz

/-- The descended outgoing map is injective. -/
theorem incomingCokernelToExterior_injective : Function.Injective (incomingCokernelToExterior k) := by
  apply (injective_iff_map_eq_zero (f := incomingCokernelToExterior k)).2
  intro z hz
  obtain ⟨v,rfl⟩ := (V).mkQ_surjective z
  exact (Submodule.Quotient.mk_eq_zero V).2 ((labelTwoNormalizedCrossings_exact k v).1 hz)

/-- The descended outgoing map has image the kernel of the simple augmentation. -/
theorem incomingCokernelToExterior_exact :
    Function.Exact (incomingCokernelToExterior k) (aug k) := by
  intro x
  constructor
  · intro hx
    obtain ⟨v,hv⟩ := (labelTwoNormalizedAugmentation_exact k x).1 hx
    exact ⟨(V).mkQ v,hv⟩
  · rintro ⟨z,rfl⟩
    obtain ⟨v,rfl⟩ := (V).mkQ_surjective z
    exact (labelTwoNormalizedAugmentation_exact k _).2 ⟨v,rfl⟩

/-- The final short exact sequence in the actual label-two exterior complex. -/
def outgoingCokernelShortComplex : ShortComplex (ModuleCat T) :=
  ShortComplex.mk (ModuleCat.ofHom (incomingCokernelToExterior k)) (ModuleCat.ofHom (aug k))
    (ModuleCat.hom_ext (LinearMap.ext fun z =>
      (incomingCokernelToExterior_exact k _).2 ⟨z,rfl⟩))

/-- Exactness at the exterior projective and its simple quotient. -/
theorem outgoingCokernelShortComplex_shortExact :
    (outgoingCokernelShortComplex k).ShortExact := by
  let S := outgoingCokernelShortComplex k
  have : Mono S.f := (ModuleCat.mono_iff_injective S.f).mpr (incomingCokernelToExterior_injective k)
  have : Epi S.g := (ModuleCat.epi_iff_surjective S.g).mpr (labelTwoNormalizedAugmentation_surjective k)
  constructor
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mpr (incomingCokernelToExterior_exact k)

end
end Categorification.Stendhal.LabelTwo
