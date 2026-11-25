/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoIncomingLiftNonzero
import Categorification.WeightedKLR.RedStrands.LabelTwoExteriorCokernelGrade

/-!
# Simplicity of the actual label-two exterior complex terms

The middle quotient and outgoing projective have explicit proper
nonzero images of their incoming differentials.
-/

namespace Categorification.Stendhal.LabelTwo

open KLR CategoryTheory Categorification.Webster.LabelTwo

noncomputable section

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable (k : Type) [Field k]
local notation "ν" => (({()} : Multiset Unit) + {()})
local notation "T" => TensorProductAlgebra k (parameter k) weights ν
local notation "S" => Standard k
local notation "B" => StandardDotSumQuotient k
local notation "U" => LinearMap.range (diagramPlus k)
local notation "V" => LinearMap.range (normalizedIncoming k)
local notation "q" => Submodule.mkQ (LinearMap.range (diagramPlus k))
local notation "E" => seqIdem (parameter k) weights loading loading_ordered
local notation "g" => leftStandardUnit (parameter k) weights loading loading_ordered

private theorem middle_generator_fixed : E • g = g := by
  have h := (middleToFixed k (1 : Middle k)).property
  change E • (middleToFixed k (1 : Middle k)).val = _ at h
  simpa only [middleToFixed_one_val] using h

private theorem middle_quotient_generator_ne_zero : q g ≠ 0 := by
  let u := fixedQuotientMap k (middleToFixed k (1 : Middle k))
  have hu : u.val = q g := congrArg q (middleToFixed_one_val k)
  have he : middleCutDotSumEquiv k u = 1 :=
    (middleCutDotSumEquiv_specialize k 1).trans (map_one specialize)
  intro hz
  have h0 : u = 0 := Subtype.ext (hu.trans hz)
  exact zero_ne_one (((middleCutDotSumEquiv k).map_zero).symm.trans
    ((congrArg (middleCutDotSumEquiv k) h0.symm).trans he))

private theorem mapRight_zero {k A N X W : Type*} [Field k] [Ring A] [Algebra k A]
    [AddCommGroup N] [Module k N] [Module Aᵐᵒᵖ N] [SMulCommClass k Aᵐᵒᵖ N]
    [AddCommGroup X] [Module k X] [Module A X] [IsScalarTower k A X]
    [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W] :
    BalancedTensor.mapRight (k := k) («B» := k) (M := N) (0 : X →ₗ[A] W) = 0 := by
  apply BalancedTensor.ext
  intro m z
  change (BalancedTensor.tmul m ((0 : X →ₗ[A] W) z) : BalancedTensor k k A N W) = 0
  rw [LinearMap.zero_apply, BalancedTensor.tmul_zero]

private theorem normalizedIncoming_ne_zero : normalizedIncoming k ≠ 0 :=
  fun h => incomingLiftTensorMap_nonzero k ((congrArg (BalancedTensor.mapRight (k := k)
    («B» := k) (M := IncomingLiftCoefficient k)) h).trans mapRight_zero)

private theorem middle_generator_notMem_incoming :
    q g ∉ V := by
  intro h
  have hJ : g ∈ incomingLiftSubmodule k := h
  obtain ⟨z,_,hz⟩ := (incomingLift_middle_fixed_iff k g (middle_generator_fixed k)).1 hJ
  exact middle_quotient_generator_ne_zero k ((Submodule.Quotient.mk_eq_zero U).2 ⟨z,hz⟩)

/-- The middle dot-sum quotient has a proper nonzero incoming submodule. -/
theorem labelTwo_middleQuotient_not_simple : ¬ Simple (ModuleCat.of T B) := by
  intro hs
  let : IsSimpleModule T B := simple_iff_isSimpleModule.1 hs
  rcases eq_bot_or_eq_top (V) with h | h
  · exact normalizedIncoming_ne_zero k (LinearMap.range_eq_bot.1 h)
  · exact middle_generator_notMem_incoming k (h.symm ▸ Submodule.mem_top)

private abbrev exteriorProjector : T := labelTwoLeftExteriorProjector (parameter k)
local notation "C" => lIdeal (exteriorProjector k)
local notation "L" => labelTwoExteriorCokernel (parameter k)
local notation "TRaw" => TensorProductAlgebra k (parameter k)
  (fun (_ : Fin 2) => Finsupp.single () 2) (Multiset.replicate 2 ())

/-- The outgoing exterior projective has a proper nonzero image of the
middle crossing as a submodule. -/
theorem labelTwo_outgoingExterior_not_simple : ¬ Simple (ModuleCat.of T C) := by
  intro hs
  let : IsSimpleModule T C := simple_iff_isSimpleModule.1 hs
  have hd0 : normalizedOutgoing k (q g) ≠ 0 := fun h =>
    middle_generator_notMem_incoming k ((labelTwoNormalizedCrossings_exact k (q g)).1 h)
  let R : Submodule T C := LinearMap.range (normalizedOutgoing k)
  rcases eq_bot_or_eq_top R with h | h
  · have hmem : normalizedOutgoing k (q g) ∈ (⊥ : Submodule T C) :=
      h ▸ (show normalizedOutgoing k (q g) ∈ LinearMap.range (normalizedOutgoing k) from ⟨q g,rfl⟩)
    exact hd0 ((Submodule.mem_bot T).1 hmem)
  · let a := labelTwoExteriorAugmentation (parameter k)
    have hsimp : IsSimpleModule TRaw L :=
      simple_iff_isSimpleModule.1 (labelTwoExteriorCokernel_simple (parameter k))
    have : Nontrivial L := hsimp.nontrivial
    obtain ⟨y,hy⟩ := exists_ne (0 : L)
    obtain ⟨z,hz⟩ := labelTwoNormalizedAugmentation_surjective k y
    have hr : z ∈ R := h.symm ▸ Submodule.mem_top
    have hz0 := (labelTwoNormalizedAugmentation_exact k z).2 hr
    exact hy (hz.symm.trans hz0)

end
end Categorification.Stendhal.LabelTwo
