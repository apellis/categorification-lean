/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PartialStandardizationAssocOrders

/-!
# The two orders of the cuts intertwine the actions of all strands

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1. The
identification `blocksStandardAssocEquiv` of the two iterations of partial standardization with
three blocks is compatible with the actions of the tensor product algebras of all strands,
`T^{λ ∘ ε}((θ + β) + γ)` and `T^λ(θ + (β + γ))`, along the relabelling `blocksAssocKLR` of the
affine KLR algebras of all strands (`blocksStandardAssocEquiv_action`).

## Main results

* `Stendhal.blocksStandardAssocEquiv_ofShuffleL`: the identification on the shuffle model.
* `Stendhal.blocksStandardAssocEquiv_action`: the identification intertwines the actions of
  affine elements `z_L`, `z_R` of all strands that correspond under the relabelling.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA
open scoped TensorProduct

variable {I k : Type*} [DecidableEq I] [CommRing k] {a m r : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (a + (m + r)) → I →₀ ℕ) (θ β γ : Multiset I)
  (N : Type*) [AddCommGroup N] [Module k N] [Module (blocksFactorAlgebra Q Λ θ β γ) N]
  [IsScalarTower k (blocksFactorAlgebra Q Λ θ β γ) N] (hQ : KLRSymm Q)

local notation "ΛL" => Λ ∘ Fin.cast (Nat.add_assoc a m r)
local notation "S" => stendhalQ Q Λ
local notation "Sₗ" => stendhalQ Q (Λ ∘ Fin.cast (Nat.add_assoc a m r))
local notation "αₗ" =>
  Multiset.map (Sum.map (id : I → I) (Fin.castAdd r)) (stendhalWeight (a + m) (θ + β))
local notation "δₗ" =>
  Multiset.map (Sum.map (id : I → I) (Fin.natAdd (a + m))) (stendhalWeight r γ)
local notation "αᵣ" =>
  Multiset.map (Sum.map (id : I → I) (Fin.castAdd (m + r))) (stendhalWeight a θ)
local notation "δᵣ" =>
  Multiset.map (Sum.map (id : I → I) (Fin.natAdd a)) (stendhalWeight (m + r) (β + γ))
local notation "Nₗ" => BlocksAssocInput Q Λ θ β γ N
local notation "Wₗ" => Ind Sₗ αₗ δₗ (BlocksShuffleInputL Q ΛL θ β γ Nₗ)

/-- The identification of the two iterations on the shuffle model. -/
theorem blocksStandardAssocEquiv_ofShuffleL (w : Wₗ) :
    blocksStandardAssocEquiv Q Λ θ β γ N hQ (blocksStandardOfShuffleL Q ΛL θ β γ Nₗ hQ w) =
      blocksStandardOfShuffle Q Λ θ β γ N hQ ((blocksShuffleIndEquiv Q Λ θ β γ N).symm
        (blocksAssocInd3Equiv Q Λ θ β γ N (blocksShuffleInd3EquivL Q ΛL θ β γ Nₗ w))) := by
  apply (blocksStandardOneStepEquiv Q Λ θ β γ N hQ).injective
  rw [blocksStandardOneStepEquiv_assocEquiv, blocksStandardOneStepEquivL_apply,
    blocksOneStepQuotAssocEquiv_mk]
  refine Eq.symm ((blocksStandardOneStepEquiv_apply Q Λ θ β γ N hQ _).trans ?_)
  exact congrArg Submodule.Quotient.mk (LinearEquiv.apply_symm_apply _ _)

/-- **The two iterations of partial standardization intertwine the actions of all strands**:
if the affine elements `z_L` of `(θ + β) + γ` and `z_R` of `θ + (β + γ)` correspond under the
relabelling `blocksAssocKLR` of the affine KLR algebras of all strands, then the
identification `blocksStandardAssocEquiv` takes the action of the image of `z_L` in
`T^{λ ∘ ε}((θ + β) + γ)` to the action of the image of `z_R` in `T^λ(θ + (β + γ))`. -/
theorem blocksStandardAssocEquiv_action (zL : KLRAlgebra k Sₗ (αₗ + δₗ))
    (zR : KLRAlgebra k S (αᵣ + δᵣ))
    (hz : blocksAssocKLR Q Λ θ β γ (castKLR Sₗ (blocksWeightL_add_eq θ β γ) zL) =
      castKLR S (add_eq_add_of_eq rfl (blocksWeight_eq β γ)) zR)
    (x : BlocksStandardL Q ΛL θ β γ Nₗ hQ) :
    blocksStandardAssocEquiv Q Λ θ β γ N hQ
      (blocksStandardActionL Q ΛL θ β γ Nₗ hQ (TensorProductAlgebra.mk Q ΛL ((θ + β) + γ)
        (orderProjection Q ΛL ((θ + β) + γ) (StendhalAlgebraAllOrders.ofKLR k Q ΛL
          ((θ + β) + γ) (castKLR Sₗ (cutInputWeights_add (a := a + m) (r := r) (θ + β) γ)
            zL)))) x) =
      blocksStandardAction Q Λ θ β γ N hQ (TensorProductAlgebra.mk Q Λ (θ + (β + γ))
        (orderProjection Q Λ (θ + (β + γ)) (StendhalAlgebraAllOrders.ofKLR k Q Λ
          (θ + (β + γ)) (castKLR S (cutInputWeights_add (a := a) (r := m + r) θ (β + γ))
            zR))))
        (blocksStandardAssocEquiv Q Λ θ β γ N hQ x) := by
  obtain ⟨w, rfl⟩ := blocksStandardOfShuffleL_surjective Q ΛL θ β γ Nₗ hQ x
  apply (blocksStandardOneStepEquiv Q Λ θ β γ N hQ).injective
  refine (blocksStandardOneStepEquiv_assocEquiv Q Λ θ β γ N hQ _).trans ?_
  refine (congrArg (blocksOneStepQuotAssocEquiv Q Λ θ β γ N)
    (blocksStandardOneStepEquivL_smul Q ΛL θ β γ Nₗ hQ zL w)).trans ?_
  refine (blocksOneStepQuotAssocEquiv_mk_smul Q Λ θ β γ N _ _).trans ?_
  rw [hz, blocksStandardAssocEquiv_ofShuffleL]
  refine Eq.symm ((blocksStandardOneStepEquiv_smul Q Λ θ β γ N hQ zR _).trans ?_)
  exact congrArg (fun u => Submodule.Quotient.mk
    (castKLR S (add_eq_add_of_eq rfl (blocksWeight_eq β γ)) zR • u))
    (LinearEquiv.apply_symm_apply _ _)

end Categorification.Stendhal
