/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapEMixed
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCrossMid

/-!
# The mixed crossing of two appended strands as a Stendhal diagram

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, the compatibility of `K ∘ 𝔈_b 𝔈_a ≅ 𝔈⁺_b 𝔈⁺_a ∘ K` with the crossing for
`a ≠ b`. The crossing `CupCap.mixedCrossElem` of two appended strands of different colours is
written as the image of a product of Stendhal diagrams (`CupCap.mixedCrossElem_eq_mk`), and the
same is done for `T^{λ⁺}` after casting to the content `({a} + ({b} + ν)) + ν₀`
(`CupCap.castOp_mixedCrossElem_plus`).

## Main results

* `CupCap.mixedCrossElem_eq_mk`, `CupCap.castOp_mixedCrossElem_plus`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Generic

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {n : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ' : Fin n → I →₀ ℕ)

theorem appendBlackAt_mk (i : I) {μ β : Multiset I} (h : ({i} : Multiset I) + μ = β)
    (z : StendhalAlgebra k Q Λ' μ) :
    appendBlackAt Λ' i h (TensorProductAlgebra.mk Q Λ' μ z) =
      TensorProductAlgebra.mk Q Λ' β
        (castPlusStendhal Q Λ' h (appendBlackStendhal Q Λ' i μ z)) := by
  subst h; rfl

theorem mixedBlackCrossing_eq_mk (μ : Multiset I) (b a : I) :
    mixedBlackCrossing (Q := Q) Λ' μ b a =
      TensorProductAlgebra.mk Q Λ' _ (orderProjection Q Λ' _
        (-StendhalAlgebraAllOrders.ψ (Multiset.card (stendhalWeight n μ)))) := by
  unfold mixedBlackCrossing
  rw [map_neg, map_neg, map_neg]
  congr 1
  change affineTensorProjection Λ' _ (castKLR (affineCoverQ Q Λ') _ (ψ _)) = _
  rw [castKLR_ψ]
  change TensorProductAlgebra.mk Q Λ' _ (orderProjection Q Λ' _ (affineCover Q Λ' _ (ψ _))) = _
  rw [affineCover_ψ]

/-- **The mixed crossing as a Stendhal diagram**: `mixedCrossElem` is the image of the idempotent
of appending first `a` then `b`, times minus the crossing of the last two strands, times the
idempotent of appending first `b` then `a`. -/
theorem mixedCrossElem_eq_mk (μ : Multiset I) (b a : I) :
    mixedCrossElem (Q := Q) Λ' μ b a = TensorProductAlgebra.mk Q Λ' _
      (appendBlackStendhal Q Λ' b _ (appendBlackStendhal Q Λ' a μ 1) *
        orderProjection Q Λ' _
          (-StendhalAlgebraAllOrders.ψ (Multiset.card (stendhalWeight n μ))) *
        castPlusStendhal Q Λ' (mixedSwap μ b a)
          (appendBlackStendhal Q Λ' a _ (appendBlackStendhal Q Λ' b μ 1))) := by
  have e1 : (1 : TensorProductAlgebra k Q Λ' μ) = TensorProductAlgebra.mk Q Λ' μ 1 :=
    (map_one _).symm
  unfold mixedCrossElem
  rw [mixedBlackCrossing_eq_mk, e1, appendBlack_mk, appendBlack_mk, appendBlack_mk,
    appendBlackAt_mk, ← map_mul, ← map_mul]

end Generic

section Plus

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} (ν : Multiset I) {ν₀ : Multiset I} (a b : I)

local notation "Λ⁺" => plusLabels Λ Λc j hj
local notation "νa" => ((Singleton.singleton a : Multiset I) + ν)
local notation "νb" => ((Singleton.singleton b : Multiset I) + ν)
local notation "νab" =>
  ((Singleton.singleton a : Multiset I) + ((Singleton.singleton b : Multiset I) + ν))
local notation "νba" =>
  ((Singleton.singleton b : Multiset I) + ((Singleton.singleton a : Multiset I) + ν))
local notation "ρ" => stendhalWeight (ℓ + 2) (ν + ν₀)

omit [DecidableEq I] in
theorem plusWeight_assoc_mixed :
    (Singleton.singleton b : Multiset I) + ((Singleton.singleton a : Multiset I) + (ν + ν₀)) =
      νba + ν₀ :=
  (congrArg (Singleton.singleton b + ·) (plusWeight_assoc ν ν₀ a)).trans
    (plusWeight_assoc νa ν₀ b)

/-- Appending two strands of colours `a`, then `b`, in `T̃^{λ⁺}` is appending them in
`T̃^{λ⁺}_{ν + ν₀}`, then casting. -/
theorem appendBlackPlus_mixed (W : StendhalAlgebra k Q Λ⁺ (ν + ν₀)) :
    appendBlackPlus Q Λ Λc j hj νa ν₀ b (appendBlackPlus Q Λ Λc j hj ν ν₀ a W) =
      castPlusStendhal Q Λ⁺ (plusWeight_assoc_mixed ν a b)
        (appendBlackStendhal Q Λ⁺ b _ (appendBlackStendhal Q Λ⁺ a (ν + ν₀) W)) := by
  change castPlusStendhal Q Λ⁺ (plusWeight_assoc νa ν₀ b) (appendBlackStendhal Q Λ⁺ b (νa + ν₀)
    (castPlusStendhal Q Λ⁺ (plusWeight_assoc ν ν₀ a) (appendBlackStendhal Q Λ⁺ a (ν + ν₀) W))) = _
  rw [appendBlackStendhal_castPlusStendhal, castPlusStendhal_trans]

/-- **The mixed crossing of the two appended strands of `T^{λ⁺}`**, cast to the content
`({a} + ({b} + ν)) + ν₀`: the image of the idempotent of appending first `a`, then `b`, times
minus the crossing of the last two strands of `λ⁺`, times the idempotent of appending first `b`,
then `a`. -/
theorem castOp_mixedCrossElem_plus (h : (Singleton.singleton b : Multiset I) +
    ((Singleton.singleton a : Multiset I) + (ν + ν₀)) = νab + ν₀) :
    castOp Q Λ⁺ h (op (mixedCrossElem (Q := Q) Λ⁺ (ν + ν₀) b a)) =
      plusQuotOp k Q Λ Λc j hj νab ν₀ (op
        (castPlusStendhal Q Λ⁺ (congrArg (· + ν₀) (mixedSwap ν a b))
            (appendBlackPlus Q Λ Λc j hj νa ν₀ b (appendBlackPlus Q Λ Λc j hj ν ν₀ a 1)) *
          botMap k Q Λ Λc j hj νab ν₀ (-KLRAlgebra.ψ (Multiset.card ρ)) *
          appendBlackPlus Q Λ Λc j hj νb ν₀ a (appendBlackPlus Q Λ Λc j hj ν ν₀ b 1))) := by
  rw [castOp_op, mixedCrossElem_eq_mk, castTensorProductAlgebra_mk_stendhal,
    appendBlackPlus_mixed, appendBlackPlus_mixed]
  simp only [map_mul, map_neg, castPlusStendhal_trans, StendhalAlgebraAllOrders.ψ,
    castPlusStendhal_orderProjection, castKLR_ψ]
  rfl

end Plus

end Categorification.Stendhal.CupCap
