/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendMixedSwap

/-!
# The mixed crossing on doubly appended diagrams of `T̃^{λ⁺}`, for a cap left of the right end

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, the mixed crossing for `j < ℓ`. Let `a ≠ b` be colours, and append `b`, then
`a`, to `ν`. With the window to the left of the appended strands, the crossing of the last two
strands of `λ` on the doubly appended loadings is the crossing `Y` of the last two strands of
`λ⁺` (`CupCap.botMap_midCross_mul_appendBlackPlus_mixed`). `Y` carries the diagrams with `b`,
then `a` appended to those with `a`, then `b` appended
(`CupCap.lastCross_mul_appendBlackPlus_mixed`).
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra MulOpposite

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} (ν : Multiset I) {ν₀ : Multiset I} (a b : I)

local notation "νa" => ((Singleton.singleton a : Multiset I) + ν)
local notation "νb" => ((Singleton.singleton b : Multiset I) + ν)
local notation "νab" =>
  ((Singleton.singleton a : Multiset I) + ((Singleton.singleton b : Multiset I) + ν))
local notation "νba" =>
  ((Singleton.singleton b : Multiset I) + ((Singleton.singleton a : Multiset I) + ν))
local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "ρ" => stendhalWeight (ℓ + 2) (ν + ν₀)
local notation "Λ⁺" => plusLabels Λ Λc j hj
local notation "aBb" => appendBlackPlus Q Λ Λc j hj ν ν₀ b
local notation "aBa" => appendBlackPlus Q Λ Λc j hj νb ν₀ a
local notation "σ₀" => midStendhal j hj Q Λ Λc ν ν₀

variable (k Q Λ Λc j hj ν₀) in
/-- The crossing `Y` of the last two strands of `λ⁺` in `T̃^{λ⁺}` at `νab + ν₀`. -/
def mixedLastCross : StendhalAlgebra k Q Λ⁺ (νab + ν₀) :=
  botMap k Q Λ Λc j hj νab ν₀ (KLRAlgebra.ψ (Multiset.card ρ))

/-- **The crossing of the last two strands of `λ` on a loading with `b`, then `a` appended**,
for `j < ℓ`: the window lies to the left, so it is the crossing `ψ` of the last two strands of
`λ⁺`. -/
theorem midCross_mul_midIdem_append_mixed (h : j < ℓ) (s : Seq (stendhalWeight ℓ ν)) :
    midCross j hj Q Λ Λc νab ν₀ m *
        midIdem j hj Q Λ Λc νab ν₀ (appendBlackLoading a νb (appendBlackLoading b ν s)) =
      KLRAlgebra.ψ (Multiset.card ρ) *
        midIdem j hj Q Λ Λc νab ν₀ (appendBlackLoading a νb (appendBlackLoading b ν s)) := by
  set t := appendBlackLoading a νb (appendBlackLoading b ν s) with ht
  have h1 := card_appendBlackWeight (ℓ := ℓ) (ν := ν) (i := b)
  have h2 := card_appendBlackWeight (ℓ := ℓ) (ν := νb) (i := a)
  have hM := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
  have hpos : midPos j t = midPos j s := by
    rw [ht, midPos_appendBlackLoading j νb a h, midPos_appendBlackLoading j ν b h]
  have hlt := midPos_lt (j := j) (s := s) h
  have hc : crossPos (midPos j t) N m = Multiset.card ρ := by
    unfold crossPos; split_ifs <;> omega
  rw [midIdem, midCross_mul_eSum]
  unfold midCrossAt
  have e1 : ¬ m + 1 = midPos j t := by omega
  have e2 : ¬ m = midPos j t := by omega
  have e3 : m + 1 < Multiset.card (stendhalWeight ℓ νab) := by omega
  simp only [e1, e2, e3, dite_true, ite_false, hc]

/-- Appending `b`, then `a`, to the unit of the diagrams at the maximum, for `j < ℓ`. -/
theorem appendBlackPlus_mixed_midStendhal_one (h : j < ℓ) :
    aBa (aBb (σ₀ 1)) = botMap k Q Λ Λc j hj νab ν₀ (∑ s : Seq (stendhalWeight ℓ ν),
      midIdem j hj Q Λ Λc νab ν₀ (appendBlackLoading a νb (appendBlackLoading b ν s))) := by
  rw [appendBlackPlus_midStendhal_one ν b h, appendIdemPlus, appendBlackPlus_botMap, map_sum]
  exact congrArg _ (Finset.sum_congr rfl fun s _ => appendPlus_midIdem νb a h _)

/-- The crossing of the last two strands of `λ`, on the loadings with `b`, then `a` appended, is
`Y`, for `j < ℓ`. -/
theorem botMap_midCross_mul_appendBlackPlus_mixed (h : j < ℓ) :
    botMap k Q Λ Λc j hj νab ν₀ (midCross j hj Q Λ Λc νab ν₀ m) * aBa (aBb (σ₀ 1)) =
      mixedLastCross k Q Λ Λc j hj ν ν₀ a b * aBa (aBb (σ₀ 1)) := by
  rw [appendBlackPlus_mixed_midStendhal_one ν a b h, mixedLastCross, ← map_mul, ← map_mul,
    Finset.mul_sum, Finset.mul_sum,
    Finset.sum_congr rfl fun s _ => midCross_mul_midIdem_append_mixed ν a b h s]

/-- The unit of the diagrams at the maximum fixes the diagrams with `b`, then `a` appended, for
`j < ℓ`. -/
theorem midStendhal_one_mul_appendBlackPlus_mixed (h : j < ℓ)
    (W : StendhalAlgebra k Q Λ⁺ (ν + ν₀)) :
    midStendhal j hj Q Λ Λc νab ν₀ 1 * aBa (aBb (σ₀ 1 * W)) = aBa (aBb (σ₀ 1 * W)) := by
  have e1 : aBb (σ₀ 1 * W) = midStendhal j hj Q Λ Λc νb ν₀ 1 * aBb (σ₀ 1 * W) := by
    rw [map_mul, appendBlackPlus_midStendhal_one ν b h, ← mul_assoc,
      midStendhal_one_mul_appendIdemPlus ν b h]
  rw [e1, map_mul, appendBlackPlus_midStendhal_one νb a h, ← mul_assoc,
    midStendhal_one_mul_appendIdemPlus νb a h]

/-- Appending two strands of colours `a`, then `b`, in `T̃^{λ⁺}` is appending them in
`T̃^{λ⁺}_{ν + ν₀}`, then casting (over any commutative ring). -/
theorem appendBlackPlus_mixed_cast (W : StendhalAlgebra k Q Λ⁺ (ν + ν₀)) :
    appendBlackPlus Q Λ Λc j hj νa ν₀ b (appendBlackPlus Q Λ Λc j hj ν ν₀ a W) =
      castPlusStendhal Q Λ⁺ (plusWeight_assoc_mixed ν a b)
        (appendBlackStendhal Q Λ⁺ b _ (appendBlackStendhal Q Λ⁺ a (ν + ν₀) W)) := by
  change castPlusStendhal Q Λ⁺ (plusWeight_assoc νa ν₀ b) (appendBlackStendhal Q Λ⁺ b (νa + ν₀)
    (castPlusStendhal Q Λ⁺ (plusWeight_assoc ν ν₀ a) (appendBlackStendhal Q Λ⁺ a (ν + ν₀) W))) = _
  rw [appendBlackStendhal_castPlusStendhal, castPlusStendhal_trans]

/-- `Y` is the crossing of the two appended strands of `T̃^{λ⁺}`, cast. -/
theorem mixedLastCross_eq :
    mixedLastCross k Q Λ Λc j hj ν ν₀ a b =
      castPlusStendhal Q Λ⁺ (plusWeight_assoc_mixed ν b a)
        (orderProjection Q Λ⁺ _ (StendhalAlgebraAllOrders.ψ (Multiset.card ρ))) := by
  change _ = castPlusStendhal Q Λ⁺ (plusWeight_assoc_mixed ν b a)
    (orderProjection Q Λ⁺ _ (StendhalAlgebraAllOrders.ofKLR k Q _ _ (KLRAlgebra.ψ _)))
  rw [castPlusStendhal_orderProjection, KLRAlgebra.castKLR_ψ]
  rfl

/-- **`Y` carries the diagrams with `b`, then `a` appended to those with `a`, then `b`
appended.** -/
theorem lastCross_mul_appendBlackPlus_mixed (W : StendhalAlgebra k Q Λ⁺ (ν + ν₀)) :
    mixedLastCross k Q Λ Λc j hj ν ν₀ a b * aBa (aBb W) =
      castPlusStendhal Q Λ⁺ (congrArg (· + ν₀) (mixedSwap ν a b))
          (appendBlackPlus Q Λ Λc j hj νa ν₀ b (appendBlackPlus Q Λ Λc j hj ν ν₀ a W)) *
        mixedLastCross k Q Λ Λc j hj ν ν₀ a b := by
  rw [mixedLastCross_eq, appendBlackPlus_mixed_cast ν b a, appendBlackPlus_mixed_cast ν a b,
    ← map_mul,
    orderProjection_ψ_mul_appendTwo, map_mul, castPlusStendhal_trans, castPlusStendhal_trans]

end Categorification.Stendhal.CupCap
