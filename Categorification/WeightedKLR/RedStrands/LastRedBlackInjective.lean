/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LastRedBlackViolated
import Categorification.WeightedKLR.RedStrands.StendhalDotInjective
import Categorification.WeightedKLR.RedStrands.AddRedInjective

/-!
# Injectivity of the bimodule map of Proposition 4.32

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §4.6,
Proposition 4.32. The map `g ↦ appendRed(g) · crossingStendhalCut` is injective on
`T̃_{i+ν} ν_i(1)`: composing with a second crossing of the black strand `i` and the last red
strand gives the bigon, which is `x^{⟨α_i^∨, λ_ℓ⟩}` on the black strand (relation (4.2),
`ψ_sq_black_red`). Dots on a black strand act injectively (`eq_zero_of_mul_e_mul_x_pow`), and
appending a red strand is injective (`appendRedStendhalValue_injective`). With the transfer of
the violating ideal (`lastRedBlackMap_eq_zero`) the map `lastRedBlackMap` of Proposition 4.32 is
injective on `T_{i+ν} ν_i(1)`.

## Main results

* `lastRedBlackStendhal_eq_zero`: `lastRedBlackStendhal g = 0` implies `g · ν_i(1) = 0`.
* `lastRedBlackMap_eq_zero_iff`: `lastRedBlackMap g = 0` if and only if `g · ν_i(1) = 0`.

## Hypotheses

The crossing polynomials are those of Webster's §2.2 (`IsRouquierQ`), as in
`appendRedStendhalValue_injective` and `linearIndependent_stendhalTerm_of_rouquier`.
-/

noncomputable section

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA Equiv

variable {I : Type} {ℓ : ℕ} [DecidableEq I] {k : Type*} [CommRing k]
  {C : QuantumGroup.CartanDatum I}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I) (ν : Multiset I)
  (hQ : IsRouquierQ C Q)

local notation "Λ₀" => (Λ ∘ Fin.castSucc)
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "μ" => stendhalWeight ℓ ν
local notation "N₀" => Multiset.card (stendhalWeight ℓ ν)
local notation "A" => StendhalAlgebraAllOrders k Q Λ νᵢ
local notation "S₀" => StendhalAlgebra k Q Λ₀ ν
local notation "S" => StendhalAlgebra k Q Λ νᵢ
local notation "ψ₀" => (StendhalAlgebraAllOrders.ψ N₀ : A)

omit [DecidableEq I] in
theorem isRedOrdered_blackRedLoading (s : Seq μ) (hs : IsRedOrdered s) :
    IsRedOrdered (blackRedLoading (ℓ := ℓ) i ν s) :=
  (appendRedLoading_ordered_iff _).2 (appendBlackLoading_ordered i ν s hs)

omit [DecidableEq I] in
private theorem lt_card : N₀ + 1 < Multiset.card (stendhalWeight (ℓ + 1) νᵢ) := by
  rw [card_stendhalWeight_append]; omega

/-- The bigon of the black strand `i` and the last red strand, below a red-ordered diagram. -/
theorem crossingStendhalCut_val_mul_ψ_mul_e (s : Seq μ) (hs : IsRedOrdered s) :
    (crossingStendhalCut Q Λ i ν).val * ψ₀ *
        StendhalAlgebraAllOrders.e (blackRedLoading i ν s) =
      StendhalAlgebraAllOrders.e (blackRedLoading i ν s) *
        StendhalAlgebraAllOrders.x ⟨N₀, Nat.lt_of_succ_lt (lt_card (ℓ := ℓ) i ν)⟩ ^
          Λ (Fin.last ℓ) i := by
  have hψ : ψ₀ * StendhalAlgebraAllOrders.e (blackRedLoading i ν s) =
      StendhalAlgebraAllOrders.e (redBlackLoading i ν s) * ψ₀ := by
    rw [StendhalAlgebraAllOrders.ψ_mul_e, swap_blackRedLoading]
  have hrb : redBlackValue Q Λ i ν (1 : S₀).val *
      StendhalAlgebraAllOrders.e (redBlackLoading i ν s) =
      StendhalAlgebraAllOrders.e (redBlackLoading i ν s) := by
    have h1 : (1 : S₀).val * StendhalAlgebraAllOrders.e s = StendhalAlgebraAllOrders.e s := by
      change (1 : S₀).val * (StendhalAlgebra.e s hs).val = (StendhalAlgebra.e s hs).val
      rw [← KLR.Corner.val_mul, one_mul]
    rw [← redBlackValue_e, ← redBlackValue_mul, h1]
  have hbig := StendhalAlgebraAllOrders.ψ_sq_black_red (Q := Q) (Λ := Λ) N₀ (lt_card i ν)
    (blackRedLoading i ν s) i (Fin.last ℓ) (blackRedLoading_lbl_of_eq s _ rfl)
    (blackRedLoading_lbl_of_last s _ rfl)
  have hc : Commute (StendhalAlgebraAllOrders.x ⟨N₀, Nat.lt_of_succ_lt (lt_card (ℓ := ℓ) i ν)⟩ ^
      Λ (Fin.last ℓ) i : A)
      (StendhalAlgebraAllOrders.e (blackRedLoading i ν s)) := by
    refine Commute.pow_left ?_ _
    change StendhalAlgebraAllOrders.ofKLR k Q Λ νᵢ _ * StendhalAlgebraAllOrders.ofKLR k Q Λ νᵢ _ =
      StendhalAlgebraAllOrders.ofKLR k Q Λ νᵢ _ * StendhalAlgebraAllOrders.ofKLR k Q Λ νᵢ _
    rw [← map_mul, ← map_mul, KLRAlgebra.x_mul_e]
  rw [crossingStendhalCut_val, mul_assoc, mul_assoc, hψ, ← mul_assoc (redBlackValue _ _ _ _ _),
    hrb, ← hψ, ← mul_assoc, hbig, hc.eq]

include hQ in
/-- **Injectivity in Proposition 4.32 before the violating quotient** (Webster,
arXiv:1309.3796v3): `lastRedBlackStendhal g = 0` implies `g · ν_i(1) = 0`. -/
theorem lastRedBlackStendhal_eq_zero (g : StendhalAlgebra k Q Λ₀ νᵢ)
    (hg : lastRedBlackStendhal Q Λ i ν g = 0) : g * appendBlackStendhal Q Λ₀ i ν 1 = 0 := by
  classical
  have hinj := appendRedStendhalValue_injective Q Λ νᵢ hQ
  set R := appendRedStendhalValue Q Λ νᵢ g with hR
  -- `R · e(s, i, λ_ℓ) = 0` for every red-ordered `s`.
  have hs0 : ∀ (s : Seq μ) (hs : IsRedOrdered s),
      R.val * StendhalAlgebraAllOrders.e (blackRedLoading i ν s) = 0 := by
    intro s hs
    have hρ : ∀ w : Perm (Fin (Multiset.card (stendhalWeight (ℓ + 1) νᵢ))),
        IsReduced _ (canWord _ w) ∧ wordProd _ (canWord _ w) = w :=
      fun w => ⟨isReduced_canWord _ w, wordProd_canWord _ w⟩
    refine eq_zero_of_mul_e_mul_x_pow (Q := Q) (Λ := Λ) (ν := νᵢ) hρ
      (linearIndependent_stendhalTerm_of_rouquier Q νᵢ Λ hQ hρ) _
      (isRedOrdered_blackRedLoading i ν s hs) ⟨N₀, Nat.lt_of_succ_lt (lt_card (ℓ := ℓ) i ν)⟩ ?_
      (Λ (Fin.last ℓ) i) R ?_
    · change ((blackRedLoading i ν s).lbl _).isLeft = true
      rw [blackRedLoading_lbl_of_eq s _ rfl]; rfl
    · have h := congrArg (fun z : S => z.val * ψ₀ *
        StendhalAlgebraAllOrders.e (blackRedLoading i ν s)) hg
      simp only [lastRedBlackStendhal_apply] at h
      rw [KLR.Corner.val_mul, mul_assoc R.val, mul_assoc R.val,
        crossingStendhalCut_val_mul_ψ_mul_e Q Λ i ν s hs] at h
      rw [mul_assoc, h]
      change (0 : A) * _ * _ = 0
      rw [zero_mul, zero_mul]
  -- Sum over the red-ordered `s`.
  apply hinj
  rw [map_zero]
  apply Subtype.ext
  have hsum : ∀ F : Finset (Seq μ), blackRedValue Q Λ i ν
      (∑ s ∈ F, StendhalAlgebraAllOrders.e s) =
        ∑ s ∈ F, StendhalAlgebraAllOrders.e (blackRedLoading i ν s) := by
    intro F
    induction F using Finset.induction_on with
    | empty => rw [Finset.sum_empty, Finset.sum_empty, blackRedValue_zero]
    | insert a F ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, blackRedValue_add, ih, blackRedValue_e]
  rw [map_mul, KLR.Corner.val_mul]
  change R.val * (blackRedStendhal Q Λ i ν 1).val = (0 : A)
  rw [blackRedStendhal_val]
  change R.val * blackRedValue Q Λ i ν (StendhalAlgebraAllOrders.redOrderedIdem k Q Λ₀ ν) = 0
  unfold StendhalAlgebraAllOrders.redOrderedIdem
  rw [hsum, Finset.mul_sum]
  exact Finset.sum_eq_zero fun s hs => hs0 s (Finset.mem_filter.1 hs).2

include hQ in
/-- **Injectivity in Webster's Proposition 4.32** (arXiv:1309.3796v3): on `T_{i+ν} ν_i(1)`, the
map `g ↦ appendRed(g) · (crossing)` of `lastRedBlackMap` is injective. -/
theorem lastRedBlackMap_eq_zero_iff (g : TensorProductAlgebra k Q Λ₀ νᵢ) :
    lastRedBlackMap Q Λ i ν g = 0 ↔ g * appendBlack Q Λ₀ i ν 1 = 0 := by
  refine ⟨lastRedBlackMap_eq_zero Q Λ i ν (lastRedBlackStendhal_eq_zero Q Λ i ν hQ) g,
    fun h => ?_⟩
  rw [← lastRedBlackMap_mul_appendBlack_lastRedIdem, ← appendRed_one_val,
    ← lastRedBlackMap_mul_appendBlack, h, map_zero]

end Categorification.Stendhal
