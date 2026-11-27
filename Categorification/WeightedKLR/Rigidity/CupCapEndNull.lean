/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapEndModel

/-!
# Diagrams in which a strand leaves the cap vanish in the model

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.17, in the case `j = ℓ`. Let `L` be a right
`T̃^{(μ,μ*)}`-module on which the idempotents of the loadings not of the form `μ ⋯ μ*` act by zero.
A diagram of `λ⁺` in which a strand at the maximum of the cap (on the last `N` strands) leaves the
window at the top factors through such an idempotent, so it gives zero in the model
`Y = L ⊗ e T̃^{λ⁺}` (`CupCap.exitSpan_mem_nullIdeal`).

## Main results

* `CupCap.commute_endStendhal_one_endBot`: the unit of the end block commutes with its diagrams.
* `CupCap.smul_eq_zero_of_mem_capNull`: the ideal `capNull` acts by zero on `L`.
* `CupCap.exitSpan_mem_nullIdeal`: the exit diagrams at the end lie in the null ideal of `Y`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)
  {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc ℓ le_rfl)) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "ι" => insertMap (j := ℓ) (hj := le_rfl) (ν₀ := ν₀) Q Λ Λc
local notation "E" s:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc ℓ le_rfl))
    (insertSet (j := ℓ) (hj := le_rfl) (ν₀ := ν₀) s m le_rfl)

theorem endBot_eq_allOrdersLift (x : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) :
    endBot Q Λ Λc ν ν₀ x =
      allOrdersLift (redRelations_endBot Q Λ Λc) (StendhalAlgebraAllOrders.ofKLR k Q Λc ν₀ x) :=
  (allOrdersLift_ofKLR _ x).symm

/-- **The unit of the end block commutes with its diagrams**: red strands do not cross, so every
diagram preserves the order of the red strands. -/
theorem commute_endStendhal_one_endBot (x : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) :
    Commute (endStendhal Q Λ Λc ν ν₀ 1) (endBot Q Λ Λc ν ν₀ x) := by
  have h1 : endStendhal Q Λ Λc ν ν₀ 1 = allOrdersLift (redRelations_endBot Q Λ Λc)
      (StendhalAlgebraAllOrders.redOrderedIdem k Q Λc ν₀) := rfl
  rw [Commute, SemiconjBy, h1, endBot_eq_allOrdersLift, ← map_mul, ← map_mul,
    (redOrderedIdem_commute Q Λc ν₀ _).eq]

theorem endStendhal_cupMap' (x : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) :
    endStendhal Q Λ Λc ν ν₀ (cupMap k Q Λc ν₀ x) =
      endStendhal Q Λ Λc ν ν₀ 1 * endBot Q Λ Λc ν ν₀ x := by
  rw [endStendhal_cupMap, (commute_endStendhal_one_endBot Q Λ Λc x).eq]

/-- A diagram at the maximum below the cap generators at `s` is the end diagram cut by `E_s`. -/
theorem endBot_mul_botMap_eSum (s : Seq (stendhalWeight ℓ ν))
    (x : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) :
    endBot Q Λ Λc ν ν₀ x * botMap k Q Λ Λc ℓ le_rfl ν ν₀ (E s) =
      botMap k Q Λ Λc ℓ le_rfl ν ν₀ (ι s m le_rfl x) := by
  rw [endBot_apply, ← map_mul, endMapKLR_eq_sum, Finset.sum_mul]
  congr 1
  rw [Finset.sum_eq_single s]
  · rw [← insertMap_one Q Λ Λc s le_rfl, ← insertMap_mul, mul_one]
  · intro s' _ hs'
    have hι : insertMap (j := ℓ) (hj := le_rfl) Q Λ Λc s' m le_rfl x =
        insertMap Q Λ Λc s' m le_rfl x * E s' := by
      rw [← insertMap_one Q Λ Λc s' le_rfl, ← insertMap_mul, mul_one]
    rw [hι, mul_assoc, KLRAlgebra.eSum_mul_eSum]
    convert mul_zero _
    convert KLRAlgebra.eSum_empty (Q := stendhalQ Q (plusLabels Λ Λc ℓ le_rfl))
    refine Finset.eq_empty_of_forall_notMem fun u hu => ?_
    obtain ⟨hu1, hu2⟩ := Finset.mem_inter.1 hu
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hu1
    exact hs' ((insertSeq_mem_insertSet (s := s') (s' := s) (t := t)).1 hu2).symm
  · intro h; exact absurd (Finset.mem_univ s) h

variable {Q Λc} in
/-- **The ideal `capNull` acts by zero** on a module on which the idempotents of the loadings not
of the form `μ ⋯ μ*` act by zero. -/
theorem smul_eq_zero_of_mem_capNull {L : Type*} [AddCommGroup L]
    [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    {z : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)}
    (hz : z ∈ capNull (k := k) Q Λc ν₀) (v : L) : op (cupMap k Q Λc ν₀ z) • v = 0 := by
  induction hz using TwoSidedIdeal.span_induction generalizing v with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    exact hL w v hw
  | zero => rw [map_zero, op_zero]; exact zero_smul (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ v
  | add x y _ _ hx hy => rw [map_add, op_add, add_smul, hx, hy, add_zero]
  | neg x _ hx => rw [map_neg, op_neg, neg_smul, hx, neg_zero]
  | left_absorb a x _ hx => rw [map_mul, op_mul, mul_smul, hx]
  | right_absorb b x _ hx => rw [map_mul, op_mul, mul_smul, hx, smul_zero]

variable (L : Type*) [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

/-- **Exit diagrams vanish in the model**: a diagram of `λ⁺` in which a strand at the maximum
leaves the window `[m, m + N)` at the top, below the unit of the end block, lies in the null ideal
of the induced module. -/
theorem exitSpan_mem_nullIdeal
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (s : Seq (stendhalWeight ℓ ν)) {y : Rp}
    (hy : y ∈ exitSpan Q Λ Λc ℓ le_rfl s m le_rfl) :
    op (endStendhal Q Λ Λc ν ν₀ 1 * botMap k Q Λ Λc ℓ le_rfl ν ν₀ y) ∈
      nullIdeal L (endOp Q Λ Λc ν ν₀) := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨z, hz, r, rfl⟩ := hy
    have h : endStendhal Q Λ Λc ν ν₀ 1 * botMap k Q Λ Λc ℓ le_rfl ν ν₀ (ι s m le_rfl z * r) =
        endStendhal Q Λ Λc ν ν₀ (cupMap k Q Λc ν₀ z) *
          botMap k Q Λ Λc ℓ le_rfl ν ν₀ (E s * r) := by
      rw [endStendhal_cupMap', map_mul, map_mul, ← endBot_mul_botMap_eSum]
      simp only [mul_assoc]
    rw [h, op_mul]
    exact mul_map_mem_nullIdeal _ (b := op (cupMap k Q Λc ν₀ z))
      (smul_eq_zero_of_mem_capNull hL hz)
  | zero => rw [map_zero, mul_zero, op_zero]; exact zero_mem _
  | add y y' _ _ h h' => rw [map_add, mul_add, op_add]; exact add_mem h h'
  | smul c y _ h =>
    rw [map_smul, mul_smul_comm, op_smul]
    exact Submodule.smul_of_tower_mem _ c h

end Categorification.Stendhal.CupCap
