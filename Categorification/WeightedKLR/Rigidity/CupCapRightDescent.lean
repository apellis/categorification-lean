/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapRightBlock

/-!
# The block of the window and a black strand, on Stendhal diagrams

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.17 and Lemma 7.16. The diagrams of
`T̃^{(μ, μ*, i)}` on the block `[n, n + N]` below the cap generators at `s` and `n` are given by
`CupCap.blockStendhal`, the block map of the strand at `n` and the window. When the strand of `s`
at `n` is black of colour `i`, it sends the diagram of `T̃^{(μ, μ*)}` with a black strand adjoined
on the right to the same diagram on the window at `n` (`CupCap.blockStendhal_appendBlack`).

## Main results

* `CupCap.appendBlackAllOrders_ofKLR_eq`: appending the black strand on KLR diagrams.
* `CupCap.blockStendhal_appendBlack`: appending the black strand, then placing on the block.
* `CupCap.botMap_leftBlockMap_redOrdered_mul_append`: only red-ordered loadings of the block
  survive below the cap generators at `n`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)
  {j : ℕ} {hj : j ≤ ℓ} {ν ν₀ : Multiset I} (i : I)

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν₀)
local notation "Rc" => KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)
local notation "Ri" => KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 νᵢ)
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "E" s:max n:max hn:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s n hn)
local notation "bot" => botMap k Q Λ Λc j hj ν ν₀

/-! ### Red-ordered loadings ending with the new black strand -/

omit [DecidableEq I] in
theorem isRedOrdered_of_appendBlackLoading {t : Seq (stendhalWeight 2 ν₀)}
    (h : IsRedOrdered (appendBlackLoading i ν₀ t)) : IsRedOrdered t := by
  have hc := card_stendhalWeight_νᵢ (ν₀ := ν₀) i
  intro a b r r' hab ha hb
  have ha' := appendBlackLoading_lbl_of_lt i ν₀ t ⟨a.val, by omega⟩ a.2
  have hb' := appendBlackLoading_lbl_of_lt i ν₀ t ⟨b.val, by omega⟩ b.2
  refine h ⟨a.val, by omega⟩ ⟨b.val, by omega⟩ r r' hab (ha'.trans ha) (hb'.trans hb)

open Classical in
theorem redOrderedKLR_mul_e_appendBlackLoading (t : Seq (stendhalWeight 2 ν₀)) :
    redOrderedKLR k Q Λc νᵢ * KLRAlgebra.e (appendBlackLoading i ν₀ t) =
      if IsRedOrdered t then KLRAlgebra.e (appendBlackLoading i ν₀ t) else 0 := by
  classical
  change KLRAlgebra.eSum _ _ * _ = _
  rw [KLRAlgebra.eSum_mul_e]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (isRedOrdered_of_appendBlackLoading i h1) h2
  · exact absurd (appendBlackLoading_ordered i ν₀ t h2) h1
  · rfl

/-- The red-ordered loadings of `(μ, μ*, i)` ending with the new black strand are the appended
red-ordered loadings of `(μ, μ*)`. -/
theorem redOrderedKLR_mul_appendKLR_one :
    redOrderedKLR k Q Λc νᵢ * appendKLR ν₀ i Q Λc 1 =
      appendKLR ν₀ i Q Λc (redOrderedKLR k Q Λc ν₀) := by
  classical
  rw [← KLRAlgebra.sum_e (Q := stendhalQ Q Λc) (ν := stendhalWeight 2 ν₀), map_sum,
    Finset.mul_sum]
  simp_rw [appendKLR_e, redOrderedKLR_mul_e_appendBlackLoading]
  rw [redOrderedKLR, map_sum, Finset.sum_filter]
  simp_rw [appendKLR_e]

/-- On a KLR diagram, appending the black strand on the right is `appendKLR`. -/
theorem appendBlackAllOrders_ofKLR_eq (z : Rc) :
    (appendBlackAllOrders Q Λc i ν₀ (StendhalAlgebraAllOrders.ofKLR k Q Λc ν₀ z)).val =
      StendhalAlgebraAllOrders.ofKLR k Q Λc νᵢ (appendKLR ν₀ i Q Λc z) := by
  rw [appendBlackAllOrders_ofKLR_val, concat_tmul, map_one, Corner.val_one, Corner.val_mul_E]
  rfl

/-! ### The block map on appended diagrams -/

/-- **Adjoining the black strand on the right, then placing on the block**, is placing on the
window at `n`, when the strand of `s` at `n` is black of colour `i`. -/
theorem blockStendhal_appendBlack (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n + 1 ≤ m)
    (hs : s.lbl ⟨n, by omega⟩ = .inl i) (w : Rc) :
    blockStendhal Q Λ Λc j hj ν₀ i s n hn (appendBlackStendhal Q Λc i ν₀ (cupMap k Q Λc ν₀ w)) =
      bot (insertMap Q Λ Λc s n (by omega) w) := by
  rw [blockStendhal, stendhalLift_apply]
  change allOrdersLift _ (appendBlackAllOrders Q Λc i ν₀ (cupMap k Q Λc ν₀ w).val).val = _
  rw [cupMap, AlgHom.comp_apply, val_orderProjection_ofKLR, appendBlackAllOrders_ofKLR_eq,
    allOrdersLift_ofKLR, blockBot_apply, leftBlockMap_append i Q Λ Λc s hn hs, insertMap_mul,
    map_mul, botMap_insertMap_redOrderedKLR, ← map_mul, ← insertMap_one Q Λ Λc s (by omega),
    ← insertMap_mul, mul_one]

section Values

variable (s : Seq (stendhalWeight ℓ ν)) {n : ℕ}
  (hn : n + 1 ≤ Multiset.card (stendhalWeight ℓ ν))
  (hs : s.lbl ⟨n, by omega⟩ = .inl i)

include hn

local notation "θ" => blockStendhal Q Λ Λc j hj ν₀ i s n hn
local notation "lb" => leftBlockMap j hj i Q Λ Λc s n hn
local notation "RO" => redOrderedKLR k Q Λc ((Singleton.singleton i : Multiset I) + ν₀)

include hs in
theorem blockStendhal_appendBlack_one :
    θ (appendBlackStendhal Q Λc i ν₀ 1) = bot (E s n (Nat.le_of_succ_le hn)) := by
  have h := blockStendhal_appendBlack (j := j) (hj := hj) (ν₀ := ν₀) Q Λ Λc i s hn hs 1
  rwa [map_one, insertMap_one] at h

include hs in
theorem eSum_insertSet_mul_eSum_leftBlockSet :
    (E s n (Nat.le_of_succ_le hn) * KLRAlgebra.eSum _ (leftBlockSet j hj ν₀ i s n hn) : Rp) =
      E s n (Nat.le_of_succ_le hn) := by
  have h := KLR.Corner.val_mul_E (lb (appendKLR ν₀ i Q Λc 1))
  rwa [leftBlockMap_append_one (j := j) (hj := hj) (ν₀ := ν₀) i Q Λ Λc s hn hs] at h

include hs in
/-- **Only red-ordered loadings of the block survive** below the cap generators at `n`. -/
theorem botMap_leftBlockMap_redOrdered_mul_append :
    bot ((lb RO).val * E s n (Nat.le_of_succ_le hn)) = bot (E s n (Nat.le_of_succ_le hn)) := by
  have h : (lb (RO * appendKLR ν₀ i Q Λc 1)).val = (lb RO).val * E s n (Nat.le_of_succ_le hn) := by
    rw [map_mul, Corner.val_mul, leftBlockMap_append_one (j := j) (hj := hj) (ν₀ := ν₀) i Q Λ Λc
      s hn hs]
  rw [← h, redOrderedKLR_mul_appendKLR_one, leftBlockMap_append i Q Λ Λc s hn hs,
    botMap_insertMap_redOrderedKLR]

end Values

end Categorification.Stendhal.CupCap
