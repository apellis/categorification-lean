/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721Induced
import Categorification.WeightedKLR.Rigidity.CupCapMidLeftFreeMackey

/-!
# `𝔉_i` of the model, window by window

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21. Appending a black strand `i` at the right of the diagrams on the window at
position `n` of a loading `s` gives the diagrams on the window at position `n` of the appended
loading `s i` (`CupCap.appendBlackPlus_posStendhal`). So, for every `j`, the induced module
`L ⊗ e T̃^{λ⁺}` of the appended corner is the product over the loadings `s` of the staged modules
at the appended loadings `s i`, with the window at `midPos s` (`CupCap.appendPosPiEquiv`).

## Main definitions

* `CupCap.appendPosPiEquiv`: `L ⊗ (appended corner) ≅ ∏_s L ⊗ e_{s i, midPos s} T̃^{λ⁺}`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} {ν ν₀ : Multiset I}

local notation "Rc" => KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)

/-- The diagrams on a window are those of any KLR lift. -/
theorem posStendhal_eq_posBot {z : StendhalAlgebra k Q Λc ν₀} {x : Rc}
    (hx : StendhalAlgebraAllOrders.ofKLR k Q Λc ν₀ x = z.val) (s : Seq (stendhalWeight ℓ ν))
    {n : ℕ} (hn : n ≤ Multiset.card (stendhalWeight ℓ ν)) :
    posStendhal j hj Q Λ Λc ν₀ s n hn z = posBot j hj Q Λ Λc ν₀ s n hn x := by
  rw [posStendhal, stendhalLift_apply, ← hx, allOrdersLift_ofKLR]

variable (i : I)

local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)

/-- **Appending a black strand to the diagrams on a window**: the diagrams on the window at `n`
of `s`, with a black strand `i` appended at the right, are the diagrams on the window at `n` of
the appended loading `s i`. -/
theorem appendBlackPlus_posStendhal (s : Seq (stendhalWeight ℓ ν)) {n : ℕ}
    (hn : n ≤ Multiset.card (stendhalWeight ℓ ν)) (hn' : n ≤ Multiset.card (stendhalWeight ℓ νᵢ))
    (z : StendhalAlgebra k Q Λc ν₀) :
    appendBlackPlus Q Λ Λc j hj ν ν₀ i (posStendhal j hj Q Λ Λc ν₀ s n hn z) =
      posStendhal j hj Q Λ Λc ν₀ (appendBlackLoading i ν s) n hn' z := by
  obtain ⟨x, hx⟩ := StendhalAlgebraAllOrders.ofKLR_surjective z.val
  rw [posStendhal_eq_posBot hx, posStendhal_eq_posBot hx, posBot_apply, posBot_apply,
    appendBlackPlus_botMap, appendPlus_insertMap]

theorem appendBlackPlusOp_posOp (s : Seq (stendhalWeight ℓ ν)) {n : ℕ}
    (hn : n ≤ Multiset.card (stendhalWeight ℓ ν)) (hn' : n ≤ Multiset.card (stendhalWeight ℓ νᵢ))
    (a : (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ) :
    appendBlackPlusOp Q Λ Λc j hj ν ν₀ i (posOp j hj Q Λ Λc ν₀ s n hn a) =
      posOp j hj Q Λ Λc ν₀ (appendBlackLoading i ν s) n hn' a := by
  rw [posOp_apply, posOp_apply, appendBlackPlusOp_op, appendBlackPlus_posStendhal]

/-- The appended corner is the sum of the windows at `midPos s` of the appended loadings. -/
theorem appendMidOp_eq_sum_posOp (a : (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ) :
    appendMidOp Q Λ Λc j hj ν ν₀ i a =
      ∑ s, posOp j hj Q Λ Λc ν₀ (appendBlackLoading i ν s) (midPos j s)
        (midPos_le_appendBlackLoading j ν i s) a := by
  change appendBlackPlusOp Q Λ Λc j hj ν ν₀ i (midOp j hj Q Λ Λc ν ν₀ a) = _
  rw [midOp_eq_sum_posOp, map_sum]
  exact Finset.sum_congr rfl fun s _ => appendBlackPlusOp_posOp i s _ _ a

/-- The windows at `midPos s` of distinct appended loadings are orthogonal. -/
theorem posOp_appendBlackLoading_mul_of_ne {s s' : Seq (stendhalWeight ℓ ν)} (h : s ≠ s')
    (a a' : (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ) :
    posOp j hj Q Λ Λc ν₀ (appendBlackLoading i ν s) (midPos j s)
        (midPos_le_appendBlackLoading j ν i s) a *
      posOp j hj Q Λ Λc ν₀ (appendBlackLoading i ν s') (midPos j s')
        (midPos_le_appendBlackLoading j ν i s') a' = 0 := by
  rw [← appendBlackPlusOp_posOp i s (midPos_le j s),
    ← appendBlackPlusOp_posOp i s' (midPos_le j s'),
    ← map_mul, posOp_mul_posOp_of_ne h, map_zero]

variable (L : Type*) [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

/-- **`𝔉_i` of the model, window by window** (arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21): the induced module of the appended corner is the product, over the loadings
`s`, of the staged modules of the appended loadings `s i` with the window at `midPos s`. -/
def appendPosPiEquiv :
    Ind L (appendMidOp Q Λ Λc j hj ν ν₀ i) ≃ₗ[(StendhalAlgebra k Q (plusLabels Λ Λc j hj)
        (νᵢ + ν₀))ᵐᵒᵖ]
      ((s : Seq (stendhalWeight ℓ ν)) →
        PosModel j hj Q Λ Λc ν₀ (appendBlackLoading i ν s) (midPos j s)
          (midPos_le_appendBlackLoading j ν i s) L) :=
  Ind.piEquivOfOrthogonal L (appendMidOp_eq_sum_posOp i)
    fun _ _ a a' h => posOp_appendBlackLoading_mul_of_ne i h a a'

theorem appendPosPiEquiv_tmul (z : Corner (appendMidOp Q Λ Λc j hj ν ν₀ i)) (v : L)
    (s : Seq (stendhalWeight ℓ ν)) :
    appendPosPiEquiv i L (Ind.tmul z v) s =
      Ind.tmul (cornerMul (intertwines_of_orthogonal_proj (appendMidOp_eq_sum_posOp i)
        (fun _ _ a a' h => posOp_appendBlackLoading_mul_of_ne i h a a') s) z) v := rfl

end Categorification.Stendhal.CupCap
