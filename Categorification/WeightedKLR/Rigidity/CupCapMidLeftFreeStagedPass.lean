/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapMidLeftFreeStaged
import Categorification.WeightedKLR.Rigidity.CupCapSlidingLeft
import Categorification.WeightedKLR.Rigidity.CupCapEndNull

/-!
# Moving the maximum past one strand of a loading

Webster, arXiv:1309.3796v3, §7.3, toward the left projectivity of `coe^{λ⁺}_λ` asserted after
Lemma 7.19 (staged transparency, step (I1) of the route). For `L` supported on the cap-good
loadings, the strand at position `q` of `s` passing under the window from its right to its left
(`underRight N q`) defines a map of right `T̃^{λ⁺}`-modules
`L ⊗ e_{s,q} T̃^{λ⁺} → L ⊗ e_{s,q+1} T̃^{λ⁺}` (`posPassRight`), and passing back under it from
its left to its right (`underLeft N q`) a map in the other direction (`posPassLeft`). They are
well defined because the diagrams of `T̃^{(μ,μ*)}` slide through the passage up to exit diagrams,
which act by zero (`exitSpan_mem_nullIdeal_pos`).

## Main definitions

* `CupCap.posPassRight`, `CupCap.posPassLeft`: the passages of the strand at `q` under the window.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "Rc" => KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
local notation "bot" => botMap k Q Λ Λc j hj ν ν₀
local notation "ι" => insertMap (j := j) (hj := hj) (ν₀ := ν₀) Q Λ Λc
local notation "E" s:max n:max hn:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s n hn)

/-- The unit of the window at position `n` of `s` is the window idempotent. -/
theorem posStendhal_one (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m) :
    posStendhal j hj Q Λ Λc ν₀ s n hn 1 = bot (E s n hn) := by
  have h1 : posStendhal j hj Q Λ Λc ν₀ s n hn 1 =
      allOrdersLift (redRelations_posBot (j := j) (hj := hj) (Q := Q) (Λ := Λ) (Λc := Λc)
        (ν₀ := ν₀) s hn) (StendhalAlgebraAllOrders.redOrderedIdem k Q Λc ν₀) := rfl
  rw [h1, ← botMap_insertMap_redOrderedKLR, ← posBot_apply,
    ← allOrdersLift_ofKLR (redRelations_posBot (j := j) (hj := hj) (Q := Q) (Λ := Λ) (Λc := Λc)
      (ν₀ := ν₀) s hn), ofKLR_redOrderedKLR]

/-- On the image of a KLR diagram, the window map is the diagram inserted at the window. -/
theorem posStendhal_cupMap' (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m) (x : Rc) :
    posStendhal j hj Q Λ Λc ν₀ s n hn (cupMap k Q Λc ν₀ x) = bot (ι s n hn x) := by
  rw [posStendhal_cupMap, posStendhal_one, posBot_apply, ← map_mul, insertMap_mul_eSum]

variable (L : Type*) [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

/-- **Exit diagrams vanish** in the induced module with the window at position `n` of `s`. -/
theorem exitSpan_mem_nullIdeal_pos
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m) {y : Rp}
    (hy : y ∈ exitSpan Q Λ Λc j hj s n hn) :
    op (bot y) ∈ nullIdeal L (posOp j hj Q Λ Λc ν₀ s n hn) := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨z, hz, r, rfl⟩ := hy
    have h : bot (ι s n hn z * r) = posStendhal j hj Q Λ Λc ν₀ s n hn (cupMap k Q Λc ν₀ z) *
        bot r := by
      rw [posStendhal_cupMap', map_mul]
    rw [h, op_mul]
    exact mul_map_mem_nullIdeal _ (b := op (cupMap k Q Λc ν₀ z))
      (smul_eq_zero_of_mem_capNull hL hz)
  | zero => rw [map_zero, op_zero]; exact zero_mem _
  | add y y' _ _ hy hy' => rw [map_add, op_add]; exact add_mem hy hy'
  | smul c y _ hy =>
    rw [map_smul, op_smul]
    exact Submodule.smul_of_tower_mem _ c hy

variable {L}

variable (j hj Q Λ Λc ν₀) in
/-- The strand at `q` passing under the window from its right to its left, cut by the window
idempotent at `q + 1`. -/
def posPassRightElt (s : Seq (stendhalWeight ℓ ν)) (q : ℕ) (hq : q + 1 ≤ m) : Tpᵐᵒᵖ :=
  op (bot (E s (q + 1) hq * underRight N q))

theorem intertwinesOn_posPassRightElt
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (s : Seq (stendhalWeight ℓ ν)) {q : ℕ} (hq : q + 1 ≤ m) :
    IntertwinesOn L (posOp j hj Q Λ Λc ν₀ s q (by omega)) (posOp j hj Q Λ Λc ν₀ s (q + 1) hq)
      (posPassRightElt j hj Q Λ Λc ν₀ s q hq) where
  unit := by
    change op (bot (E s (q + 1) hq * underRight N q)) *
      op (posStendhal j hj Q Λ Λc ν₀ s (q + 1) hq 1) = op (bot (E s (q + 1) hq * underRight N q))
    rw [← op_mul, posStendhal_one, ← map_mul, ← mul_assoc,
      (KLRAlgebra.eSum_idem _).eq]
  slide a z v := by
    refine IntertwinesOn.slide_of_mem_nullIdeal _ ?_ z v
    obtain ⟨w, hw⟩ := cupMap_surjective Q Λc a.unop
    obtain rfl : a = op (cupMap k Q Λc ν₀ w) := by rw [hw, op_unop]
    have hD := slides (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) s hq w
    unfold Slides at hD
    have key : posOp j hj Q Λ Λc ν₀ s q (by omega) (op (cupMap k Q Λc ν₀ w)) *
          posPassRightElt j hj Q Λ Λc ν₀ s q hq -
        posPassRightElt j hj Q Λ Λc ν₀ s q hq *
          posOp j hj Q Λ Λc ν₀ s (q + 1) hq (op (cupMap k Q Λc ν₀ w)) =
        op (bot (-(ι s (q + 1) hq w * underRight N q - underRight N q * ι s q (by omega) w))) := by
      change op (posStendhal j hj Q Λ Λc ν₀ s q _ (cupMap k Q Λc ν₀ w)) *
          op (bot (E s (q + 1) hq * underRight N q)) -
        op (bot (E s (q + 1) hq * underRight N q)) *
          op (posStendhal j hj Q Λ Λc ν₀ s (q + 1) hq (cupMap k Q Λc ν₀ w)) = _
      rw [posStendhal_cupMap', posStendhal_cupMap', ← op_mul, ← op_mul, ← op_sub, ← map_mul,
        ← map_mul, ← map_sub, ← eSum_mul_slidesDiff (Q := Q) (Λ := Λ) (Λc := Λc) s hq w]
      congr 2
      simp only [mul_sub, neg_sub, ← mul_assoc, insertMap_mul_eSum, eSum_mul_insertMap]
    rw [key]
    exact exitSpan_mem_nullIdeal_pos L hL s hq (neg_mem hD)

variable (L) in
/-- **The strand at `q` passing under the window from its right to its left**:
`L ⊗ e_{s,q} T̃^{λ⁺} → L ⊗ e_{s,q+1} T̃^{λ⁺}`. -/
def posPassRight
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (s : Seq (stendhalWeight ℓ ν)) (q : ℕ) (hq : q + 1 ≤ m) :
    PosModel j hj Q Λ Λc ν₀ s q (by omega) L →ₗ[Tpᵐᵒᵖ] PosModel j hj Q Λ Λc ν₀ s (q + 1) hq L :=
  natMapOn (intertwinesOn_posPassRightElt hL s hq)

variable (j hj Q Λ Λc ν₀) in
/-- The strand at `q` passing under the window from its left to its right, cut by the window
idempotent at `q`. -/
def posPassLeftElt (s : Seq (stendhalWeight ℓ ν)) (q : ℕ) (hq : q + 1 ≤ m) : Tpᵐᵒᵖ :=
  op (bot (E s q (Nat.le_of_succ_le hq) * underLeft N q))

theorem intertwinesOn_posPassLeftElt
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (s : Seq (stendhalWeight ℓ ν)) {q : ℕ} (hq : q + 1 ≤ m) :
    IntertwinesOn L (posOp j hj Q Λ Λc ν₀ s (q + 1) hq)
      (posOp j hj Q Λ Λc ν₀ s q (Nat.le_of_succ_le hq))
      (posPassLeftElt j hj Q Λ Λc ν₀ s q hq) where
  unit := by
    change op (bot (E s q (Nat.le_of_succ_le hq) * underLeft N q)) *
      op (posStendhal j hj Q Λ Λc ν₀ s q (Nat.le_of_succ_le hq) 1) =
        op (bot (E s q (Nat.le_of_succ_le hq) * underLeft N q))
    rw [← op_mul, posStendhal_one, ← map_mul, ← mul_assoc, (KLRAlgebra.eSum_idem _).eq]
  slide a z v := by
    refine IntertwinesOn.slide_of_mem_nullIdeal _ ?_ z v
    obtain ⟨w, hw⟩ := cupMap_surjective Q Λc a.unop
    obtain rfl : a = op (cupMap k Q Λc ν₀ w) := by rw [hw, op_unop]
    have hD := slidesLeft (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) s hq w
    unfold SlidesLeft at hD
    have key : posOp j hj Q Λ Λc ν₀ s (q + 1) hq (op (cupMap k Q Λc ν₀ w)) *
          posPassLeftElt j hj Q Λ Λc ν₀ s q hq -
        posPassLeftElt j hj Q Λ Λc ν₀ s q hq *
          posOp j hj Q Λ Λc ν₀ s q (Nat.le_of_succ_le hq) (op (cupMap k Q Λc ν₀ w)) =
        op (bot (-(ι s q (Nat.le_of_succ_le hq) w * underLeft N q -
          underLeft N q * ι s (q + 1) hq w))) := by
      change op (posStendhal j hj Q Λ Λc ν₀ s (q + 1) hq (cupMap k Q Λc ν₀ w)) *
          op (bot (E s q (Nat.le_of_succ_le hq) * underLeft N q)) -
        op (bot (E s q (Nat.le_of_succ_le hq) * underLeft N q)) *
          op (posStendhal j hj Q Λ Λc ν₀ s q (Nat.le_of_succ_le hq) (cupMap k Q Λc ν₀ w)) = _
      rw [posStendhal_cupMap', posStendhal_cupMap', ← op_mul, ← op_mul, ← op_sub, ← map_mul,
        ← map_mul, ← map_sub, ← eSum_mul_slidesLeftDiff (Q := Q) (Λ := Λ) (Λc := Λc) s hq w]
      congr 2
      simp only [mul_sub, neg_sub, ← mul_assoc, insertMap_mul_eSum, eSum_mul_insertMap]
    rw [key]
    exact exitSpan_mem_nullIdeal_pos L hL s _ (neg_mem hD)

variable (L) in
/-- **The strand at `q` passing under the window from its left to its right**:
`L ⊗ e_{s,q+1} T̃^{λ⁺} → L ⊗ e_{s,q} T̃^{λ⁺}`. -/
def posPassLeft
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (s : Seq (stendhalWeight ℓ ν)) (q : ℕ) (hq : q + 1 ≤ m) :
    PosModel j hj Q Λ Λc ν₀ s (q + 1) hq L →ₗ[Tpᵐᵒᵖ]
      PosModel j hj Q Λ Λc ν₀ s q (Nat.le_of_succ_le hq) L :=
  natMapOn (intertwinesOn_posPassLeftElt hL s hq)

end Categorification.Stendhal.CupCap
