/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FrontWindow

/-!
# The strands at the maximum at the left end, on `T̃`

Webster, arXiv:1309.3796v3, proof of Lemma 7.19, the block decomposition (B3) with the black
block at the right end. The two block embeddings of `CupCap.frontMapKLR` (a diagram at the
maximum on the first `N` strands) and `CupCap.suffixMapKLR` (a diagram of `λ` on the last `m`
strands) kill the dots on red strands and the crossings of two red strands, so they descend to
maps `T̃^{(μ,μ*)} → T̃^{λ⁺}` (`CupCap.frontStendhal`) and `T̃^λ → T̃^{λ⁺}`
(`CupCap.suffixStendhal`), for the red strands `(μ, μ*)` inserted before those of `λ`. Their
images commute (`CupCap.commute_suffixStendhal_frontStendhal`). This is the mirror of
`CupCap.prefixStendhal` and `CupCap.endStendhal`.

## Main definitions

* `CupCap.frontStendhal`, `CupCap.suffixStendhal`: the two blocks on `T̃`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section FrontDescent

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)
  {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "z₀" => Nat.zero_le ℓ
local notation "zm" => Nat.zero_le (Multiset.card (stendhalWeight ℓ ν))
local notation "σ₀" => Multiset.map (cupColour (I := I) 0 (Nat.zero_le ℓ)) (stendhalWeight 2 ν₀)
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc 0 (Nat.zero_le ℓ))) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc 0 (Nat.zero_le ℓ)) (ν + ν₀)
local notation "β" => botMap k Q Λ Λc 0 (Nat.zero_le ℓ) ν ν₀

/-! ### The strands at the maximum on the first `N` strands -/

variable (ν ν₀) in
/-- The diagrams at the maximum on the first `N` strands of `λ⁺`, in `T̃^{λ⁺}`, before
descending. -/
def frontBot : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀) →ₙₐ[k] Tp where
  toFun x := β (frontMapKLR Q Λ Λc ν ν₀ x)
  map_zero' := by rw [frontMapKLR_zero, map_zero]
  map_add' a b := by rw [frontMapKLR_add, map_add]
  map_mul' a b := by rw [frontMapKLR_mul, map_mul]
  map_smul' c a := by
    change β (frontMapKLR Q Λ Λc ν ν₀ (c • a)) = c • β (frontMapKLR Q Λ Λc ν ν₀ a)
    rw [frontMapKLR_smul, map_smul]

theorem frontBot_apply (x : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) :
    frontBot Q Λ Λc ν ν₀ x = β (frontMapKLR Q Λ Λc ν ν₀ x) := rfl

theorem redRelations_frontBot : RedRelations (frontBot Q Λ Λc ν ν₀) where
  red_dot b w hb := by
    rw [frontBot_apply, frontMapKLR_eq_sum, map_sum]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [insertMap_mul, insertMap_x, insertMap_e, mul_assoc, eSum_mul_e_insertSeq, botMap,
      AlgHom.comp_apply, map_mul]
    change orderProjection _ _ _ (StendhalAlgebraAllOrders.x _ * StendhalAlgebraAllOrders.e _) = 0
    rw [StendhalAlgebraAllOrders.x_mul_e_of_red, map_zero]
    rw [insertSeq_lbl_win s zm _ ⟨b.val, by rw [Multiset.card_map]; exact b.2⟩ rfl,
      Seq.map_lbl]
    obtain ⟨r, hr⟩ : ∃ r, w.lbl b = .inr r := by cases h : w.lbl b <;> simp_all
    exact (congrArg (fun a => (cupColour (I := I) 0 z₀ a).isRight) hr).trans rfl
  red_cross p hp w ha hb := by
    rw [frontBot_apply, frontMapKLR_eq_sum, map_sum]
    refine Finset.sum_eq_zero fun s _ => ?_
    have hM := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
    rw [insertMap_mul, insertMap_ψ s zm hp, insertMap_e, mul_assoc, eSum_mul_e_insertSeq,
      botMap, AlgHom.comp_apply, ofKLR_ψ_mul_e_of_red (0 + p) (by omega) _ ?_ ?_, map_zero]
    · rw [insertSeq_lbl_win s zm _ ⟨p, by rw [Multiset.card_map]; omega⟩ rfl, Seq.map_lbl]
      obtain ⟨r, hr⟩ : ∃ r, w.lbl ⟨p, by omega⟩ = .inr r := by
        cases h : w.lbl ⟨p, by omega⟩ <;> simp_all
      exact (congrArg (fun a => (cupColour (I := I) 0 z₀ a).isRight) hr).trans rfl
    · rw [insertSeq_lbl_win s zm _ ⟨p + 1, by rw [Multiset.card_map]; omega⟩ (by simp),
        Seq.map_lbl]
      obtain ⟨r, hr⟩ : ∃ r, w.lbl ⟨p + 1, hp⟩ = .inr r := by
        cases h : w.lbl ⟨p + 1, hp⟩ <;> simp_all
      exact (congrArg (fun a => (cupColour (I := I) 0 z₀ a).isRight) hr).trans rfl

variable (ν ν₀) in
/-- **The diagrams at the maximum on the first `N` strands of `λ⁺`**, as a map
`T̃^{(μ,μ*)} → T̃^{λ⁺}`. -/
def frontStendhal : StendhalAlgebra k Q Λc ν₀ →ₙₐ[k] Tp :=
  stendhalLift (redRelations_frontBot Q Λ Λc)

theorem frontStendhal_eq (z : StendhalAlgebra k Q Λc ν₀) :
    ∃ x, frontStendhal Q Λ Λc ν ν₀ z = frontBot Q Λ Λc ν ν₀ x := by
  obtain ⟨x, hx⟩ := StendhalAlgebraAllOrders.ofKLR_surjective z.val
  refine ⟨x, ?_⟩
  rw [frontStendhal, stendhalLift_apply, ← hx, allOrdersLift_ofKLR]

variable (ν ν₀) in
/-- The idempotent cutting `T̃^{λ⁺}` to the loadings with the maximum at the left end. -/
abbrev frontIdem : Tp := β (KLRAlgebra.eSum _ (frontSet ν ν₀))

theorem frontIdem_mul_frontBot (x : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) :
    frontIdem Q Λ Λc ν ν₀ * frontBot Q Λ Λc ν ν₀ x = frontBot Q Λ Λc ν ν₀ x := by
  rw [frontBot_apply, ← map_mul, frontMapKLR]
  exact congrArg _ (KLR.Corner.E_mul_val _)

theorem frontBot_mul_frontIdem (x : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) :
    frontBot Q Λ Λc ν ν₀ x * frontIdem Q Λ Λc ν ν₀ = frontBot Q Λ Λc ν ν₀ x := by
  rw [frontBot_apply, ← map_mul, frontMapKLR]
  exact congrArg _ (KLR.Corner.val_mul_E _)

/-! ### The strands of `λ` on the last `m` strands -/

variable (ν ν₀) in
/-- The diagrams of `λ` on the last `m` strands of `λ⁺`, in `T̃^{λ⁺}`, before descending. -/
def suffixBot : KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν) →ₙₐ[k] Tp where
  toFun a := β (suffixMapKLR Q Λ Λc ν ν₀ a)
  map_zero' := by rw [suffixMapKLR_zero, map_zero]
  map_add' a b := by rw [suffixMapKLR_add, map_add]
  map_mul' a b := by rw [suffixMapKLR_mul, map_mul]
  map_smul' c a := by
    change β (suffixMapKLR Q Λ Λc ν ν₀ (c • a)) = c • β (suffixMapKLR Q Λ Λc ν ν₀ a)
    rw [suffixMapKLR_smul, map_smul]

theorem suffixBot_apply (a : KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)) :
    suffixBot Q Λ Λc ν ν₀ a = β (suffixMapKLR Q Λ Λc ν ν₀ a) := rfl

theorem suffixBot_eSum (s : Seq (stendhalWeight ℓ ν)) (y : Rp) :
    β (y * KLRAlgebra.eSum _ (frontSet ν ν₀) * suffixMapKLR Q Λ Λc ν ν₀ (KLRAlgebra.e s)) =
      ∑ t, β (y * KLRAlgebra.e (insertSeq (j := 0) (hj := z₀) s 0 zm t)) := by
  rw [suffixMapKLR_e, mul_assoc, KLRAlgebra.eSum_mul_eSum,
    Finset.inter_eq_right.2 (insertSet_subset_frontSet s), KLRAlgebra.eSum, Finset.mul_sum,
    map_sum, insertSet, Finset.sum_image (fun t _ t' _ h => insertSeq_injective s zm h)]

theorem redRelations_suffixBot : RedRelations (suffixBot Q Λ Λc ν ν₀) where
  red_dot a s ha := by
    rw [suffixBot_apply, suffixMapKLR_mul, suffixMapKLR_x, suffixBot_eSum]
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [botMap, AlgHom.comp_apply, map_mul]
    change orderProjection _ _ _ (StendhalAlgebraAllOrders.x _ * StendhalAlgebraAllOrders.e _) = 0
    rw [StendhalAlgebraAllOrders.x_mul_e_of_red, map_zero]
    rw [insertSeq_lbl_ge s zm t a (Nat.zero_le _) (Nat.add_comm _ _)]
    cases h : s.lbl a with
    | inl i => rw [h] at ha; exact absurd ha (by simp)
    | inr r => rfl
  red_cross p hp s ha hb := by
    rw [suffixBot_apply, suffixMapKLR_mul, suffixMapKLR_ψ hp, suffixBot_eSum]
    refine Finset.sum_eq_zero fun t _ => ?_
    have hp' : N + p + 1 < M := by
      have := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀); omega
    rw [botMap, AlgHom.comp_apply, ofKLR_ψ_mul_e_of_red (N + p) hp' _ ?_ ?_, map_zero]
    · rw [insertSeq_lbl_ge s zm t ⟨p, by omega⟩ (Nat.zero_le _) (by simp; omega)]
      cases h : s.lbl ⟨p, by omega⟩ with
      | inl i => rw [h] at ha; exact absurd ha (by simp)
      | inr r => rfl
    · rw [insertSeq_lbl_ge s zm t ⟨p + 1, hp⟩ (Nat.zero_le _) (by simp; omega)]
      cases h : s.lbl ⟨p + 1, hp⟩ with
      | inl i => rw [h] at hb; exact absurd hb (by simp)
      | inr r => rfl

variable (ν ν₀) in
/-- **The diagrams of `λ` right of the maximum at the left end**: the map `T̃^λ → T̃^{λ⁺}` placing
a diagram of `λ` on the last `m` strands, beside the identity on the strands at the maximum. -/
def suffixStendhal : StendhalAlgebra k Q Λ ν →ₙₐ[k] Tp :=
  stendhalLift (redRelations_suffixBot Q Λ Λc)

theorem suffixStendhal_eq (z : StendhalAlgebra k Q Λ ν) :
    ∃ a, suffixStendhal Q Λ Λc ν ν₀ z = suffixBot Q Λ Λc ν ν₀ a := by
  obtain ⟨a, ha⟩ := StendhalAlgebraAllOrders.ofKLR_surjective z.val
  refine ⟨a, ?_⟩
  rw [suffixStendhal, stendhalLift_apply, ← ha, allOrdersLift_ofKLR]

open Classical in
theorem suffixStendhal_one :
    suffixStendhal Q Λ Λc ν ν₀ 1 =
      ∑ s ∈ Finset.univ.filter (fun s : Seq (stendhalWeight ℓ ν) => IsRedOrdered s),
        β (KLRAlgebra.eSum _ (insertSet (j := 0) (hj := z₀) (ν₀ := ν₀) s 0 zm)) := by
  classical
  rw [suffixStendhal, stendhalLift_apply, KLR.Corner.val_one]
  have hE : allOrdersLift (redRelations_suffixBot Q Λ Λc (ν := ν) (ν₀ := ν₀))
      (StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν) =
      allOrdersLift (redRelations_suffixBot Q Λ Λc (ν := ν) (ν₀ := ν₀))
        (∑ s ∈ Finset.univ.filter (fun s : Seq (stendhalWeight ℓ ν) => IsRedOrdered s),
          StendhalAlgebraAllOrders.e s) := rfl
  rw [hE, map_sum]
  refine Finset.sum_congr (by congr) fun s _ => ?_
  rw [StendhalAlgebraAllOrders.e, allOrdersLift_ofKLR, suffixBot_apply, suffixMapKLR_e]

theorem suffixStendhal_one_mul_e (s : Seq (stendhalWeight ℓ ν)) (t : Seq σ₀) :
    suffixStendhal Q Λ Λc ν ν₀ 1 * β (KLRAlgebra.e (insertSeq (j := 0) (hj := z₀) s 0 zm t)) =
      β (KLRAlgebra.e (insertSeq (j := 0) (hj := z₀) s 0 zm t)) := by
  classical
  by_cases hs : IsRedOrdered s
  · rw [suffixStendhal_one, Finset.sum_mul, Finset.sum_eq_single_of_mem s
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, hs⟩)]
    · rw [← map_mul, KLRAlgebra.eSum_mul_e,
        ite_eq_left_of_eq_true _ _ (eq_true (insertSeq_mem_insertSet_front.2 rfl))]
    · intro s' _ hs'
      rw [← map_mul, KLRAlgebra.eSum_mul_e,
        ite_eq_right_of_eq_false _ _ (eq_false fun h => hs' (insertSeq_mem_insertSet_front.1 h)),
        map_zero]
  · have h0 : β (KLRAlgebra.e (insertSeq (j := 0) (hj := z₀) s 0 zm t)) = 0 :=
      orderProjection_e_of_not (fun h => hs (isRedOrdered_of_insertSeq_front h))
    rw [h0, mul_zero]

/-- `T̃^λ` acts unitally on the diagrams whose bottom is cut by the loadings `insertSeq s 0 t`. -/
theorem suffixStendhal_one_mul_frontIdem :
    suffixStendhal Q Λ Λc ν ν₀ 1 * frontIdem Q Λ Λc ν ν₀ = frontIdem Q Λ Λc ν ν₀ := by
  rw [frontIdem, KLRAlgebra.eSum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u hu => ?_
  obtain ⟨s, t, rfl⟩ := mem_frontSet.1 hu
  exact suffixStendhal_one_mul_e Q Λ Λc s t

/-! ### The two blocks commute -/

theorem commute_suffixBot_frontBot (a : KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν))
    (x : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) :
    Commute (suffixBot Q Λ Λc ν ν₀ a) (frontBot Q Λ Λc ν ν₀ x) :=
  (commute_suffixMapKLR_frontMapKLR Q Λ Λc ν ν₀ a x).map β

/-- **The two blocks commute on `T̃`.** -/
theorem commute_suffixStendhal_frontStendhal (z : StendhalAlgebra k Q Λ ν)
    (c : StendhalAlgebra k Q Λc ν₀) :
    Commute (suffixStendhal Q Λ Λc ν ν₀ z) (frontStendhal Q Λ Λc ν ν₀ c) := by
  obtain ⟨a, ha⟩ := suffixStendhal_eq Q Λ Λc (ν₀ := ν₀) z
  obtain ⟨x, hx⟩ := frontStendhal_eq Q Λ Λc (ν := ν) c
  rw [ha, hx]
  exact commute_suffixBot_frontBot Q Λ Λc a x

/-- The unit of the front block absorbs the left action of `T̃^λ`. -/
theorem suffixStendhal_one_mul_frontUnit :
    suffixStendhal Q Λ Λc ν ν₀ 1 * frontStendhal Q Λ Λc ν ν₀ 1 = frontStendhal Q Λ Λc ν ν₀ 1 := by
  obtain ⟨x, hx⟩ := frontStendhal_eq Q Λ Λc (ν := ν) (ν₀ := ν₀) 1
  rw [hx, ← frontIdem_mul_frontBot, ← mul_assoc, suffixStendhal_one_mul_frontIdem]

end FrontDescent

end Categorification.Stendhal.CupCap
