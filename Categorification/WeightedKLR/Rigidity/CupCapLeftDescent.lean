/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapLeftBlock
import Categorification.WeightedKLR.Rigidity.CupCapEndNull

/-!
# The block of a black strand and the window, on Stendhal diagrams

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.17. The diagrams of `R((i, μ, μ*))` placed on
the block `[n, n + N]` below the cap generators at `s` and `n + 1` (`CupCap.leftBlockMap`) kill
the dots on red strands and the crossings of two red strands in `T̃^{λ⁺}`, so they descend to a
map `T̃^{(i, μ, μ*)} → T̃^{λ⁺}` (`CupCap.blockStendhal`). When the strand of `s` at `n` is black of
colour `i`, it sends the diagram of `T̃^{(μ, μ*)}` with a black strand adjoined on the left to the
same diagram on the window at `n + 1` (`CupCap.blockStendhal_prependBlack`).

## Main definitions

* `CupCap.blockBot`: the block map, into `T̃^{λ⁺}`, before descending.
* `CupCap.blockStendhal`: the block map on `T̃^{(i, μ, μ*)}`.

## Main results

* `CupCap.blockStendhal_prependBlack`: prepending the black strand, then placing on the block.
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
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν₀)
local notation "Rc" => KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)
local notation "Ri" => KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 νᵢ)
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)

/-! ### Idempotents with red strands out of order -/

theorem botMap_e_of_not {u : Seq (stendhalWeight (ℓ + 2) (ν + ν₀))} (h : ¬ IsRedOrdered u) :
    botMap k Q Λ Λc j hj ν ν₀ (KLRAlgebra.e u) = 0 := by
  rw [botMap, AlgHom.comp_apply, orderProjection_e_of_not h]

omit [DecidableEq I] in
/-- The strands at the maximum keep the order of their red strands below the cap. -/
theorem not_isRedOrdered_insertSeq (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m)
    {t : Seq (stendhalWeight 2 ν₀)} (ht : ¬ IsRedOrdered t) :
    ¬ IsRedOrdered (insertSeq (j := j) (hj := hj) s n hn (Seq.map (cupColour j hj) t)) := by
  intro h
  apply ht
  intro a b r r' hab ha hb
  have hcard := card_plus j hj ν ν₀
  have hN : Multiset.card ((stendhalWeight 2 ν₀).map (cupColour (I := I) (ℓ := ℓ) j hj)) = N :=
    Multiset.card_map _ _
  have ha' := insertSeq_lbl_win s hn (Seq.map (cupColour j hj) t) (c := ⟨n + a.val, by omega⟩)
    ⟨a.val, by omega⟩ rfl
  have hb' := insertSeq_lbl_win s hn (Seq.map (cupColour j hj) t) (c := ⟨n + b.val, by omega⟩)
    ⟨b.val, by omega⟩ rfl
  rw [Seq.map_lbl] at ha' hb'
  simp only [Fin.cast_mk, Fin.eta, ha] at ha'
  simp only [Fin.cast_mk, Fin.eta, hb] at hb'
  have := h _ _ _ _ (Fin.mk_lt_mk.2 (by rw [Fin.lt_def] at hab; omega)) ha' hb'
  rw [Fin.lt_def, cupRed_val, cupRed_val] at this
  rw [Fin.lt_def]
  omega

section RedOrdered

variable {ℓ' : ℕ} (Λ' : Fin ℓ' → I →₀ ℕ) (ν' : Multiset I)

open Classical in
variable (k) in
/-- The sum of the idempotents of the loadings whose red strands are in order, in the KLR
algebra. -/
def redOrderedKLR : KLRAlgebra k (stendhalQ Q Λ') (stendhalWeight ℓ' ν') :=
  ∑ t ∈ Finset.univ.filter (fun t : Seq (stendhalWeight ℓ' ν') => IsRedOrdered t), KLRAlgebra.e t

theorem ofKLR_redOrderedKLR :
    StendhalAlgebraAllOrders.ofKLR k Q Λ' ν' (redOrderedKLR k Q Λ' ν') =
      StendhalAlgebraAllOrders.redOrderedIdem k Q Λ' ν' := by
  classical
  rw [redOrderedKLR, map_sum, StendhalAlgebraAllOrders.redOrderedIdem]
  exact Finset.sum_congr (by congr) fun _ _ => rfl

theorem val_orderProjection_ofKLR (w : KLRAlgebra k (stendhalQ Q Λ') (stendhalWeight ℓ' ν')) :
    (orderProjection Q Λ' ν' (StendhalAlgebraAllOrders.ofKLR k Q Λ' ν' w)).val =
      StendhalAlgebraAllOrders.ofKLR k Q Λ' ν' (w * redOrderedKLR k Q Λ' ν') := by
  rw [map_mul, ofKLR_redOrderedKLR]
  rfl

end RedOrdered

theorem insertMap_sum (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m) {ι' : Type*}
    (S : Finset ι') (f : ι' → Rc) :
    insertMap (j := j) (hj := hj) Q Λ Λc s n hn (∑ c ∈ S, f c) =
      ∑ c ∈ S, insertMap (j := j) (hj := hj) Q Λ Λc s n hn (f c) := by
  simp only [insertMap, map_sum, Corner.val_sum]

/-- Below the cap, only the red-ordered loadings of the strands at the maximum survive in
`T̃^{λ⁺}`. -/
theorem botMap_insertMap_redOrderedKLR (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m) :
    botMap k Q Λ Λc j hj ν ν₀ (insertMap Q Λ Λc s n hn (redOrderedKLR k Q Λc ν₀)) =
      botMap k Q Λ Λc j hj ν ν₀
        (KLRAlgebra.eSum _ (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s n hn)) := by
  classical
  rw [← insertMap_one, ← KLRAlgebra.sum_e (Q := stendhalQ Q Λc) (ν := stendhalWeight 2 ν₀),
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun t => IsRedOrdered t),
    insertMap_add, map_add, redOrderedKLR, left_eq_add, insertMap_sum, map_sum]
  refine Finset.sum_eq_zero fun t ht => ?_
  rw [insertMap_e, botMap_e_of_not Q Λ Λc
    (not_isRedOrdered_insertSeq s hn (Finset.mem_filter.1 ht).2)]

/-! ### The block map on Stendhal diagrams -/

variable (j hj ν₀) in
/-- The diagrams of `R((i, μ, μ*))` on the block `[n, n + N]`, in `T̃^{λ⁺}`, before descending. -/
def blockBot (s : Seq (stendhalWeight ℓ ν)) (n : ℕ) (hn : n + 1 ≤ m) : Ri →ₙₐ[k] Tp where
  toFun z := botMap k Q Λ Λc j hj ν ν₀ (leftBlockMap j hj i Q Λ Λc s n hn z).val
  map_zero' := by rw [map_zero, Corner.val_zero, map_zero]
  map_add' a b := by rw [map_add, Corner.val_add, map_add]
  map_mul' a b := by rw [map_mul, Corner.val_mul, map_mul]
  map_smul' c a := by
    change botMap k Q Λ Λc j hj ν ν₀ (leftBlockMap j hj i Q Λ Λc s n hn (c • a)).val =
      c • botMap k Q Λ Λc j hj ν ν₀ (leftBlockMap j hj i Q Λ Λc s n hn a).val
    rw [leftBlockMap_smul, map_smul]

theorem blockBot_apply (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n + 1 ≤ m) (z : Ri) :
    blockBot Q Λ Λc j hj ν₀ i s n hn z =
      botMap k Q Λ Λc j hj ν ν₀ (leftBlockMap j hj i Q Λ Λc s n hn z).val := rfl

open Classical in
omit [DecidableEq I] in
theorem isRight_of_mem_leftBlock_F (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n + 1 ≤ m)
    (u : Seq (stendhalWeight 2 νᵢ)) {u' : Seq (stendhalWeight (ℓ + 2) (ν + ν₀))}
    [DecidableEq I]
    (hu' : u' ∈ (leftBlock j hj ν₀ i s n hn).F (Seq.map (cupColour j hj) u))
    (a : Fin (Multiset.card (stendhalWeight 2 νᵢ))) (hM : n + a.val < M)
    (ha : (u.lbl a).isRight) : (u'.lbl ⟨n + a.val, hM⟩).isRight := by
  have hw := (Finset.mem_filter.1 hu').2 ⟨a.val, by rw [Multiset.card_map]; exact a.2⟩
  change (u'.1 (windowPos n (leftBlock_le (j := j) (hj := hj) i hn)
    ⟨a.val, by rw [Multiset.card_map]; exact a.2⟩)).isRight
  rw [hw]
  change ((Seq.map (cupColour j hj) u).lbl _).isRight
  rw [Seq.map_lbl]
  obtain ⟨r, hr⟩ : ∃ r, u.lbl a = .inr r := by cases h : u.lbl a <;> simp_all
  simp only [Fin.cast_mk, Fin.eta, hr]
  rfl

theorem botMap_x_mul_e_of_red (p : Fin M) (u : Seq (stendhalWeight (ℓ + 2) (ν + ν₀)))
    (h : (u.lbl p).isRight) :
    botMap k Q Λ Λc j hj ν ν₀ (KLRAlgebra.x p * KLRAlgebra.e u) = 0 := by
  rw [botMap, AlgHom.comp_apply, map_mul]
  change orderProjection _ _ _ (StendhalAlgebraAllOrders.x _ * StendhalAlgebraAllOrders.e _) = 0
  rw [StendhalAlgebraAllOrders.x_mul_e_of_red _ _ h, map_zero]

theorem botMap_ψ_mul_e_of_red (p : ℕ) (hp : p + 1 < M) (u : Seq (stendhalWeight (ℓ + 2) (ν + ν₀)))
    (h₁ : (u.lbl ⟨p, Nat.lt_of_succ_lt hp⟩).isRight) (h₂ : (u.lbl ⟨p + 1, hp⟩).isRight) :
    botMap k Q Λ Λc j hj ν ν₀ (KLRAlgebra.ψ p * KLRAlgebra.e u) = 0 := by
  rw [botMap, AlgHom.comp_apply, ofKLR_ψ_mul_e_of_red p hp u h₁ h₂, map_zero]

omit [DecidableEq I] in
theorem card_stendhalWeight_νᵢ : Multiset.card (stendhalWeight 2 νᵢ) = N + 1 := by
  have := card_μB i (j := 0) (hj := Nat.zero_le 0) (ν₀ := ν₀) (ℓ := 0)
  rwa [Multiset.card_map] at this

theorem redRelations_blockBot (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n + 1 ≤ m) :
    RedRelations (blockBot Q Λ Λc j hj ν₀ i s n hn) where
  red_dot a u ha := by
    classical
    have hM := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
    have hB := card_stendhalWeight_νᵢ (ν₀ := ν₀) i
    have ha' : n + a.val < M := by have := a.2; omega
    rw [blockBot_apply, map_mul, Corner.val_mul, leftBlockMap_x i Q Λ Λc s hn a ha', mul_assoc,
      Corner.E_mul_val, leftBlockMap_e, KLRAlgebra.eSum, Finset.mul_sum, map_sum]
    exact Finset.sum_eq_zero fun u' hu' => botMap_x_mul_e_of_red Q Λ Λc _ u'
      (isRight_of_mem_leftBlock_F i s hn u hu' a ha' ha)
  red_cross p hp u ha hb := by
    classical
    have hM := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
    have hB := card_stendhalWeight_νᵢ (ν₀ := ν₀) i
    have hp' : n + p + 1 < M := by omega
    rw [blockBot_apply, map_mul, Corner.val_mul, leftBlockMap_ψ i Q Λ Λc s hn (by omega),
      mul_assoc, Corner.E_mul_val, leftBlockMap_e, KLRAlgebra.eSum, Finset.mul_sum, map_sum]
    exact Finset.sum_eq_zero fun u' hu' => botMap_ψ_mul_e_of_red Q Λ Λc _ hp' u'
      (isRight_of_mem_leftBlock_F i s hn u hu' ⟨p, by omega⟩ (by simp; omega) ha)
      (isRight_of_mem_leftBlock_F i s hn u hu' ⟨p + 1, hp⟩ (by simp; omega) hb)

variable (j hj ν₀) in
/-- **The diagrams of `T̃^{(i, μ, μ*)}` on the block `[n, n + N]`** of `λ⁺`, below the cap
generators at `s` and `n + 1`. -/
def blockStendhal (s : Seq (stendhalWeight ℓ ν)) (n : ℕ) (hn : n + 1 ≤ m) :
    StendhalAlgebra k Q Λc νᵢ →ₙₐ[k] Tp :=
  stendhalLift (redRelations_blockBot Q Λ Λc i s hn)

theorem blockStendhal_cupMap (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n + 1 ≤ m) (y : Ri) :
    blockStendhal Q Λ Λc j hj ν₀ i s n hn (cupMap k Q Λc νᵢ y) =
      blockBot Q Λ Λc j hj ν₀ i s n hn y *
        blockBot Q Λ Λc j hj ν₀ i s n hn (redOrderedKLR k Q Λc νᵢ) := by
  rw [blockStendhal, stendhalLift_topMap, ← ofKLR_redOrderedKLR Q Λc ({i} + ν₀), allOrdersLift_ofKLR]

/-- **Adjoining the black strand on the left, then placing on the block**, is placing on the
window at `n + 1`, when the strand of `s` at `n` is black of colour `i`. -/
theorem blockStendhal_prependBlack (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n + 1 ≤ m)
    (hs : s.lbl ⟨n, by omega⟩ = .inl i) (w : Rc) :
    blockStendhal Q Λ Λc j hj ν₀ i s n hn (prependBlackStendhal Q Λc i ν₀ (cupMap k Q Λc ν₀ w)) =
      botMap k Q Λ Λc j hj ν ν₀ (insertMap Q Λ Λc s (n + 1) hn w) := by
  rw [blockStendhal, stendhalLift_apply]
  change allOrdersLift _ (prependBlackAllOrders Q Λc i ν₀ (cupMap k Q Λc ν₀ w).val).val = _
  rw [cupMap, AlgHom.comp_apply, val_orderProjection_ofKLR, prependBlackAllOrders_ofKLR]
  change allOrdersLift _ (StendhalAlgebraAllOrders.ofKLR k Q Λc νᵢ
    (prependKLR ν₀ i Q Λc (w * redOrderedKLR k Q Λc ν₀))) = _
  rw [allOrdersLift_ofKLR, blockBot_apply, leftBlockMap_prepend i Q Λ Λc s hn hs, insertMap_mul,
    map_mul, botMap_insertMap_redOrderedKLR, ← map_mul, ← insertMap_one Q Λ Λc s hn,
    ← insertMap_mul, mul_one]

end Categorification.Stendhal.CupCap
