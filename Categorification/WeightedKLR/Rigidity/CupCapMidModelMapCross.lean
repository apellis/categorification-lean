/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapMidModelMapDiagrams

/-!
# The map from `K̃^{λ⁺}_λ` to the model of a cap after `λ_j`: dots and crossings

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.17, for a cap inserted after the red strand
`λ_j`. This file checks the dot and crossing relations of Definition 7.15 in the model
`CupCap.MidModel` and descends the map on the free bimodule (`CupCap.midPhiFree`) to
`K̃^{λ⁺}_λ`. A crossing of `λ_{j+1}` with the black strand on its left uses the right pull-off
identity of `L` (`CupCap.rightLoop_midModel`); with the black strand on its right it moves the
passage by one step; a crossing of `λ_{j+1}` with a red strand vanishes on both sides.

## Main definitions

* `CupCap.midCapToModel`: the map `K̃^{λ⁺}_λ → MidModel`.

## Main results

* `CupCap.midPhiFree_dot`, `CupCap.midPhiFree_cross`: the dot and crossing relations.
* `CupCap.relations_le_ker_midPhiFree`: every relation of Definition 7.15 holds in the model.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Rλ" => KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)
local notation "T" => StendhalAlgebra k Q Λ ν
local notation "Tc" => StendhalAlgebra k Q Λc ν₀
local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
local notation "Eat" s:max n:max hn:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s n hn)
local notation "E" s:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s (midPos j s) (midPos_le j s))
local notation "P" n:max d:max => passU Q Λ Λc j hj ν ν₀ n d
local notation "bot" => botMap k Q Λ Λc j hj ν ν₀
local notation "Ev" => Env k Q Λ Λc j hj ν ν₀

/-! ### The crossings at the loading `s` -/

theorem midCrossAt_far (s : Seq (stendhalWeight ℓ ν)) {p : ℕ} (hp : p + 1 < m)
    (h1 : p + 1 ≠ midPos j s) (h2 : p ≠ midPos j s) :
    midCrossAt j hj Q Λ Λc ν ν₀ s p = KLRAlgebra.ψ (crossPos (midPos j s) N p) * E s := by
  simp [midCrossAt, hp, h1, h2]

theorem midCrossAt_left (s : Seq (stendhalWeight ℓ ν)) {p : ℕ} (hp : p + 1 < m)
    (hc : p + 1 = midPos j s) {i : I} (hi : s.lbl ⟨p, by omega⟩ = .inl i) :
    midCrossAt j hj Q Λ Λc ν ν₀ s p = KLRAlgebra.ψ (p + N) * underLeft N p * E s := by
  simp [midCrossAt, hp, eq_true hc, hi]

theorem midCrossAt_left_red (s : Seq (stendhalWeight ℓ ν)) {p : ℕ} (hp : p + 1 < m)
    (hc : p + 1 = midPos j s) {r : Fin ℓ} (hi : s.lbl ⟨p, by omega⟩ = .inr r) :
    midCrossAt j hj Q Λ Λc ν ν₀ s p = 0 := by
  simp [midCrossAt, hp, eq_true hc, hi]

theorem midCrossAt_right (s : Seq (stendhalWeight ℓ ν)) {p : ℕ} (hp : p + 1 < m)
    (hc : p = midPos j s) {i : I} (hi : s.lbl ⟨p + 1, hp⟩ = .inl i) :
    midCrossAt j hj Q Λ Λc ν ν₀ s p = Ring.inverse (cupScalar Q ν₀ i) •
      (underRight N p * KLRAlgebra.ψ (p + N) * E s) := by
  have h1 : p + 1 ≠ midPos j s := by omega
  simp [midCrossAt, hp, h1, eq_true hc, hi]

theorem midCrossAt_right_red (s : Seq (stendhalWeight ℓ ν)) {p : ℕ} (hp : p + 1 < m)
    (hc : p = midPos j s) {r : Fin ℓ} (hi : s.lbl ⟨p + 1, hp⟩ = .inr r) :
    midCrossAt j hj Q Λ Λc ν ν₀ s p = 0 := by
  have h1 : p + 1 ≠ midPos j s := by omega
  simp [midCrossAt, hp, h1, eq_true hc, hi]

omit [DecidableEq I] in
/-- The strand of `s` at the position of `λ_{j+1}` is red. -/
theorem lbl_isRight_of_eq_midPos (s : Seq (stendhalWeight ℓ ν)) {c : ℕ} (hc : c < m)
    (h : c = midPos j s) : (s.lbl ⟨c, hc⟩).isRight := by
  obtain ⟨a, ha, hla⟩ := midPos_of_lt j s (lt_of_midPos_lt j hc h.ge)
  have : (⟨c, hc⟩ : Fin m) = a := Fin.ext (by simp only; omega)
  rw [this, hla]
  rfl

/-! ### The model -/

variable (L : Type*) [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)

local notation "img" =>
  midCapImage (j := j) (hj := hj) (Q := Q) (Λ := Λ) (Λc := Λc) (ν₀ := ν₀) L

theorem tmul_midGen_smul (c : k) (Z : Tp) (v : L) :
    (Ind.tmul (midGen j hj Q Λ Λc ν ν₀ (c • Z)) v : MidModel j hj Q Λ Λc ν ν₀ L) =
      c • Ind.tmul (midGen j hj Q Λ Λc ν ν₀ Z) v := by
  rw [Algebra.smul_def, Algebra.commutes, ← op_smul_tmul_midGen, ← MulOpposite.algebraMap_apply,
    ← midModel_algebraMap_smul]

/-- The right pull-off identity of `L` at a loading whose maximum is at `c`. -/
theorem rightLoop_midModel_of (hP : PullOff k Q Λc ν₀ L) (i : I) (t : Seq (stendhalWeight ℓ ν))
    {c : ℕ} (htc : midPos j t = c) (hc1 : c + 1 < m) (hs : t.lbl ⟨c + 1, hc1⟩ = .inl i) (v : L) :
    (Ind.tmul (midGen j hj Q Λ Λc ν ν₀ (bot (KLRAlgebra.ψ (c + N) *
        (underLeft N c * underRight N c) * Eat (sadj m c • t) c (by omega)))) v :
          MidModel j hj Q Λ Λc ν ν₀ L) =
      Ind.tmul (midGen j hj Q Λ Λc ν ν₀ (bot (KLRAlgebra.ψ (c + N) *
        Eat (sadj m c • t) c (by omega))))
        (op (algebraMap k Tc (cupScalar Q ν₀ i)) • v) := by
  subst htc
  exact rightLoop_midModel Q Λ Λc L hP i t hc1 hs v

variable {L} in
theorem midKLRAct_ψ_img (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) (s : Seq (stendhalWeight ℓ ν))
    (n : Fin (m + 1)) (v : L) (h : n.val ≤ midPos j s) (p : ℕ) :
    midKLRAct hR (KLRAlgebra.ψ p) (img (s, n) v) = midCapScalar j Q ν₀ s n •
      Ind.tmul (midGen j hj Q Λ Λc ν ν₀ (bot (midCrossAt j hj Q Λ Λc ν ν₀ s p *
        (P n (midPos j s - n) * Eat s n (h.trans (midPos_le j s)))))) v := by
  rw [midCapImage_of_le s n v h, map_smul, midKLRAct_ψ, midEnd_tmul_midGen L hL, ← map_mul,
    midCapBot, mul_assoc (E s), ← mul_assoc, midCross_mul_eSum]

theorem op_smul_img (s : Seq (stendhalWeight ℓ ν)) (n : Fin (m + 1)) (v : L)
    (h : n.val ≤ midPos j s) (b : Rp) :
    (op (bot b) : Tpᵐᵒᵖ) • img (s, n) v = midCapScalar j Q ν₀ s n •
      Ind.tmul (midGen j hj Q Λ Λc ν ν₀ (bot (midCapBot j hj Q Λ Λc ν₀ s n h * b))) v := by
  rw [midCapImage_of_le s n v h, smul_comm, op_smul_tmul_midGen, ← map_mul]

/-! ### The crossing relation -/

include hL in
/-- **The crossing relation away from `λ_{j+1}`.** -/
theorem mid_cross_far (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) (s : Seq (stendhalWeight ℓ ν))
    (n : Fin (m + 1)) (v : L) {p : ℕ} (hp : p + 1 < n.val ∨ n.val ≤ p) (hpm : p + 1 < m)
    (hfar : p + 1 < midPos j s ∨ midPos j s + 1 ≤ p) :
    midKLRAct hR (KLRAlgebra.ψ p) (img (s, n) v) =
      (op (bot (KLRAlgebra.ψ (crossPos n N p))) : Tpᵐᵒᵖ) • img (sadj m p • s, n) v := by
  have hm : midPos j (sadj m p • s) = midPos j s := midPos_sadj_of_far j s hpm hfar
  by_cases hn : n.val ≤ midPos j s
  · have hn' : n.val ≤ midPos j (sadj m p • s) := hm ▸ hn
    rw [midKLRAct_ψ_img hL hR s n v hn, op_smul_img L (sadj m p • s) n v hn',
      midCrossAt_far s hpm (by omega) (by omega),
      midCapBot_eq_of (sadj m p • s) hn' hm (midPos_le j s)]
    have hsc : midCapScalar j Q ν₀ (sadj m p • s) n = midCapScalar j Q ν₀ s n := by
      unfold midCapScalar; rw [hm]; exact prod_Ico_midFac_sadj s hpm _ _ (by omega)
    rw [hsc, tmul_midGen_bot_eq L hL (mem_midExit_of_eq (sadj m p • s) (midPos_le j s) hm.symm
      (mid_cross_far_diff_mem s hn hp hpm hfar)) v]
  · rw [midCapImage_of_lt s n v (by omega), midCapImage_of_lt (sadj m p • s) n v (by omega),
      map_zero, smul_zero]

include hL in
/-- **The crossing relation of `λ_{j+1}` with the strand on its left**, from the right pull-off
identity of `L`. -/
theorem mid_cross_left (hP : PullOff k Q Λc ν₀ L) (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))
    (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) (s : Seq (stendhalWeight ℓ ν))
    (n : Fin (m + 1)) (v : L) {p : ℕ} (hp : p + 1 < n.val ∨ n.val ≤ p) (hpm : p + 1 < m)
    (hc : p + 1 = midPos j s) :
    midKLRAct hR (KLRAlgebra.ψ p) (img (s, n) v) =
      (op (bot (KLRAlgebra.ψ (crossPos n N p))) : Tpᵐᵒᵖ) • img (sadj m p • s, n) v := by
  have hm : midPos j (sadj m p • s) = p := midPos_sadj_left j s hpm hc
  by_cases hn : n.val ≤ midPos j s
  swap
  · rw [midCapImage_of_lt s n v (by omega), midCapImage_of_lt (sadj m p • s) n v (by omega),
      map_zero, smul_zero]
  have hnp : n.val ≤ p := by omega
  have hcn : crossPos n N p = p + N := by unfold crossPos; split_ifs <;> omega
  have hn' : n.val ≤ midPos j (sadj m p • s) := by omega
  rw [hcn, op_smul_img L (sadj m p • s) n v hn',
    midCapBot_eq_of (sadj m p • s) hn' hm (by omega), midKLRAct_ψ_img hL hR s n v hn]
  rcases hlbl : s.lbl ⟨p, by omega⟩ with i | r
  swap
  · rw [midCrossAt_left_red s hpm hc hlbl, zero_mul, map_zero, tmul_midGen_zero, smul_zero,
      botMap_mul_eSum_mul_ψ_of_red s hnp hpm (by rw [hlbl]; rfl)
        (lbl_isRight_of_eq_midPos s hpm hc), tmul_midGen_zero, smul_zero]
  rw [midCrossAt_left s hpm hc hlbl]
  -- the diagram below the cap generator splits off the loop on the right of the maximum
  have hcn' : midPos j s - n = p - n + 1 := by omega
  have hU : P n (midPos j s - n) = underRight N p * P n (p - n) := by
    rw [hcn', passU_succ, show n.val + (p - n) = p by omega]
  have hEc : E s = Eat s (p + 1) (by omega) := by
    rw [insertSet_congr' s (midPos_le j s) (show p + 1 ≤ m by omega) hc.symm]
  have hPE := passU_mul_eSum (j := j) (hj := hj) (ν₀ := ν₀) Q Λ Λc s n (p - n) (by omega)
  rw [insertSet_congr' s (p := n + (p - n)) _ (show p ≤ m by omega) (by omega)] at hPE
  have hUE := underRight_mul_eSum (j := j) (hj := hj) (ν₀ := ν₀) (Q := Q) (Λ := Λ) (Λc := Λc) s
    (show p + 1 ≤ m by omega)
  have hD : KLRAlgebra.ψ (p + N) * underLeft N p * E s *
        (P n (midPos j s - n) * Eat s n (hn.trans (midPos_le j s))) =
      KLRAlgebra.ψ (p + N) * (underLeft N p * underRight N p) * Eat s p (by omega) *
        (P n (p - n) * Eat s n (hn.trans (midPos_le j s))) := by
    have i1 : ∀ X : Rp, Eat s p (show p ≤ m by omega) * (Eat s p (show p ≤ m by omega) * X) =
        Eat s p (show p ≤ m by omega) * X := fun X => by
      rw [← mul_assoc, (KLRAlgebra.eSum_idem _).eq]
    have i2 : ∀ X : Rp, Eat s (p + 1) (show p + 1 ≤ m by omega) *
        (Eat s (p + 1) (show p + 1 ≤ m by omega) * X) =
        Eat s (p + 1) (show p + 1 ≤ m by omega) * X := fun X => by
      rw [← mul_assoc, (KLRAlgebra.eSum_idem _).eq]
    have i3 : ∀ X : Rp, underRight N p * (Eat s p (show p ≤ m by omega) * X) =
        Eat s (p + 1) (show p + 1 ≤ m by omega) * (underRight N p * X) := fun X => by
      rw [← mul_assoc, hUE, mul_assoc]
    rw [hU, hEc]
    simp only [mul_assoc]
    rw [hPE]
    simp only [i1, i2, i3]
  have hlp : (sadj m p • s).lbl ⟨p + 1, hpm⟩ = .inl i := by
    rw [lbl_sadj_of_swapNat s hpm _ ⟨p, by omega⟩ (by unfold swapNat; simp),
      hlbl]
  have hloop := rightLoop_midModel_of (hj := hj) (Λ := Λ) L hP i (sadj m p • s) hm hpm hlp v
  rw [sadj_smul_sadj_smul] at hloop
  rw [hD, map_mul, ← op_smul_tmul_midGen, hloop, tmul_midGen_algebraMap,
    smul_comm _ (cupScalar Q ν₀ i), op_smul_tmul_midGen, ← map_mul, smul_smul,
    ψ_eSum_passU_eSum' s hnp hpm]
  have hsc : midCapScalar j Q ν₀ s n * cupScalar Q ν₀ i =
      midCapScalar j Q ν₀ (sadj m p • s) n := by
    unfold midCapScalar
    rw [hm, ← hc, Finset.prod_Ico_succ_top hnp, midFac_inl s (by omega) hlbl, mul_assoc,
      Ring.inverse_mul_cancel _ (hκ i), mul_one,
      prod_Ico_midFac_sadj s hpm _ _ (Or.inr (Or.inl le_rfl))]
  rw [hsc]

include hL in
/-- **The crossing relation of `λ_{j+1}` with the strand on its right**: it moves the passage of
the cap generator by one step. -/
theorem mid_cross_right (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) (s : Seq (stendhalWeight ℓ ν))
    (n : Fin (m + 1)) (v : L) {p : ℕ} (hp : p + 1 < n.val ∨ n.val ≤ p) (hpm : p + 1 < m)
    (hc : p = midPos j s) :
    midKLRAct hR (KLRAlgebra.ψ p) (img (s, n) v) =
      (op (bot (KLRAlgebra.ψ (crossPos n N p))) : Tpᵐᵒᵖ) • img (sadj m p • s, n) v := by
  have hm : midPos j (sadj m p • s) = p + 1 := midPos_sadj_right j s hpm hc
  by_cases hn : n.val ≤ midPos j s
  swap
  · rw [midCapImage_of_lt s n v (by omega), midCapImage_of_lt (sadj m p • s) n v (by omega),
      map_zero, smul_zero]
  have hnp : n.val ≤ p := by omega
  have hcn : crossPos n N p = p + N := by unfold crossPos; split_ifs <;> omega
  have hn' : n.val ≤ midPos j (sadj m p • s) := by omega
  rw [hcn, op_smul_img L (sadj m p • s) n v hn',
    midCapBot_eq_of (sadj m p • s) hn' hm (by omega), midKLRAct_ψ_img hL hR s n v hn]
  rcases hlbl : s.lbl ⟨p + 1, hpm⟩ with i | r
  swap
  · rw [midCrossAt_right_red s hpm hc hlbl, zero_mul, map_zero, tmul_midGen_zero, smul_zero,
      botMap_mul_eSum_mul_ψ_of_red s hnp hpm (lbl_isRight_of_eq_midPos s (by omega) hc)
        (by rw [hlbl]; rfl), tmul_midGen_zero, smul_zero]
  rw [midCrossAt_right s hpm hc hlbl, smul_mul_assoc, map_smul, tmul_midGen_smul, smul_smul]
  have hcn' : midPos j s - n = p - n := by omega
  have hEc : E s = Eat s p (by omega) := by
    rw [insertSet_congr' s (midPos_le j s) (show p ≤ m by omega) hc.symm]
  have hU : P n (p + 1 - n) = underRight N p * P n (p - n) := by
    rw [show p + 1 - n.val = p - n + 1 by omega, passU_succ, show n.val + (p - n) = p by omega]
  have hUE := underRight_mul_eSum (j := j) (hj := hj) (ν₀ := ν₀) (Q := Q) (Λ := Λ) (Λc := Λc)
    (sadj m p • s) (show p + 1 ≤ m by omega)
  have hD : underRight N p * KLRAlgebra.ψ (p + N) * E s *
        (P n (midPos j s - n) * Eat s n (hn.trans (midPos_le j s))) =
      Eat (sadj m p • s) (p + 1) (by omega) * P n (p + 1 - n) *
        Eat (sadj m p • s) n (by omega) * KLRAlgebra.ψ (p + N) := by
    rw [hcn', hEc, mul_assoc (underRight N p), mul_assoc (underRight N p),
      ψ_eSum_passU_eSum' s hnp hpm, hU]
    simp only [← mul_assoc]
    rw [hUE]
  have hsc : midCapScalar j Q ν₀ s n * Ring.inverse (cupScalar Q ν₀ i) =
      midCapScalar j Q ν₀ (sadj m p • s) n := by
    unfold midCapScalar
    rw [hm, ← hc, Finset.prod_Ico_succ_top hnp,
      prod_Ico_midFac_sadj s hpm _ _ (Or.inr (Or.inl le_rfl)), midFac_sadj s hpm,
      Equiv.swap_apply_left, midFac_inl s hpm hlbl]
  rw [hD, hsc]

/-! ### The dot and crossing relations in the model -/

include hL in
/-- **The dot relation** holds in the model. -/
theorem midPhiFree_dot (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) (s : Seq (stendhalWeight ℓ ν))
    (n : Fin (m + 1)) (v : L) (a : Fin m) :
    midPhiFree L hL hR (act (topMap k Q Λ ν (KLRAlgebra.x a)) 1
        (gen (s, n) v : FreeCap k Q Λ Λc j hj ν ν₀ L) -
      act 1 (bot (KLRAlgebra.x (dotPos (j := j) (hj := hj) (ν₀ := ν₀) n a)))
        (gen (s, n) v)) = 0 := by
  rw [map_sub, midPhiFree_act, midPhiFree_act, midPhiFree_gen, op_one, one_smul,
    midLeftAlg_topMap, map_one, sub_eq_zero]
  change midKLRAct hR (KLRAlgebra.x a) (img (s, n) v) =
    (op (bot (KLRAlgebra.x (dotPos (j := j) (hj := hj) (ν₀ := ν₀) n a))) : Tpᵐᵒᵖ) •
      img (s, n) v
  by_cases h : n.val ≤ midPos j s
  · rw [op_smul_img L s n v h, midCapImage_of_le s n v h, map_smul, midKLRAct_x,
      midEnd_tmul_midGen L hL, ← map_mul]
    have e1 : midDot j hj Q Λ Λc ν ν₀ a * midCapBot j hj Q Λ Λc ν₀ s n h =
        KLRAlgebra.x (dotPos (j := j) (hj := hj) (ν₀ := ν₀)
          ⟨midPos j s, Nat.lt_succ_of_le (midPos_le j s)⟩ a) * E s *
          (P n (midPos j s - n) * Eat s n (h.trans (midPos_le j s))) := by
      rw [midCapBot, mul_assoc (E s), ← mul_assoc, midDot_mul_eSum]
    have hmem : midDot j hj Q Λ Λc ν ν₀ a * midCapBot j hj Q Λ Λc ν₀ s n h -
        midCapBot j hj Q Λ Λc ν₀ s n h *
          KLRAlgebra.x (dotPos (j := j) (hj := hj) (ν₀ := ν₀) n a) ∈
        midExit j hj Q Λ Λc ν ν₀ := by
      rw [e1]
      exact mem_midExit s (mid_dot_diff_mem s h a _ _ (dotPos_val_mid _ a) (dotPos_val_mid n a))
    rw [tmul_midGen_bot_eq L hL hmem v]
  · rw [midCapImage_of_lt s n v (by omega), map_zero, smul_zero]

omit [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
theorem act_zero_left_mid (b : Tp) (z : FreeCap k Q Λ Λc j hj ν ν₀ L) : act 0 b z = 0 := by
  rw [act, Env.mk, TensorProduct.zero_tmul]
  exact zero_smul _ z

omit [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
theorem act_zero_right_mid (a : T) (z : FreeCap k Q Λ Λc j hj ν ν₀ L) : act a 0 z = 0 := by
  rw [act, Env.mk, op_zero, TensorProduct.tmul_zero]
  exact zero_smul _ z

include hL in
/-- **The crossing relation** holds in the model. -/
theorem midPhiFree_cross (hP : PullOff k Q Λc ν₀ L) (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))
    (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) (s : Seq (stendhalWeight ℓ ν))
    (n : Fin (m + 1)) (v : L) (p : ℕ) (hp : p + 1 < n.val ∨ n.val ≤ p) :
    midPhiFree L hL hR (act (topMap k Q Λ ν (KLRAlgebra.ψ p)) 1
        (gen (s, n) v : FreeCap k Q Λ Λc j hj ν ν₀ L) -
      act 1 (bot (KLRAlgebra.ψ (crossPos n N p))) (gen (sadj m p • s, n) v)) = 0 := by
  by_cases hpm : p + 1 < m
  · rw [map_sub, midPhiFree_act, midPhiFree_act, midPhiFree_gen, midPhiFree_gen, op_one,
      one_smul, midLeftAlg_topMap, map_one, sub_eq_zero]
    change midKLRAct hR (KLRAlgebra.ψ p) (img (s, n) v) =
      (op (bot (KLRAlgebra.ψ (crossPos n N p))) : Tpᵐᵒᵖ) • img (sadj m p • s, n) v
    by_cases hfar : p + 1 < midPos j s ∨ midPos j s + 1 ≤ p
    · exact mid_cross_far L hL hR s n v hp hpm hfar
    · rcases (by omega : p + 1 = midPos j s ∨ p = midPos j s) with hc | hc
      · exact mid_cross_left L hL hP hκ hR s n v hp hpm hc
      · exact mid_cross_right L hL hR s n v hp hpm hc
  · have h1 : (KLRAlgebra.ψ p : Rλ) = 0 := KLRAlgebra.ψ_eq_zero p (by omega)
    have h2 : (KLRAlgebra.ψ (crossPos n N p) : Rp) = 0 :=
      KLRAlgebra.ψ_eq_zero _ (by
        have := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
        unfold crossPos; split_ifs <;> omega)
    rw [h1, h2, map_zero, map_zero, act_zero_left_mid, act_zero_right_mid, sub_zero, map_zero]

/-! ### The map from `K̃^{λ⁺}_λ` -/

include hL in
/-- **The relations of `K̃^{λ⁺}_λ` hold in the model of a cap after `λ_j`**: under the support
hypothesis on `L`, the two pull-off identities and invertible scalars of (max1), every relation
of Definition 7.15 maps to zero. -/
theorem relations_le_ker_midPhiFree (hP : PullOff k Q Λc ν₀ L) (hPL : PullOffLeft k Q Λc ν₀ L)
    (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i)) (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) :
    relations k Q Λ Λc j hj ν ν₀ L ≤ LinearMap.ker (midPhiFree L hL hR) := by
  refine Submodule.span_le.2 fun z hz => ?_
  rw [SetLike.mem_coe, LinearMap.mem_ker]
  induction hz with
  | add σ v w => exact midPhiFree_add hR σ v w
  | idem s n v => exact midPhiFree_idem hR s n v
  | box s n v x => exact midPhiFree_box hR s n v x
  | dot s n v a => exact midPhiFree_dot L hL hR s n v a
  | cross s n v p hp => exact midPhiFree_cross L hL hP hκ hR s n v p hp
  | «over» s n v i hn hi => exact midPhiFree_over hκ hR s n v i hn hi
  | under s n v i hn hi => exact midPhiFree_under hκ hPL hR s n v i hn hi

/-- **The map from `K̃^{λ⁺}_λ` to the model of a cap after `λ_j`** (Webster, arXiv:1309.3796v3,
proof of Lemma 7.17): `cap s n v` goes to `c(s, n) · e E_{s,c} U E_{s,n} ⊗ v` when
`n ≤ c = midPos j s`, and to `0` otherwise. -/
def midCapToModel (hP : PullOff k Q Λc ν₀ L) (hPL : PullOffLeft k Q Λc ν₀ L)
    (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i)) (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) :
    CapTilde k Q Λ Λc j hj ν ν₀ L →ₗ[Ev] MidBimod L hL hR :=
  (relations k Q Λ Λc j hj ν ν₀ L).liftQ (midPhiFree L hL hR)
    (relations_le_ker_midPhiFree L hL hP hPL hκ hR)

theorem midCapToModel_mk (hP : PullOff k Q Λc ν₀ L) (hPL : PullOffLeft k Q Λc ν₀ L)
    (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i)) (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)
    (q : CapIdx ℓ ν) (v : L) :
    midCapToModel L hL hP hPL hκ hR (Submodule.Quotient.mk (gen q v)) =
      toMidBimod L hL hR (img q v) := by
  rw [midCapToModel, Submodule.liftQ_apply, midPhiFree_gen]

end Categorification.Stendhal.CupCap
