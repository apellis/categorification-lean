/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapMidRelBase

/-!
# The idempotent, dot and red relations on the model of a cap after `λ_j`

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.17. The diagrams of the generators of `T̃^λ`
on the model `L ⊗ e T̃^{λ⁺}` (`CupCap.midIdem`, `CupCap.midDot`, `CupCap.midCross`) satisfy the
relations of the KLR algebra of `λ` on idempotents, on dots and on crossings out of range, already
in `λ⁺`, except that the sum of the idempotents is the sum of the window idempotents, which acts as
the identity. Dots on red strands and crossings of two red strands act by zero, since they vanish
in `T̃^{λ⁺}`.

## Main results

* `CupCap.midIdem_mul_midIdem`, `CupCap.midRel_sum_midIdem`, `CupCap.midDot_mul_midIdem`,
  `CupCap.midCross_mul_midIdem`, `CupCap.midCross_eq_zero`, `CupCap.midDot_mul_midDot`.
* `CupCap.midRel_red_dot`, `CupCap.midRel_red_cross`: the red relations.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MulOpposite InductionAlong

section Exact

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "E" s:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s (midPos j s) (midPos_le j s))

variable (j hj Q Λ Λc ν ν₀) in
/-- The dot of `λ⁺` representing the dot on the strand `a` of the loading `s` of `λ`. -/
abbrev midDotAt (s : Seq (stendhalWeight ℓ ν)) (a : Fin m) : Rp :=
  KLRAlgebra.x (dotPos (j := j) (hj := hj) (ν₀ := ν₀)
    ⟨midPos j s, Nat.lt_succ_of_le (midPos_le j s)⟩ a)

local notation "X" => midDotAt j hj Q Λ Λc ν ν₀

theorem midIdem_mul_midIdem (s t : Seq (stendhalWeight ℓ ν)) :
    midIdem j hj Q Λ Λc ν ν₀ s * midIdem j hj Q Λ Λc ν ν₀ t =
      if s = t then midIdem j hj Q Λ Λc ν ν₀ s else 0 :=
  midIdem_mul_eSum s t

theorem eSum_mul_midDot (t : Seq (stendhalWeight ℓ ν)) (a : Fin m) :
    E t * midDot j hj Q Λ Λc ν ν₀ a = X t a * E t := by
  rw [midDot, Finset.mul_sum, Finset.sum_eq_single t (fun s _ h => by
    rw [← mul_assoc, ← (commute_x_eSum _ _).eq, mul_assoc, eSum_mid_mul_eSum_mid]
    simp [Ne.symm h]) (by simp), ← mul_assoc, ← (commute_x_eSum _ _).eq, mul_assoc,
    (KLRAlgebra.eSum_idem _).eq]

theorem midDot_mul_midIdem (a : Fin m) (t : Seq (stendhalWeight ℓ ν)) :
    midDot j hj Q Λ Λc ν ν₀ a * midIdem j hj Q Λ Λc ν ν₀ t =
      midIdem j hj Q Λ Λc ν ν₀ t * midDot j hj Q Λ Λc ν ν₀ a := by
  rw [midIdem, midDot_mul_eSum, eSum_mul_midDot]

theorem midCross_mul_midIdem (p : ℕ) (t : Seq (stendhalWeight ℓ ν)) :
    midCross j hj Q Λ Λc ν ν₀ p * midIdem j hj Q Λ Λc ν ν₀ t =
      midIdem j hj Q Λ Λc ν ν₀ (sadj m p • t) * midCross j hj Q Λ Λc ν ν₀ p := by
  rw [midIdem, midIdem, midCross_mul_eSum, midCross, Finset.mul_sum,
    Finset.sum_eq_single t (fun s _ h => by
      have h' : sadj m p • t ≠ sadj m p • s := fun h' => h (smul_left_cancel _ h').symm
      rw [← eSum_mul_midCrossAt, ← mul_assoc, eSum_mid_mul_eSum_mid]
      simp [h']) (by simp), eSum_mul_midCrossAt]

theorem midCross_eq_zero (p : ℕ) (h : m ≤ p + 1) : midCross j hj Q Λ Λc ν ν₀ p = 0 :=
  Finset.sum_eq_zero fun s _ => by
    have hp : ¬ p + 1 < m := by omega
    simp [midCrossAt, hp]

theorem midDot_mul_midDot_eq (a b : Fin m) :
    midDot j hj Q Λ Λc ν ν₀ a * midDot j hj Q Λ Λc ν ν₀ b =
      ∑ s : Seq (stendhalWeight ℓ ν), X s a * X s b * E s := by
  rw [midDot, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [mul_assoc, eSum_mul_midDot, ← mul_assoc]

theorem midDot_mul_midDot (a b : Fin m) :
    midDot j hj Q Λ Λc ν ν₀ a * midDot j hj Q Λ Λc ν ν₀ b =
      midDot j hj Q Λ Λc ν ν₀ b * midDot j hj Q Λ Λc ν ν₀ a := by
  rw [midDot_mul_midDot_eq a b, midDot_mul_midDot_eq b a]
  exact Finset.sum_congr rfl fun s _ => by rw [KLRAlgebra.x_mul_x]

end Exact

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Model

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "E" s:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s (midPos j s) (midPos_le j s))
local notation "bot" => botMap k Q Λ Λc j hj ν ν₀
local notation "σ" => midStendhal j hj Q Λ Λc ν ν₀
local notation "μ" => midMapKLR j hj Q Λ Λc ν ν₀

variable {L : Type*} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}

/-- The sum of the idempotents acts as the identity. -/
theorem midRel_sum_midIdem :
    MidRel j hj Q Λ Λc ν ν₀ L hL (∑ s : Seq (stendhalWeight ℓ ν), midIdem j hj Q Λ Λc ν ν₀ s)
      1 := by
  refine MidRel.of_midElt_eq ?_
  have h1 : (∑ s : Seq (stendhalWeight ℓ ν), midIdem j hj Q Λ Λc ν ν₀ s) = μ 1 :=
    (midMapKLR_one (j := j) (hj := hj) (Q := Q) (Λ := Λ) (Λc := Λc) (ν := ν) (ν₀ := ν₀)).symm
  have hA : bot (μ 1) * σ 1 = σ 1 := by
    rw [midStendhal_one_eq_bot, ← map_mul, ← midMapKLR_mul, one_mul]
  have hB : bot 1 * σ 1 = σ 1 := by
    rw [show (bot 1 : StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)) = 1 from
      map_one (botMap k Q Λ Λc j hj ν ν₀), one_mul]
  rw [h1, midElt, midElt, mul_assoc, hA, mul_assoc, hB]

theorem midRel_of_bot_eq_zero {Y : Rp} (h : bot Y = 0) : MidRel j hj Q Λ Λc ν ν₀ L hL Y 0 :=
  MidRel.of_midElt_eq (by rw [midElt, midElt, h, map_zero])

theorem bot_x_mul_e_of_red (d : Fin M) (t : Seq (stendhalWeight (ℓ + 2) (ν + ν₀)))
    (h : (t.lbl d).isRight) : bot (KLRAlgebra.x d * KLRAlgebra.e t) = 0 := by
  rw [botMap, AlgHom.comp_apply, map_mul]
  change orderProjection _ _ _ (StendhalAlgebraAllOrders.x _ * StendhalAlgebraAllOrders.e _) = 0
  rw [StendhalAlgebraAllOrders.x_mul_e_of_red _ _ h, map_zero]

theorem bot_ψ_mul_e_of_red (q : ℕ) (hq : q + 1 < M) (t : Seq (stendhalWeight (ℓ + 2) (ν + ν₀)))
    (h₁ : (t.lbl ⟨q, by omega⟩).isRight) (h₂ : (t.lbl ⟨q + 1, hq⟩).isRight) :
    bot (KLRAlgebra.ψ q * KLRAlgebra.e t) = 0 := by
  rw [botMap, AlgHom.comp_apply, ofKLR_ψ_mul_e_of_red q hq t h₁ h₂, map_zero]

/-- **Red strands carry no dots** on the model. -/
theorem midRel_red_dot (a : Fin m) (s : Seq (stendhalWeight ℓ ν)) (h : (s.lbl a).isRight) :
    MidRel j hj Q Λ Λc ν ν₀ L hL (midDot j hj Q Λ Λc ν ν₀ a * midIdem j hj Q Λ Λc ν ν₀ s) 0 := by
  refine midRel_of_bot_eq_zero ?_
  rw [midIdem, midDot_mul_eSum, eSum_insertSet, Finset.mul_sum, map_sum]
  refine Finset.sum_eq_zero fun w _ => bot_x_mul_e_of_red _ _ ?_
  rw [dotPos, insertSeq_lbl_old]
  obtain ⟨r, hr⟩ : ∃ r, s.lbl a = .inr r := by cases h' : s.lbl a <;> simp_all
  rw [hr]; rfl

/-- **Red strands do not cross** on the model. -/
theorem midRel_red_cross (p : ℕ) (hp : p + 1 < m) (s : Seq (stendhalWeight ℓ ν))
    (h₁ : (s.lbl ⟨p, by omega⟩).isRight) (h₂ : (s.lbl ⟨p + 1, hp⟩).isRight) :
    MidRel j hj Q Λ Λc ν ν₀ L hL (midCross j hj Q Λ Λc ν ν₀ p * midIdem j hj Q Λ Λc ν ν₀ s)
      0 := by
  rw [midIdem, midCross_mul_eSum]
  obtain ⟨r₁, hr₁⟩ : ∃ r, s.lbl ⟨p, by omega⟩ = .inr r := by
    cases h' : s.lbl ⟨p, by omega⟩ <;> simp_all
  obtain ⟨r₂, hr₂⟩ : ∃ r, s.lbl ⟨p + 1, hp⟩ = .inr r := by
    cases h' : s.lbl ⟨p + 1, hp⟩ <;> simp_all
  unfold midCrossAt
  split_ifs with hc1 hc2
  · split
    · simp_all
    · exact MidRel.refl _
  · split
    · simp_all
    · exact MidRel.refl _
  · refine midRel_of_bot_eq_zero ?_
    have hM := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
    have hlt : p + 1 < midPos j s ∨ midPos j s + 1 ≤ p := by omega
    rw [eSum_insertSet, Finset.mul_sum, map_sum]
    refine Finset.sum_eq_zero fun w _ =>
      bot_ψ_mul_e_of_red _ (by unfold crossPos; split_ifs <;> omega) _ ?_ ?_
    · rcases hlt with hlt | hlt
      · rw [insertSeq_lbl_lt s _ _ ⟨p, by omega⟩ (by simp; omega)
          (by unfold crossPos; simp [show p < midPos j s by omega]), hr₁]; rfl
      · rw [insertSeq_lbl_ge s _ _ ⟨p, by omega⟩ (by simp; omega)
          (by unfold crossPos; simp [show ¬ p < midPos j s by omega]), hr₁]; rfl
    · rcases hlt with hlt | hlt
      · rw [insertSeq_lbl_lt s _ _ ⟨p + 1, hp⟩ (by simp; omega)
          (by unfold crossPos; simp [show p < midPos j s by omega]), hr₂]; rfl
      · rw [insertSeq_lbl_ge s _ _ ⟨p + 1, hp⟩ (by simp; omega)
          (by unfold crossPos; simp [show ¬ p < midPos j s by omega]; omega), hr₂]; rfl

end Model

end Categorification.Stendhal.CupCap
