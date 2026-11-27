/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapMidLeftFreeSurjStep
import Categorification.WeightedKLR.Rigidity.CupCapMidLeftFreeDots
import Categorification.WeightedKLR.Rigidity.CupCapMidLeftFreeSurjWords

/-!
# Surjectivity of the comparison map over the block shuffles

Webster, arXiv:1309.3796v3, §7.3, the assertion after Lemma 7.19 that `coe^{λ⁺}_λ` is projective
as a left `T^λ`-module, for a cap after the red strand `λ_j`: the comparison map
`midThetaBlock : ⨁_g T̃^λ e(s_g) ⊗_k L e(t_g) → K̃^{λ⁺}_λ` over the block shuffles is
surjective.

Write `Z ⊗ v` for the element `Ind.tmul (midGen (bot Z)) v` of the model (`midTmul`), for a KLR
diagram `Z` of `λ⁺` with top the window of a loading `s` of `λ`. The proof is by induction on
`n + N · B(s)`, where `n` is the crossing filtration degree of `Z` and `B(s) = m - midPos s` the
number of strands of `s` from `λ_{j+1}` on. Expanding `Z` with dots on top
(`KLRAlgebra.mem_span_dotsTop_of_mem_filt`), dots act through `T̃^λ` or through `L`, and a basis
element `ψ_{ρ w} e(i)` either is a block shuffle generator or has a left descent of one of four
kinds: two strands of the window (absorbed in `L`), a crossing away from `λ_{j+1}`
(`midKLRAct_ψ_tmul_midGen_of_far`), a black strand crossing `λ_{j+1}` from the left
(`tmul_midGen_ψ_eq_midKLRAct`, the pull-off identity), or a black strand crossing the window
and `λ_{j+1}` from the right (the right case of `midCrossAt`). Each lowers the measure.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA Equiv MulOpposite InductionAlong MvPolynomial

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "T" => StendhalAlgebra k Q Λ ν
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Rc" => KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)
local notation "ι" => insertMap (j := j) (hj := hj) (ν₀ := ν₀) Q Λ Λc
local notation "E" s:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s (midPos j s) (midPos_le j s))
local notation "Eat" s:max n:max hn:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s n hn)
local notation "bot" => botMap k Q Λ Λc j hj ν ν₀
local notation "𝓕" => KLRAlgebra.filt k (stendhalQ Q (plusLabels Λ Λc j hj))
  (stendhalWeight (ℓ + 2) (ν + ν₀))

variable {L : Type*} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}

/-! ### The elements `Z ⊗ v` of the model -/

variable (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)

/-- The element `Z ⊗ v` of the model, for a KLR diagram `Z` of `λ⁺` and `v ∈ L`. -/
def midTmul (Z : Rp) (v : L) : MidLeftModel L hL hR :=
  (Ind.tmul (midGen j hj Q Λ Λc ν ν₀ (bot Z)) v : MidModel j hj Q Λ Λc ν ν₀ L)

theorem midTmul_add (Z Z' : Rp) (v : L) :
    midTmul hR (Z + Z') v = midTmul hR Z v + midTmul hR Z' v := by
  simp only [midTmul, map_add, midGen_add, Ind.add_tmul]

theorem midTmul_smul (c : k) (Z : Rp) (v : L) :
    midTmul hR (c • Z) v = c • midTmul hR Z v := by
  simp only [midTmul, map_smul, midGen_smul, ← Ind.smul_tmul]
  rfl

theorem midTmul_of_bot_eq_zero {Z : Rp} (hZ : bot Z = 0) (v : L) : midTmul hR Z v = 0 := by
  have h : midGen j hj Q Λ Λc ν ν₀ 0 = 0 :=
    Subtype.ext (by rw [midGen_val, mul_zero, op_zero]; rfl)
  simp only [midTmul, hZ, h, Ind.zero_tmul]

/-- The action of the KLR algebra of `λ` on the model is the action of `T̃^λ`. -/
theorem midKLRAct_tmul_eq_smul (a : KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)) (Z : Rp)
    (v : L) :
    (midKLRAct hR a (Ind.tmul (midGen j hj Q Λ Λc ν ν₀ (bot Z)) v) : MidLeftModel L hL hR) =
      topMap k Q Λ ν a • midTmul hR Z v := by
  rw [midLeftModel_smul, midLeftAlg_topMap]
  rfl

/-- **A diagram at the maximum acts through `L`**: `ι_s(x) Z ⊗ v = E_s Z ⊗ x v`. -/
theorem midTmul_insertMap (s : Seq (stendhalWeight ℓ ν)) (x : Rc) (Z : Rp) (v : L) :
    midTmul hR (ι s (midPos j s) (midPos_le j s) x * Z) v =
      midTmul hR (E s * Z) (op (cupMap k Q Λc ν₀ x) • v) := by
  simp only [midTmul]
  rw [tmul_midGen_box, map_mul, map_mul, ← mul_assoc, midBot_mul_botMap_eSum]

theorem midTmul_zero_right (Z : Rp) : midTmul hR Z (0 : L) = 0 := by
  simp only [midTmul, Ind.tmul_zero]

/-! ### Dots -/

theorem eSum_commute_pol (S : Finset (Seq (stendhalWeight (ℓ + 2) (ν + ν₀))))
    (q : MvPolynomial (Fin M) k) :
    (KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj)) S * pol q : Rp) =
      pol q * KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj)) S := by
  rw [KLRAlgebra.eSum, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => (e_commute_pol i q).eq

theorem eSum_mul_mem_filt (S : Finset (Seq (stendhalWeight (ℓ + 2) (ν + ν₀)))) {n : ℕ} {r : Rp}
    (hr : r ∈ 𝓕 n) : KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj)) S * r ∈ 𝓕 n := by
  rw [KLRAlgebra.eSum, Finset.sum_mul]
  exact Submodule.sum_mem _ fun i _ => e_mul_mem i hr

theorem e_mem_filt (i : Seq (stendhalWeight (ℓ + 2) (ν + ν₀))) (n : ℕ) :
    (KLRAlgebra.e i : Rp) ∈ 𝓕 n := by
  simpa using pol_mul_e_mem (Q := stendhalQ Q (plusLabels Λ Λc j hj)) 1 i n

variable [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  [DecidableEq (MidBlockShuffle j hj ν ν₀)]
  (ρ₃ : Perm (Fin (Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀)))) → List ℕ)

/-- `Z ⊗ v` lies in the image of `midThetaBlock` for every `v ∈ L`. -/
def MidInIm (Z : Rp) : Prop := ∀ v : L, midTmul hR Z v ∈ LinearMap.range (midThetaBlock L hL ρ₃ hR)

theorem midInIm_add {Z Z' : Rp} (h : MidInIm hR ρ₃ Z) (h' : MidInIm hR ρ₃ Z') :
    MidInIm hR ρ₃ (Z + Z') := fun v => by
  rw [midTmul_add]; exact add_mem (h v) (h' v)

theorem midInIm_smul (c : k) {Z : Rp} (h : MidInIm hR ρ₃ Z) : MidInIm hR ρ₃ (c • Z) := fun v => by
  rw [midTmul_smul]; exact Submodule.smul_of_tower_mem _ c (h v)

theorem midInIm_zero : MidInIm hR ρ₃ (0 : Rp) := fun v =>
  (midTmul_of_bot_eq_zero hR (map_zero _) v) ▸ zero_mem _

theorem midInIm_of_bot_eq_zero {Z : Rp} (hZ : bot Z = 0) : MidInIm hR ρ₃ Z := fun v =>
  (midTmul_of_bot_eq_zero hR hZ v) ▸ zero_mem _

/-- **A dot acts through `T̃^λ` or through `L`**: for `Z` with top the window of `s`, if `Z ⊗ v`
lies in the image for all `v`, so does `x_a Z ⊗ v`. -/
theorem midInIm_x_mul (s : Seq (stendhalWeight ℓ ν)) {Z : Rp} (hZ : E s * Z = Z)
    (h : MidInIm hR ρ₃ Z) (a : Fin M) : MidInIm hR ρ₃ (KLRAlgebra.x a * Z) := fun v => by
  obtain ⟨b | b, hb⟩ : ∃ x, midPosEquiv j ν₀ s x = a := ⟨_, Equiv.apply_symm_apply _ a⟩
  · have hx : (KLRAlgebra.x a : Rp) = pol (rename (outPos j ν₀ s) (X b)) := by
      rw [rename_X, pol_X, outPos, hb]
    have h1 := midKLRAct_pol_tmul_midGen hR s (X b) Z hZ v
    rw [hx]
    change (Ind.tmul (midGen j hj Q Λ Λc ν ν₀ (bot (pol (rename (outPos j ν₀ s) (X b)) * Z))) v :
      MidLeftModel L hL hR) ∈ _
    rw [← h1, midKLRAct_tmul_eq_smul]
    exact Submodule.smul_mem _ _ (h v)
  · have hx : (KLRAlgebra.x a * Z : Rp) =
        ι s (midPos j s) (midPos_le j s) (KLRAlgebra.x b) * Z := by
      rw [insertMap_x, mul_assoc, hZ]
      congr 2
      rw [← hb, midPosEquiv_inr]
      rfl
    rw [hx, midTmul_insertMap, hZ]
    exact h _

/-- **Polynomials in the dots act through `T̃^λ` and `L`.** -/
theorem midInIm_pol_mul (s : Seq (stendhalWeight ℓ ν)) (q : MvPolynomial (Fin M) k) :
    ∀ {Z : Rp}, E s * Z = Z → MidInIm hR ρ₃ Z → MidInIm hR ρ₃ (pol q * Z) := by
  induction q using MvPolynomial.induction_on with
  | C c =>
    intro Z _ h
    rw [algHom_C, ← Algebra.smul_def]
    exact midInIm_smul hR ρ₃ c h
  | add p q hp hq =>
    intro Z hZ h
    rw [map_add, add_mul]
    exact midInIm_add hR ρ₃ (hp hZ h) (hq hZ h)
  | mul_X p a hp =>
    intro Z hZ h
    rw [map_mul, pol_X, mul_assoc]
    refine hp ?_ (midInIm_x_mul hR ρ₃ s hZ h a)
    rw [← mul_assoc, ← pol_X, eSum_commute_pol, mul_assoc, hZ]

/-! ### The induction measure and its steps -/

/-- **The surjectivity claim at measure `K`**: for every loading `s` of `λ` and every `r` in the
crossing filtration step `n` with `n + N · (m - midPos s) ≤ K`, `E_s r ⊗ v` lies in the image of
`midThetaBlock` for every `v`. -/
def MidSurjAt (K : ℕ) : Prop :=
  ∀ (s : Seq (stendhalWeight ℓ ν)) (n : ℕ) (r : Rp), r ∈ 𝓕 n →
    n + N * (m - midPos j s) ≤ K → MidInIm hR ρ₃ (E s * r)

/-- **A correction of lower degree**: if `ψ_{ρ w} y ≡ y'` modulo `filt (length w - 1)` and the
measure of `w` is at most `K`, the claim at `K - 1` reduces `E_s ψ_{ρ w} y` to `E_s y'`. -/
theorem midInIm_of_sub_mem {K : ℕ} (ih : MidSurjAt hR ρ₃ (K - 1)) (s : Seq (stendhalWeight ℓ ν))
    {n : ℕ} {X Y : Rp} (hXY : X - Y ∈ 𝓕 (n - 1)) (hn : 1 ≤ n) (hK : n + N * (m - midPos j s) ≤ K)
    (hY : MidInIm hR ρ₃ (E s * Y)) : MidInIm hR ρ₃ (E s * X) := by
  have h := ih s (n - 1) _ hXY (by omega)
  have : E s * X = E s * (X - Y) + E s * Y := by rw [mul_sub]; abel
  rw [this]
  exact midInIm_add hR ρ₃ h hY

/-- **Step: a crossing of two strands of the window** is absorbed in `L`. -/
theorem midInIm_window_step {K : ℕ} (ih : MidSurjAt hR ρ₃ (K - 1)) (s : Seq (stendhalWeight ℓ ν))
    {q : ℕ} (hq : q + 1 < N) {n : ℕ} {Y : Rp} (hY : Y ∈ 𝓕 n)
    (hK : n + N * (m - midPos j s) ≤ K - 1) :
    MidInIm hR ρ₃ (E s * (KLRAlgebra.ψ (midPos j s + q) * Y)) := fun v => by
  rw [← mul_assoc, eSum_insertSet_mul_ψ s (midPos_le j s) hq, ← insertMap_ψ s (midPos_le j s) hq,
    midTmul_insertMap]
  exact ih s n Y hY hK _

/-- **Step (i): a crossing away from `λ_{j+1}`** is the crossing `ψ_b` of `T̃^λ`. -/
theorem midInIm_far_step {K : ℕ} (ih : MidSurjAt hR ρ₃ (K - 1)) (s : Seq (stendhalWeight ℓ ν))
    {b : ℕ} (hb : b + 1 < m) (h1 : b + 1 ≠ midPos j s) (h2 : b ≠ midPos j s) {n : ℕ} {Y : Rp}
    (hY : Y ∈ 𝓕 n) (hK : n + N * (m - midPos j s) ≤ K - 1) :
    MidInIm hR ρ₃ (E s * (KLRAlgebra.ψ (crossPos (midPos j s) N b) * Y)) := fun v => by
  set s₁ := sadj m b • s
  have hm : midPos j s₁ = midPos j s := midPos_sadj_of_far j s hb (by omega)
  have hp : b + 1 < midPos j s ∨ midPos j s ≤ b := by omega
  have hc := ψ_crossPos_mul_eSum (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) s₁
    (midPos_le j s) hp
  rw [show sadj m b • s₁ = s from KLRAlgebra.sadj_smul_smul b s] at hc
  have hE : (E s₁ : Rp) = Eat s₁ (midPos j s) (midPos_le j s) :=
    eSum_insertSet_congr s₁ hm _ _
  have h := midKLRAct_ψ_tmul_midGen_of_far hR s₁ hb (by omega) (by omega) (E s₁ * Y)
    (by rw [← mul_assoc, (KLRAlgebra.eSum_idem (Q := stendhalQ Q (plusLabels Λ Λc j hj)) _).eq]) v
  rw [hE, hm, ← mul_assoc, hc] at h
  change (Ind.tmul (midGen j hj Q Λ Λc ν ν₀ (bot (E s * (_ * Y)))) v : MidLeftModel L hL hR) ∈ _
  rw [← mul_assoc, ← h, midKLRAct_tmul_eq_smul, ← hE]
  exact Submodule.smul_mem _ _ (ih s₁ n Y hY (by rw [hm]; exact hK) v)

/-- **Step (iii): a black strand crossing `λ_{j+1}` from the left**, by the pull-off identity
(`tmul_midGen_ψ_eq_midKLRAct`): the measure drops, as `underRight` adds `N` crossings and the
top has one strand fewer from `λ_{j+1}` on. -/
theorem midInIm_left_step (hP : PullOff k Q Λc ν₀ L) {K : ℕ} (ih : MidSurjAt hR ρ₃ (K - 1))
    (s : Seq (stendhalWeight ℓ ν)) (hc1 : midPos j s + 1 < m) {i₀ : I}
    (hs : s.lbl ⟨midPos j s + 1, hc1⟩ = .inl i₀) (hκ : IsUnit (cupScalar Q ν₀ i₀)) {n : ℕ}
    {Y : Rp} (hY : Y ∈ 𝓕 n) (hK : N + n + N * (m - (midPos j s + 1)) ≤ K - 1) :
    MidInIm hR ρ₃ (E s * (KLRAlgebra.ψ (midPos j s + N) * Y)) := fun v => by
  set c := midPos j s with hcdef
  set s₁ := sadj m c • s
  have hm : midPos j s₁ = c + 1 := midPos_sadj_right j s hc1 rfl
  have hcp := ψ_crossPos_mul_eSum (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) s₁
    (midPos_le j s) (p := c) (Or.inr le_rfl)
  rw [show sadj m c • s₁ = s from KLRAlgebra.sadj_smul_smul c s,
    show crossPos c N c = c + N by simp [crossPos]] at hcp
  have hZ : Eat s₁ c (midPos_le j s) * (Eat s₁ c (midPos_le j s) * Y) =
      Eat s₁ c (midPos_le j s) * Y := by
    rw [← mul_assoc, (KLRAlgebra.eSum_idem (Q := stendhalQ Q (plusLabels Λ Λc j hj)) _).eq]
  have h := tmul_midGen_ψ_eq_midKLRAct hR hP i₀ hκ s hc1 hs _ hZ v
  have hZ' : E s₁ * (underRight N c * (Eat s₁ c (midPos_le j s) * Y)) =
      underRight N c * (Eat s₁ c (midPos_le j s) * Y) := by
    rw [eSum_insertSet_congr s₁ hm (midPos_le j s₁) (by omega), ← mul_assoc,
      ← underRight_mul_eSum Q Λ Λc s₁ (q := c) (by omega), mul_assoc, hZ]
  change (Ind.tmul (midGen j hj Q Λ Λc ν ν₀ (bot (E s * (_ * Y)))) v : MidLeftModel L hL hR) ∈ _
  rw [← mul_assoc, ← hcp, mul_assoc, h, midKLRAct_tmul_eq_smul, ← hZ']
  refine Submodule.smul_mem _ _ (ih s₁ (N + n) _ ?_ (by rw [hm]; exact hK) _)
  have := ψw_mul_mem (List.range' c N)
    (eSum_mul_mem_filt (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s₁ c (midPos_le j s)) hY)
  simpa [underRight] using this

/-- **Step (ii): a black strand crossing the window and `λ_{j+1}` from the right** is the right
case of `midCrossAt`, the crossing `ψ_b` of `T̃^λ` with `λ_{j+1}` at `b + 1`, up to the unit
`κ`: the measure drops, as `N + 1` crossings go and the top gains a strand from `λ_{j+1}` on. -/
theorem midInIm_right_step {K : ℕ} (ih : MidSurjAt hR ρ₃ (K - 1)) (s : Seq (stendhalWeight ℓ ν))
    {b : ℕ} (hb : b + 1 < m) (hc : b + 1 = midPos j s) {i₀ : I}
    (hs : s.lbl ⟨b, by omega⟩ = .inl i₀) (hκ : IsUnit (cupScalar Q ν₀ i₀)) {n : ℕ} {Y : Rp}
    (hY : Y ∈ 𝓕 n) (hK : n + N * (m - b) ≤ K - 1) :
    MidInIm hR ρ₃ (E s * (ψw (List.range' b (N + 1)) * Y)) := fun v => by
  set s₁ := sadj m b • s
  have hm : midPos j s₁ = b := midPos_sadj_left j s hb hc
  have hlbl : s₁.lbl ⟨b + 1, hb⟩ = .inl i₀ := by
    change s.lbl ((sadj m b)⁻¹ ⟨b + 1, hb⟩) = _
    rw [sadj_inv, sadj_apply_right hb]; exact hs
  have hu := underRight_mul_eSum (j := j) (hj := hj) (ν₀ := ν₀) Q Λ Λc s (q := b) (by omega)
  have hcp := ψ_crossPos_mul_eSum (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) s₁
    (n := b) (by omega) (p := b) (Or.inr le_rfl)
  rw [show sadj m b • s₁ = s from KLRAlgebra.sadj_smul_smul b s,
    show crossPos b N b = b + N by simp [crossPos]] at hcp
  have hE : (E s : Rp) = Eat s (b + 1) (by omega) := eSum_insertSet_congr s hc.symm _ _
  have hE₁ : (E s₁ : Rp) = Eat s₁ b (by omega) := eSum_insertSet_congr s₁ hm _ _
  have hcross := midCrossAt_of_right (j := j) (hj := hj) (Q := Q) (Λ := Λ) (Λc := Λc) (ν := ν)
    (ν₀ := ν₀) s₁ hb hm.symm hlbl
  have hidem := (KLRAlgebra.eSum_idem (Q := stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s₁ b (by omega))).eq
  have key : E s * (ψw (List.range' b (N + 1)) * Y) =
      cupScalar Q ν₀ i₀ • (midCrossAt j hj Q Λ Λc ν ν₀ s₁ b * (E s₁ * Y)) := by
    rw [hcross, smul_mul_assoc, smul_smul, Ring.mul_inverse_cancel _ hκ, one_smul,
      List.range'_concat, one_mul, ψw_append, ψw_cons, ψw_nil, mul_one, hE, hE₁,
      show (ψw (List.range' b N) : Rp) = underRight N b from rfl]
    rw [← mul_assoc, ← mul_assoc, ← hu, mul_assoc (underRight N b), ← hcp]
    simp only [mul_assoc, ← mul_assoc (Eat s₁ b _) (Eat s₁ b _) Y, hidem]
  have h := midKLRAct_ψ_tmul_midGen hR s₁ b (E s₁ * Y)
    (by rw [← mul_assoc, (KLRAlgebra.eSum_idem (Q := stendhalQ Q (plusLabels Λ Λc j hj)) _).eq]) v
  have h2 : midTmul hR (midCrossAt j hj Q Λ Λc ν ν₀ s₁ b * (E s₁ * Y)) v =
      topMap k Q Λ ν (KLRAlgebra.ψ b) • midTmul hR (E s₁ * Y) v := by
    rw [← midKLRAct_tmul_eq_smul, h]; rfl
  rw [key, midTmul_smul, h2]
  exact Submodule.smul_of_tower_mem _ _
    (Submodule.smul_mem _ _ (ih s₁ n Y hY (by rw [hm]; exact hK) v))

/-! ### The block shuffles -/


/-- The element `v γ_g` of a block shuffle `g` is in the image of `midThetaBlock`. -/
theorem midLeftGen_mem_range (g : MidBlockShuffle j hj ν ν₀)
    (v : BalancedTensor.idemPart k L (midGenIdem (k := k) Q Λc g.1.1)) :
    midLeftGen L hL ρ₃ hR g.1 v ∈ LinearMap.range (midThetaBlock L hL ρ₃ hR) := by
  refine ⟨DirectSum.lof T _ (fun g => MidLeftSummand Q Λ Λc L g.1) g
    (⟨_, Submodule.subset_span rfl⟩ ⊗ₜ v), ?_⟩
  rw [midThetaBlock, DirectSum.toModule_lof, TensorProduct.AlgebraTensorModule.lift_tmul]
  change (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λ) g.1.1.s g.1.1.hs : T) •
    midLeftGen L hL ρ₃ hR g.1 v = _
  rw [midLeftModel_smul, midLeftGen_apply, midLeftAlg_e_tmul_midGenCorner hR g.1.1 (v : L)]

/-- **The base case: a block shuffle**. If the window strands and the strands of `λ` of
`ψ_{ρ w} e(i)`, with top `midSeq s t`, both keep their order, it is the generator of a block
shuffle, so `E_s ψ_{ρ w} e(i) ⊗ v` is in the image. -/
theorem midInIm_block (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w)
    (s : Seq (stendhalWeight ℓ ν)) (t : Seq (stendhalWeight 2 ν₀)) (w : Perm (Fin M))
    (i : Seq (stendhalWeight (ℓ + 2) (ν + ν₀))) (hx : midSeq j hj s t = w • i)
    (hi : IsRedOrdered i) (hxo : IsRedOrdered (midSeq j hj s t))
    (hW : StrictMono fun q : Fin N => w⁻¹ (winPos (midPos_add_N_le j ν₀ s) q))
    (hL₀ : StrictMono fun b : Fin m => w⁻¹ (outPos j ν₀ s b)) :
    MidInIm hR ρ₃ (E s * (ψw (ρ₃ w) * KLRAlgebra.e i)) := fun v => by
  obtain ⟨hs, ht⟩ := (isRedOrdered_midSeq s t).1 hxo
  let g : MidGen j hj ν ν₀ :=
    ⟨s, t, 0, w, hs, ht, by simp, hW, by rw [hx, inv_smul_smul]; exact hi⟩
  have hbot : g.bot = i := by
    change w⁻¹ • midSeq j hj s t = i
    rw [hx, inv_smul_smul]
  have hperm : g.perm = 1 := by
    have hbo : (fun b => w⁻¹ (outPos j ν₀ s b)) = g.botOrd :=
      Finset.orderEmbOfFin_unique g.card_botSet
        (fun b => Finset.mem_map_of_mem _ (Finset.mem_univ b)) hL₀
    ext b
    have h1 := g.botEquiv_perm b
    rw [← hbo] at h1
    exact congrArg Fin.val (Sum.inl_injective (g.botEquiv.injective h1))
  have h1 : (ψw (ρ₃ w) * KLRAlgebra.e i : Rp) =
      KLRAlgebra.e (midSeq j hj s t) * (ψw (ρ₃ w) * KLRAlgebra.e i) := by
    rw [hx, ← mul_assoc, e_mul_ψw, (hρ₃ w).2, inv_smul_smul, mul_assoc, e_mul_self]
  have hEm : (E s * KLRAlgebra.e (midSeq j hj s t) : Rp) = KLRAlgebra.e (midSeq j hj s t) :=
    eSum_mul_e_insertSeq Q Λ Λc s _ _
  have hι : ι s (midPos j s) (midPos_le j s) (KLRAlgebra.e t) =
      KLRAlgebra.e (midSeq j hj s t) := insertMap_e s _ t
  have hgen : midGenKLR Q Λ Λc ρ₃ g = E s * (ψw (ρ₃ w) * KLRAlgebra.e i) := by
    rw [h1, ← mul_assoc, hEm]
    change KLRAlgebra.e (midSeq j hj s t) * pol (rename (outPos j ν₀ s) (monomial 0 1)) *
      ψw (ρ₃ w) * KLRAlgebra.e g.bot = _
    rw [hbot, monomial_zero', C_1, map_one, map_one, mul_one, mul_assoc]
  have hct : cupMap k Q Λc ν₀ (KLRAlgebra.e t) =
      StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht :=
    topMap_e_of_isRedOrdered t ht
  set v' := op (cupMap k Q Λc ν₀ (KLRAlgebra.e t)) • v
  have hv' : v' ∈ BalancedTensor.idemPart k L (midGenIdem (k := k) Q Λc g) := by
    change midGenIdem (k := k) Q Λc g • v' = v'
    have he := isIdempotentElem_midGenIdem (k := k) (Q := Q) (Λc := Λc) g
    simp only [v', hct]
    change midGenIdem (k := k) Q Λc g • midGenIdem (k := k) Q Λc g • v = midGenIdem Q Λc g • v
    rw [← mul_smul, he.eq]
  have hval : midTmul hR (E s * (ψw (ρ₃ w) * KLRAlgebra.e i)) v =
      midLeftGen L hL ρ₃ hR ⟨g, rfl⟩ ⟨v', hv'⟩ := by
    rw [midLeftGen_apply, midGenCorner_eq_midGen, midGenElt, hgen]
    conv_lhs => rw [h1, ← mul_assoc, hEm, ← hι, midTmul_insertMap]
    rfl
  rw [hval]
  exact midLeftGen_mem_range hR ρ₃ ⟨⟨g, rfl⟩, hperm⟩ _

/-! ### The induction -/

omit [DecidableEq I] in
/-- Red strands keep their order: if `i` and `w • i` are red-ordered, two red strands at the top
positions `a < a'` come from bottom positions `w⁻¹ a < w⁻¹ a'`. -/
theorem lt_of_isRedOrdered_smul {μ : Multiset (I ⊕ Fin (ℓ + 2))} {w : Perm (Fin (Multiset.card μ))}
    {i : Seq μ} (hi : IsRedOrdered i) (hwi : IsRedOrdered (w • i)) {a a' : Fin (Multiset.card μ)}
    (h : a < a') {r r' : Fin (ℓ + 2)} (ha : (w • i).lbl a = .inr r)
    (ha' : (w • i).lbl a' = .inr r') :
    w⁻¹ a < w⁻¹ a' := by
  rcases lt_trichotomy (w⁻¹ a) (w⁻¹ a') with hlt | heq | hgt
  · exact hlt
  · exact absurd (w⁻¹.injective heq) h.ne
  · exact absurd (hi _ _ r' r hgt ha' ha) (hwi a a' r r' h ha ha').asymm

omit [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  [DecidableEq (MidBlockShuffle j hj ν ν₀)] in
theorem ψw_e_mem_filt (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w) (w : Perm (Fin M))
    (i : Seq (stendhalWeight (ℓ + 2) (ν + ν₀))) :
    (ψw (ρ₃ w) * KLRAlgebra.e i : Rp) ∈ 𝓕 (length M w) := by
  have h := mem_filt (Q := stendhalQ Q (plusLabels Λ Λc j hj)) (hρ₃ w).1.1
    (n := length M w) (by rw [(hρ₃ w).1.length_eq, (hρ₃ w).2]) 1 i
  simpa using h

/-- **The induction step on a basis element** `E_s ψ_{ρ w} e(i)` of measure at most `K`:
a block shuffle generator, zero, or reduced by one of the four steps to the claim at `K - 1`. -/
theorem midInIm_basis (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w)
    (hP : PullOff k Q Λc ν₀ L) (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i)) {K : ℕ}
    (ih : 1 ≤ K → MidSurjAt hR ρ₃ (K - 1)) (s : Seq (stendhalWeight ℓ ν)) (w : Perm (Fin M))
    (i : Seq (stendhalWeight (ℓ + 2) (ν + ν₀))) (hK : length M w + N * (m - midPos j s) ≤ K) :
    MidInIm hR ρ₃ (E s * (ψw (ρ₃ w) * KLRAlgebra.e i)) := by
  set c := midPos j s with hcdef
  have hK' : length M w + N * (m - midPos j s) ≤ K := hK
  have hcN : c + N ≤ M := midPos_add_N_le j ν₀ s
  have hcm : c ≤ m := midPos_le j s
  have hMm : M = m + N := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
  have hN2 : 2 ≤ N := two_le_card_stendhalWeight ν₀
  have hψe : (ψw (ρ₃ w) * KLRAlgebra.e i : Rp) = KLRAlgebra.e (w • i) * ψw (ρ₃ w) := by
    rw [ψw_mul_e, (hρ₃ w).2]
  by_cases hmem : w • i ∈ insertSet (j := j) (hj := hj) (ν₀ := ν₀) s c (midPos_le j s)
  swap
  · have h0 : E s * (ψw (ρ₃ w) * KLRAlgebra.e i) = 0 := by
      rw [hψe, ← mul_assoc, KLRAlgebra.eSum_mul_e, ite_eq_right_iff.2 (fun h => absurd h hmem),
        zero_mul]
    rw [h0]; exact midInIm_zero hR ρ₃
  obtain ⟨t', -, ht'⟩ := Finset.mem_image.1 hmem
  obtain ⟨t, rfl⟩ := (Seq.mapEquiv (cupColour_injective j hj) (stendhalWeight 2 ν₀)).surjective t'
  have hx : midSeq j hj s t = w • i := ht'
  by_cases hi : IsRedOrdered i
  swap
  · apply midInIm_of_bot_eq_zero
    rw [map_mul, map_mul, botMap_e_of_not Q Λ Λc hi, mul_zero, mul_zero]
  by_cases hxo : IsRedOrdered (midSeq j hj s t)
  swap
  · apply midInIm_of_bot_eq_zero
    rw [hψe, ← hx, map_mul, map_mul, botMap_e_of_not Q Λ Λc hxo, zero_mul, mul_zero]
  have hwi : IsRedOrdered (w • i) := hx ▸ hxo
  have h1 : (ψw (ρ₃ w) * KLRAlgebra.e i : Rp) =
      KLRAlgebra.e (midSeq j hj s t) * (ψw (ρ₃ w) * KLRAlgebra.e i) := by
    rw [hx, ← mul_assoc, e_mul_ψw, (hρ₃ w).2, inv_smul_smul, mul_assoc, e_mul_self]
  by_cases hcap : IsCapGood ν₀ t
  swap
  · intro v
    have hEm : (E s * KLRAlgebra.e (midSeq j hj s t) : Rp) = KLRAlgebra.e (midSeq j hj s t) :=
      eSum_mul_e_insertSeq Q Λ Λc s _ _
    have hι : ι s (midPos j s) (midPos_le j s) (KLRAlgebra.e t) =
        KLRAlgebra.e (midSeq j hj s t) := insertMap_e s _ t
    rw [h1, ← mul_assoc, hEm, ← hι, midTmul_insertMap, hL t v hcap, midTmul_zero_right]
    exact zero_mem _
  -- labels at the top
  have hred : ∀ a a' : Fin M, a < a' → ∀ r r' : Fin (ℓ + 2),
      (midSeq j hj s t).lbl a = .inr r → (midSeq j hj s t).lbl a' = .inr r' → w⁻¹ a < w⁻¹ a' :=
    fun a a' h r r' ha ha' => lt_of_isRedOrdered_smul hi hwi h (hx ▸ ha) (hx ▸ ha')
  have hlblL : ∀ a : Fin m, (midSeq j hj s t).lbl (outPos j ν₀ s a) = oldColour j hj (s.lbl a) :=
    fun a => by
      have e : outPos j ν₀ s a = Fin.cast (card_plus j hj ν ν₀).symm
          (insertPos _ _ (midPos j s) (midPos_le j s) (.inl a)) :=
        Fin.ext (by rw [outPos_val]; simp)
      rw [e]; exact midSeq_lbl_old s t a
  have hpos : ∀ a : Fin m, (outPos j ν₀ s a).val = if a.val < c then a.val else a.val + N :=
    fun a => outPos_val s a
  -- a window descent
  by_cases hW : StrictMono fun q : Fin N => w⁻¹ (winPos hcN q)
  swap
  · obtain ⟨q, hq, hlt⟩ := exists_lt_of_not_strictMono
      (fun a b h => winPos_injective hcN (w⁻¹.injective h)) hW
    have ha : c + q + 1 < M := by omega
    have hlt' : w⁻¹ ⟨c + q + 1, ha⟩ < w⁻¹ ⟨c + q, by omega⟩ := hlt
    have hd := ψw_sub_ψ_mul_mem_filt ρ₃ hρ₃ ha hlt'
      (e_mem_filt (Q := Q) (Λ := Λ) (Λc := Λc) (hj := hj) i 0)
    have hl := length_sadj_mul_of_gt ha hlt'
    rw [add_zero] at hd
    exact midInIm_of_sub_mem hR ρ₃ (ih (by omega)) s hd (by omega) hK
      (midInIm_window_step hR ρ₃ (ih (by omega)) s hq (ψw_e_mem_filt ρ₃ hρ₃ _ i) (by omega))
  by_cases hLam : StrictMono fun b : Fin m => w⁻¹ (outPos j ν₀ s b)
  · exact midInIm_block hR ρ₃ hρ₃ s t w i hx hi hxo hW hLam
  obtain ⟨b, hb, hlt⟩ := exists_lt_of_not_strictMono
    (fun a b h => outPos_injective s (w⁻¹.injective h)) hLam
  -- a red strand of `λ` next to a red strand cannot cross it
  have hnored : ∀ r r' : Fin ℓ, s.lbl ⟨b, by omega⟩ = .inr r → s.lbl ⟨b + 1, hb⟩ = .inr r' →
      False := by
    intro r r' hr hr'
    have hlt2 : outPos j ν₀ s ⟨b, by omega⟩ < outPos j ν₀ s ⟨b + 1, hb⟩ :=
      Fin.lt_def.2 (by rw [hpos, hpos]; dsimp only; split_ifs <;> omega)
    have := hred _ _ hlt2 _ _ (by rw [hlblL, hr]; rfl) (by rw [hlblL, hr']; rfl)
    exact (lt_asymm this hlt)
  have hjl : ∀ (hc : c < m), ∃ h : j < ℓ, s.lbl ⟨c, hc⟩ = .inr ⟨j, h⟩ := by
    intro hc
    have h : j < ℓ := lt_of_midPos_lt j hc le_rfl
    obtain ⟨a, ha, hla⟩ := midPos_of_lt j s h
    exact ⟨h, by rw [← hla]; congr 1; exact Fin.ext ha.symm⟩
  by_cases h1c : b + 1 = c
  · -- (ii): a black strand crosses the window and `λ_{j+1}` from the right
    obtain ⟨hjl', hredJ⟩ := hjl (by omega)
    rcases hsb : s.lbl ⟨b, by omega⟩ with i₀ | r
    swap
    · exact (hnored r ⟨j, hjl'⟩ hsb (by rw [← hredJ]; congr 1; exact Fin.ext h1c)).elim
    have e0 : outPos j ν₀ s ⟨b, by omega⟩ = ⟨b, by omega⟩ := Fin.ext (by rw [hpos]; simp; omega)
    have e1 : outPos j ν₀ s ⟨b + 1, hb⟩ = ⟨b + 1 + N, by omega⟩ :=
      Fin.ext (by rw [hpos]; simp; omega)
    rw [e0, e1] at hlt
    have hlast : (midSeq j hj s t).lbl (winPos hcN ⟨N - 1, by omega⟩) = .inr (cupRed j hj 1) := by
      rw [midSeq_lbl_winPos, hcap.2]; rfl
    have hredLbl : (midSeq j hj s t).lbl ⟨b + 1 + N, by omega⟩ = .inr (oldRed j hj ⟨j, hjl'⟩) := by
      rw [← e1, hlblL, show (⟨b + 1, hb⟩ : Fin m) = ⟨c, by omega⟩ from Fin.ext h1c, hredJ]; rfl
    have hinv : ∀ q (hq : q < N + 1), w⁻¹ ⟨b + 1 + q, by omega⟩ < w⁻¹ ⟨b, by omega⟩ := by
      intro q hq
      refine lt_of_le_of_lt ?_ hlt
      rcases Nat.lt_or_ge q N with hqN | hqN
      · have ew : (⟨b + 1 + q, by omega⟩ : Fin M) = winPos hcN ⟨q, hqN⟩ :=
          Fin.ext (by simp; omega)
        rw [ew]
        refine le_of_lt (lt_of_le_of_lt (hW.monotone (show (⟨q, hqN⟩ : Fin N) ≤ ⟨N - 1, by omega⟩
          from Fin.mk_le_mk.2 (by omega))) ?_)
        exact hred _ _ (Fin.lt_def.2 (by simp; omega)) _ _ hlast hredLbl
      · exact le_of_eq (congrArg _ (Fin.ext (by simp; omega)))
    obtain ⟨u', hu', hd⟩ := exists_ψw_range_sub_mem_filt ρ₃ hρ₃ (N + 1) b w (by omega) hinv
      (e_mem_filt (Q := Q) (Λ := Λ) (Λc := Λc) (hj := hj) i 0)
    rw [add_zero] at hd
    have hmeas : N * (m - b) = N * (m - c) + N := by
      rw [show m - b = (m - c) + 1 by omega, Nat.mul_succ]
    exact midInIm_of_sub_mem hR ρ₃ (ih (by omega)) s hd (by omega) hK'
      (midInIm_right_step hR ρ₃ (ih (by omega)) s hb h1c hsb (hκ i₀)
        (ψw_e_mem_filt ρ₃ hρ₃ u' i) (by omega))
  by_cases h2c : b = c
  · -- (iii): `λ_{j+1}` crosses the black strand to its right, together with the window
    subst h2c
    obtain ⟨hjl', hredJ⟩ := hjl (by omega)
    rcases hsb : s.lbl ⟨c + 1, hb⟩ with i₀ | r
    swap
    · exact (hnored ⟨j, hjl'⟩ r hredJ hsb).elim
    have e0 : outPos j ν₀ s ⟨c, by omega⟩ = ⟨c + N, by omega⟩ :=
      Fin.ext (by rw [hpos]; simp)
    have e1 : outPos j ν₀ s ⟨c + 1, hb⟩ = ⟨c + N + 1, by omega⟩ :=
      Fin.ext (by rw [hpos]; simp; omega)
    rw [e0, e1] at hlt
    have ha : c + N + 1 < M := by omega
    have hd := ψw_sub_ψ_mul_mem_filt ρ₃ hρ₃ ha hlt
      (e_mem_filt (Q := Q) (Λ := Λ) (Λc := Λc) (hj := hj) i 0)
    have hl := length_sadj_mul_of_gt ha hlt
    rw [add_zero] at hd
    have hmeas : N * (m - midPos j s) = N * (m - (midPos j s + 1)) + N := by
      rw [show m - midPos j s = (m - (midPos j s + 1)) + 1 by omega, Nat.mul_succ]
    exact midInIm_of_sub_mem hR ρ₃ (ih (by omega)) s hd (by omega) hK'
      (midInIm_left_step hR ρ₃ hP (ih (by omega)) s hb hsb (hκ i₀)
        (ψw_e_mem_filt ρ₃ hρ₃ _ i) (by omega))
  -- (i): two strands of `λ` away from `λ_{j+1}` cross
  have ha : crossPos c N b + 1 < M := by simp only [crossPos]; split_ifs <;> omega
  have e0 : outPos j ν₀ s ⟨b, by omega⟩ = ⟨crossPos c N b, by omega⟩ :=
    Fin.ext (by rw [hpos]; dsimp only; unfold crossPos; split_ifs <;> omega)
  have e1 : outPos j ν₀ s ⟨b + 1, hb⟩ = ⟨crossPos c N b + 1, ha⟩ :=
    Fin.ext (by rw [hpos]; dsimp only; unfold crossPos; split_ifs <;> omega)
  rw [e0, e1] at hlt
  have hd := ψw_sub_ψ_mul_mem_filt ρ₃ hρ₃ ha hlt
    (e_mem_filt (Q := Q) (Λ := Λ) (Λc := Λc) (hj := hj) i 0)
  have hl := length_sadj_mul_of_gt ha hlt
  rw [add_zero] at hd
  exact midInIm_of_sub_mem hR ρ₃ (ih (by omega)) s hd (by omega) hK'
    (midInIm_far_step hR ρ₃ (ih (by omega)) s hb h1c h2c (ψw_e_mem_filt ρ₃ hρ₃ _ i) (by omega))

/-- **The induction on the measure** `n + N · (m - midPos s)`: every `E_s r ⊗ v` with
`r ∈ filt n` lies in the image of `midThetaBlock`. -/
theorem midSurjAt_all (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w)
    (hP : PullOff k Q Λc ν₀ L) (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i)) (K : ℕ) :
    MidSurjAt hR ρ₃ K := by
  induction K using Nat.strong_induction_on with
  | _ K ihK =>
  intro s n r hr hK
  have ih : 1 ≤ K → MidSurjAt hR ρ₃ (K - 1) := fun h => ihK _ (by omega)
  have hspan := mem_span_dotsTop_of_mem_filt ρ₃ hρ₃ hr
  clear hr
  induction hspan using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, u, i, hw, rfl⟩ := hy
    have hE : E s * (pol (monomial u 1) * ψw (ρ₃ w) * KLRAlgebra.e i) =
        pol (monomial u 1) * (E s * (ψw (ρ₃ w) * KLRAlgebra.e i)) := by
      rw [mul_assoc (pol _), ← mul_assoc, eSum_commute_pol, mul_assoc]
    rw [hE]
    exact midInIm_pol_mul hR ρ₃ s _ (by rw [← mul_assoc, eSum_mul_eSum, Finset.inter_self])
      (midInIm_basis hR ρ₃ hρ₃ hP hκ ih s w i (by omega))
  | zero => rw [mul_zero]; exact midInIm_zero hR ρ₃
  | add y y' _ _ h h' => rw [mul_add]; exact midInIm_add hR ρ₃ h h'
  | smul c y _ h => rw [mul_smul_comm]; exact midInIm_smul hR ρ₃ c h

/-- **The comparison map over the block shuffles is surjective** (Webster, arXiv:1309.3796v3,
§7.3, a cap after `λ_j`), when the cup scalars are units and `L` satisfies the pull-off
identity. -/
theorem midThetaBlock_surjective (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w)
    (hP : PullOff k Q Λc ν₀ L) (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i)) :
    Function.Surjective (midThetaBlock L hL ρ₃ hR) := by
  intro y
  refine Ind.induction_on (motive := fun y : MidModel j hj Q Λ Λc ν ν₀ L =>
    (y : MidLeftModel L hL hR) ∈ LinearMap.range (midThetaBlock L hL ρ₃ hR)) y
    (zero_mem _) (fun z v => ?_) (fun _ _ h h' => add_mem h h')
  rw [← midGen_botMap_midMapKLR_one z]
  obtain ⟨Z, hZ⟩ := botMap_surjective (k := k) (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj)
    (ν := ν) (ν₀ := ν₀) z.1.unop
  rw [← hZ, ← map_mul, midMapKLR_one, Finset.sum_mul, map_sum, ← sum_tmul_midGen]
  refine sum_mem fun s _ => ?_
  obtain ⟨n, hn⟩ := exists_mem_filt Z
  exact midSurjAt_all hR ρ₃ hρ₃ hP hκ _ s n Z hn le_rfl v

end Categorification.Stendhal.CupCap
