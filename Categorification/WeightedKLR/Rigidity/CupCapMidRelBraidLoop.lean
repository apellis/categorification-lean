/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapMidRelBraidCases

/-!
# The braid relation on the model of a cap after `λ_j`

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.17. Two diagrams of `λ⁺` act alike on the
model `L ⊗ e T̃^{λ⁺}` as soon as they act alike on the elements `e Z ⊗ v`
(`CupCap.MidTmulRel`). This relation is linear, contains the diagrams in which a strand leaves
the window at the top, and removes the loops of a black strand under the maximum: on the left of
the maximum at the top or at the bottom of a diagram, and on its right at the top, each with the
scalar of (max1). With these, the braid relation with `λ_{j+1}` between the two black strands
is checked on the model, and the braid relation holds on the model in all positions.

## Main results

* `CupCap.midRel_braid`: the braid relation of `T̃^λ` on the model.
* `CupCap.midTmulRel_braid_of_mid`: the case with `λ_{j+1}` at `p + 1`.
* `CupCap.passing_ncEval_mem`: polynomials in the dots slide down a passage.

* `CupCap.MidTmulRel.of_sub_mem`: diagrams that differ by exits act alike.
* `CupCap.MidTmulRel.leftLoop_top`, `CupCap.MidTmulRel.leftLoop_bottom`,
  `CupCap.MidTmulRel.rightLoop_top`: removing loops.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MulOpposite InductionAlong

section Passing

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Eat" s:max n:max hn:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s n hn)
local notation "uL" => underLeft (k := k) (Q := stendhalQ Q (plusLabels Λ Λc j hj))
  (ν := stendhalWeight (ℓ + 2) (ν + ν₀)) N

omit [DecidableEq I] in
theorem add_N_add_two_lt_M {p : ℕ} (hq : p + 2 < m) : p + N + 2 < M := by
  have := card_plus_braid (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀); omega

omit [DecidableEq I] in
theorem commute_ncEval {A : Type*} [Ring A] [Algebra k A] {n : ℕ} (y : Fin n → A) {e : A}
    (h : ∀ a, Commute (y a) e) (P : MvPolynomial (Fin n) k) : Commute (ncEval y P) e := by
  induction P using MvPolynomial.induction_on' with
  | monomial u c =>
    rw [ncEval_monomial]
    refine (Algebra.commute_algebraMap_left c e).mul_left
      (Commute.list_prod_left _ _ fun z hz => ?_)
    obtain ⟨a, rfl⟩ := (List.mem_ofFn' _ _).1 hz
    exact (h a).pow_left _
  | add P P' hP hP' => rw [ncEval_add]; exact hP.add_left hP'

/-- **Polynomials in the dots slide down a passage** to the left of the maximum, modulo diagrams
in which a strand leaves the window at the top: the dot on the passing strand moves from
`p + N` to `p`, and the dots on the next two strands stay. -/
theorem passing_ncEval_mem (s : Seq (stendhalWeight ℓ ν)) {p : ℕ} (hq : p + 2 < m)
    (P : MvPolynomial (Fin 3) k) :
    ncEval ![(KLRAlgebra.x ⟨p + N, add_N_lt_M_of_succ_le (by omega : p + 1 ≤ m)⟩ : Rp),
          KLRAlgebra.x ⟨p + N + 1, by have := add_N_add_two_lt_M (ν₀ := ν₀) hq; omega⟩,
          KLRAlgebra.x ⟨p + N + 2, add_N_add_two_lt_M (ν₀ := ν₀) hq⟩] P *
        Eat s p (by omega) * uL p * Eat s (p + 1) (by omega) -
      uL p * (ncEval ![(KLRAlgebra.x ⟨p, lt_M_of_succ_le (by omega : p + 1 ≤ m)⟩ : Rp),
          KLRAlgebra.x ⟨p + N + 1, by have := add_N_add_two_lt_M (ν₀ := ν₀) hq; omega⟩,
          KLRAlgebra.x ⟨p + N + 2, add_N_add_two_lt_M (ν₀ := ν₀) hq⟩] P *
        Eat s (p + 1) (by omega)) ∈ exitSpan Q Λ Λc j hj s p (by omega) := by
  have hq1 : p + 1 ≤ m := by omega
  set B : Rp := KLRAlgebra.x ⟨p + N + 1, by have := add_N_add_two_lt_M (ν₀ := ν₀) hq; omega⟩
  set C' : Rp := KLRAlgebra.x ⟨p + N + 2, add_N_add_two_lt_M (ν₀ := ν₀) hq⟩
  set y : Rp := KLRAlgebra.x ⟨p + N, add_N_lt_M_of_succ_le hq1⟩
  set z : Rp := KLRAlgebra.x ⟨p, lt_M_of_succ_le hq1⟩
  set E0 : Rp := Eat s p (by omega)
  set E1 : Rp := Eat s (p + 1) hq1
  have hLE : uL p * E1 = E0 * uL p := underLeft_mul_eSum s hq1
  have hE1 : E1 * E1 = E1 := (KLRAlgebra.eSum_idem _).eq
  have hBC : ∀ T : Rp, Commute B T → Commute C' T → ∀ a : Fin 2, Commute (![B, C'] a) T :=
    fun T hB hC a => by fin_cases a <;> assumption
  have hBL : Commute B (uL p) := KLRAlgebra.commute_x_ψw fun l hl => by
    rw [List.mem_reverse, List.mem_range'_1] at hl; dsimp only; omega
  have hCL : Commute C' (uL p) := KLRAlgebra.commute_x_ψw fun l hl => by
    rw [List.mem_reverse, List.mem_range'_1] at hl; dsimp only; omega
  induction P using MvPolynomial.induction_on' with
  | monomial u c =>
    set w : Rp := (List.ofFn fun a : Fin 2 => ![B, C'] a ^ u a.succ).prod
    have hsplit : ∀ y0 : Rp, ncEval ![y0, B, C'] (MvPolynomial.monomial u c) =
        algebraMap k Rp c * (y0 ^ u 0 * w) := fun y0 => by
      rw [ncEval_monomial, List.ofFn_succ, List.prod_cons]; rfl
    rw [hsplit, hsplit]
    have hw : ∀ T : Rp, Commute B T → Commute C' T → Commute w T := fun T hB hC =>
      Commute.list_prod_left _ _ fun e he => by
        obtain ⟨a, rfl⟩ := (List.mem_ofFn' _ _).1 he
        exact (hBC T hB hC a).pow_left _
    have hwL := (hw _ hBL hCL).eq
    have hw0 := (hw E0 (commute_x_eSum _ _) (commute_x_eSum _ _)).eq
    have hw1 := (hw E1 (commute_x_eSum _ _) (commute_x_eSum _ _)).eq
    have hy0 : y ^ u 0 * E0 = E0 * y ^ u 0 := ((commute_x_eSum _ _).pow_left _).eq
    have hz1 : z ^ u 0 * E1 = E1 * z ^ u 0 := ((commute_x_eSum _ _).pow_left _).eq
    have hA := fun T : Rp => (Algebra.commutes c T)
    have e1 : algebraMap k Rp c * (y ^ u 0 * w) * E0 * uL p * E1 =
        algebraMap k Rp c * (E0 * (y ^ u 0 * uL p) * E1 * w) := by
      simp only [mul_assoc]
      rw [← mul_assoc w E0, hw0, mul_assoc E0 w, ← mul_assoc w (uL p), hwL, mul_assoc (uL p) w,
        hw1, ← mul_assoc (y ^ u 0) E0, hy0]
      simp only [mul_assoc]
    have l : uL p * (algebraMap k Rp c * (z ^ u 0 * w) * E1) =
        algebraMap k Rp c * (uL p * (z ^ u 0 * (w * E1))) := by
      rw [← mul_assoc, ← mul_assoc, ← hA (uL p)]
      simp only [mul_assoc]
    have r : algebraMap k Rp c * (E0 * (uL p * z ^ u 0) * E1 * w) =
        algebraMap k Rp c * (uL p * (z ^ u 0 * (w * E1))) := by
      congr 1
      simp only [← mul_assoc]
      rw [← hLE]
      simp only [mul_assoc]
      rw [← mul_assoc E1 (z ^ u 0), ← hz1, mul_assoc (z ^ u 0) E1, ← mul_assoc E1 E1, hE1, hw1]
    have e2 : uL p * (algebraMap k Rp c * (z ^ u 0 * w) * E1) =
        algebraMap k Rp c * (E0 * (uL p * z ^ u 0) * E1 * w) := by rw [l, r]
    rw [e1, e2, ← mul_sub, ← Algebra.smul_def,
      show E0 * (y ^ u 0 * uL p) * E1 * w - E0 * (uL p * z ^ u 0) * E1 * w =
        E0 * (y ^ u 0 * uL p - uL p * z ^ u 0) * E1 * w by noncomm_ring]
    exact Submodule.smul_mem _ c (exitSpan_mul_right s _
      (passing_x_pow_mem (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) s hq1 (u 0)) w)
  | add P P' hP hP' =>
    rw [ncEval_add, ncEval_add, add_mul, add_mul, add_mul, add_mul, mul_add,
      show ∀ a b c d : Rp, a + b - (c + d) = (a - c) + (b - d) from fun _ _ _ _ => by abel]
    exact add_mem hP hP'

end Passing

section Model

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Eat" s:max n:max hn:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s n hn)
local notation "E" s:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s (midPos j s) (midPos_le j s))
local notation "bot" => botMap k Q Λ Λc j hj ν ν₀
local notation "σ" => midStendhal j hj Q Λ Λc ν ν₀
local notation "μ" => midMapKLR j hj Q Λ Λc ν ν₀

variable {L : Type*} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}

variable (j hj Q Λ Λc ν ν₀ L) in
/-- **Two diagrams of `λ⁺` act alike on the elements `e Z ⊗ v`** of the model. -/
def MidTmulRel (Y Y' : Rp) : Prop :=
  ∀ (Z : Tp) (v : L),
    (Ind.tmul (midGen j hj Q Λ Λc ν ν₀ (bot Y * σ 1 * Z)) v : MidModel j hj Q Λ Λc ν ν₀ L) =
      Ind.tmul (midGen j hj Q Λ Λc ν ν₀ (bot Y' * σ 1 * Z)) v

theorem MidTmulRel.refl (Y : Rp) : MidTmulRel j hj Q Λ Λc ν ν₀ L Y Y := fun _ _ => rfl

theorem MidTmulRel.of_eq {Y Y' : Rp} (h : Y = Y') : MidTmulRel j hj Q Λ Λc ν ν₀ L Y Y' := by
  subst h; exact MidTmulRel.refl _

theorem MidTmulRel.symm {Y Y' : Rp} (h : MidTmulRel j hj Q Λ Λc ν ν₀ L Y Y') :
    MidTmulRel j hj Q Λ Λc ν ν₀ L Y' Y := fun Z v => (h Z v).symm

theorem MidTmulRel.trans {Y Y' Y'' : Rp} (h : MidTmulRel j hj Q Λ Λc ν ν₀ L Y Y')
    (h' : MidTmulRel j hj Q Λ Λc ν ν₀ L Y' Y'') : MidTmulRel j hj Q Λ Λc ν ν₀ L Y Y'' :=
  fun Z v => (h Z v).trans (h' Z v)

theorem tmul_midGen_add (A B : Tp) (v : L) :
    (Ind.tmul (midGen j hj Q Λ Λc ν ν₀ (A + B)) v : MidModel j hj Q Λ Λc ν ν₀ L) =
      Ind.tmul (midGen j hj Q Λ Λc ν ν₀ A) v + Ind.tmul (midGen j hj Q Λ Λc ν ν₀ B) v := by
  rw [← Ind.add_tmul]
  congr 1
  apply Subtype.ext
  change op (σ 1 * (A + B)) = op (σ 1 * A) + op (σ 1 * B)
  rw [mul_add, op_add]

theorem MidTmulRel.add {Y₁ Y₂ Y₁' Y₂' : Rp} (h₁ : MidTmulRel j hj Q Λ Λc ν ν₀ L Y₁ Y₁')
    (h₂ : MidTmulRel j hj Q Λ Λc ν ν₀ L Y₂ Y₂') :
    MidTmulRel j hj Q Λ Λc ν ν₀ L (Y₁ + Y₂) (Y₁' + Y₂') := fun Z v => by
  rw [map_add, add_mul, add_mul, tmul_midGen_add, h₁, h₂, map_add, add_mul, add_mul,
    tmul_midGen_add]

theorem MidTmulRel.smul (c : k) {Y Y' : Rp} (h : MidTmulRel j hj Q Λ Λc ν ν₀ L Y Y') :
    MidTmulRel j hj Q Λ Λc ν ν₀ L (c • Y) (c • Y') := fun Z v => by
  rw [map_smul, smul_mul_assoc, smul_mul_assoc, tmul_midGen_smul, h, map_smul, smul_mul_assoc,
    smul_mul_assoc, tmul_midGen_smul]

theorem MidTmulRel.sub {Y₁ Y₂ Y₁' Y₂' : Rp} (h₁ : MidTmulRel j hj Q Λ Λc ν ν₀ L Y₁ Y₁')
    (h₂ : MidTmulRel j hj Q Λ Λc ν ν₀ L Y₂ Y₂') :
    MidTmulRel j hj Q Λ Λc ν ν₀ L (Y₁ - Y₂) (Y₁' - Y₂') := by
  have h := h₁.add (h₂.smul (-1))
  simpa only [neg_one_smul, ← sub_eq_add_neg] using h

include hL in
/-- A diagram in which a strand leaves the window at the top acts by `0`. -/
theorem tmul_midGen_eq_zero_of_mem {y : Rp} (hy : y ∈ midExit j hj Q Λ Λc ν ν₀) (Z : Tp)
    (v : L) :
    (Ind.tmul (midGen j hj Q Λ Λc ν ν₀ (bot y * σ 1 * Z)) v : MidModel j hj Q Λ Λc ν ν₀ L) =
      0 := by
  have hn := mul_mem_nullIdeal (op Z) (midElt_mem_nullIdeal L hL hy)
  have he : midGen j hj Q Λ Λc ν ν₀ (bot y * σ 1 * Z) =
      ⟨op Z * midElt j hj Q Λ Λc ν ν₀ y, mem_lIdeal_of_mem_nullIdeal hn⟩ := by
    apply Subtype.ext
    change op (σ 1 * (bot y * σ 1 * Z)) = op Z * op (σ 1 * bot y * σ 1)
    rw [← op_mul]
    simp only [mul_assoc]
  rw [he]
  exact tmul_eq_zero_of_mem_nullIdeal hn v

include hL in
/-- **Diagrams that differ by exits at the top act alike.** -/
theorem MidTmulRel.of_sub_mem {Y Y' : Rp} (h : Y - Y' ∈ midExit j hj Q Λ Λc ν ν₀) :
    MidTmulRel j hj Q Λ Λc ν ν₀ L Y Y' := fun Z v => by
  have he : bot Y * σ 1 * Z = bot Y' * σ 1 * Z + bot (Y - Y') * σ 1 * Z := by
    rw [map_sub, sub_mul, sub_mul]; abel
  rw [he, tmul_midGen_add, tmul_midGen_eq_zero_of_mem (hL := hL) h, add_zero]

theorem MidTmulRel.midRel {Y Y' : Rp} (h : MidTmulRel j hj Q Λ Λc ν ν₀ L Y Y') :
    MidRel j hj Q Λ Λc ν ν₀ L hL Y Y' :=
  MidRel.of_tmul h

/-- A diagram ending in a window idempotent is unchanged by the idempotent at the maximum. -/
theorem bot_mul_midStendhal_one {s : Seq (stendhalWeight ℓ ν)} {Y : Rp} (h : Y * E s = Y) :
    bot Y * σ 1 = bot Y := by
  rw [← h, map_mul, mul_assoc, midStendhal_one_eq_bot, ← map_mul, eSum_mul_midMapKLR,
    botMap_insertMap_redOrderedKLR]

/-- **The loop on the left of the maximum, at the top of a diagram.** -/
theorem MidTmulRel.leftLoop_top (hPL : PullOffLeft k Q Λc ν₀ L) {i : I}
    (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n + 1 ≤ m) (hc : n + 1 = midPos j s)
    (hs : s.lbl ⟨n, by omega⟩ = .inl i) (X : Rp) :
    MidTmulRel j hj Q Λ Λc ν ν₀ L
      (Eat s (n + 1) hn * (underRight N n * underLeft N n) * Eat s (n + 1) hn * X)
      (cupScalar Q ν₀ i • (Eat s (n + 1) hn * X)) := fun Z v => by
  rw [map_mul, mul_assoc, mul_assoc, tmul_midGen_mul,
    leftLoop_midModel Q Λ Λc L hPL i s hn hc hs, ← tmul_midGen_mul, tmul_op_algebraMap,
    map_smul, smul_mul_assoc, smul_mul_assoc, tmul_midGen_smul]
  simp only [map_mul, mul_assoc]

/-- **The loop on the right of the maximum, at the top of a diagram.** -/
theorem MidTmulRel.rightLoop_top (hP : PullOff k Q Λc ν₀ L) {i : I}
    (s : Seq (stendhalWeight ℓ ν)) {c : ℕ} (hcm : midPos j s = c) (hc1 : c + 1 < m)
    (hs : s.lbl ⟨c + 1, hc1⟩ = .inl i) (X : Rp) :
    MidTmulRel j hj Q Λ Λc ν ν₀ L
      (KLRAlgebra.ψ (c + N) * (underLeft N c * underRight N c) *
        Eat (sadj m c • s) c (by omega) * X)
      (cupScalar Q ν₀ i • (KLRAlgebra.ψ (c + N) * Eat (sadj m c • s) c (by omega) * X)) := by
  subst hcm
  intro Z v
  rw [map_mul, mul_assoc, mul_assoc, tmul_midGen_mul,
    rightLoop_midModel Q Λ Λc L hP i s hc1 hs, ← tmul_midGen_mul, tmul_op_algebraMap,
    map_smul, smul_mul_assoc, smul_mul_assoc, tmul_midGen_smul]
  simp only [map_mul, mul_assoc]

include hL in
/-- **The loop on the left of the maximum, at the bottom of a sliding diagram.** -/
theorem MidTmulRel.leftLoop_bottom (hPL : PullOffLeft k Q Λc ν₀ L) {i : I}
    (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n + 1 ≤ m) (hc : n + 1 = midPos j s)
    (hs : s.lbl ⟨n, by omega⟩ = .inl i) {W : Rp} (hW : MidSlides j hj Q Λ Λc ν ν₀ W)
    (hWE : W * Eat s (n + 1) hn = W) :
    MidTmulRel j hj Q Λ Λc ν ν₀ L
      (W * (Eat s (n + 1) hn * (underRight N n * underLeft N n) * Eat s (n + 1) hn))
      (cupScalar Q ν₀ i • W) := fun Z v => by
  have hE : (E s : Rp) = Eat s (n + 1) hn :=
    congrArg _ (insertSet_congr' s (midPos_le j s) hn hc.symm)
  have hσ : bot W * σ 1 = bot W := bot_mul_midStendhal_one (s := s) (by rw [hE]; exact hWE)
  have e : bot (W * (Eat s (n + 1) hn * (underRight N n * underLeft N n) * Eat s (n + 1) hn)) *
      σ 1 * Z = bot W * σ 1 * (bot (Eat s (n + 1) hn * (underRight N n * underLeft N n) *
        Eat s (n + 1) hn) * (σ 1 * Z)) := by
    rw [map_mul, hσ]
    simp only [mul_assoc]
  rw [e, ← midEnd_tmul (hL := hL) hW, tmul_midGen_mul, leftLoop_midModel Q Λ Λc L hPL i s hn hc hs,
    ← tmul_midGen_mul, midEnd_tmul (hL := hL) hW, tmul_op_algebraMap, map_smul, smul_mul_assoc,
    smul_mul_assoc, tmul_midGen_smul]
  congr 2
  simp only [← mul_assoc]
  rw [hσ, ← map_mul, hWE, hσ]

end Model

section Mid

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Eat" s:max n:max hn:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s n hn)
local notation "E" s:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s (midPos j s) (midPos_le j s))
local notation "C" => midCross j hj Q Λ Λc ν ν₀
local notation "D" => midDot j hj Q Λ Λc ν ν₀
local notation "uR" => underRight (k := k) (Q := stendhalQ Q (plusLabels Λ Λc j hj))
  (ν := stendhalWeight (ℓ + 2) (ν + ν₀)) N
local notation "uL" => underLeft (k := k) (Q := stendhalQ Q (plusLabels Λ Λc j hj))
  (ν := stendhalWeight (ℓ + 2) (ν + ν₀)) N
local notation "ψ'" a:max => (KLRAlgebra.ψ a : Rp)

variable {L : Type*} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}

include hL in
/-- **The braid relation with `λ_{j+1}` at `p + 1`** on the elements `e Z ⊗ v` of the model.
The strand at `p` is pulled under the maximum and back at the bottom of the right-hand side
(the loop of (max1) on its left), the crossing slides through the passage of the two black
strands, and the loop on the right of the maximum is removed at the top. What remains differs
from the left-hand side by the braid relation of `λ⁺` on the strands `p, p + 1, p + 2` of the
loading with the window at `p`; its correction term has its dots on the passing strand slid
down, and the loop on the left of the maximum at the top removes the scalars. -/
theorem midTmulRel_braid_of_mid (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))
    (hP : PullOff k Q Λc ν₀ L) (hPL : PullOffLeft k Q Λc ν₀ L) (p : ℕ) (h : p + 2 < m)
    (i : Seq (stendhalWeight ℓ ν)) (hc : p + 1 = midPos j i) :
    MidTmulRel j hj Q Λ Λc ν ν₀ L
      ((C p * C (p + 1) * C p - C (p + 1) * C p * C (p + 1)) * E i)
      (if i.lbl ⟨p, by omega⟩ = i.lbl ⟨p + 2, h⟩ ∧ i.lbl ⟨p, by omega⟩ ≠ i.lbl ⟨p + 1, by omega⟩
      then ncEval ![D ⟨p, by omega⟩, D ⟨p + 1, by omega⟩, D ⟨p + 2, h⟩]
          (qbar (stendhalQ Q Λ (i.lbl ⟨p, by omega⟩) (i.lbl ⟨p + 1, by omega⟩))) * E i
      else 0) := by
  have hM := card_plus_braid (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
  have hq : p + 1 ≤ m := by omega
  set s1 := sadj m p • i
  set s2 := sadj m (p + 1) • s1
  set r1 := sadj m (p + 1) • i
  set r2 := sadj m p • r1
  have e1 : midPos j s1 = p := midPos_sadj_left j i (by omega) hc
  have e2 : midPos j s2 = p := (midPos_sadj_of_far j s1 h (by omega)).trans e1
  have f1 : midPos j r1 = p + 1 + 1 := midPos_sadj_right j i h hc
  have f2 : midPos j r2 = p + 1 + 1 :=
    (midPos_sadj_of_far j r1 (by omega) (by omega)).trans f1
  rw [sub_mul, midCross_triple_mul_eSum, midCross_triple_mul_eSum]
  have lb2 : s2.lbl ⟨p + 1, by omega⟩ = i.lbl ⟨p + 2, h⟩ := by
    rw [lbl_sadj_self s1 h]
    exact lbl_sadj_other i (q := p) (a := p + 2) (by omega) h (by omega) (by omega)
  have la2 : r2.lbl ⟨p + 1, by omega⟩ = i.lbl ⟨p, by omega⟩ := by
    rw [lbl_sadj_succ r1 (q := p) (by omega)]
    exact lbl_sadj_other i (q := p + 1) (a := p) h (by omega) (by omega) (by omega)
  have hsplit : ∀ z : I ⊕ Fin ℓ, (∃ a, z = .inl a) ∨ ∃ r, z = .inr r := fun z => by
    cases z <;> simp
  obtain ⟨α, ha⟩ | ⟨ra, ha⟩ := hsplit (i.lbl ⟨p, by omega⟩)
  swap
  · rw [midCrossAt_braid_left_red i (p := p) (by omega) hc ha, mul_zero,
      midCrossAt_braid_left_red r2 (p := p + 1) h f2.symm (la2.trans ha), zero_mul, zero_mul,
      sub_zero, ite_eq_right_iff.2 fun hcd => by
        have h' := congrArg Fin.val (lbl_eq_inr_unique (hcd.1.symm.trans ha) ha)
        simp at h']
    exact MidTmulRel.refl _
  obtain ⟨β, hb⟩ | ⟨rb, hb⟩ := hsplit (i.lbl ⟨p + 2, h⟩)
  swap
  · rw [midCrossAt_braid_right_red s2 (p := p) (by omega) e2.symm (lb2.trans hb), zero_mul,
      zero_mul, midCrossAt_braid_right_red i (p := p + 1) h hc hb, mul_zero, sub_zero,
      ite_eq_right_iff.2 fun hcd => absurd (hcd.1.trans hb) (by rw [ha]; simp)]
    exact MidTmulRel.refl _
  obtain ⟨κα, hκα⟩ : ∃ c : k, c = Ring.inverse (cupScalar Q ν₀ α) := ⟨_, rfl⟩
  obtain ⟨κβ, hκβ⟩ : ∃ c : k, c = Ring.inverse (cupScalar Q ν₀ β) := ⟨_, rfl⟩
  have hcα : κα * cupScalar Q ν₀ α = 1 := by rw [hκα]; exact Ring.inverse_mul_cancel _ (hκ α)
  have hL3 := midCrossAt_triple_of_body i p (p + 1) (ψ' (p + N) * uL p : Rp)
    (ψ' (p + 1 + N)) (κβ • (uR p * ψ' (p + N)))
    (midCrossAt_braid_left_black i (p := p) (by omega) hc ha)
    (midCrossAt_braid_far_eq s1 (p + 1) (p + 1 + N) h (by rw [e1]; omega)
      (by rw [e1]; unfold crossPos; split_ifs <;> omega))
    (by rw [midCrossAt_braid_right_black s2 (p := p) (by omega) e2.symm (lb2.trans hb), ← hκβ,
      smul_mul_assoc])
  have hR3 := midCrossAt_triple_of_body i (p + 1) p
    (κβ • (uR (p + 1) * ψ' (p + 1 + N)) : Rp) (ψ' p) (ψ' (p + 1 + N) * uL (p + 1))
    (by rw [midCrossAt_braid_right_black i (p := p + 1) h hc hb, ← hκβ, smul_mul_assoc])
    (midCrossAt_braid_far_eq r1 p p (by omega) (by rw [f1]; omega)
      (by rw [f1]; unfold crossPos; split_ifs <;> omega))
    (midCrossAt_braid_left_black r2 (p := p + 1) h f2.symm (la2.trans ha))
  -- idempotents and passages
  have hE : (E i : Rp) = Eat i (p + 1) hq :=
    congrArg _ (insertSet_congr' i (midPos_le j i) hq hc.symm)
  have hLE : uL p * Eat i (p + 1) hq = Eat i p (by omega) * uL p := underLeft_mul_eSum i hq
  have hRE : uR p * Eat i p (by omega) = Eat i (p + 1) hq * uR p :=
    underRight_mul_eSum Q Λ Λc i hq
  have hE1 : Eat i (p + 1) hq * Eat i (p + 1) hq = Eat i (p + 1) hq := (KLRAlgebra.eSum_idem _).eq
  have hE0 : Eat i p (by omega) * Eat i p (by omega) = Eat i p (by omega) :=
    (KLRAlgebra.eSum_idem _).eq
  have key : uR p * uL p * Eat i (p + 1) hq = Eat i (p + 1) hq * (uR p * uL p) := by
    rw [mul_assoc, hLE, ← mul_assoc, hRE, mul_assoc]
  have hloop : Eat i (p + 1) hq * (uR p * uL p) * Eat i (p + 1) hq =
      uR p * uL p * Eat i (p + 1) hq := by
    rw [mul_assoc, key, ← mul_assoc, hE1]
  have key2 : Eat i (p + 1) hq * (uR p * (uL p * Eat i (p + 1) hq)) =
      uR p * (uL p * Eat i (p + 1) hq) := by
    rw [← mul_assoc (uR p), key, ← mul_assoc, hE1]
  have hcommR := (commute_ψ_uR (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj)
    (ν₀ := ν₀) (ν := ν) (k := k) (a := p + 1 + N) (q := p) (by omega)).eq
  have hP0 : passU Q Λ Λc j hj ν ν₀ p 2 = uR (p + 1) * uR p := by
    rw [passU_succ, passU_succ, passU_zero, mul_one]; rfl
  have hPE : ∀ t : Seq (stendhalWeight ℓ ν), uR (p + 1) * uR p * Eat t p (by omega) =
      Eat t (p + 1 + 1) (by omega) * (uR (p + 1) * uR p) := fun t => by
    rw [mul_assoc, underRight_mul_eSum Q Λ Λc t hq, ← mul_assoc,
      underRight_mul_eSum Q Λ Λc t (q := p + 1) (by omega), mul_assoc]
  have hψ''E : ψ' (p + 1 + N) * Eat i p (by omega) = Eat r1 p (by omega) * ψ' (p + 1 + N) := by
    have := ψ_crossPos_mul_eSum (j := j) (hj := hj) (Q := Q) (Λ := Λ) (Λc := Λc) (ν₀ := ν₀) i
      (n := p) (by omega) (p := p + 1) (Or.inr (by omega))
    rwa [show crossPos p N (p + 1) = p + 1 + N by unfold crossPos; split_ifs <;> omega] at this
  have hψpE : ψ' p * Eat r1 (p + 1 + 1) (by omega) = Eat r2 (p + 1 + 1) (by omega) * ψ' p := by
    have := ψ_crossPos_mul_eSum (j := j) (hj := hj) (Q := Q) (Λ := Λ) (Λc := Λc) (ν₀ := ν₀) r1
      (n := p + 1 + 1) (by omega) (p := p) (Or.inl (by omega))
    rwa [show crossPos (p + 1 + 1) N p = p by unfold crossPos; split_ifs <;> omega] at this
  have hψNE : ψ' (p + N) * Eat r1 p (by omega) = Eat r2 p (by omega) * ψ' (p + N) := by
    have := ψ_crossPos_mul_eSum (j := j) (hj := hj) (Q := Q) (Λ := Λ) (Λc := Λc) (ν₀ := ν₀) r1
      (n := p) (by omega) (p := p) (Or.inr le_rfl)
    rwa [crossPos_self] at this
  obtain ⟨X, hXd⟩ : ∃ X : Rp, X = ψ' (p + 1 + N) * (uL p * Eat i (p + 1) hq) := ⟨_, rfl⟩
  have hXr : X = Eat r1 p (by omega) * (ψ' (p + 1 + N) * uL p) := by
    rw [hXd, hLE, ← mul_assoc, hψ''E, mul_assoc]
  -- the right-hand side, with the loop at the bottom
  have hRsl : MidSlides j hj Q Λ Λc ν ν₀
      (midCrossAt j hj Q Λ Λc ν ν₀ r2 (p + 1) * midCrossAt j hj Q Λ Λc ν ν₀ r1 p *
        midCrossAt j hj Q Λ Λc ν ν₀ i (p + 1)) :=
    ((midSlides_midCrossAt _ _).mul (midSlides_midCrossAt _ _)).mul (midSlides_midCrossAt _ _)
  have hRtE : midCrossAt j hj Q Λ Λc ν ν₀ r2 (p + 1) * midCrossAt j hj Q Λ Λc ν ν₀ r1 p *
      midCrossAt j hj Q Λ Λc ν ν₀ i (p + 1) * Eat i (p + 1) hq =
      midCrossAt j hj Q Λ Λc ν ν₀ r2 (p + 1) * midCrossAt j hj Q Λ Λc ν ν₀ r1 p *
        midCrossAt j hj Q Λ Λc ν ν₀ i (p + 1) := by
    rw [hR3, hE, mul_assoc _ (Eat i (p + 1) hq), hE1]
  have tA := MidTmulRel.leftLoop_bottom (hL := hL) hPL i hq hc ha hRsl hRtE
  have tA' := (tA.smul κα).symm
  rw [smul_smul, hcα, one_smul] at tA'
  have eB : midCrossAt j hj Q Λ Λc ν ν₀ r2 (p + 1) * midCrossAt j hj Q Λ Λc ν ν₀ r1 p *
      midCrossAt j hj Q Λ Λc ν ν₀ i (p + 1) *
        (Eat i (p + 1) hq * (uR p * uL p) * Eat i (p + 1) hq) =
      κβ • (ψ' (p + 1 + N) * (uL (p + 1) * (ψ' p * (uR (p + 1) * uR p * X)))) := by
    rw [hR3, hloop, hE, hXd]
    simp only [smul_mul_assoc, mul_smul_comm, mul_assoc]
    rw [key2, ← mul_assoc (ψ' (p + 1 + N)) (uR p), hcommR, mul_assoc]
  -- the crossing slides through the passage
  have hEq1 : ψ' p * (uR (p + 1) * uR p * X) = Eat r2 (p + 1 + 1) (by omega) *
      (ψ' p * (uR (p + 1) * uR p)) * (ψ' (p + 1 + N) * uL p) := by
    rw [hXr, ← mul_assoc (uR (p + 1) * uR p), hPE, ← mul_assoc (ψ' p), ← mul_assoc (ψ' p), hψpE]
    simp only [mul_assoc]
  have hEq2 : uR (p + 1) * uR p * (ψ' (p + N) * X) = Eat r2 (p + 1 + 1) (by omega) *
      (uR (p + 1) * uR p * ψ' (p + N)) * (ψ' (p + 1 + N) * uL p) := by
    rw [hXr, ← mul_assoc (ψ' (p + N)), hψNE, mul_assoc (Eat r2 p (by omega)),
      ← mul_assoc (uR (p + 1) * uR p), hPE]
    simp only [mul_assoc]
  have hD : Eat r2 (p + 1 + 1) (by omega) * (ψ' p * (uR (p + 1) * uR p) -
      uR (p + 1) * uR p * ψ' (p + N)) ∈ exitSpan Q Λ Λc j hj r2 (p + 1 + 1) (by omega) := by
    have := slides_passing_ψ (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) r2
      (q := p) (by omega)
    rw [hP0] at this
    exact this
  have eT : midPos j (sadj m (p + 1) • r2) = p + 1 := midPos_sadj_left j r2 h f2.symm
  have hmem : κβ • (ψ' (p + 1 + N) * (uL (p + 1) * (ψ' p * (uR (p + 1) * uR p * X)))) -
      κβ • (ψ' (p + 1 + N) * (uL (p + 1) * (uR (p + 1) * uR p * (ψ' (p + N) * X)))) ∈
        midExit j hj Q Λ Λc ν ν₀ := by
    rw [← smul_sub, ← mul_sub, ← mul_sub, hEq1, hEq2, ← sub_mul, ← mul_sub]
    refine Submodule.smul_mem _ _ (mem_midExit (sadj m (p + 1) • r2) ?_)
    rw [exitSpan_congr' _ (midPos_le j _) (by omega) eT]
    have h1 := exitSpan_mul_right r2 _ hD (ψ' (p + 1 + N) * uL p)
    have h2 := underLeft_mul_mem (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) r2
      (q := p + 1) (by omega) h1
    have h3 := ψ_crossPos_mul_mem_exitSpan r2 (n := p + 1) (by omega) (p := p + 1)
      (Or.inr le_rfl) h2
    rw [crossPos_self] at h3
    exact h3
  -- the loop on the right of the maximum at the top
  have hY : uR p * (ψ' (p + N) * X) =
      Eat r2 (p + 1) hq * (uR p * (ψ' (p + N) * (ψ' (p + 1 + N) * uL p))) := by
    rw [hXr, ← mul_assoc (ψ' (p + N)), hψNE, mul_assoc, ← mul_assoc (uR p),
      underRight_mul_eSum Q Λ Λc r2 hq, mul_assoc]
  have hY' : Eat r2 (p + 1) hq * (uR p * (ψ' (p + N) * X)) = uR p * (ψ' (p + N) * X) := by
    rw [hY, ← mul_assoc, (KLRAlgebra.eSum_idem _).eq]
  have tD := MidTmulRel.rightLoop_top (j := j) (hj := hj) (L := L) hP (sadj m (p + 1) • r2)
    eT h ((lbl_sadj_succ r2 (q := p + 1) h).trans (la2.trans ha)) (uR p * (ψ' (p + N) * X))
  rw [smul_smul, KLRAlgebra.sadj_mul_self, one_smul] at tD
  have eD1 : ψ' (p + 1 + N) * (uL (p + 1) * (uR (p + 1) * uR p * (ψ' (p + N) * X))) =
      ψ' (p + 1 + N) * (uL (p + 1) * uR (p + 1)) * Eat r2 (p + 1) hq *
        (uR p * (ψ' (p + N) * X)) := by
    rw [mul_assoc (ψ' (p + 1 + N) * (uL (p + 1) * uR (p + 1))), hY']
    simp only [mul_assoc]
  have eD2 : ψ' (p + 1 + N) * Eat r2 (p + 1) hq * (uR p * (ψ' (p + N) * X)) =
      uR p * (ψ' (p + N + 1) * (ψ' (p + N) * (ψ' (p + N + 1) *
        (uL p * Eat i (p + 1) hq)))) := by
    rw [mul_assoc, hY', ← mul_assoc (ψ' (p + 1 + N)) (uR p), hcommR, hXd,
      show p + 1 + N = p + N + 1 by omega]
    simp only [mul_assoc]
  obtain ⟨Xf, hXf⟩ : ∃ Xf : Rp, Xf = κβ • (uR p * (ψ' (p + N + 1) * (ψ' (p + N) *
      (ψ' (p + N + 1) * (uL p * Eat i (p + 1) hq))))) := ⟨_, rfl⟩
  have tRHS : MidTmulRel j hj Q Λ Λc ν ν₀ L
      (midCrossAt j hj Q Λ Λc ν ν₀ r2 (p + 1) * midCrossAt j hj Q Λ Λc ν ν₀ r1 p *
        midCrossAt j hj Q Λ Λc ν ν₀ i (p + 1)) Xf := by
    refine tA'.trans ?_
    rw [eB, smul_smul]
    refine (MidTmulRel.of_sub_mem (hL := hL) (Y' := (κα * κβ) • (ψ' (p + 1 + N) *
      (uL (p + 1) * (uR (p + 1) * uR p * (ψ' (p + N) * X))))) (by
        have := Submodule.smul_mem _ κα hmem
        rwa [smul_sub, smul_smul, smul_smul] at this)).trans ?_
    have tD' : MidTmulRel j hj Q Λ Λc ν ν₀ L
        (ψ' (p + 1 + N) * (uL (p + 1) * (uR (p + 1) * uR p * (ψ' (p + N) * X))))
        (cupScalar Q ν₀ α • (uR p * (ψ' (p + N + 1) * (ψ' (p + N) * (ψ' (p + N + 1) *
          (uL p * Eat i (p + 1) hq)))))) := by
      rw [eD1, ← eD2]; exact tD
    refine (tD'.smul (κα * κβ)).trans (MidTmulRel.of_eq ?_)
    rw [smul_smul, hXf, mul_comm κα κβ, mul_assoc, hcα, mul_one]
  -- the left-hand side
  have eLHS : midCrossAt j hj Q Λ Λc ν ν₀ s2 p * midCrossAt j hj Q Λ Λc ν ν₀ s1 (p + 1) *
      midCrossAt j hj Q Λ Λc ν ν₀ i p = κβ • (uR p * (ψ' (p + N) * (ψ' (p + N + 1) *
        (ψ' (p + N) * (uL p * Eat i (p + 1) hq))))) := by
    rw [hL3, hE]
    simp only [smul_mul_assoc, mul_assoc]
    rw [show p + 1 + N = p + N + 1 by omega]
  have hbr := braid_mul_eSum_old (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) i
    (n := p) (by omega) h (Or.inr le_rfl) (a := p + N) (crossPos_self p).symm (by omega)
  have eDiff : κβ • (uR p * (ψ' (p + N) * (ψ' (p + N + 1) * (ψ' (p + N) *
        (uL p * Eat i (p + 1) hq))))) - Xf =
      κβ • (uR p * ((ψ' (p + N) * ψ' (p + N + 1) * ψ' (p + N) -
        ψ' (p + N + 1) * ψ' (p + N) * ψ' (p + N + 1)) * Eat i p (by omega)) * uL p) := by
    rw [hXf, hLE, ← smul_sub]
    congr 1
    noncomm_ring
  rw [hbr] at eDiff
  have hfin : MidTmulRel j hj Q Λ Λc ν ν₀ L (κβ • (uR p * (ψ' (p + N) * (ψ' (p + N + 1) *
      (ψ' (p + N) * (uL p * Eat i (p + 1) hq))))) - Xf)
      (if i.lbl ⟨p, by omega⟩ = i.lbl ⟨p + 2, h⟩ ∧ i.lbl ⟨p, by omega⟩ ≠ i.lbl ⟨p + 1, by omega⟩
      then ncEval ![D ⟨p, by omega⟩, D ⟨p + 1, by omega⟩, D ⟨p + 2, h⟩]
          (qbar (stendhalQ Q Λ (i.lbl ⟨p, by omega⟩) (i.lbl ⟨p + 1, by omega⟩))) * E i
      else 0) := by
    rw [eDiff]
    split_ifs with hcd
    swap
    · rw [mul_zero, zero_mul, smul_zero]; exact MidTmulRel.refl _
    have hαβ : α = β := Sum.inl.inj (ha.symm.trans (hcd.1.trans hb))
    subst hαβ
    set Pq := qbar (stendhalQ Q Λ (i.lbl ⟨p, by omega⟩) (i.lbl ⟨p + 1, by omega⟩))
    set y' : Fin 3 → Rp := ![KLRAlgebra.x ⟨p, lt_M_of_succ_le hq⟩,
      KLRAlgebra.x ⟨p + N + 1, by omega⟩, KLRAlgebra.x ⟨p + N + 2, by omega⟩]
    have hG := passing_ncEval_mem (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀)
      i h Pq
    have hcom : Commute (ncEval y' Pq) (Eat i (p + 1) hq) :=
      commute_ncEval _ (fun a => by fin_cases a <;> exact commute_x_eSum _ _) Pq
    have hdiff : κβ • (uR p * (ncEval ![KLRAlgebra.x ⟨p + N, by omega⟩,
          KLRAlgebra.x ⟨p + N + 1, by omega⟩, KLRAlgebra.x ⟨p + N + 2, by omega⟩] Pq *
          Eat i p (by omega)) * uL p) -
        κβ • (uR p * (uL p * (ncEval y' Pq * Eat i (p + 1) hq))) =
        κβ • (uR p * (ncEval ![KLRAlgebra.x ⟨p + N, by omega⟩,
          KLRAlgebra.x ⟨p + N + 1, by omega⟩, KLRAlgebra.x ⟨p + N + 2, by omega⟩] Pq *
          Eat i p (by omega) * uL p * Eat i (p + 1) hq -
          uL p * (ncEval y' Pq * Eat i (p + 1) hq))) := by
      rw [← smul_sub]
      congr 1
      rw [mul_sub]
      congr 1
      simp only [mul_assoc]
      rw [hLE, ← mul_assoc (Eat i p (by omega)), hE0]
    have t1 := MidTmulRel.of_sub_mem (hL := hL) (L := L) (by
        rw [hdiff]
        refine Submodule.smul_mem _ _ (mem_midExit i ?_)
        rw [exitSpan_congr' i (midPos_le j i) hq hc.symm]
        exact underRight_mul_mem Q Λ Λc i hq hG)
    have hEX : Eat i (p + 1) hq * (ncEval y' Pq * Eat i (p + 1) hq) =
        ncEval y' Pq * Eat i (p + 1) hq := by
      rw [← mul_assoc, ← hcom.eq, mul_assoc, hE1]
    have eH : uR p * (uL p * (ncEval y' Pq * Eat i (p + 1) hq)) =
        Eat i (p + 1) hq * (uR p * uL p) * Eat i (p + 1) hq *
          (ncEval y' Pq * Eat i (p + 1) hq) := by
      rw [hloop, mul_assoc (uR p * uL p), hEX, mul_assoc]
    have tH := MidTmulRel.leftLoop_top (j := j) (hj := hj) (L := L) hPL i hq hc ha
      (ncEval y' Pq * Eat i (p + 1) hq)
    rw [hEX, ← eH] at tH
    have hscal : κβ * cupScalar Q ν₀ α = 1 := by rw [hκβ]; exact Ring.inverse_mul_cancel _ (hκ α)
    refine t1.trans ((tH.smul κβ).trans (MidTmulRel.of_eq ?_))
    rw [smul_smul, hscal, one_smul, ncEval_midDot_three_mul_eSum, hE]
    have d0 : dotPos (j := j) (hj := hj) (ν₀ := ν₀)
        ⟨midPos j i, Nat.lt_succ_of_le (midPos_le j i)⟩ ⟨p, by omega⟩ = ⟨p, lt_M_of_succ_le hq⟩ :=
      Fin.ext (by rw [dotPos_val_crossPos, ← hc]; dsimp only; unfold crossPos; split_ifs <;> omega)
    have d1 : dotPos (j := j) (hj := hj) (ν₀ := ν₀)
        ⟨midPos j i, Nat.lt_succ_of_le (midPos_le j i)⟩ ⟨p + 1, by omega⟩ =
          ⟨p + N + 1, by omega⟩ :=
      Fin.ext (by rw [dotPos_val_crossPos, ← hc]; dsimp only; unfold crossPos; split_ifs <;> omega)
    have d2 : dotPos (j := j) (hj := hj) (ν₀ := ν₀)
        ⟨midPos j i, Nat.lt_succ_of_le (midPos_le j i)⟩ ⟨p + 2, h⟩ = ⟨p + N + 2, by omega⟩ :=
      Fin.ext (by rw [dotPos_val_crossPos, ← hc]; dsimp only; unfold crossPos; split_ifs <;> omega)
    rw [d0, d1, d2]
  have hsum := hfin.add ((MidTmulRel.refl Xf).sub tRHS)
  rw [sub_add_sub_cancel, sub_self, add_zero, ← eLHS] at hsum
  exact hsum

include hL in
/-- **The braid relation on the model of a cap after `λ_j`** (Webster, arXiv:1309.3796v3, proof
of Lemma 7.17): on the loading `i` of `λ`, the braid relation of the crossings `ψ_p`, `ψ_{p+1}`
of `T̃^λ` holds on the model with the correction term of `T̃^λ`. -/
theorem midRel_braid (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i)) (hP : PullOff k Q Λc ν₀ L)
    (hPL : PullOffLeft k Q Λc ν₀ L) (p : ℕ) (h : p + 2 < m) (i : Seq (stendhalWeight ℓ ν)) :
    MidRel j hj Q Λ Λc ν ν₀ L hL ((C p * C (p + 1) * C p - C (p + 1) * C p * C (p + 1)) * E i)
      (if i.lbl ⟨p, by omega⟩ = i.lbl ⟨p + 2, h⟩ ∧ i.lbl ⟨p, by omega⟩ ≠ i.lbl ⟨p + 1, by omega⟩
      then ncEval ![D ⟨p, by omega⟩, D ⟨p + 1, by omega⟩, D ⟨p + 2, h⟩]
          (qbar (stendhalQ Q Λ (i.lbl ⟨p, by omega⟩) (i.lbl ⟨p + 1, by omega⟩))) * E i
      else 0) := by
  by_cases hf : p + 2 < midPos j i ∨ midPos j i + 1 ≤ p
  · exact midRel_braid_of_far p h i hf
  rcases (by omega : midPos j i = p ∨ midPos j i = p + 1 ∨ midPos j i = p + 2) with hc | hc | hc
  · rw [ite_eq_right_iff.2 fun hcd =>
      absurd hcd.1.symm (lbl_ne_of_midPos j i (by omega) h hc.symm (by omega))]
    exact MidRel.of_sub_mem (by rw [sub_zero]; exact braid_mem_midExit_of_right p h i hc.symm)
  · exact (midTmulRel_braid_of_mid (hL := hL) hκ hP hPL p h i hc.symm).midRel
  · rw [ite_eq_right_iff.2 fun hcd =>
      absurd hcd.1 (lbl_ne_of_midPos j i h (by omega) hc.symm (by omega))]
    exact MidRel.of_sub_mem (by rw [sub_zero]; exact braid_mem_midExit_of_left p h i hc.symm)

end Mid

end Categorification.Stendhal.CupCap
