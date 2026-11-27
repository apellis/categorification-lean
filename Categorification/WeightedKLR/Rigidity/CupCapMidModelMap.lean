/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapMidModelMapLoop
import Categorification.WeightedKLR.Rigidity.CupCapMidModule
import Categorification.WeightedKLR.Rigidity.CupCapMidRightLoop

/-!
# The map from `K̃^{λ⁺}_λ` to the model of a cap after `λ_j`

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.17, for a cap inserted after the red strand
`λ_j` (any `j ≤ ℓ`). Let `c = midPos j s` be the position of the red strand `λ_{j+1}` in the
loading `s` of `λ` (the right end when `j = ℓ`). The cap generator `cap s n v` of `K̃^{λ⁺}_λ` goes
to the element `c(s, n) · e E_{s,c} U E_{s,n} ⊗ v` of the model `L ⊗ e T̃^{λ⁺}`
(`CupCap.MidModel`) when `n ≤ c`, where `U` passes the strands of `s` at `n, …, c - 1` under the
maximum (`CupCap.midCapBot`) and `c(s, n)` is the product of the inverses of the scalars of
(max1) of these strands (`CupCap.midCapScalar`); it goes to `0` when `n > c`, where the red
strands of the cap lie right of `λ_{j+1}`. The model is a bimodule through
`CupCap.midEnvAlg` (`CupCap.MidBimod`).

This file sets up the map on the free bimodule on the cap generators and checks the relations
of Definition 7.15 other than the dots and the crossings: additivity, the top idempotent, the
diagrams at the maximum, (max1) and (max2) (by the left pull-off identity along a passage,
`CupCap.leftLoop_midPass`).

## Main definitions

* `CupCap.midCapScalar`: the normalization `c(s, n)`.
* `CupCap.midCapBot`: the diagram `E_{s,c} U E_{s,n}` below the cap generator.
* `CupCap.midCapImage`: the image of the cap generator.
* `CupCap.MidBimod`: the model with its bimodule structure.
* `CupCap.midPhiFree`: the map from the free bimodule.

## Main results

* `CupCap.midEnd_tmul_midGen`: a sliding diagram acts by multiplication on the left.
* `CupCap.midPhiFree_idem`, `CupCap.midPhiFree_box`, `CupCap.midPhiFree_over`,
  `CupCap.midPhiFree_under`: the corresponding relations hold in the model.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MulOpposite InductionAlong

section Scalars

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {ν : Multiset I}
  (Q : I → I → MvPolynomial (Fin 2) k) (ν₀ : Multiset I)

local notation "m" => Multiset.card (stendhalWeight ℓ ν)

/-- The inverse of the scalar of (max1) of the strand of `s` at `r` (`1` for a red strand). -/
def midFac (s : Seq (stendhalWeight ℓ ν)) (r : ℕ) : k :=
  if h : r < m then Ring.inverse (labelScalar Q ν₀ (s.lbl ⟨r, h⟩)) else 1

/-- **The normalization of the cap generator `cap s n`** in the model of a cap after `λ_j`: the
product of the inverses of the scalars of (max1) of the strands of `s` at `n, …, c - 1`, with
`c = midPos j s`. -/
def midCapScalar (j : ℕ) (Q' : I → I → MvPolynomial (Fin 2) k) (ν₀' : Multiset I)
    (s : Seq (stendhalWeight ℓ ν)) (n : ℕ) : k :=
  ∏ r ∈ Finset.Ico n (midPos j s), midFac Q' ν₀' s r

variable {Q ν₀} {j : ℕ}

theorem midCapScalar_self (s : Seq (stendhalWeight ℓ ν)) :
    midCapScalar j Q ν₀ s (midPos j s) = 1 := by
  simp [midCapScalar]

theorem midCapScalar_eq_mul (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n < midPos j s) :
    midCapScalar j Q ν₀ s n = midFac Q ν₀ s n * midCapScalar j Q ν₀ s (n + 1) :=
  Finset.prod_eq_prod_Ico_succ_bot hn _

theorem midFac_inl (s : Seq (stendhalWeight ℓ ν)) {r : ℕ} (hr : r < m) {i : I}
    (hi : s.lbl ⟨r, hr⟩ = .inl i) : midFac Q ν₀ s r = Ring.inverse (cupScalar Q ν₀ i) := by
  simp [midFac, hr, hi, labelScalar]

theorem midFac_sadj (s : Seq (stendhalWeight ℓ ν)) {p : ℕ} (hp : p + 1 < m) (r : ℕ) :
    midFac Q ν₀ (sadj m p • s) r = midFac Q ν₀ s (Equiv.swap p (p + 1) r) := by
  have hsw : Equiv.swap p (p + 1) r = swapNat p r := by
    rw [Equiv.swap_apply_def]; rfl
  by_cases h : r < m
  · have h' : Equiv.swap p (p + 1) r < m := by
      rw [hsw]; unfold swapNat; split_ifs <;> omega
    simp only [midFac, h, h', ↓reduceDIte]
    rw [lbl_sadj_of_swapNat s hp ⟨r, h⟩ ⟨_, h'⟩ hsw.symm]
  · have h' : ¬ Equiv.swap p (p + 1) r < m := by
      rw [hsw]; unfold swapNat; split_ifs <;> omega
    simp only [midFac, h, h', ↓reduceDIte]

/-- The product of the factors over an interval containing both or neither of `p`, `p + 1` is
invariant under the crossing `s_p`. -/
theorem prod_Ico_midFac_sadj (s : Seq (stendhalWeight ℓ ν)) {p : ℕ} (hp : p + 1 < m) (a b : ℕ)
    (h : p + 1 < a ∨ b ≤ p ∨ (a ≤ p ∧ p + 1 < b)) :
    ∏ r ∈ Finset.Ico a b, midFac Q ν₀ (sadj m p • s) r =
      ∏ r ∈ Finset.Ico a b, midFac Q ν₀ s r :=
  Finset.prod_equiv (Equiv.swap p (p + 1))
    (fun r => by
      simp only [Finset.mem_Ico, Equiv.swap_apply_def]
      split_ifs <;> omega)
    (fun r _ => midFac_sadj s hp r)

end Scalars

section Position

variable {I : Type*} {ℓ : ℕ} {j : ℕ} {ν : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)

/-- The strand of `s` at `midPos j s` is red. -/
theorem lbl_midPos_ne_inl (s : Seq (stendhalWeight ℓ ν)) (h : midPos j s < m) (i : I) :
    s.lbl ⟨midPos j s, h⟩ ≠ .inl i := by
  obtain ⟨a, ha, hla⟩ := midPos_of_lt j s (lt_of_midPos_lt j h le_rfl)
  have : (⟨midPos j s, h⟩ : Fin m) = a := Fin.ext ha.symm
  rw [this, hla]
  exact Sum.inr_ne_inl

end Position

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Model

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Rλ" => KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)
local notation "Rc" => KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)
local notation "T" => StendhalAlgebra k Q Λ ν
local notation "Tc" => StendhalAlgebra k Q Λc ν₀
local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
local notation "ι" => insertMap (j := j) (hj := hj) (ν₀ := ν₀) Q Λ Λc
local notation "Eat" s:max n:max hn:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s n hn)
local notation "E" s:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s (midPos j s) (midPos_le j s))
local notation "bot" => botMap k Q Λ Λc j hj ν ν₀
local notation "σ" => midStendhal j hj Q Λ Λc ν ν₀
local notation "μ" => midMapKLR j hj Q Λ Λc ν ν₀
local notation "Ev" => Env k Q Λ Λc j hj ν ν₀

/-! ### Passages to the maximum -/

theorem passU_mid_mul_eSum (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ midPos j s) :
    passU Q Λ Λc j hj ν ν₀ n (midPos j s - n) * Eat s n (hn.trans (midPos_le j s)) =
      E s * passU Q Λ Λc j hj ν ν₀ n (midPos j s - n) := by
  have h := passU_mul_eSum (j := j) (hj := hj) (ν₀ := ν₀) Q Λ Λc s n (midPos j s - n)
    (by have := midPos_le j s; omega)
  rwa [insertSet_congr' s (p := n + (midPos j s - n)) _ (midPos_le j s) (by omega)] at h

theorem slides_passU_mid (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ midPos j s) (x : Rc) :
    ι s (midPos j s) (midPos_le j s) x * passU Q Λ Λc j hj ν ν₀ n (midPos j s - n) -
        passU Q Λ Λc j hj ν ν₀ n (midPos j s - n) * ι s n (hn.trans (midPos_le j s)) x ∈
      exitSpan Q Λ Λc j hj s (midPos j s) (midPos_le j s) := by
  have h := slides_passU (j := j) (hj := hj) Q Λ Λc s n x (midPos j s - n)
    (by have := midPos_le j s; omega)
  rwa [insertMap_congr' s (p := n + (midPos j s - n)) _ (midPos_le j s) (by omega),
    exitSpan_congr' s (p := n + (midPos j s - n)) _ (midPos_le j s) (by omega)] at h

variable (j hj Q Λ Λc ν₀) in
/-- **The diagram below the cap generator `cap s n`** in the model of a cap after `λ_j`, for
`n ≤ c = midPos j s`: the strands of `s` at `n, …, c - 1` pass under the maximum to the left. -/
def midCapBot (s : Seq (stendhalWeight ℓ ν)) (n : ℕ) (hn : n ≤ midPos j s) : Rp :=
  E s * passU Q Λ Λc j hj ν ν₀ n (midPos j s - n) * Eat s n (hn.trans (midPos_le j s))

theorem midCapBot_congr (s : Seq (stendhalWeight ℓ ν)) {n n' : ℕ} (hn : n ≤ midPos j s)
    (hn' : n' ≤ midPos j s) (h : n = n') :
    midCapBot j hj Q Λ Λc ν₀ s n hn = midCapBot j hj Q Λ Λc ν₀ s n' hn' := by
  subst h; rfl

theorem eSum_mul_midCapBot (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ midPos j s) :
    E s * midCapBot j hj Q Λ Λc ν₀ s n hn = midCapBot j hj Q Λ Λc ν₀ s n hn := by
  rw [midCapBot, ← mul_assoc, ← mul_assoc, (KLRAlgebra.eSum_idem _).eq]

theorem midCapBot_eq (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ midPos j s) :
    midCapBot j hj Q Λ Λc ν₀ s n hn =
      passU Q Λ Λc j hj ν ν₀ n (midPos j s - n) * Eat s n (hn.trans (midPos_le j s)) := by
  rw [midCapBot, mul_assoc, passU_mid_mul_eSum s hn, ← mul_assoc, (KLRAlgebra.eSum_idem _).eq,
    ← passU_mid_mul_eSum s hn]

/-- (max1) on the diagram below the cap generator: passing one more strand. -/
theorem midCapBot_mul_underRight (s : Seq (stendhalWeight ℓ ν)) {q : ℕ}
    (hq : q + 1 ≤ midPos j s) :
    midCapBot j hj Q Λ Λc ν₀ s (q + 1) hq * underRight N q =
      midCapBot j hj Q Λ Λc ν₀ s q (by omega) := by
  have hm := midPos_le j s
  have h1 := (underRight_mul_eSum (j := j) (hj := hj) (ν₀ := ν₀) Q Λ Λc s
    (hq.trans hm)).symm
  have h2 := (passU_succ_left Q Λ Λc (j := j) (hj := hj) (ν := ν) (ν₀ := ν₀) q
    (midPos j s - (q + 1))).symm
  rw [show midPos j s - (q + 1) + 1 = midPos j s - q by omega] at h2
  rw [midCapBot, midCapBot, mul_assoc, h1, ← mul_assoc, mul_assoc (E s), h2]

/-- (max2) on the diagram below the cap generator: a loop appears. -/
theorem midCapBot_mul_underLeft (s : Seq (stendhalWeight ℓ ν)) {n : ℕ}
    (hn : n + 1 ≤ midPos j s) :
    midCapBot j hj Q Λ Λc ν₀ s n (by omega) * underLeft N n =
      E s * midPass j hj Q Λ Λc ν ν₀ s n * (underRight N n * underLeft N n) *
        Eat s (n + 1) (hn.trans (midPos_le j s)) := by
  have hm := midPos_le j s
  have h1 := underLeft_mul_eSum (j := j) (hj := hj) (ν₀ := ν₀) (Q := Q) (Λ := Λ) (Λc := Λc)
    s (hn.trans hm)
  have h2 := passU_succ_left Q Λ Λc (j := j) (hj := hj) (ν := ν) (ν₀ := ν₀) n
    (midPos j s - (n + 1))
  rw [show midPos j s - (n + 1) + 1 = midPos j s - n by omega] at h2
  rw [midCapBot, mul_assoc, ← h1, h2]
  simp only [mul_assoc]

/-! ### Elements of the model -/

variable (L : Type*) [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)

include hL in
theorem op_midStendhal_one_mul_mem_nullIdeal {y : Rp} (hy : y ∈ midExit j hj Q Λ Λc ν ν₀) :
    op (σ 1 * bot y) ∈ nullIdeal L (midOp j hj Q Λ Λc ν ν₀) := by
  refine Submodule.iSup_induction _
    (motive := fun y => op (σ 1 * bot y) ∈ nullIdeal L (midOp j hj Q Λ Λc ν ν₀)) hy
    (fun s y hy => exitSpan_midPos_mem_nullIdeal L hL s hy) ?_ ?_
  · rw [map_zero, mul_zero, op_zero]; exact zero_mem _
  · intro y y' h h'; rw [map_add, mul_add, op_add]; exact add_mem h h'

theorem tmul_midGen_eq_of_sub_mem {Z Z' : Tp}
    (h : op (σ 1 * (Z - Z')) ∈ nullIdeal L (midOp j hj Q Λ Λc ν ν₀)) (v : L) :
    (Ind.tmul (midGen j hj Q Λ Λc ν ν₀ Z) v : MidModel j hj Q Λ Λc ν ν₀ L) =
      Ind.tmul (midGen j hj Q Λ Λc ν ν₀ Z') v := by
  have hsplit : midGen j hj Q Λ Λc ν ν₀ Z =
      ⟨op (σ 1 * (Z - Z')), mem_lIdeal_of_mem_nullIdeal h⟩ + midGen j hj Q Λ Λc ν ν₀ Z' :=
    Subtype.ext (by
      rw [Submodule.coe_add, midGen_val, midGen_val]
      change op (σ 1 * Z) = op (σ 1 * (Z - Z')) + op (σ 1 * Z')
      rw [← op_add, mul_sub, sub_add_cancel])
  rw [hsplit, Ind.add_tmul, tmul_eq_zero_of_mem_nullIdeal h, zero_add]

include hL in
/-- Diagrams differing by diagrams in which a strand leaves the window give the same element of
the model. -/
theorem tmul_midGen_bot_eq {X X' : Rp} (h : X - X' ∈ midExit j hj Q Λ Λc ν ν₀) (v : L) :
    (Ind.tmul (midGen j hj Q Λ Λc ν ν₀ (bot X)) v : MidModel j hj Q Λ Λc ν ν₀ L) =
      Ind.tmul (midGen j hj Q Λ Λc ν ν₀ (bot X')) v :=
  tmul_midGen_eq_of_sub_mem L (by rw [← map_sub]; exact op_midStendhal_one_mul_mem_nullIdeal L hL h)
    v

include hL in
/-- **A sliding diagram acts on the model by multiplication on the left.** -/
theorem midEnd_tmul_midGen {Y : Rp} (hY : MidSlides j hj Q Λ Λc ν ν₀ Y) (Z : Tp) (v : L) :
    midEnd L hL hY (Ind.tmul (midGen j hj Q Λ Λc ν ν₀ Z) v) =
      Ind.tmul (midGen j hj Q Λ Λc ν ν₀ (bot Y * Z)) v := by
  rw [midEnd_tmul]
  refine tmul_midGen_eq_of_sub_mem L ?_ v
  have he := midStendhal_one_mul_self (j := j) (hj := hj) (Q := Q) (Λ := Λ) (Λc := Λc)
    (ν := ν) (ν₀ := ν₀)
  have h1 : σ 1 * (bot Y * σ 1 * Z - bot Y * Z) =
      σ 1 * bot (Y * μ (redOrderedKLR k Q Λc ν₀) - μ (redOrderedKLR k Q Λc ν₀) * Y) * Z := by
    rw [map_sub, map_mul, map_mul, ← midStendhal_one_eq_bot]
    simp only [mul_sub, sub_mul, mul_assoc]
    rw [← mul_assoc (σ 1) (σ 1), he]
  rw [h1, op_mul]
  exact mul_mem_nullIdeal _ (op_midStendhal_one_mul_mem_nullIdeal L hL (hY _))

/-- A diagram at the maximum acting on `L` is the same diagram placed at the maximum. -/
theorem tmul_midGen_box (Z : Tp) (x : Rc) (v : L) :
    (Ind.tmul (midGen j hj Q Λ Λc ν ν₀ Z) (op (cupMap k Q Λc ν₀ x) • v) :
      MidModel j hj Q Λ Λc ν ν₀ L) =
      Ind.tmul (midGen j hj Q Λ Λc ν ν₀ (midBot j hj Q Λ Λc ν ν₀ x * Z)) v := by
  have he := midStendhal_one_mul_self (j := j) (hj := hj) (Q := Q) (Λ := Λ) (Λc := Λc)
    (ν := ν) (ν₀ := ν₀)
  rw [← Ind.op_smul_tmul]
  congr 1
  apply Subtype.ext
  change op (σ 1 * Z) * midOp j hj Q Λ Λc ν ν₀ (op (cupMap k Q Λc ν₀ x)) =
    op (σ 1 * (midBot j hj Q Λ Λc ν ν₀ x * Z))
  rw [midOp_apply, unop_op, midStendhal_cupMap', ← op_mul]
  congr 1
  rw [mul_assoc (σ 1) (midBot j hj Q Λ Λc ν ν₀ x), ← mul_assoc (midBot j hj Q Λ Λc ν ν₀ x),
    ← (commute_midStendhal_one_midBot x).eq, ← mul_assoc, ← mul_assoc, he, mul_assoc]

theorem tmul_midGen_algebraMap (Z : Tp) (c : k) (v : L) :
    (Ind.tmul (midGen j hj Q Λ Λc ν ν₀ Z) (op (algebraMap k Tc c) • v) :
      MidModel j hj Q Λ Λc ν ν₀ L) = c • Ind.tmul (midGen j hj Q Λ Λc ν ν₀ Z) v := by
  have he := midStendhal_one_mul_self (j := j) (hj := hj) (Q := Q) (Λ := Λ) (Λc := Λc)
    (ν := ν) (ν₀ := ν₀)
  rw [← Ind.op_smul_tmul, midModel_algebraMap_smul, Ind.smul_tmul]
  congr 1
  apply Subtype.ext
  change op (σ 1 * Z) * midOp j hj Q Λ Λc ν ν₀ (op (algebraMap k Tc c)) =
    algebraMap k Tpᵐᵒᵖ c * op (σ 1 * Z)
  rw [midOp_apply, unop_op, Algebra.algebraMap_eq_smul_one, map_smul, ← op_mul, smul_mul_assoc,
    ← mul_assoc, he, op_smul]
  exact Algebra.smul_def (A := Tpᵐᵒᵖ) c _

theorem op_smul_tmul_midGen (b Z : Tp) (v : L) :
    (op b : Tpᵐᵒᵖ) • (Ind.tmul (midGen j hj Q Λ Λc ν ν₀ Z) v : MidModel j hj Q Λ Λc ν ν₀ L) =
      Ind.tmul (midGen j hj Q Λ Λc ν ν₀ (Z * b)) v := by
  rw [Ind.smul_tmul, op_smul_midGen]

theorem tmul_midGen_zero (v : L) :
    (Ind.tmul (midGen j hj Q Λ Λc ν ν₀ 0) v : MidModel j hj Q Λ Λc ν ν₀ L) = 0 := by
  have h : midGen j hj Q Λ Λc ν ν₀ 0 = 0 := Subtype.ext (by
    change op (σ 1 * 0) = 0
    rw [mul_zero, op_zero])
  rw [h, Ind.zero_tmul]

/-! ### The left action on the generators -/

variable {L hL}

theorem midKLRAct_e (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) (t : Seq (stendhalWeight ℓ ν))
    (y : MidModel j hj Q Λ Λc ν ν₀ L) :
    midKLRAct hR (KLRAlgebra.e t) y = midEnd L hL (midSlides_midIdem t) y := by
  rw [KLRAlgebra.e, midKLRAct_mk, midEndAlg_apply,
    midEnd_eq_of_eq hL _ (midSlides_midIdem t) (midFree_fe t)]

theorem midKLRAct_x (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) (a : Fin m)
    (y : MidModel j hj Q Λ Λc ν ν₀ L) :
    midKLRAct hR (KLRAlgebra.x a) y = midEnd L hL (midSlides_midDot a) y := by
  rw [KLRAlgebra.x, midKLRAct_mk, midEndAlg_apply,
    midEnd_eq_of_eq hL _ (midSlides_midDot a) (midFree_fx a)]

theorem midKLRAct_ψ (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) (p : ℕ)
    (y : MidModel j hj Q Λ Λc ν ν₀ L) :
    midKLRAct hR (KLRAlgebra.ψ p) y = midEnd L hL (midSlides_midCross p) y := by
  rw [KLRAlgebra.ψ, midKLRAct_mk, midEndAlg_apply,
    midEnd_eq_of_eq hL _ (midSlides_midCross p) (midFree_fψ p)]

theorem midLeftAlg_topMap (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) (a : Rλ) :
    midLeftAlg L hL hR (topMap k Q Λ ν a) = midKLRAct hR a := by
  have h1 : midLeftAlg L hL hR 1 = 1 := map_one _
  change stendhalLift (redRelations_midKLRAct hR) (topMap k Q Λ ν a) = midKLRAct hR a
  rw [stendhalLift_topMap]
  change midKLRAct hR a * midLeftAlg L hL hR 1 = _
  rw [h1, mul_one]

theorem midLeftAlg_algebraMap (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) (c : k)
    (y : MidModel j hj Q Λ Λc ν ν₀ L) : midLeftAlg L hL hR (algebraMap k T c) y = c • y := by
  rw [AlgHom.commutes, Module.algebraMap_end_apply]

/-! ### The images of the cap generators -/

variable (L) in
/-- **The image of the cap generator `cap s n v`** in the model of a cap after `λ_j`. -/
def midCapImage (q : CapIdx ℓ ν) (v : L) : MidModel j hj Q Λ Λc ν ν₀ L :=
  if h : q.2.val ≤ midPos j q.1 then
    midCapScalar j Q ν₀ q.1 q.2 •
      Ind.tmul (midGen j hj Q Λ Λc ν ν₀ (bot (midCapBot j hj Q Λ Λc ν₀ q.1 q.2 h))) v
  else 0

local notation "img" =>
  midCapImage (j := j) (hj := hj) (Q := Q) (Λ := Λ) (Λc := Λc) (ν₀ := ν₀) L

theorem midCapImage_of_le (s : Seq (stendhalWeight ℓ ν)) (n : Fin (m + 1)) (v : L)
    (h : n.val ≤ midPos j s) :
    img (s, n) v = midCapScalar j Q ν₀ s n •
      Ind.tmul (midGen j hj Q Λ Λc ν ν₀ (bot (midCapBot j hj Q Λ Λc ν₀ s n h))) v := by
  simp only [midCapImage, h, ↓reduceDIte]

theorem midCapImage_of_lt (s : Seq (stendhalWeight ℓ ν)) (n : Fin (m + 1)) (v : L)
    (h : midPos j s < n.val) :
    img (s, n) v = 0 := by
  simp only [midCapImage, show ¬ n.val ≤ midPos j s by omega, ↓reduceDIte]

/-! ### The bimodule structure -/

variable (L hL) in
/-- **The model of `K̃^{λ⁺}_λ` for a cap after `λ_j`, as a bimodule**: the right
`T̃^{λ⁺}`-module `MidModel` with the left action of `T̃^λ` given by `hR`. -/
def MidBimod (_hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) : Type _ := MidModel j hj Q Λ Λc ν ν₀ L

instance (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) : AddCommGroup (MidBimod L hL hR) :=
  inferInstanceAs (AddCommGroup (MidModel j hj Q Λ Λc ν ν₀ L))

instance (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) : Module Ev (MidBimod L hL hR) :=
  Module.compHom (MidModel j hj Q Λ Λc ν ν₀ L) (midEnvAlg L hL hR)

theorem midBimod_smul (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) (r : Ev) (y : MidBimod L hL hR) :
    r • y = (midEnvAlg L hL hR r y : MidModel j hj Q Λ Λc ν ν₀ L) := rfl

variable (L hL) in
/-- An element of the model, viewed in the bimodule. -/
def toMidBimod (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) (y : MidModel j hj Q Λ Λc ν ν₀ L) :
    MidBimod L hL hR := y

variable (L hL) in
/-- An element of the bimodule, viewed in the model. -/
def ofMidBimod (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) (y : MidBimod L hL hR) :
    MidModel j hj Q Λ Λc ν ν₀ L := y

variable (L hL) in
/-- **The map from the free bimodule on the cap generators to the model.** -/
def midPhiFree (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) :
    FreeCap k Q Λ Λc j hj ν ν₀ L →ₗ[Ev] MidBimod L hL hR :=
  Finsupp.linearCombination _ fun p => toMidBimod L hL hR (img p.1 p.2)

theorem midPhiFree_gen (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) (q : CapIdx ℓ ν) (v : L) :
    midPhiFree L hL hR (gen q v) = toMidBimod L hL hR (img q v) := by
  rw [midPhiFree, gen, Finsupp.linearCombination_single, one_smul]

theorem midPhiFree_act (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) (a : T) (b : Tp)
    (z : FreeCap k Q Λ Λc j hj ν ν₀ L) :
    midPhiFree L hL hR (act a b z) = toMidBimod L hL hR (midLeftAlg L hL hR a
      ((op b : Tpᵐᵒᵖ) • ofMidBimod L hL hR (midPhiFree L hL hR z))) := by
  rw [act, map_smul]
  rfl

/-! ### The relations other than dots and crossings -/

theorem midPhiFree_add (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) (q : CapIdx ℓ ν) (v w : L) :
    midPhiFree L hL hR ((gen q (v + w) : FreeCap k Q Λ Λc j hj ν ν₀ L) - gen q v - gen q w) =
      0 := by
  rw [map_sub, map_sub, midPhiFree_gen, midPhiFree_gen, midPhiFree_gen, sub_sub, sub_eq_zero]
  have key : (img q (v + w) : MidModel j hj Q Λ Λc ν ν₀ L) =
      img q v + img q w := by
    unfold midCapImage
    split_ifs
    · rw [Ind.tmul_add, smul_add]
    · rw [add_zero]
  exact key

theorem midPhiFree_idem (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) (s : Seq (stendhalWeight ℓ ν))
    (n : Fin (m + 1)) (v : L) :
    midPhiFree L hL hR (act (topMap k Q Λ ν (KLRAlgebra.e s)) 1
      (gen (s, n) v : FreeCap k Q Λ Λc j hj ν ν₀ L) - gen (s, n) v) = 0 := by
  rw [map_sub, midPhiFree_act, midPhiFree_gen, op_one, one_smul, midLeftAlg_topMap, sub_eq_zero]
  change midKLRAct hR (KLRAlgebra.e s) (img (s, n) v) = img (s, n) v
  by_cases h : n.val ≤ midPos j s
  · rw [midCapImage_of_le s n v h, map_smul, midKLRAct_e, midEnd_tmul_midGen L hL, ← map_mul,
      midIdem, eSum_mul_midCapBot]
  · rw [midCapImage_of_lt s n v (by omega), map_zero]

theorem midPhiFree_box (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) (s : Seq (stendhalWeight ℓ ν))
    (n : Fin (m + 1)) (v : L) (x : Rc) :
    midPhiFree L hL hR ((gen (s, n) (op (cupMap k Q Λc ν₀ x) • v) :
      FreeCap k Q Λ Λc j hj ν ν₀ L) -
        act 1 (bot (ι s n (Nat.lt_succ_iff.1 n.2) x)) (gen (s, n) v)) = 0 := by
  rw [map_sub, midPhiFree_act, midPhiFree_gen, midPhiFree_gen, map_one, sub_eq_zero]
  change img (s, n) (op (cupMap k Q Λc ν₀ x) • v) =
    (op (bot (ι s n (Nat.lt_succ_iff.1 n.2) x)) : Tpᵐᵒᵖ) • img (s, n) v
  by_cases h : n.val ≤ midPos j s
  · have hn := h.trans (midPos_le j s)
    rw [midCapImage_of_le s n v h, midCapImage_of_le s n (op (cupMap k Q Λc ν₀ x) • v) h,
      smul_comm, op_smul_tmul_midGen,
      tmul_midGen_box, midCapBot, mul_assoc (E s), map_mul bot (E s), ← mul_assoc,
      midBot_mul_botMap_eSum, ← map_mul, ← map_mul]
    rw [← map_mul bot]
    have h1 : E s * passU Q Λ Λc j hj ν ν₀ n (midPos j s - n) * Eat s n hn * ι s n hn x =
        passU Q Λ Λc j hj ν ν₀ n (midPos j s - n) * ι s n hn x := by
      rw [mul_assoc, eSum_mul_insertMap, ← passU_mid_mul_eSum s h, mul_assoc,
        eSum_mul_insertMap]
    have h2 : ι s n hn x * Eat s n hn = ι s n hn x := insertMap_mul_eSum s hn x
    have hmem : ι s (midPos j s) (midPos_le j s) x *
          (passU Q Λ Λc j hj ν ν₀ n (midPos j s - n) * Eat s n hn) -
        E s * (passU Q Λ Λc j hj ν ν₀ n (midPos j s - n) * Eat s n hn) * ι s n hn x ∈
          midExit j hj Q Λ Λc ν ν₀ := by
      rw [← mul_assoc (E s), h1, show ι s (midPos j s) (midPos_le j s) x *
          (passU Q Λ Λc j hj ν ν₀ n (midPos j s - n) * Eat s n hn) -
            passU Q Λ Λc j hj ν ν₀ n (midPos j s - n) * ι s n hn x =
          (ι s (midPos j s) (midPos_le j s) x * passU Q Λ Λc j hj ν ν₀ n (midPos j s - n) -
            passU Q Λ Λc j hj ν ν₀ n (midPos j s - n) * ι s n hn x) * Eat s n hn by
        rw [sub_mul, mul_assoc, mul_assoc, h2]]
      exact mem_midExit s (exitSpan_mul_right s _ (slides_passU_mid s h x) _)
    rw [tmul_midGen_bot_eq L hL hmem v]
  · rw [midCapImage_of_lt s n v (by omega),
      midCapImage_of_lt s n (op (cupMap k Q Λc ν₀ x) • v) (by omega), smul_zero]

variable (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))

include hκ in
theorem midPhiFree_over (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) (s : Seq (stendhalWeight ℓ ν))
    (n : Fin (m + 1)) (v : L) (i : I) (hn : 0 < n.val)
    (hi : s.lbl ⟨n - 1, by omega⟩ = .inl i) :
    midPhiFree L hL hR (act 1 (bot (underRight N (n - 1)))
        (gen (s, n) v : FreeCap k Q Λ Λc j hj ν ν₀ L) -
      act (algebraMap k _ (cupScalar Q ν₀ i)) 1 (gen (s, ⟨n - 1, by omega⟩) v)) = 0 := by
  rw [map_sub, midPhiFree_act, midPhiFree_act, midPhiFree_gen, midPhiFree_gen, map_one, op_one,
    one_smul, sub_eq_zero]
  change (op (bot (underRight N (n - 1))) : Tpᵐᵒᵖ) • img (s, n) v =
    midLeftAlg L hL hR (algebraMap k T (cupScalar Q ν₀ i)) (img (s, ⟨n - 1, by omega⟩) v)
  rw [midLeftAlg_algebraMap]
  by_cases h : n.val ≤ midPos j s
  · have h' : (⟨n - 1, by omega⟩ : Fin (m + 1)).val ≤ midPos j s := by simp only; omega
    rw [midCapImage_of_le s n v h, midCapImage_of_le s _ v h', smul_comm, op_smul_tmul_midGen,
      ← map_mul, smul_smul]
    have hc : midCapScalar j Q ν₀ s n =
        cupScalar Q ν₀ i * midCapScalar j Q ν₀ s (⟨n - 1, by omega⟩ : Fin (m + 1)) := by
      have h1 := midCapScalar_eq_mul (j := j) (Q := Q) (ν₀ := ν₀) s (n := n - 1) (by omega)
      rw [show n.val - 1 + 1 = n.val by omega, midFac_inl s (by omega) hi] at h1
      rw [show ((⟨n - 1, by omega⟩ : Fin (m + 1)) : ℕ) = n.val - 1 from rfl, h1,
        Ring.mul_inverse_cancel_left _ _ (hκ i)]
    rw [← hc]
    congr 3
    rw [midCapBot_congr (j := j) s h (show n.val - 1 + 1 ≤ midPos j s by omega) (by omega),
      midCapBot_mul_underRight]
  · have h' : midPos j s < (⟨n - 1, by omega⟩ : Fin (m + 1)).val := by
      simp only
      by_contra h''
      have hc : n.val - 1 = midPos j s := by omega
      exact lbl_midPos_ne_inl (j := j) s (by omega) i (by
        rw [← hi]; exact congrArg s.lbl (Fin.ext hc.symm))
    rw [midCapImage_of_lt s n v (by omega), midCapImage_of_lt s _ v h', smul_zero, smul_zero]

include hκ in
theorem midPhiFree_under (hP : PullOffLeft k Q Λc ν₀ L) (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)
    (s : Seq (stendhalWeight ℓ ν)) (n : Fin (m + 1)) (v : L) (i : I) (hn : n.val < m)
    (hi : s.lbl ⟨n, hn⟩ = .inl i) :
    midPhiFree L hL hR (act 1 (bot (underLeft N n))
        (gen (s, n) v : FreeCap k Q Λ Λc j hj ν ν₀ L) - gen (s, ⟨n + 1, by omega⟩) v) = 0 := by
  rw [map_sub, midPhiFree_act, midPhiFree_gen, midPhiFree_gen, map_one, sub_eq_zero]
  change (op (bot (underLeft N n)) : Tpᵐᵒᵖ) • img (s, n) v =
    img (s, ⟨n + 1, by omega⟩) v
  by_cases h : n.val + 1 ≤ midPos j s
  · have h0 : n.val ≤ midPos j s := by omega
    rw [midCapImage_of_le s n v h0, midCapImage_of_le s _ v h, smul_comm, op_smul_tmul_midGen,
      ← map_mul, midCapBot_mul_underLeft s h,
      leftLoop_midPass (hj := hj) Q Λ Λc L hL hP i s h hi v, tmul_midGen_algebraMap, smul_smul]
    have hc : midCapScalar j Q ν₀ s n * cupScalar Q ν₀ i =
        midCapScalar j Q ν₀ s (⟨n + 1, by omega⟩ : Fin (m + 1)) := by
      rw [midCapScalar_eq_mul s (by omega), midFac_inl s hn hi, mul_comm, ← mul_assoc,
        Ring.mul_inverse_cancel _ (hκ i), one_mul]
    rw [hc]
    rfl
  · have h' : midPos j s < n.val := by
      by_contra h''
      have hc : n.val = midPos j s := by omega
      exact lbl_midPos_ne_inl (j := j) s (by omega) i (by
        rw [← hi]; exact congrArg s.lbl (Fin.ext hc.symm))
    rw [midCapImage_of_lt s n v h', midCapImage_of_lt s _ v (by simp only; omega), smul_zero]

end Model

end Categorification.Stendhal.CupCap
