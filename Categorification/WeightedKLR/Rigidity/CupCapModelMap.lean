/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapLeftLoop
import Categorification.WeightedKLR.Rigidity.CupCapPairPassage

/-!
# The map from `K̃^{λ⁺}_λ` to the model of a cap at the right end

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.17, in the case `j = ℓ`. The cap generator
`cap s n v` of `K̃^{λ⁺}_λ` goes to the element `c(s, n) · e E_{s,m} U_n E_{s,n} ⊗ v` of the
induced model `Y` (`CupCap.EndModel`), where `U_n` passes the strands of `s` right of `n` under
the maximum to the right end (`CupCap.capBot`) and `c(s, n)` is the product of the scalars of
(max1) of the black strands of `s` left of `n` (`CupCap.capScalar`). Every relation of
Definition 7.15 holds in `Y`: diagrams at the maximum, dots and crossings slide through the
passage modulo diagrams in which a strand leaves the maximum, which vanish on a module `L`
supported on the loadings `μ ⋯ μ*`; (max1) holds by the normalization, and (max2) by the left
pull-off identity (`CupCap.leftLoop_endModel`).

## Main results

* `CupCap.underLeft_mul_eSum`: the passage of a strand under the maximum to the left moves the
  window.
* `CupCap.passU_succ_left`, `CupCap.passU_add`: splitting passages.
* `CupCap.dot_diff_mem`, `CupCap.cross_diff_mem`: dots and crossings on the top pass below the
  passage.
* `CupCap.relations_le_ker_phiFree`: the relations of Definition 7.15 hold in the model.
* `CupCap.capToModel`: the bimodule map `K̃^{λ⁺}_λ → Y`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MulOpposite InductionAlong

section Window

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)
  {j : ℕ} {hj : j ≤ ℓ} {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "E" s:max n:max hn:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s n hn)

theorem underLeft_mul_e_insertSeq (s : Seq (stendhalWeight ℓ ν))
    (t : Seq ((stendhalWeight 2 ν₀).map (cupColour j hj))) {q : ℕ} (hq : q + 1 ≤ m) :
    (underLeft N q * KLRAlgebra.e (insertSeq s (q + 1) hq t) : Rp) =
      KLRAlgebra.e (insertSeq s q (by omega) t) * underLeft N q := by
  rw [underLeft, KLRAlgebra.ψw_mul_e, wordProd_reverse, ← range'_smul_insertSeq s t hq,
    inv_smul_smul]

variable {Q Λ Λc} in
theorem underLeft_mul_eSum (s : Seq (stendhalWeight ℓ ν)) {q : ℕ} (hq : q + 1 ≤ m) :
    (underLeft N q * E s (q + 1) hq : Rp) = E s q (by omega) * underLeft N q := by
  rw [eSum_insertSet, eSum_insertSet, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun w _ => underLeft_mul_e_insertSeq Q Λ Λc s _ hq

/-- A passage splits off its first strand. -/
theorem passU_succ_left (q : ℕ) : ∀ d : ℕ,
    passU Q Λ Λc j hj ν ν₀ q (d + 1) = passU Q Λ Λc j hj ν ν₀ (q + 1) d * underRight N q
  | 0 => by rw [passU_succ, passU_zero, passU_zero, one_mul, mul_one, add_zero]
  | d + 1 => by
    rw [passU_succ, passU_succ_left q d, passU_succ, mul_assoc, show q + (d + 1) = q + 1 + d by
      omega]

/-- A passage splits into two consecutive passages. -/
theorem passU_add (q d : ℕ) : ∀ e : ℕ,
    passU Q Λ Λc j hj ν ν₀ q (d + e) = passU Q Λ Λc j hj ν ν₀ (q + d) e * passU Q Λ Λc j hj ν ν₀ q d
  | 0 => by rw [add_zero, passU_zero, one_mul]
  | e + 1 => by
    rw [← add_assoc, passU_succ, passU_add q d e, passU_succ, mul_assoc, add_assoc]

variable {Q Λ Λc} in
theorem commute_passU {y : Rp} (q : ℕ) : ∀ d : ℕ,
    (∀ p, q ≤ p → p < q + d → Commute y (underRight N p)) →
      Commute y (passU Q Λ Λc j hj ν ν₀ q d)
  | 0, _ => by rw [passU_zero]; exact Commute.one_right y
  | d + 1, h => by
    rw [passU_succ]
    exact (h _ (by omega) (by omega)).mul_right
      (commute_passU q d fun p hp hp' => h p hp (by omega))

variable {Q Λ Λc} in
theorem commute_x_underRight (a : Fin M) {p : ℕ} (h : (a : ℕ) < p ∨ p + N < a) :
    Commute (KLRAlgebra.x a : Rp) (underRight N p) :=
  KLRAlgebra.commute_x_ψw fun r hr => by rw [List.mem_range'_1] at hr; omega

variable {Q Λ Λc} in
theorem commute_ψ_underRight (a : ℕ) {p : ℕ} (h : a + 1 < p ∨ p + N < a) :
    Commute (KLRAlgebra.ψ a : Rp) (underRight N p) :=
  KLRAlgebra.commute_ψ_ψw fun r hr => by rw [List.mem_range'_1] at hr; omega

variable {Q Λ Λc} in
theorem ψ_crossPos_mul_eSum (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m) {p : ℕ}
    (hp : p + 1 < n ∨ n ≤ p) :
    (KLRAlgebra.ψ (crossPos n N p) * E s n hn : Rp) =
      E (sadj m p • s) n hn * KLRAlgebra.ψ (crossPos n N p) := by
  rw [eSum_insertSet, eSum_insertSet, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [KLRAlgebra.ψ_mul_e]
  congr 2
  have h := smul_insertSeq_old s hn (Seq.map (cupColour j hj) w) hp
  rw [Multiset.card_map] at h
  exact h

end Window

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Model

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)
  {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "T" => StendhalAlgebra k Q Λ ν
local notation "Tc" => StendhalAlgebra k Q Λc ν₀
local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc ℓ le_rfl) (ν + ν₀)
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc ℓ le_rfl)) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Rc" => KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)
local notation "ι" => insertMap (j := ℓ) (hj := le_rfl) (ν₀ := ν₀) Q Λ Λc
local notation "E" s:max n:max hn:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc ℓ le_rfl))
    (insertSet (j := ℓ) (hj := le_rfl) (ν₀ := ν₀) s n hn)
local notation "bot" => botMap k Q Λ Λc ℓ le_rfl ν ν₀

theorem endGen_add (Z Z' : Tp) :
    endGen Q Λ Λc ν ν₀ (Z + Z') = endGen Q Λ Λc ν ν₀ Z + endGen Q Λ Λc ν ν₀ Z' :=
  Subtype.ext (by
    rw [Submodule.coe_add, endGen_val, endGen_val, endGen_val, mul_add, op_add])

theorem endGen_zero : endGen Q Λ Λc ν ν₀ (0 : Tp) = 0 :=
  Subtype.ext (by rw [endGen_val, mul_zero, op_zero]; rfl)

theorem endGen_neg (Z : Tp) : endGen Q Λ Λc ν ν₀ (-Z) = -endGen Q Λ Λc ν ν₀ Z :=
  eq_neg_of_add_eq_zero_left (by rw [← endGen_add, neg_add_cancel, endGen_zero])

theorem endGen_sub (Z Z' : Tp) :
    endGen Q Λ Λc ν ν₀ (Z - Z') = endGen Q Λ Λc ν ν₀ Z - endGen Q Λ Λc ν ν₀ Z' := by
  rw [sub_eq_add_neg, endGen_add, endGen_neg, ← sub_eq_add_neg]

theorem prefixStendhal_one_mul_eSum (s : Seq (stendhalWeight ℓ ν)) :
    prefixStendhal Q Λ Λc ν ν₀ 1 * bot (E s m le_rfl) = bot (E s m le_rfl) := by
  rw [eSum_insertSet, map_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun t _ => prefixStendhal_one_mul_e Q Λ Λc s _

theorem prefixStendhal_topMap (a : KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)) :
    prefixStendhal Q Λ Λc ν ν₀ (topMap k Q Λ ν a) =
      prefixBot Q Λ Λc ν ν₀ a * prefixStendhal Q Λ Λc ν ν₀ 1 := by
  rw [prefixStendhal, stendhalLift_topMap]
  rfl

theorem prefixStendhal_topMap_mul (a : KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν))
    (s : Seq (stendhalWeight ℓ ν)) (y : Rp) :
    prefixStendhal Q Λ Λc ν ν₀ (topMap k Q Λ ν a) * bot (E s m le_rfl * y) =
      bot (prefixMapKLR Q Λ Λc ν ν₀ a * E s m le_rfl * y) := by
  rw [prefixStendhal_topMap, map_mul bot (E s m le_rfl), mul_assoc, ← mul_assoc _ (bot _),
    prefixStendhal_one_mul_eSum, prefixBot_apply, ← map_mul, ← map_mul, mul_assoc]

variable (L : Type*) [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

theorem leftAct_endGen (z : T) (Z : Tp) (v : L) :
    leftAct Q Λ Λc ν ν₀ L z (Ind.tmul (endGen Q Λ Λc ν ν₀ Z) v) =
      Ind.tmul (endGen Q Λ Λc ν ν₀ (prefixStendhal Q Λ Λc ν ν₀ z * Z)) v := by
  rw [leftAct_tmul]
  congr 1
  apply Subtype.ext
  change op (endStendhal Q Λ Λc ν ν₀ 1 * Z) * op (endStendhal Q Λ Λc ν ν₀ 1 *
    prefixStendhal Q Λ Λc ν ν₀ z) =
      op (endStendhal Q Λ Λc ν ν₀ 1 * (prefixStendhal Q Λ Λc ν ν₀ z * Z))
  rw [← op_mul]
  congr 1
  have hc := (commute_prefixStendhal_endStendhal Q Λ Λc z (1 : Tc)).eq
  have he : endStendhal Q Λ Λc ν ν₀ 1 * endStendhal Q Λ Λc ν ν₀ 1 = endStendhal Q Λ Λc ν ν₀ 1 := by
    rw [← map_mul, one_mul]
  rw [mul_assoc, ← mul_assoc (prefixStendhal Q Λ Λc ν ν₀ z), hc, ← mul_assoc, ← mul_assoc, he,
    mul_assoc]

theorem op_smul_tmul_endGen (b Z : Tp) (v : L) :
    (op b : Tpᵐᵒᵖ) • (Ind.tmul (endGen Q Λ Λc ν ν₀ Z) v : EndModel Q Λ Λc ν ν₀ L) =
      Ind.tmul (endGen Q Λ Λc ν ν₀ (Z * b)) v := by
  rw [Ind.smul_tmul, op_smul_endGen]

theorem tmul_endGen_algebraMap (Z : Tp) (c : k) (v : L) :
    (Ind.tmul (endGen Q Λ Λc ν ν₀ Z) (op (algebraMap k Tc c) • v) : EndModel Q Λ Λc ν ν₀ L) =
      c • Ind.tmul (endGen Q Λ Λc ν ν₀ Z) v := by
  rw [← Ind.op_smul_tmul, algebraMap_smul, Ind.smul_tmul]
  congr 1
  apply Subtype.ext
  change op (endStendhal Q Λ Λc ν ν₀ 1 * Z) * endOp Q Λ Λc ν ν₀ (op (algebraMap k Tc c)) =
    algebraMap k Tpᵐᵒᵖ c * op (endStendhal Q Λ Λc ν ν₀ 1 * Z)
  have he : endStendhal Q Λ Λc ν ν₀ 1 * endStendhal Q Λ Λc ν ν₀ 1 = endStendhal Q Λ Λc ν ν₀ 1 := by
    rw [← map_mul, one_mul]
  rw [endOp_apply, unop_op, Algebra.algebraMap_eq_smul_one, map_smul, ← op_mul, smul_mul_assoc,
    ← mul_assoc, he, op_smul]
  exact Algebra.smul_def (A := Tpᵐᵒᵖ) c _

/-- Diagrams whose difference has a strand leaving the maximum at the top give the same
element of the model. -/
theorem tmul_endGen_eq
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (s : Seq (stendhalWeight ℓ ν)) {y y' : Rp} (h : y - y' ∈ exitSpan Q Λ Λc ℓ le_rfl s m le_rfl)
    (v : L) :
    (Ind.tmul (endGen Q Λ Λc ν ν₀ (bot y)) v : EndModel Q Λ Λc ν ν₀ L) =
      Ind.tmul (endGen Q Λ Λc ν ν₀ (bot y')) v := by
  have h0 := tmul_eq_zero_of_mem_nullIdeal (exitSpan_mem_nullIdeal Q Λ Λc L hL s h) v
  rw [← sub_eq_zero, sub_eq_add_neg, ← Ind.neg_tmul, ← Ind.add_tmul, ← endGen_neg, ← endGen_add,
    ← sub_eq_add_neg, ← map_sub]
  exact h0

variable (ν₀) in
/-- The scalar of (max1) attached to a label: `κ_i` for a black strand of colour `i`, and `1`
for a red strand. -/
def labelScalar : I ⊕ Fin ℓ → k := Sum.elim (cupScalar Q ν₀) fun _ => 1

variable (ν₀) in
/-- The normalization of the cap generator `cap s n`: the product of the scalars of (max1) of
the strands of `s` left of `n`. -/
def capScalar (s : Seq (stendhalWeight ℓ ν)) (n : ℕ) : k :=
  ∏ r ∈ Finset.range n, if h : r < m then labelScalar Q ν₀ (s.lbl ⟨r, h⟩) else 1

theorem capScalar_succ (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n < m) :
    capScalar Q ν₀ s (n + 1) = labelScalar Q ν₀ (s.lbl ⟨n, hn⟩) * capScalar Q ν₀ s n := by
  simp only [capScalar, Finset.prod_range_succ, hn, ↓reduceDIte]
  rw [mul_comm]

theorem capScalar_sadj (s : Seq (stendhalWeight ℓ ν)) {n p : ℕ} (hn : n ≤ m)
    (hp : p + 1 < n ∨ n ≤ p) :
    capScalar Q ν₀ (sadj m p • s) n = capScalar Q ν₀ s n := by
  rcases hp with hp | hp
  · refine Finset.prod_equiv (Equiv.swap p (p + 1)) (fun r => ?_) (fun r hr => ?_)
    · simp only [Finset.mem_range]
      rcases eq_or_ne r p with rfl | h1
      · rw [Equiv.swap_apply_left]; omega
      rcases eq_or_ne r (p + 1) with rfl | h2
      · rw [Equiv.swap_apply_right]; omega
      rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
    · rw [Finset.mem_range] at hr
      by_cases h : r < m
      · have h' : Equiv.swap p (p + 1) r < m := by
          rcases eq_or_ne r p with rfl | h1
          · rw [Equiv.swap_apply_left]; omega
          rcases eq_or_ne r (p + 1) with rfl | h2
          · rw [Equiv.swap_apply_right]; omega
          rw [Equiv.swap_apply_of_ne_of_ne h1 h2]; exact h
        simp only [h, h', ↓reduceDIte]
        have hl : (sadj m p • s).lbl ⟨r, h⟩ = s.lbl (sadj m p ⟨r, h⟩) := by
          simp only [Seq.lbl, Seq.smul_apply, ← Equiv.Perm.inv_def, sadj_inv]
        rw [hl]
        congr 2
        apply Fin.ext
        rw [sadj_val_of_lt (by omega)]
        simp only [swapNat, Equiv.swap_apply_def]
      · have h' : ¬ Equiv.swap p (p + 1) r < m := by
          rcases eq_or_ne r p with rfl | h1
          · rw [Equiv.swap_apply_left]; omega
          rcases eq_or_ne r (p + 1) with rfl | h2
          · rw [Equiv.swap_apply_right]; omega
          rw [Equiv.swap_apply_of_ne_of_ne h1 h2]; exact h
        simp only [h, h', ↓reduceDIte]
  · refine Finset.prod_congr rfl fun r hr => ?_
    rw [Finset.mem_range] at hr
    by_cases h : r < m
    · simp only [h, ↓reduceDIte]
      rw [lbl_sadj_of_ne s _ (by simp; omega) (by simp; omega)]
    · simp only [h, ↓reduceDIte]

variable (ν₀) in
/-- **The diagram below the cap generator `cap s n`** in the model: the strands of `s` right of
`n` pass under the maximum to the right end. -/
def capBot (s : Seq (stendhalWeight ℓ ν)) (n : ℕ) (hn : n ≤ m) : Rp :=
  E s m le_rfl * passU Q Λ Λc ℓ le_rfl ν ν₀ n (m - n) * E s n hn

variable (ν₀) in
/-- The image of the cap generator `cap s n v` in the model. -/
def capImage (σ : CapIdx ℓ ν) (v : L) : EndModel Q Λ Λc ν ν₀ L :=
  capScalar Q ν₀ σ.1 σ.2 •
    Ind.tmul (endGen Q Λ Λc ν ν₀ (bot (capBot Q Λ Λc ν₀ σ.1 σ.2 (Nat.lt_succ_iff.1 σ.2.2)))) v

variable (ν₀) in
/-- The map from the free bimodule on the cap generators to the model. -/
def phiFree : FreeCap k Q Λ Λc ℓ le_rfl ν ν₀ L →ₗ[Env k Q Λ Λc ℓ le_rfl ν ν₀]
    EndModel Q Λ Λc ν ν₀ L :=
  Finsupp.linearCombination _ fun p => capImage Q Λ Λc ν₀ L p.1 p.2

theorem phiFree_gen (σ : CapIdx ℓ ν) (v : L) :
    phiFree Q Λ Λc ν₀ L (gen σ v) = capImage Q Λ Λc ν₀ L σ v := by
  rw [phiFree, gen, Finsupp.linearCombination_single, one_smul]

theorem phiFree_act (a : T) (b : Tp) (z : FreeCap k Q Λ Λc ℓ le_rfl ν ν₀ L) :
    phiFree Q Λ Λc ν₀ L (act a b z) =
      leftAct Q Λ Λc ν ν₀ L a ((op b : Tpᵐᵒᵖ) • phiFree Q Λ Λc ν₀ L z) := by
  rw [act, map_smul, envMk_smul]

theorem passU_end_mul_eSum (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m) :
    passU Q Λ Λc ℓ le_rfl ν ν₀ n (m - n) * E s n hn =
      E s m le_rfl * passU Q Λ Λc ℓ le_rfl ν ν₀ n (m - n) := by
  have h := passU_mul_eSum (j := ℓ) (hj := le_rfl) (ν₀ := ν₀) Q Λ Λc s n (m - n) (by omega)
  rwa [insertSet_congr s (p := n + (m - n)) _ le_rfl (by omega)] at h

theorem passU_end_mul_mem (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m) {y : Rp}
    (hy : y ∈ exitSpan Q Λ Λc ℓ le_rfl s n hn) :
    passU Q Λ Λc ℓ le_rfl ν ν₀ n (m - n) * y ∈ exitSpan Q Λ Λc ℓ le_rfl s m le_rfl := by
  have h := passU_mul_mem (j := ℓ) (hj := le_rfl) Q Λ Λc s n (m - n) (by omega) hy
  rwa [exitSpan_congr Q Λ Λc s (p := n + (m - n)) _ le_rfl (by omega)] at h

theorem slides_passU_end (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m) (x : Rc) :
    ι s m le_rfl x * passU Q Λ Λc ℓ le_rfl ν ν₀ n (m - n) -
        passU Q Λ Λc ℓ le_rfl ν ν₀ n (m - n) * ι s n hn x ∈
      exitSpan Q Λ Λc ℓ le_rfl s m le_rfl := by
  have h := slides_passU (j := ℓ) (hj := le_rfl) Q Λ Λc s n x (m - n) (by omega)
  rwa [insertMap_congr Q Λ Λc s (p := n + (m - n)) _ le_rfl (by omega),
    exitSpan_congr Q Λ Λc s (p := n + (m - n)) _ le_rfl (by omega)] at h

theorem eSum_end_mul_mem (s : Seq (stendhalWeight ℓ ν)) {y : Rp}
    (hy : y ∈ exitSpan Q Λ Λc ℓ le_rfl s m le_rfl) :
    E s m le_rfl * y ∈ exitSpan Q Λ Λc ℓ le_rfl s m le_rfl := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨z, hz, r, rfl⟩ := hy
    rw [← mul_assoc, eSum_mul_insertMap]
    exact mem_exitSpan s le_rfl hz r
  | zero => rw [mul_zero]; exact zero_mem _
  | add y y' _ _ h h' => rw [mul_add]; exact add_mem h h'
  | smul c y _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ c h

theorem capBot_congr (s : Seq (stendhalWeight ℓ ν)) {p p' : ℕ} (hp : p ≤ m) (hp' : p' ≤ m)
    (h : p = p') : capBot Q Λ Λc ν₀ s p hp = capBot Q Λ Λc ν₀ s p' hp' := by
  subst h; rfl

theorem eSum_endSet_mul_eSum (s : Seq (stendhalWeight ℓ ν)) :
    (KLRAlgebra.eSum _ (endSet ν ν₀) * E s m le_rfl : Rp) = E s m le_rfl := by
  rw [KLRAlgebra.eSum_mul_eSum, Finset.inter_eq_right.2 (insertSet_subset_endSet s)]

theorem capImage_mk (s : Seq (stendhalWeight ℓ ν)) (n : Fin (m + 1)) (v : L) :
    capImage Q Λ Λc ν₀ L (s, n) v = capScalar Q ν₀ s n •
      Ind.tmul (endGen Q Λ Λc ν ν₀ (bot (capBot Q Λ Λc ν₀ s n (Nat.lt_succ_iff.1 n.2)))) v := rfl

theorem op_smul_capImage (s : Seq (stendhalWeight ℓ ν)) (n : Fin (m + 1)) (v : L) (b : Tp) :
    (op b : Tpᵐᵒᵖ) • capImage Q Λ Λc ν₀ L (s, n) v = capScalar Q ν₀ s n •
      Ind.tmul (endGen Q Λ Λc ν ν₀ (bot (capBot Q Λ Λc ν₀ s n (Nat.lt_succ_iff.1 n.2)) * b)) v := by
  rw [capImage_mk, smul_comm, op_smul_tmul_endGen]

theorem phiFree_add (σ : CapIdx ℓ ν) (v w : L) :
    phiFree Q Λ Λc ν₀ L ((gen σ (v + w) : FreeCap k Q Λ Λc ℓ le_rfl ν ν₀ L) - gen σ v - gen σ w) =
      0 := by
  rw [map_sub, map_sub, phiFree_gen, phiFree_gen, phiFree_gen, capImage, capImage, capImage,
    Ind.tmul_add, smul_add, sub_sub, sub_self]

theorem phiFree_idem (s : Seq (stendhalWeight ℓ ν)) (n : Fin (m + 1)) (v : L) :
    phiFree Q Λ Λc ν₀ L (act (topMap k Q Λ ν (KLRAlgebra.e s)) 1
      (gen (s, n) v : FreeCap k Q Λ Λc ℓ le_rfl ν ν₀ L) - gen (s, n) v) = 0 := by
  rw [map_sub, phiFree_act, phiFree_gen, op_one, one_smul, capImage_mk,
    LinearMap.map_smul_of_tower, leftAct_endGen, capBot, mul_assoc,
    prefixStendhal_topMap_mul, prefixMapKLR_e,
    (KLRAlgebra.eSum_idem (Q := stendhalQ Q (plusLabels Λ Λc ℓ le_rfl)) _).eq, sub_self]

theorem op_smul_endGen_capBot (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m) (x : Rc) :
    (op (op (cupMap k Q Λc ν₀ x)) : Tcᵐᵒᵖᵐᵒᵖ) •
      endGen Q Λ Λc ν ν₀ (bot (capBot Q Λ Λc ν₀ s n hn)) =
      endGen Q Λ Λc ν ν₀ (bot (ι s m le_rfl x * (passU Q Λ Λc ℓ le_rfl ν ν₀ n (m - n) *
        E s n hn))) := by
  have hc := (commute_endStendhal_one_endBot Q Λ Λc (ν := ν) x).eq
  have he : endStendhal Q Λ Λc ν ν₀ 1 * endStendhal Q Λ Λc ν ν₀ 1 =
      endStendhal Q Λ Λc ν ν₀ 1 := by rw [← map_mul, one_mul]
  apply Subtype.ext
  change op (endStendhal Q Λ Λc ν ν₀ 1 * bot (capBot Q Λ Λc ν₀ s n hn)) *
    op (endStendhal Q Λ Λc ν ν₀ (cupMap k Q Λc ν₀ x)) = _
  rw [endStendhal_cupMap', ← op_mul, endGen_val]
  congr 1
  have hb : bot (capBot Q Λ Λc ν₀ s n hn) = bot (E s m le_rfl) *
      bot (passU Q Λ Λc ℓ le_rfl ν ν₀ n (m - n) * E s n hn) := by
    rw [capBot, mul_assoc, map_mul]
  have hι : bot (ι s m le_rfl x * (passU Q Λ Λc ℓ le_rfl ν ν₀ n (m - n) * E s n hn)) =
      endBot Q Λ Λc ν ν₀ x * bot (E s m le_rfl) *
        bot (passU Q Λ Λc ℓ le_rfl ν ν₀ n (m - n) * E s n hn) := by
    rw [map_mul bot (ι s m le_rfl x), ← endBot_mul_botMap_eSum]
  calc endStendhal Q Λ Λc ν ν₀ 1 * endBot Q Λ Λc ν ν₀ x *
        (endStendhal Q Λ Λc ν ν₀ 1 * bot (capBot Q Λ Λc ν₀ s n hn))
      = endStendhal Q Λ Λc ν ν₀ 1 * (endBot Q Λ Λc ν ν₀ x * endStendhal Q Λ Λc ν ν₀ 1) *
          bot (capBot Q Λ Λc ν₀ s n hn) := by simp only [mul_assoc]
    _ = endStendhal Q Λ Λc ν ν₀ 1 * endStendhal Q Λ Λc ν ν₀ 1 * endBot Q Λ Λc ν ν₀ x *
          bot (capBot Q Λ Λc ν₀ s n hn) := by rw [← hc]; simp only [mul_assoc]
    _ = _ := by rw [he, hι, hb]; simp only [mul_assoc]

theorem tmul_capBot_op_smul (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m) (x : Rc) (v : L) :
    (Ind.tmul (endGen Q Λ Λc ν ν₀ (bot (capBot Q Λ Λc ν₀ s n hn)))
      (op (cupMap k Q Λc ν₀ x) • v) : EndModel Q Λ Λc ν ν₀ L) =
      Ind.tmul (endGen Q Λ Λc ν ν₀ (bot (ι s m le_rfl x * (passU Q Λ Λc ℓ le_rfl ν ν₀ n (m - n) *
        E s n hn)))) v := by
  rw [← op_smul_endGen_capBot]
  exact (Ind.op_smul_tmul (φ := endOp Q Λ Λc ν ν₀) _ _ _).symm

theorem capBot_mul_insertMap (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m) (x : Rc) :
    capBot Q Λ Λc ν₀ s n hn * ι s n hn x =
      passU Q Λ Λc ℓ le_rfl ν ν₀ n (m - n) * ι s n hn x * E s n hn := by
  have h2 : ι s n hn x * E s n hn = ι s n hn x := by
    rw [← insertMap_one Q Λ Λc s hn, ← insertMap_mul, mul_one]
  rw [capBot, ← passU_end_mul_eSum Q Λ Λc s hn]
  simp only [mul_assoc]
  rw [← mul_assoc (E s n hn) (E s n hn),
    (KLRAlgebra.eSum_idem (Q := stendhalQ Q (plusLabels Λ Λc ℓ le_rfl)) _).eq,
    eSum_mul_insertMap, h2]

theorem phiFree_box
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (s : Seq (stendhalWeight ℓ ν)) (n : Fin (m + 1)) (v : L) (x : Rc) :
    phiFree Q Λ Λc ν₀ L ((gen (s, n) (op (cupMap k Q Λc ν₀ x) • v) :
      FreeCap k Q Λ Λc ℓ le_rfl ν ν₀ L) -
        act 1 (bot (ι s n (Nat.lt_succ_iff.1 n.2) x)) (gen (s, n) v)) = 0 := by
  have hn := Nat.lt_succ_iff.1 n.2
  rw [map_sub, phiFree_act, phiFree_gen, phiFree_gen, op_smul_capImage, leftAct_one,
    LinearMap.id_apply, capImage_mk, tmul_capBot_op_smul, sub_eq_zero]
  refine congrArg (capScalar Q ν₀ s n • ·) ?_
  rw [← map_mul bot (capBot Q Λ Λc ν₀ s n hn)]
  refine tmul_endGen_eq Q Λ Λc L hL s ?_ v
  rw [capBot_mul_insertMap, ← mul_assoc, ← sub_mul]
  exact exitSpan_mul_right s le_rfl (slides_passU_end Q Λ Λc s hn x) _

omit [DecidableEq I] in
theorem dotPos_val (n : Fin (m + 1)) (a : Fin m) :
    (dotPos (j := ℓ) (hj := le_rfl) (ν₀ := ν₀) n a).val =
      if a.val < n then a.val else a.val + N := by
  rw [dotPos, Fin.val_cast, insertPos_inl_val, Multiset.card_map]

omit [DecidableEq I] in
theorem lt_M_of_lt {a : ℕ} (ha : a < m) : a < Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀)) := by
  have := m_add_N (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀); omega

/-- **A dot on the top passes below the passage of the cap generator**, modulo diagrams in which
a strand leaves the maximum. -/
theorem dot_diff_mem (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m) (a : Fin m)
    (d : Fin (Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))))
    (hd : d.val = if a.val < n then a.val else a.val + N) :
    (KLRAlgebra.x ⟨a.val, lt_M_of_lt a.2⟩ * E s m le_rfl *
        (passU Q Λ Λc ℓ le_rfl ν ν₀ n (m - n) * E s n hn) -
      E s m le_rfl * passU Q Λ Λc ℓ le_rfl ν ν₀ n (m - n) * E s n hn * KLRAlgebra.x d : Rp) ∈
      exitSpan Q Λ Λc ℓ le_rfl s m le_rfl := by
  set P := passU Q Λ Λc ℓ le_rfl ν ν₀ n (m - n)
  set xa : Rp := KLRAlgebra.x ⟨a.val, lt_M_of_lt a.2⟩
  have hxm := (commute_x_eSum (Q' := stendhalQ Q (plusLabels Λ Λc ℓ le_rfl)) ⟨a.val, lt_M_of_lt a.2⟩
    (insertSet (j := ℓ) (hj := le_rfl) (ν₀ := ν₀) s m le_rfl)).eq
  have hxn := (commute_x_eSum (Q' := stendhalQ Q (plusLabels Λ Λc ℓ le_rfl)) d
    (insertSet (j := ℓ) (hj := le_rfl) (ν₀ := ν₀) s n hn)).eq
  have hre : xa * E s m le_rfl * (P * E s n hn) - E s m le_rfl * P * E s n hn * KLRAlgebra.x d =
      E s m le_rfl * (xa * P - P * KLRAlgebra.x d) * E s n hn := by
    calc xa * E s m le_rfl * (P * E s n hn) - E s m le_rfl * P * E s n hn * KLRAlgebra.x d
        = E s m le_rfl * xa * P * E s n hn - E s m le_rfl * P * (KLRAlgebra.x d * E s n hn) := by
          rw [hxm]; simp only [mul_assoc]; rw [← hxn]
      _ = _ := by noncomm_ring
  rw [hre]
  refine exitSpan_mul_right s le_rfl ?_ _
  by_cases ha : a.val < n
  · have hda : d = ⟨a.val, lt_M_of_lt a.2⟩ := Fin.ext (by simp [hd, ha])
    have hc : Commute xa P := commute_passU n (m - n) fun p hp _ =>
      commute_x_underRight _ (Or.inl (by simp only; omega))
    rw [hda, hc.eq, sub_self, mul_zero]
    exact zero_mem _
  · have hda : d.val = a.val + N := by simp [hd, ha]
    have ham := a.2
    have h1 := passU_add Q Λ Λc (j := ℓ) (hj := le_rfl) (ν := ν) (ν₀ := ν₀) n (a - n) (m - a)
    rw [show a.val - n + (m - a.val) = m - n by omega, show n + (a.val - n) = a.val by omega] at h1
    have h2 := passU_succ_left Q Λ Λc (j := ℓ) (hj := le_rfl) (ν := ν) (ν₀ := ν₀) a (m - a - 1)
    rw [show m - a.val - 1 + 1 = m - a.val by omega] at h2
    set P' := passU Q Λ Λc ℓ le_rfl ν ν₀ (a + 1) (m - a - 1)
    set P'' := passU Q Λ Λc ℓ le_rfl ν ν₀ n (a - n)
    have hP : P = P' * underRight N a * P'' := by
      change passU Q Λ Λc ℓ le_rfl ν ν₀ n (m - n) = _
      rw [h1, h2]
    have hc1 : Commute xa P' := commute_passU _ _ fun p hp _ =>
      commute_x_underRight _ (Or.inl (by simp only; omega))
    have hc2 : Commute (KLRAlgebra.x d : Rp) P'' := commute_passU _ _ fun p _ hp =>
      commute_x_underRight _ (Or.inr (by omega))
    have hE := passU_mul_eSum (j := ℓ) (hj := le_rfl) (ν₀ := ν₀) Q Λ Λc s (a + 1) (m - a - 1)
      (by omega)
    rw [insertSet_congr s (p := a.val + 1 + (m - a.val - 1)) _ le_rfl (by omega)] at hE
    have hD := slides_passing_x (j := ℓ) (hj := le_rfl) (ν₀ := ν₀) Q Λ Λc s (q := a) (by omega)
    have hxa : (KLRAlgebra.x ⟨a.val, lt_M_of_succ_le (ν₀ := ν₀) (by omega : a.val + 1 ≤ m)⟩ :
        Rp) = xa :=
      rfl
    have hxd : (KLRAlgebra.x ⟨a.val + N, add_N_lt_M_of_succ_le (ν₀ := ν₀)
        (by omega : a.val + 1 ≤ m)⟩ : Rp) = KLRAlgebra.x d := congrArg _ (Fin.ext hda.symm)
    rw [hxa, hxd] at hD
    have hre2 : E s m le_rfl * (xa * P - P * KLRAlgebra.x d) =
        P' * (E s (a + 1) (by omega) * (xa * underRight N a - underRight N a * KLRAlgebra.x d)) *
          P'' := by
      have h4 : xa * (P' * underRight N a * P'') - P' * underRight N a * P'' * KLRAlgebra.x d =
          P' * (xa * underRight N a - underRight N a * KLRAlgebra.x d) * P'' := by
        have e1 : xa * (P' * underRight N a * P'') = P' * xa * underRight N a * P'' := by
          simp only [← mul_assoc]; rw [hc1.eq]
        have e2 : P' * underRight N a * P'' * KLRAlgebra.x d =
            P' * underRight N a * KLRAlgebra.x d * P'' := by
          simp only [mul_assoc]; rw [hc2.eq]
        rw [e1, e2]; noncomm_ring
      rw [hP, h4]
      simp only [← mul_assoc]
      rw [← hE]
    rw [hre2]
    refine exitSpan_mul_right s le_rfl ?_ _
    have h3 := passU_mul_mem (j := ℓ) (hj := le_rfl) Q Λ Λc s (a + 1) (m - a - 1) (by omega) hD
    rwa [exitSpan_congr Q Λ Λc s (p := a.val + 1 + (m - a.val - 1)) _ le_rfl (by omega)] at h3

theorem phiFree_dot
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (s : Seq (stendhalWeight ℓ ν)) (n : Fin (m + 1)) (v : L) (a : Fin m) :
    phiFree Q Λ Λc ν₀ L (act (topMap k Q Λ ν (KLRAlgebra.x a)) 1
        (gen (s, n) v : FreeCap k Q Λ Λc ℓ le_rfl ν ν₀ L) -
      act 1 (bot (KLRAlgebra.x (dotPos (j := ℓ) (hj := le_rfl) (ν₀ := ν₀) n a)))
        (gen (s, n) v)) = 0 := by
  have hn := Nat.lt_succ_iff.1 n.2
  rw [map_sub, phiFree_act, phiFree_act, phiFree_gen, op_one, one_smul, op_smul_capImage,
    leftAct_one, LinearMap.id_apply, capImage_mk, LinearMap.map_smul_of_tower, leftAct_endGen,
    capBot, mul_assoc (E s m le_rfl), prefixStendhal_topMap_mul, sub_eq_zero]
  refine congrArg (capScalar Q ν₀ s n • ·) ?_
  rw [← map_mul bot]
  refine tmul_endGen_eq Q Λ Λc L hL s ?_ v
  rw [prefixMapKLR_x, mul_assoc (KLRAlgebra.x _), eSum_endSet_mul_eSum]
  simpa only [mul_assoc] using dot_diff_mem (ν₀ := ν₀) Q Λ Λc s hn a _ (dotPos_val n a)

omit [DecidableEq I] in
theorem crossPos_end {p : ℕ} (hp : p + 1 < m) : crossPos m N p = p := by
  unfold crossPos; split_ifs <;> omega

/-- **A crossing on the top passes below the passage of the cap generator**, modulo diagrams in
which a strand leaves the maximum. -/
theorem cross_diff_mem (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m) {p : ℕ}
    (hp : p + 1 < n ∨ n ≤ p) (hpm : p + 1 < m) :
    (KLRAlgebra.ψ p * E s m le_rfl * (passU Q Λ Λc ℓ le_rfl ν ν₀ n (m - n) * E s n hn) -
      E (sadj m p • s) m le_rfl * (passU Q Λ Λc ℓ le_rfl ν ν₀ n (m - n) *
        E (sadj m p • s) n hn) * KLRAlgebra.ψ (crossPos n N p) : Rp) ∈
      exitSpan Q Λ Λc ℓ le_rfl (sadj m p • s) m le_rfl := by
  set s' := sadj m p • s
  set P := passU Q Λ Λc ℓ le_rfl ν ν₀ n (m - n)
  have h1 := ψ_crossPos_mul_eSum (Q := Q) (Λ := Λ) (Λc := Λc) (j := ℓ) (hj := le_rfl) (ν₀ := ν₀) s
    (le_refl m) (p := p)
    (Or.inl hpm)
  rw [crossPos_end hpm] at h1
  have h2 := ψ_crossPos_mul_eSum (Q := Q) (Λ := Λ) (Λc := Λc) (j := ℓ) (hj := le_rfl) (ν₀ := ν₀) s
    hn hp
  have hre : KLRAlgebra.ψ p * E s m le_rfl * (P * E s n hn) -
      E s' m le_rfl * (P * E s' n hn) * KLRAlgebra.ψ (crossPos n N p) =
      E s' m le_rfl * (KLRAlgebra.ψ p * P - P * KLRAlgebra.ψ (crossPos n N p)) * E s n hn := by
    rw [h1]
    simp only [mul_assoc]
    rw [← h2]
    noncomm_ring
  rw [hre]
  refine exitSpan_mul_right _ le_rfl ?_ _
  rcases hp with hp | hp
  · have hc : crossPos n N p = p := by unfold crossPos; split_ifs <;> omega
    have hcom : Commute (KLRAlgebra.ψ p : Rp) P := commute_passU n (m - n) fun q hq _ =>
      commute_ψ_underRight _ (Or.inl (by omega))
    rw [hc, hcom.eq, sub_self, mul_zero]
    exact zero_mem _
  · have hc : crossPos n N p = p + N := by unfold crossPos; split_ifs <;> omega
    rw [hc]
    have h3 := passU_add Q Λ Λc (j := ℓ) (hj := le_rfl) (ν := ν) (ν₀ := ν₀) n (p - n) (m - p)
    rw [show p - n + (m - p) = m - n by omega, show n + (p - n) = p by omega] at h3
    have h4 := passU_add Q Λ Λc (j := ℓ) (hj := le_rfl) (ν := ν) (ν₀ := ν₀) p 2 (m - p - 2)
    rw [show 2 + (m - p - 2) = m - p by omega] at h4
    set P' := passU Q Λ Λc ℓ le_rfl ν ν₀ (p + 2) (m - p - 2)
    set P'' := passU Q Λ Λc ℓ le_rfl ν ν₀ n (p - n)
    set P2 := passU Q Λ Λc ℓ le_rfl ν ν₀ p 2
    have hP : P = P' * P2 * P'' := by
      change passU Q Λ Λc ℓ le_rfl ν ν₀ n (m - n) = _
      rw [h3, h4]
    have hc1 : Commute (KLRAlgebra.ψ p : Rp) P' := commute_passU _ _ fun q hq _ =>
      commute_ψ_underRight _ (Or.inl (by omega))
    have hc2 : Commute (KLRAlgebra.ψ (p + N) : Rp) P'' := commute_passU _ _ fun q _ hq =>
      commute_ψ_underRight _ (Or.inr (by omega))
    have hE := passU_mul_eSum (j := ℓ) (hj := le_rfl) (ν₀ := ν₀) Q Λ Λc s' (p + 2) (m - p - 2)
      (by omega)
    rw [insertSet_congr s' (p := p + 2 + (m - p - 2)) _ le_rfl (by omega)] at hE
    have hD := slides_passing_ψ (Q := Q) (Λ := Λ) (Λc := Λc) (j := ℓ) (hj := le_rfl) (ν₀ := ν₀) s'
      (q := p) (by omega)
    have h5 : KLRAlgebra.ψ p * P - P * KLRAlgebra.ψ (p + N) =
        P' * (KLRAlgebra.ψ p * P2 - P2 * KLRAlgebra.ψ (p + N)) * P'' := by
      have e1 : KLRAlgebra.ψ p * (P' * P2 * P'') = P' * KLRAlgebra.ψ p * P2 * P'' := by
        simp only [← mul_assoc]; rw [hc1.eq]
      have e2 : P' * P2 * P'' * KLRAlgebra.ψ (p + N) = P' * P2 * KLRAlgebra.ψ (p + N) * P'' := by
        simp only [mul_assoc]; rw [hc2.eq]
      rw [hP, e1, e2]; noncomm_ring
    rw [h5]
    simp only [← mul_assoc]
    rw [← hE]
    refine exitSpan_mul_right _ le_rfl ?_ _
    rw [mul_assoc]
    have h6 := passU_mul_mem (j := ℓ) (hj := le_rfl) Q Λ Λc s' (p + 2) (m - p - 2) (by omega) hD
    rwa [exitSpan_congr Q Λ Λc s' (p := p + 2 + (m - p - 2)) _ le_rfl (by omega)] at h6

omit [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
theorem act_zero_left (b : Tp) (z : FreeCap k Q Λ Λc ℓ le_rfl ν ν₀ L) : act 0 b z = 0 := by
  rw [act, Env.mk, TensorProduct.zero_tmul]
  exact zero_smul _ z

omit [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
theorem act_zero_right (a : T) (z : FreeCap k Q Λ Λc ℓ le_rfl ν ν₀ L) : act a 0 z = 0 := by
  rw [act, Env.mk, op_zero, TensorProduct.tmul_zero]
  exact zero_smul _ z

theorem phiFree_cross
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (s : Seq (stendhalWeight ℓ ν)) (n : Fin (m + 1)) (v : L) (p : ℕ)
    (hp : p + 1 < n.val ∨ n.val ≤ p) :
    phiFree Q Λ Λc ν₀ L (act (topMap k Q Λ ν (KLRAlgebra.ψ p)) 1
        (gen (s, n) v : FreeCap k Q Λ Λc ℓ le_rfl ν ν₀ L) -
      act 1 (bot (KLRAlgebra.ψ (crossPos n N p))) (gen (sadj m p • s, n) v)) = 0 := by
  have hn := Nat.lt_succ_iff.1 n.2
  by_cases hpm : p + 1 < m
  · rw [map_sub, phiFree_act, phiFree_act, phiFree_gen, phiFree_gen, op_one, one_smul,
      op_smul_capImage, leftAct_one, LinearMap.id_apply, capImage_mk, LinearMap.map_smul_of_tower,
      leftAct_endGen, capBot, mul_assoc (E s m le_rfl), prefixStendhal_topMap_mul,
      capScalar_sadj Q s hn hp, sub_eq_zero]
    refine congrArg (capScalar Q ν₀ s n • ·) ?_
    rw [← map_mul bot]
    refine tmul_endGen_eq Q Λ Λc L hL (sadj m p • s) ?_ v
    rw [prefixMapKLR_ψ _ _ _ hpm, mul_assoc (KLRAlgebra.ψ _), eSum_endSet_mul_eSum]
    simpa only [capBot, mul_assoc] using cross_diff_mem (ν₀ := ν₀) Q Λ Λc s hn hp hpm
  · have h1 : (KLRAlgebra.ψ p : KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)) = 0 :=
      KLRAlgebra.ψ_eq_zero p (by omega)
    have hc : crossPos n N p = p + N := by unfold crossPos; split_ifs <;> omega
    have h2 : (KLRAlgebra.ψ (crossPos n N p) : Rp) = 0 :=
      KLRAlgebra.ψ_eq_zero _ (by have := m_add_N (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀); omega)
    rw [h1, h2, map_zero, map_zero, act_zero_left, act_zero_right, sub_zero, map_zero]

theorem leftAct_algebraMap (c : k) (y : EndModel Q Λ Λc ν ν₀ L) :
    leftAct Q Λ Λc ν ν₀ L (algebraMap k T c) y = c • y := by
  rw [Algebra.algebraMap_eq_smul_one, leftAct_smul, leftAct_one, LinearMap.id_apply]

theorem capBot_succ_mul_underRight (s : Seq (stendhalWeight ℓ ν)) (q : ℕ) (hq : q + 1 ≤ m) :
    capBot Q Λ Λc ν₀ s (q + 1) hq * underRight N q = capBot Q Λ Λc ν₀ s q (by omega) := by
  have h1 := (underRight_mul_eSum (j := ℓ) (hj := le_rfl) (ν₀ := ν₀) Q Λ Λc s hq).symm
  have h2 := (passU_succ_left Q Λ Λc (j := ℓ) (hj := le_rfl) (ν := ν) (ν₀ := ν₀) q
    (m - (q + 1))).symm
  rw [show m - (q + 1) + 1 = m - q by omega] at h2
  rw [capBot, capBot, mul_assoc, h1, ← mul_assoc, mul_assoc (E s m le_rfl), h2]

theorem phiFree_over (s : Seq (stendhalWeight ℓ ν)) (n : Fin (m + 1)) (v : L) (i : I)
    (hn : 0 < n.val) (hi : s.lbl ⟨n - 1, by omega⟩ = .inl i) :
    phiFree Q Λ Λc ν₀ L (act 1 (bot (underRight N (n - 1)))
        (gen (s, n) v : FreeCap k Q Λ Λc ℓ le_rfl ν ν₀ L) -
      act (algebraMap k _ (cupScalar Q ν₀ i)) 1 (gen (s, ⟨n - 1, by omega⟩) v)) = 0 := by
  have hnm := Nat.lt_succ_iff.1 n.2
  have hc : capScalar Q ν₀ s n = cupScalar Q ν₀ i * capScalar Q ν₀ s (n - 1) := by
    have h := capScalar_succ Q (ν₀ := ν₀) s (n := n - 1) (by omega)
    rw [show n.val - 1 + 1 = n.val by omega, hi] at h
    exact h
  rw [map_sub, phiFree_act, phiFree_act, phiFree_gen, phiFree_gen, op_smul_capImage, leftAct_one,
    LinearMap.id_apply, op_one, one_smul, leftAct_algebraMap, capImage_mk, smul_smul, ← hc,
    sub_eq_zero]
  refine congrArg (capScalar Q ν₀ s n • ·) ?_
  rw [← map_mul bot, capBot_congr Q Λ Λc s _ (show n.val - 1 + 1 ≤ m by omega) (by omega),
    capBot_succ_mul_underRight]

theorem capBot_mul_underLeft (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n + 1 ≤ m) :
    capBot Q Λ Λc ν₀ s n (by omega) * underLeft N n =
      E s m le_rfl * passEnd Q Λ Λc ν ν₀ n * (underRight N n * underLeft N n) * E s (n + 1) hn := by
  have h1 := underLeft_mul_eSum (j := ℓ) (hj := le_rfl) (ν₀ := ν₀) (Q := Q) (Λ := Λ) (Λc := Λc)
    s hn
  have h2 := passU_succ_left Q Λ Λc (j := ℓ) (hj := le_rfl) (ν := ν) (ν₀ := ν₀) n (m - (n + 1))
  rw [show m - (n + 1) + 1 = m - n by omega] at h2
  rw [capBot, mul_assoc, ← h1, h2]
  simp only [mul_assoc]

theorem phiFree_under
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (hP : PullOffLeft k Q Λc ν₀ L) (s : Seq (stendhalWeight ℓ ν)) (n : Fin (m + 1)) (v : L)
    (i : I) (hn : n.val < m) (hi : s.lbl ⟨n, hn⟩ = .inl i) :
    phiFree Q Λ Λc ν₀ L (act 1 (bot (underLeft N n))
        (gen (s, n) v : FreeCap k Q Λ Λc ℓ le_rfl ν ν₀ L) - gen (s, ⟨n + 1, by omega⟩) v) = 0 := by
  have hc : capScalar Q ν₀ s (n + 1) = cupScalar Q ν₀ i * capScalar Q ν₀ s n := by
    rw [capScalar_succ Q s hn, hi]; rfl
  rw [map_sub, phiFree_act, phiFree_gen, phiFree_gen, op_smul_capImage, leftAct_one,
    LinearMap.id_apply, capImage_mk, ← map_mul bot, capBot_mul_underLeft Q Λ Λc s hn,
    leftLoop_endModel Q Λ Λc L hL hP i s hn hi v, tmul_endGen_algebraMap, smul_smul, mul_comm, ← hc,
    sub_eq_zero]
  rfl

/-- **The relations of `K̃^{λ⁺}_λ` hold in the model**: under the support hypothesis on `L` and
the left pull-off identity, every relation of Definition 7.15 maps to zero. -/
theorem relations_le_ker_phiFree
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (hP : PullOffLeft k Q Λc ν₀ L) :
    relations k Q Λ Λc ℓ le_rfl ν ν₀ L ≤ LinearMap.ker (phiFree Q Λ Λc ν₀ L) := by
  refine Submodule.span_le.2 fun z hz => ?_
  rw [SetLike.mem_coe, LinearMap.mem_ker]
  induction hz with
  | add σ v w => exact phiFree_add Q Λ Λc L σ v w
  | idem s n v => exact phiFree_idem Q Λ Λc L s n v
  | box s n v x => exact phiFree_box Q Λ Λc L hL s n v x
  | dot s n v a => exact phiFree_dot Q Λ Λc L hL s n v a
  | cross s n v p hp => exact phiFree_cross Q Λ Λc L hL s n v p hp
  | «over» s n v i hn hi => exact phiFree_over Q Λ Λc L s n v i hn hi
  | under s n v i hn hi => exact phiFree_under Q Λ Λc L hL hP s n v i hn hi

/-- **The map from `K̃^{λ⁺}_λ` to the model of a cap at the right end** (Webster,
arXiv:1309.3796v3, proof of Lemma 7.17, `j = ℓ`): `cap s n v` goes to the diagram in which the
strands of `s` right of `n` pass under the maximum, with `v` at the maximum, normalized by the
scalars of (max1) of the strands left of `n`. -/
def capToModel
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (hP : PullOffLeft k Q Λc ν₀ L) :
    CapTilde k Q Λ Λc ℓ le_rfl ν ν₀ L →ₗ[Env k Q Λ Λc ℓ le_rfl ν ν₀] EndModel Q Λ Λc ν ν₀ L :=
  (relations k Q Λ Λc ℓ le_rfl ν ν₀ L).liftQ (phiFree Q Λ Λc ν₀ L)
    (relations_le_ker_phiFree Q Λ Λc L hL hP)

theorem capToModel_mk
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (hP : PullOffLeft k Q Λc ν₀ L) (σ : CapIdx ℓ ν) (v : L) :
    capToModel Q Λ Λc L hL hP (Submodule.Quotient.mk (gen σ v)) = capImage Q Λ Λc ν₀ L σ v := by
  rw [capToModel, Submodule.liftQ_apply, phiFree_gen]

end Model

end Categorification.Stendhal.CupCap
