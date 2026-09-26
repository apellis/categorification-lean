/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.NilHeckeBlockSplitting
import Categorification.KLR.GradedModules
import Categorification.QuantumGroup.QBinomial

/-!
# Characters at divided-power sequences

M. Khovanov, A. Lauda, *A diagrammatic approach to categorification of quantum groups I*,
arXiv:0803.4121v2, §2.5 (TeX lines ~1583–1615):

  "We have the equality of graded dimensions
  `gdim (1_î M) = q^{-⟨i⟩} i! · gdim (1_i M)`, `⟨i⟩ = ∑_k n_k (n_k - 1)/2`,
  which follows from the structure of the nilHecke algebra. Let
  `ch(M, i) = q^{-⟨i⟩} gdim (1_i M)`, then `ch(M, î) = i! · ch(M, i)`."

Here `i = i_1^{(n_1)} ⋯ i_r^{(n_r)} ∈ Seq'(ν)` is a divided-power expression, given as the list
`d` of pairs `(i_a, n_a)`, `î = expandDiv d` its expansion, `1_i = divIdemOf d h`, and
`i! = [n_1]! ⋯ [n_r]!` with `[n] = (q^n - q^{-n})/(q - q^{-1})`. We work with the KL I grading
(`klGradingDatum`, `deg x = 2`) over a field `k` and any graded `R(ν)`-module `M` with a graded
dimension (`HasGdim`, e.g. finitely generated modules).

Quantum integers are those of `Categorification.QuantumGroup` (`qint`, `qfact`, `qbinom`)
evaluated at the unit `q ∈ ℤ((q))` (`qUnitLS`); `qint_qUnitLS` identifies
`[n] = q^{n-1} + q^{n-3} + ⋯ + q^{1-n}`.

## Main results

* `gdim_divIdem_succ_of_grading` : for any grading datum, the splitting of
  `1_{…i^{(n)} i…}` gives `gdim (1_{…i^{(n)} i…} M) = (∑_{j ≤ n} q^{degX(i)·(j-n)})
  gdim (1_{…i^{(n+1)}…} M)`;
* `gdim_divIdem_succ` : for KL I, `gdim (1_{…i^{(n)} i…} M) = q^{-n} [n+1] gdim (1_{…i^{(n+1)}…} M)`;
* `gdim_divIdem_block` : `gdim (1_{…i…i…} M) = q^{-n(n-1)/2} [n]! gdim (1_{…i^{(n)}…} M)`;
* `gdim_e_ofList_expandDiv` : **KL I §2.5**, `gdim (1_î M) = q^{-⟨i⟩} i! gdim (1_i M)`;
* `chDiv`, `ch_ofList_expandDiv` : `ch(M, i) = q^{-⟨i⟩} gdim (1_i M)` and `ch(M, î) = i! ch(M, i)`;
* `chDiv_append_pair` : **KL I, Corollary 2.15, third equality**,
  `ch(M, …i^{(a)} i^{(b)}…) = [a+b choose a] ch(M, …i^{(a+b)}…)`.
-/

noncomputable section

namespace Categorification.KLR

open Graded HahnSeries QuantumGroup KLRAlgebra Finset

/-! ### Quantum integers in `ℤ((q))` -/


/-- The unit `q ∈ ℤ((q))`. -/
def qUnitLS : (LaurentSeries ℤ)ˣ where
  val := single 1 1
  inv := single (-1) 1
  val_inv := by rw [single_mul_single]; simp
  inv_val := by rw [single_mul_single]; simp

set_option synthInstance.maxHeartbeats 100000 in
theorem val_qUnitLS_zpow (z : ℤ) :
    ((qUnitLS ^ z : (LaurentSeries ℤ)ˣ) : LaurentSeries ℤ) = single z 1 := by
  rcases z with n | n
  · rw [Int.ofNat_eq_coe, zpow_natCast, Units.val_pow_eq_pow_val]
    show (single (1 : ℤ) (1 : ℤ)) ^ n = _
    rw [single_pow, one_pow, nsmul_one]
  · rw [zpow_negSucc, ← inv_pow, Units.val_pow_eq_pow_val]
    show (single (-1 : ℤ) (1 : ℤ)) ^ (n + 1) = _
    rw [single_pow, one_pow, Int.negSucc_eq]
    congr 1
    ring_nf

/-- `[n] = q^{n-1} + q^{n-3} + ⋯ + q^{1-n}` in `ℤ((q))`. -/
theorem qint_qUnitLS (n : ℕ) :
    qint qUnitLS n = ∑ j ∈ range n, (single ((n : ℤ) - 1 - 2 * j) 1 : LaurentSeries ℤ) := by
  rw [qint_eq_sum]
  exact sum_congr rfl fun j _ => val_qUnitLS_zpow _

theorem qint_qUnitLS_ne_zero {n : ℕ} (hn : 0 < n) : qint qUnitLS n ≠ 0 := by
  intro h0
  have h := congrArg (fun x : LaurentSeries ℤ => x.coeff ((n : ℤ) - 1)) h0
  simp only [qint_qUnitLS, HahnSeries.coeff_sum, HahnSeries.coeff_zero] at h
  rw [sum_eq_single 0 (fun j _ hj => by
    rw [HahnSeries.coeff_single, if_neg (by omega)]) (fun h' => absurd (mem_range.2 hn) h')] at h
  simp at h

theorem qfact_qUnitLS_ne_zero (n : ℕ) : qfact qUnitLS n ≠ 0 :=
  prod_ne_zero_iff.2 fun j _ => qint_qUnitLS_ne_zero (Nat.succ_pos j)

/-- The factor `q^{-n(n-1)/2} [n]!` contributed by a divided power `i^{(n)}`. -/
def blockFactor (n : ℕ) : LaurentSeries ℤ := single (-(n.choose 2 : ℤ)) 1 * qfact qUnitLS n

theorem blockFactor_zero : blockFactor 0 = 1 := by simp [blockFactor]

theorem blockFactor_succ (n : ℕ) :
    blockFactor (n + 1) = blockFactor n * (single (-(n : ℤ)) 1 * qint qUnitLS (n + 1)) := by
  rw [blockFactor, blockFactor, qfact_succ, NilHecke.choose_two_succ,
    show (-(((n.choose 2 + n : ℕ)) : ℤ)) = -(n.choose 2 : ℤ) + -(n : ℤ) by push_cast; ring,
    ← mul_one (1 : ℤ), ← single_mul_single]
  ring_nf

/-- `∑_{j ≤ n} q^{2(j - n)} = q^{-n} [n+1]`. -/
theorem sum_single_two_mul_sub (n : ℕ) :
    ∑ j : Fin (n + 1), (single (2 * ((j : ℤ) - n)) 1 : LaurentSeries ℤ) =
      single (-(n : ℤ)) 1 * qint qUnitLS (n + 1) := by
  rw [qint_qUnitLS, mul_sum, Fin.sum_univ_eq_sum_range (fun j => (single (2 * ((j : ℤ) - n)) 1 :
    LaurentSeries ℤ)) (n + 1), ← sum_range_reflect]
  refine sum_congr rfl fun j hj => ?_
  rw [mem_range] at hj
  rw [single_mul_single, one_mul]
  congr 1
  push_cast [Nat.cast_sub (show j ≤ n by omega)]
  ring_nf

/-! ### The inductive step -/

section Step

variable {I : Type*} [DecidableEq I] {k : Type*} [Field k] {ν : Multiset I}

local notation "m" => Multiset.card ν

/-- **Splitting a divided power, graded dimensions** (any grading datum): for a divided-power
block `(p, n + 1)` in a context `bs`,
`gdim (1_{…i^{(n)} i…} M) = (∑_{j ≤ n} q^{degX(c) (j - n)}) gdim (1_{…i^{(n+1)}…} M)`,
where `c` is the label of the block. -/
theorem gdim_divIdem_succ_of_grading {Q : I → I → MvPolynomial (Fin 2) k} (G : GradingDatum Q)
    (M : GMod (G.grade ν)) [HasGdim M.grading] {i : Seq ν} {p n : ℕ} {bs : List (ℕ × ℕ)}
    (h : IsBlocks i ((p, n + 1) :: bs)) {c : I}
    (hcl : ∀ a : Fin (Multiset.card ν), p ≤ a → (a : ℕ) < p + (n + 1) → i.lbl a = c) :
    gdim (idem M.grading (divIdem i ((p, n) :: bs) : KLRAlgebra k Q ν)) =
      (∑ j : Fin (n + 1), (single (G.degX c * ((j : ℤ) - n)) 1 : LaurentSeries ℤ)) *
        gdim (idem M.grading (divIdem i ((p, n + 1) :: bs) : KLRAlgebra k Q ν)) := by
  have hpn := h.le _ List.mem_cons_self
  have hc := h.const _ List.mem_cons_self
  rw [sum_mul]
  refine gdim_idem_eq_sum_of_isSplitting (𝒜 := G.grade ν) (ℳ := M.grading)
    (isSplitting_divIdem_succ h)
    (fun j => ?_) (fun j => ?_)
  · rw [← zero_add (G.degX c * ((j : ℤ) - n))]
    exact SetLike.mul_mem_graded (divIdem_mem_grade G h.tail)
      (blockA_mem_grade G hpn hcl hc j)
  · have := blockB_mem_grade G hpn hcl hc (show (j : ℕ) ≤ n by omega)
    convert this using 2
    ring

variable {Γ : SimpleGraph I} [DecidableRel Γ.Adj]

local notation "A" => KLRAlgebra k (klQ (k := k) Γ) ν
local notation "Gkl" => klGradingDatum k Γ

/-- **Splitting a divided power** (KL I grading):
`gdim (1_{…i^{(n)} i…} M) = q^{-n} [n+1] gdim (1_{…i^{(n+1)}…} M)`. -/
theorem gdim_divIdem_succ (M : GMod ((klGradingDatum k Γ).grade ν)) [HasGdim M.grading]
    {i : Seq ν} {p n : ℕ} {bs : List (ℕ × ℕ)} (h : IsBlocks i ((p, n + 1) :: bs)) :
    gdim (idem M.grading (divIdem i ((p, n) :: bs) : A)) =
      single (-(n : ℤ)) 1 * qint qUnitLS (n + 1) *
        gdim (idem M.grading (divIdem i ((p, n + 1) :: bs) : A)) := by
  have hpn := h.le _ List.mem_cons_self
  have hc := h.const _ List.mem_cons_self
  simp only at hpn
  rw [gdim_divIdem_succ_of_grading (Gkl) M h (c := i.lbl ⟨p, by omega⟩)
    (fun a h1 h2 => hc a _ h1 h2 le_rfl (by simp only; omega))]
  congr 1
  exact sum_single_two_mul_sub n

/-- **A divided power `i^{(n)}` in a context** (KL I §2.5):
`gdim (1_{…i ⋯ i…} M) = q^{-n(n-1)/2} [n]! gdim (1_{…i^{(n)}…} M)`. -/
theorem gdim_divIdem_block (M : GMod ((klGradingDatum k Γ).grade ν)) [HasGdim M.grading]
    {i : Seq ν} {p : ℕ} {bs : List (ℕ × ℕ)} :
    ∀ {n : ℕ}, IsBlocks i ((p, n) :: bs) →
      gdim (idem M.grading (divIdem i bs : A)) =
        blockFactor n * gdim (idem M.grading (divIdem i ((p, n) :: bs) : A))
  | 0, _ => by
    rw [blockFactor_zero, one_mul, divIdem, divIdem, blocksElt_cons]
    simp only
    rw [blockElt_zero, one_mul]
  | n + 1, h => by
    rw [gdim_divIdem_block M (h.cons_mono (Nat.le_succ n)), gdim_divIdem_succ M h,
      blockFactor_succ]
    simp only [mul_assoc]

/-- Iterating over all divided-power blocks:
`gdim (1_t M) = ∏_b q^{-n_b(n_b-1)/2} [n_b]! · gdim (divIdem t bs M)`. -/
theorem gdim_e_eq_prod_mul (M : GMod ((klGradingDatum k Γ).grade ν)) [HasGdim M.grading]
    {t : Seq ν} : ∀ {bs : List (ℕ × ℕ)}, IsBlocks t bs →
      gdim (idem M.grading (e t : A)) =
        (bs.map fun b => blockFactor b.2).prod * gdim (idem M.grading (divIdem t bs : A))
  | [], _ => by rw [divIdem_nil]; simp
  | b :: bs, h => by
    rw [gdim_e_eq_prod_mul M h.tail, gdim_divIdem_block M (p := b.1) (n := b.2) h,
      List.map_cons, List.prod_cons]
    ring

end Step

/-! ### Divided-power expressions -/

section DivSeq

variable {I : Type*} [DecidableEq I]

/-- `⟨i⟩ = ∑_a n_a (n_a - 1)/2` for `i = i_1^{(n_1)} ⋯ i_r^{(n_r)}`. -/
def divAngle (d : List (I × ℕ)) : ℕ := (d.map fun q => q.2.choose 2).sum

/-- `i! = [n_1]! ⋯ [n_r]!` in `ℤ((q))`. -/
def divQFact (d : List (I × ℕ)) : LaurentSeries ℤ := (d.map fun q => qfact qUnitLS q.2).prod

omit [DecidableEq I] in
theorem divQFact_ne_zero (d : List (I × ℕ)) : divQFact d ≠ 0 := by
  rw [divQFact]
  exact List.prod_ne_zero (by
    simp only [List.mem_map, not_exists, not_and]
    exact fun q _ h => qfact_qUnitLS_ne_zero q.2 h)

omit [DecidableEq I] in
theorem prod_blockFactor_blocksDiv (d : List (I × ℕ)) (p : ℕ) :
    ((KLRAlgebra.blocksDiv d p).map fun b => blockFactor b.2).prod =
      single (-(divAngle d : ℤ)) 1 * divQFact d := by
  induction d generalizing p with
  | nil => simp [KLRAlgebra.blocksDiv, divAngle, divQFact]
  | cons q d ih =>
    simp only [KLRAlgebra.blocksDiv, List.map_cons, List.prod_cons, ih, divAngle, divQFact,
      List.sum_cons]
    rw [blockFactor, show (-(((q.2.choose 2 + (d.map fun q => q.2.choose 2).sum : ℕ)) : ℤ)) =
      -(q.2.choose 2 : ℤ) + -(((d.map fun q => q.2.choose 2).sum : ℕ) : ℤ) by push_cast; ring,
      ← mul_one (1 : ℤ), ← single_mul_single]
    ring_nf

variable {k : Type*} [Field k] {ν : Multiset I} {Γ : SimpleGraph I} [DecidableRel Γ.Adj]

local notation "A" => KLRAlgebra k (klQ (k := k) Γ) ν

/-- **KL I §2.5**: `gdim (1_î M) = q^{-⟨i⟩} i! gdim (1_i M)` for a divided-power expression
`i = i_1^{(n_1)} ⋯ i_r^{(n_r)}` (the list `d`) with expansion `î`, and any graded
`R(ν)`-module `M` with a graded dimension. -/
theorem gdim_e_ofList_expandDiv (M : GMod ((klGradingDatum k Γ).grade ν)) [HasGdim M.grading]
    (d : List (I × ℕ)) (h : (KLRAlgebra.expandDiv d : Multiset I) = ν) :
    gdim (idem M.grading (e (Seq.ofList (KLRAlgebra.expandDiv d) h) : A)) =
      single (-(divAngle d : ℤ)) 1 * divQFact d * gdim (idem M.grading (divIdemOf d h : A)) := by
  rw [gdim_e_eq_prod_mul M (isBlocks_ofList d h), prod_blockFactor_blocksDiv]
  rfl

variable (Γ) in
/-- The character `ch(M, i) = q^{-⟨i⟩} gdim (1_i M)` at a divided-power expression
(KL I §2.5). -/
def chDiv (M : GMod ((klGradingDatum k Γ).grade ν)) (d : List (I × ℕ))
    (h : (KLRAlgebra.expandDiv d : Multiset I) = ν) : LaurentSeries ℤ :=
  single (-(divAngle d : ℤ)) 1 * gdim (idem M.grading (divIdemOf d h : A))

/-- **KL I §2.5**: `ch(M, î) = i! · ch(M, i)`. -/
theorem ch_ofList_expandDiv (M : GMod ((klGradingDatum k Γ).grade ν)) [HasGdim M.grading]
    (d : List (I × ℕ)) (h : (KLRAlgebra.expandDiv d : Multiset I) = ν) :
    (klGradingDatum k Γ).ch M (Seq.ofList (KLRAlgebra.expandDiv d) h) = divQFact d * chDiv Γ M d h := by
  rw [GradingDatum.ch, gdim_e_ofList_expandDiv, chDiv]
  ring

omit [DecidableEq I] in
theorem expandDiv_append_pair (d' d'' : List (I × ℕ)) (c : I) (a b : ℕ) :
    KLRAlgebra.expandDiv (d' ++ (c, a) :: (c, b) :: d'') =
      KLRAlgebra.expandDiv (d' ++ (c, a + b) :: d'') := by
  rw [KLRAlgebra.expandDiv, KLRAlgebra.expandDiv, List.flatMap_append, List.flatMap_append,
    List.flatMap_cons, List.flatMap_cons, List.flatMap_cons, List.replicate_add,
    List.append_assoc]

omit [DecidableEq I] in
theorem Seq.ofList_congr {l₁ l₂ : List I} (hl : l₁ = l₂) (h₁ : (l₁ : Multiset I) = ν)
    (h₂ : (l₂ : Multiset I) = ν) : Seq.ofList l₁ h₁ = Seq.ofList l₂ h₂ := by
  subst hl; rfl

/-- **KL I, Corollary 2.15, third equality**: for every graded `R(ν)`-module `M` with a graded
dimension, `ch(M, …i^{(a)} i^{(b)}…) = [a+b choose a] ch(M, …i^{(a+b)}…)`. -/
theorem chDiv_append_pair (M : GMod ((klGradingDatum k Γ).grade ν)) [HasGdim M.grading]
    (d' d'' : List (I × ℕ)) (c : I) (a b : ℕ)
    (h₁ : (KLRAlgebra.expandDiv (d' ++ (c, a) :: (c, b) :: d'') : Multiset I) = ν)
    (h₂ : (KLRAlgebra.expandDiv (d' ++ (c, a + b) :: d'') : Multiset I) = ν) :
    chDiv Γ M (d' ++ (c, a) :: (c, b) :: d'') h₁ =
      qbinom qUnitLS (a + b) a * chDiv Γ M (d' ++ (c, a + b) :: d'') h₂ := by
  have e1 := ch_ofList_expandDiv M _ h₁
  have e2 := ch_ofList_expandDiv M _ h₂
  rw [Seq.ofList_congr (expandDiv_append_pair d' d'' c a b) h₁ h₂, e2] at e1
  have hq := qbinom_mul_qfact qUnitLS b a
  rw [add_comm b a] at hq
  simp only [divQFact, List.map_append, List.map_cons, List.prod_append, List.prod_cons] at e1
  rw [← hq] at e1
  have hne : (d'.map fun q => qfact qUnitLS q.2).prod * (qfact qUnitLS a * (qfact qUnitLS b *
      (d''.map fun q => qfact qUnitLS q.2).prod)) ≠ 0 := by
    have h1 := divQFact_ne_zero d'
    have h2 := divQFact_ne_zero d''
    exact mul_ne_zero h1 (mul_ne_zero (qfact_qUnitLS_ne_zero a)
      (mul_ne_zero (qfact_qUnitLS_ne_zero b) h2))
  refine mul_left_cancel₀ hne ?_
  linear_combination -e1

end DivSeq

end Categorification.KLR
