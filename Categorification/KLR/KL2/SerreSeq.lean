/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.KL2.NilHeckeBlocks

/-!
# Sequences for the categorified Serre relations (KL II)

M. Khovanov, A. Lauda, *A diagrammatic approach to categorification of quantum groups II*,
arXiv:0804.2080v1, §3, "Quantum Serre relations" (TeX lines ~760–1010).

Positions are zero-indexed. We fix a window `[p, p + N]` of `N + 1` strands (`N = d + 1` in the
paper) inside sequences of weight `ν`, labels `i ≠ j`, and a sequence `t` with `t_p = j` and
`t_r = i` for `p < r ≤ p + N`, i.e. `t = …j i^N…` in the window (the context `…` is arbitrary).
The sequences `serreSeq t p a` (`0 ≤ a ≤ N`) are `…i^a j i^{N-a}…`: the `j` sits at position
`p + a` (`lbl_serreSeq`). We also record how the crossings `chainL`, `chainR` of
`Categorification.KLR.KL2.NilHeckeBlocks` move between these sequences.

* `lfun q l`, `rfun q l` : the permutations of positions `wordProd (range' q l)` and
  `wordProd (range' q l).reverse` (`val_wordProd_range'`, `val_wordProd_range'_reverse`).
* `chainL_mul_e`, `chainR_mul_e` : `chainL q l * e s = e (w • s) * chainL q l` etc.
* `chainL_mul_serre`, `chainR_mul_serre` : `chainL (p + a) l 1_{S a} = 1_{S (a + 1)} chainL (p + a) l`
  and `chainR (p + a - l) l 1_{S a} = 1_{S (a - 1)} chainR (p + a - l) l`.
-/

namespace Categorification.KLR.KL2

open Equiv MvPolynomial KLRAlgebra TypeA

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I}

local notation "m" => Multiset.card ν
local notation "A" => KLRAlgebra k Q ν

/-! ### Permutations of positions -/

/-- The strand at the bottom position `q + l` moves to the top position `q` (the permutation of
`chainL q l`). -/
def lfun (q l r : ℕ) : ℕ := if r = q + l then q else if q ≤ r ∧ r < q + l then r + 1 else r

/-- The strand at the bottom position `q` moves to the top position `q + l` (the permutation of
`chainR q l`). -/
def rfun (q l r : ℕ) : ℕ := if r = q then q + l else if q < r ∧ r ≤ q + l then r - 1 else r

omit [DecidableEq I] in
theorem val_wordProd_range' {q l : ℕ} (h : q + l < m) (r : Fin m) :
    (wordProd m (List.range' q l) r : ℕ) = lfun q l r := by
  induction l generalizing r with
  | zero =>
    simp only [List.range'_zero, wordProd, List.map_nil, List.prod_nil, Perm.one_apply]
    unfold lfun; split_ifs <;> omega
  | succ l ih =>
    rw [List.range'_concat, wordProd_append, wordProd_singleton, Perm.mul_apply,
      ih (by omega), sadj_val_of_lt (by omega)]
    have := swapNat_cases (q + 1 * l) r
    generalize swapNat (q + 1 * l) r = y at *
    unfold lfun
    split_ifs <;> omega

omit [DecidableEq I] in
theorem val_wordProd_range'_reverse {q l : ℕ} (h : q + l < m) (r : Fin m) :
    (wordProd m (List.range' q l).reverse r : ℕ) = rfun q l r := by
  induction l generalizing r with
  | zero =>
    simp only [List.range'_zero, List.reverse_nil, wordProd, List.map_nil, List.prod_nil,
      Perm.one_apply]
    unfold rfun; split_ifs <;> omega
  | succ l ih =>
    rw [List.range'_concat, List.reverse_append, wordProd_append, List.reverse_singleton,
      wordProd_singleton, Perm.mul_apply, sadj_val_of_lt (by omega), ih (by omega)]
    have := swapNat_cases (q + 1 * l) (rfun q l r)
    generalize swapNat (q + 1 * l) (rfun q l r) = y at *
    unfold rfun at *
    split_ifs at * <;> omega

omit [DecidableEq I] in
/-- Labels after `chainL q l`: `(w • s)_r = s_{w⁻¹ r}`. -/
theorem lbl_range'_smul {q l : ℕ} (h : q + l < m) (s : Seq ν) (r r' : Fin m)
    (hr : (r' : ℕ) = rfun q l r) : (wordProd m (List.range' q l) • s).lbl r = s.lbl r' := by
  simp only [Seq.lbl, Seq.smul_apply]
  refine congrArg s.1 (Fin.ext ?_)
  rw [hr, ← val_wordProd_range'_reverse h, wordProd_reverse]
  rfl

omit [DecidableEq I] in
/-- Labels after `chainR q l`. -/
theorem lbl_range'_reverse_smul {q l : ℕ} (h : q + l < m) (s : Seq ν) (r r' : Fin m)
    (hr : (r' : ℕ) = lfun q l r) :
    (wordProd m (List.range' q l).reverse • s).lbl r = s.lbl r' := by
  simp only [Seq.lbl, Seq.smul_apply]
  refine congrArg s.1 (Fin.ext ?_)
  rw [hr, ← val_wordProd_range' h, wordProd_reverse]
  simp [Perm.inv_def]

omit [DecidableEq I] in
theorem lfun_lt {q l r : ℕ} (h : q + l < m) (hr : r < m) : lfun q l r < m := by
  unfold lfun; split_ifs <;> omega

omit [DecidableEq I] in
theorem rfun_lt {q l r : ℕ} (h : q + l < m) (hr : r < m) : rfun q l r < m := by
  unfold rfun; split_ifs <;> omega

theorem chainL_mul_e (q l : ℕ) (s : Seq ν) :
    (chainL q l * e s : A) = e (wordProd m (List.range' q l) • s) * chainL q l :=
  ψw_mul_e _ s

theorem chainR_mul_e (q l : ℕ) (s : Seq ν) :
    (chainR q l * e s : A) = e (wordProd m (List.range' q l).reverse • s) * chainR q l :=
  ψw_mul_e _ s

/-- Crossings inside a block of equal labels commute with `1_s`. -/
theorem ψw_mul_e_of_const {ρ : List ℕ} {s : Seq ν} {lo n : ℕ} (hc : IsConstOn s lo n)
    (hρ : ∀ j ∈ ρ, lo ≤ j ∧ j + 1 < lo + n) : (ψw ρ * e s : A) = e s * ψw ρ :=
  ψw_mul_e_of_forall fun j hj h => hc.lbl_succ (hρ j hj).1 (hρ j hj).2 h

theorem chainL_mul_e_of_const {q l : ℕ} {s : Seq ν} (hc : IsConstOn s q (l + 1)) :
    (chainL q l * e s : A) = e s * chainL q l :=
  ψw_mul_e_of_const hc fun j hj => by rw [List.mem_range'_1] at hj; omega

theorem chainR_mul_e_of_const {q l : ℕ} {s : Seq ν} (hc : IsConstOn s q (l + 1)) :
    (chainR q l * e s : A) = e s * chainR q l :=
  ψw_mul_e_of_const hc fun j hj => by rw [List.mem_reverse, List.mem_range'_1] at hj; omega

/-! ### The sequences `…i^a j i^{N-a}…` -/

section serre

variable (t : Seq ν) (p : ℕ)

/-- The sequence `…i^a j i^{N-a}…`, obtained from `t = …j i^N…` by moving the `j` at position `p`
to position `p + a`. -/
def serreSeq (a : ℕ) : Seq ν := wordProd m (List.range' p a).reverse • t

variable {t p} {N : ℕ} {i j : I} (hpN : p + N < Multiset.card ν)
  (ht₀ : ∀ r : Fin (Multiset.card ν), (r : ℕ) = p → t.lbl r = j)
  (ht : ∀ r : Fin (Multiset.card ν), p < r → (r : ℕ) ≤ p + N → t.lbl r = i)

include hpN ht₀ ht in
/-- The labels of `…i^a j i^{N-a}…`. -/
theorem lbl_serreSeq {a : ℕ} (ha : a ≤ N) (r : Fin m) :
    (serreSeq t p a).lbl r =
      if (r : ℕ) = p + a then j else if p ≤ (r : ℕ) ∧ (r : ℕ) ≤ p + N then i else t.lbl r := by
  rw [serreSeq, lbl_range'_reverse_smul (by omega) t r ⟨lfun p a r, lfun_lt (by omega) r.2⟩ rfl]
  have hv : ((⟨lfun p a r, lfun_lt (by omega) r.2⟩ : Fin m) : ℕ) = lfun p a r := rfl
  generalize (⟨lfun p a r, lfun_lt (by omega) r.2⟩ : Fin m) = r' at hv ⊢
  unfold lfun at hv
  split_ifs at hv ⊢ <;> first
    | exact ht₀ r' (by omega)
    | exact ht r' (by omega) (by omega)
    | omega
    | exact congrArg t.lbl (Fin.ext (by omega))

include hpN ht₀ ht in
theorem serreSeq_lbl_eq_i {a : ℕ} (ha : a ≤ N) (r : Fin m) (h₁ : p ≤ r) (h₂ : (r : ℕ) ≤ p + N)
    (h₃ : (r : ℕ) ≠ p + a) : (serreSeq t p a).lbl r = i := by
  rw [lbl_serreSeq hpN ht₀ ht ha, if_neg h₃, if_pos ⟨h₁, h₂⟩]

include hpN ht₀ ht in
theorem serreSeq_lbl_eq_j {a : ℕ} (ha : a ≤ N) (r : Fin m) (h : (r : ℕ) = p + a) :
    (serreSeq t p a).lbl r = j := by
  rw [lbl_serreSeq hpN ht₀ ht ha, if_pos h]

include hpN ht₀ ht in
theorem serreSeq_lbl_of_lt {a : ℕ} (ha : a ≤ N) (r : Fin m) (h : (r : ℕ) < p ∨ p + N < r) :
    (serreSeq t p a).lbl r = t.lbl r := by
  rw [lbl_serreSeq hpN ht₀ ht ha, if_neg (by omega), if_neg (by omega)]

include hpN ht₀ ht in
/-- The block `[p, p + a)` of `…i^a j i^{N-a}…` is constant (labels `i`). -/
theorem isConstOn_serreSeq_left {a c n : ℕ} (ha : a ≤ N) (hc : p ≤ c) (hn : c + n ≤ p + a) :
    IsConstOn (serreSeq t p a) c n := by
  intro r r' h1 h2 h3 h4
  rw [serreSeq_lbl_eq_i hpN ht₀ ht ha r (by omega) (by omega) (by omega),
    serreSeq_lbl_eq_i hpN ht₀ ht ha r' (by omega) (by omega) (by omega)]

include hpN ht₀ ht in
/-- The block `[p + a + 1, p + N]` of `…i^a j i^{N-a}…` is constant (labels `i`). -/
theorem isConstOn_serreSeq_right {a c n : ℕ} (ha : a ≤ N) (hc : p + a < c)
    (hn : c + n ≤ p + N + 1) : IsConstOn (serreSeq t p a) c n := by
  intro r r' h1 h2 h3 h4
  rw [serreSeq_lbl_eq_i hpN ht₀ ht ha r (by omega) (by omega) (by omega),
    serreSeq_lbl_eq_i hpN ht₀ ht ha r' (by omega) (by omega) (by omega)]

include hpN ht₀ ht in
/-- `chainL (p + a) l` moves the strand at `p + a + l` (label `i`) across the `j` at `p + a`:
`…i^a j i^{N-a}… ↦ …i^{a+1} j i^{N-a-1}…`. -/
theorem smul_serreSeq_L {a l : ℕ} (hl : 1 ≤ l) (hal : a + l ≤ N) :
    wordProd m (List.range' (p + a) l) • serreSeq t p a = serreSeq t p (a + 1) := by
  apply Subtype.ext; funext r
  change (wordProd m (List.range' (p + a) l) • serreSeq t p a).lbl r = (serreSeq t p (a + 1)).lbl r
  rw [lbl_range'_smul (by omega) _ r ⟨rfun (p + a) l r, rfun_lt (by omega) r.2⟩ rfl]
  have hv : ((⟨rfun (p + a) l r, rfun_lt (by omega) r.2⟩ : Fin m) : ℕ) = rfun (p + a) l r := rfl
  generalize (⟨rfun (p + a) l r, rfun_lt (by omega) r.2⟩ : Fin m) = r' at hv ⊢
  rw [lbl_serreSeq hpN ht₀ ht (by omega), lbl_serreSeq hpN ht₀ ht (by omega)]
  unfold rfun at hv
  split_ifs at hv ⊢ <;> first | rfl | omega | exact congrArg t.lbl (Fin.ext (by omega))

include hpN ht₀ ht in
/-- `chainR (p + a - l) l` moves the strand at `p + a - l` (label `i`) across the `j` at `p + a`:
`…i^a j i^{N-a}… ↦ …i^{a-1} j i^{N-a+1}…`. -/
theorem smul_serreSeq_R {a l : ℕ} (hl : 1 ≤ l) (hla : l ≤ a) (ha : a ≤ N) :
    wordProd m (List.range' (p + a - l) l).reverse • serreSeq t p a = serreSeq t p (a - 1) := by
  apply Subtype.ext; funext r
  change (wordProd m (List.range' (p + a - l) l).reverse • serreSeq t p a).lbl r =
    (serreSeq t p (a - 1)).lbl r
  rw [lbl_range'_reverse_smul (by omega) _ r ⟨lfun (p + a - l) l r, lfun_lt (by omega) r.2⟩ rfl]
  have hv : ((⟨lfun (p + a - l) l r, lfun_lt (by omega) r.2⟩ : Fin m) : ℕ) =
    lfun (p + a - l) l r := rfl
  generalize (⟨lfun (p + a - l) l r, lfun_lt (by omega) r.2⟩ : Fin m) = r' at hv ⊢
  rw [lbl_serreSeq hpN ht₀ ht (by omega), lbl_serreSeq hpN ht₀ ht (by omega)]
  unfold lfun at hv
  split_ifs at hv ⊢ <;> first | rfl | omega | exact congrArg t.lbl (Fin.ext (by omega))

include hpN ht₀ ht in
theorem chainL_mul_serre {a l : ℕ} (hl : 1 ≤ l) (hal : a + l ≤ N) :
    (chainL (p + a) l * e (serreSeq t p a) : A) = e (serreSeq t p (a + 1)) * chainL (p + a) l := by
  rw [chainL_mul_e, smul_serreSeq_L hpN ht₀ ht hl hal]

include hpN ht₀ ht in
theorem chainR_mul_serre {a l : ℕ} (hl : 1 ≤ l) (hla : l ≤ a) (ha : a ≤ N) :
    (chainR (p + a - l) l * e (serreSeq t p a) : A) =
      e (serreSeq t p (a - 1)) * chainR (p + a - l) l := by
  rw [chainR_mul_e, smul_serreSeq_R hpN ht₀ ht hl hla ha]

end serre

end Categorification.KLR.KL2
