/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.KL2.Datum
import Categorification.KLR.KL2.SerreSeq

/-!
# The maps `α^±_{a,b}` of the categorified Serre relations (KL II)

M. Khovanov, A. Lauda, *A diagrammatic approach to categorification of quantum groups II*,
arXiv:0804.2080v1, §3, "Quantum Serre relations" (TeX lines ~760–1010, equations (17)–(26)).

We work in `R(ν)` for a Cartan datum `C` (`R2 k C ν`), with labels `i ≠ j`, `d = d_ij`, a window
`[p, p + N]` of positions with `N = d + 1`, and the sequences `S a = serreSeq t p a = …i^a j i^b…`
(`a + b = N = d + 1`, the `j` at position `p + a`). Positions are zero-indexed.

* `etop a = (e_{i,a} ⊗ 1_j ⊗ e_{i,b}) 1_{S a}`;
* `aplus a = (e_{i,a+1} ⊗ 1_j ⊗ e_{i,b-1}) ψ_{p+a} ⋯ ψ_{p+N-1} 1_{S a}` (KL II (17): the strand at
  the bottom position `p + N` moves to the top position `p + a`, crossing the `j` and `b - 1`
  strands `i`);
* `aminus a = (e_{i,a-1} ⊗ 1_j ⊗ e_{i,b+1}) ψ_{p+a-1} ⋯ ψ_p 1_{S a}` (KL II (21): the strand at
  the bottom position `p` moves to the top position `p + a`, crossing `a - 1` strands `i` and
  the `j`).

## Main results

* `aminus_mul_aplus`, `aplus_mul_aminus` : the simplified composites (KL II, "Relations (10),
  (11) imply …").
* `serre_A` : `α^+_{a-1,b+1} α^-_{a,b} - α^-_{a+1,b-1} α^+_{a,b} = (-1)^{a-1} e_{i,a} ⊗ 1_j ⊗ e_{i,b}`
  for `1 ≤ a ≤ d` (KL II, the display before Proposition 6).
* `serre_B` : `α^-_{1,d} α^+_{0,d+1} = 1_j ⊗ e_{i,d+1}`.
* `serre_C` : `α^+_{d,1} α^-_{d+1,0} = (-1)^d e_{i,d+1} ⊗ 1_j`.
* `serre_Dplus`, `serre_Dminus` : `α^+ α^+ = 0` and `α^- α^- = 0` (implicit in the proof of
  Proposition 6: the composites of consecutive arrows of (24) in the same direction vanish).
-/

namespace Categorification.KLR.KL2

open Equiv MvPolynomial KLRAlgebra TypeA QuantumGroup

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]

/-! ### Commutation of chains -/

section commute

variable {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I}

local notation "m" => Multiset.card ν
local notation "A" => KLRAlgebra k Q ν

theorem commute_chainL_blockElt {q l c n : ℕ} (h : q + l < c ∨ c + n ≤ q) :
    Commute (chainL q l : A) (blockElt c n) :=
  commute_ψw_blockElt fun j hj => by rw [List.mem_range'_1] at hj; omega

theorem commute_chainR_blockElt {q l c n : ℕ} (h : q + l < c ∨ c + n ≤ q) :
    Commute (chainR q l : A) (blockElt c n) :=
  commute_ψw_blockElt fun j hj => by rw [List.mem_reverse, List.mem_range'_1] at hj; omega

theorem commute_ψ_chainL {j q l : ℕ} (h : j + 1 < q ∨ q + l < j) :
    Commute (ψ j : A) (chainL q l) :=
  commute_ψ_ψw fun j' hj' => by rw [List.mem_range'_1] at hj'; omega

theorem commute_ψ_chainR {j q l : ℕ} (h : j + 1 < q ∨ q + l < j) :
    Commute (ψ j : A) (chainR q l) :=
  commute_ψ_ψw fun j' hj' => by rw [List.mem_reverse, List.mem_range'_1] at hj'; omega

theorem commute_x_chainL {a : Fin m} {q l : ℕ} (h : (a : ℕ) < q ∨ q + l < a) :
    Commute (x a : A) (chainL q l) :=
  commute_x_ψw fun j hj => by rw [List.mem_range'_1] at hj; omega

theorem commute_x_chainR {a : Fin m} {q l : ℕ} (h : (a : ℕ) < q ∨ q + l < a) :
    Commute (x a : A) (chainR q l) :=
  commute_x_ψw fun j hj => by rw [List.mem_reverse, List.mem_range'_1] at hj; omega

theorem commute_chainL_chainR {q l q' l' : ℕ} (h : q + l < q' ∨ q' + l' < q) :
    Commute (chainL q l : A) (chainR q' l') := by
  refine Commute.list_prod_left _ _ fun y hy => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
  rw [List.mem_range'_1] at hj
  exact commute_ψ_chainR (by omega)

theorem chainR_eq_ψ_mul {q a : ℕ} (ha : 1 ≤ a) :
    (chainR q a : A) = ψ (q + a - 1) * chainR q (a - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, a = n + 1 := ⟨a - 1, by omega⟩
  rw [chainR_succ', Nat.add_sub_cancel, show q + (n + 1) - 1 = q + n by omega]

theorem chainL_eq_ψ_mul {q l : ℕ} (hl : 1 ≤ l) :
    (chainL q l : A) = ψ q * chainL (q + 1) (l - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, l = n + 1 := ⟨l - 1, by omega⟩
  rw [chainL_succ, Nat.add_sub_cancel]

theorem commute_x_x (a b : Fin m) : Commute (x a : A) (x b) := x_mul_x a b

theorem commute_e_x (s : Seq ν) (a : Fin m) : Commute (e s : A) (x a) := (x_mul_e a s).symm

end commute

/-! ### The maps `α^±` -/

variable {C : CartanDatum I} {ν : Multiset I}

local notation "m" => Multiset.card ν
local notation "A" => R2 k C ν

section helpers

/-- KL II (13) in the form used for `α^±`: the block `[p, p + a)`. -/
theorem blockElt_mul_x_pow_mul_chainR' {s : Seq ν} {q a c : ℕ} (h : q + a ≤ m) (ha1 : 1 ≤ a)
    (hc : IsConstOn s q a) (hca : c ≤ a - 1) :
    (blockElt q a * x ⟨q + a - 1, by omega⟩ ^ c * chainR q (a - 1) * e s : A) =
      if c = a - 1 then (-1) ^ (a - 1) * (blockElt q a * e s) else 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, a = n + 1 := ⟨a - 1, by omega⟩
  have := blockElt_mul_x_pow_mul_chainR (k := k) (Q := klQ2 k C) (t := s) (q := q) (n := n)
    (a := c) h hc (by omega)
  simp only [Nat.add_sub_cancel] at hca ⊢
  convert this using 5

/-- KL II (12) in the form used for `α^±`: the block `[q, q + b)`. -/
theorem blockElt_mul_x_pow_mul_chainL' {s : Seq ν} {q b c : ℕ} (h : q + b ≤ m) (hb1 : 1 ≤ b)
    (hc : IsConstOn s q b) (hcb : c ≤ b - 1) :
    (blockElt q b * x ⟨q, by omega⟩ ^ c * chainL q (b - 1) * e s : A) =
      if c = b - 1 then blockElt q b * e s else 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
  exact blockElt_mul_x_pow_mul_chainL (k := k) (Q := klQ2 k C) (t := s) (q := q) (n := n)
    (a := c) h hc (by omega)

end helpers

section maps

variable (t : Seq ν) (p N : ℕ)

/-- `(e_{i,a} ⊗ 1_j ⊗ e_{i,b}) 1_{…i^a j i^b…}` (`b = N - a`). -/
noncomputable def etop (a : ℕ) : A :=
  blockElt p a * blockElt (p + a + 1) (N - a) * e (serreSeq t p a)

/-- KL II (17): `α^+_{a,b} = (e_{i,a+1} ⊗ 1_j ⊗ e_{i,b-1}) ψ_{p+a} ⋯ ψ_{p+N-1} 1_{…i^a j i^b…}`. -/
noncomputable def aplus (a : ℕ) : A :=
  blockElt p (a + 1) * blockElt (p + a + 2) (N - a - 1) * chainL (p + a) (N - a) *
    e (serreSeq t p a)

/-- KL II (21): `α^-_{a,b} = (e_{i,a-1} ⊗ 1_j ⊗ e_{i,b+1}) ψ_{p+a-1} ⋯ ψ_p 1_{…i^a j i^b…}`. -/
noncomputable def aminus (a : ℕ) : A :=
  blockElt p (a - 1) * blockElt (p + a) (N - a + 1) * chainR p a * e (serreSeq t p a)

variable {t p N} {i j : I} (hpN : p + N < Multiset.card ν)
  (ht₀ : ∀ r : Fin (Multiset.card ν), (r : ℕ) = p → t.lbl r = j)
  (ht : ∀ r : Fin (Multiset.card ν), p < r → (r : ℕ) ≤ p + N → t.lbl r = i)

local notation "S" => serreSeq t p

include hpN ht₀ ht

theorem commute_blockElt_left_e {a c n : ℕ} (ha : a ≤ N) (hc : p ≤ c) (hn : c + n ≤ p + a) :
    Commute (blockElt c n : A) (e (S a)) :=
  blockElt_mul_e (isConstOn_serreSeq_left hpN ht₀ ht ha hc hn)

theorem commute_blockElt_right_e {a c n : ℕ} (ha : a ≤ N) (hc : p + a < c)
    (hn : c + n ≤ p + N + 1) : Commute (blockElt c n : A) (e (S a)) :=
  blockElt_mul_e (isConstOn_serreSeq_right hpN ht₀ ht ha hc hn)

theorem chainL_serre {a l : ℕ} (hl : 1 ≤ l) (hal : a + l ≤ N) :
    (chainL (p + a) l * e (S a) : A) = e (S (a + 1)) * chainL (p + a) l :=
  chainL_mul_serre hpN ht₀ ht hl hal

theorem chainR_serre {a : ℕ} (ha1 : 1 ≤ a) (ha : a ≤ N) :
    (chainR p a * e (S a) : A) = e (S (a - 1)) * chainR p a := by
  have := chainR_mul_serre (k := k) (Q := klQ2 k C) hpN ht₀ ht (a := a) (l := a) ha1 le_rfl ha
  rwa [show p + a - a = p by omega] at this

theorem ψ_serre_L {a : ℕ} (ha : a + 1 ≤ N) :
    (ψ (p + a) * e (S a) : A) = e (S (a + 1)) * ψ (p + a) := by
  have := chainL_serre (k := k) (C := C) hpN ht₀ ht (a := a) (l := 1) le_rfl ha
  rwa [chainL_one] at this

theorem ψ_serre_R {a : ℕ} (ha1 : 1 ≤ a) (ha : a ≤ N) :
    (ψ (p + a - 1) * e (S a) : A) = e (S (a - 1)) * ψ (p + a - 1) := by
  have := chainR_mul_serre (k := k) (Q := klQ2 k C) hpN ht₀ ht (a := a) (l := 1) le_rfl ha1 ha
  rwa [chainR_one] at this

theorem commute_chainL_right_e {a q l : ℕ} (ha : a ≤ N) (hq : p + a < q) (hl : q + l ≤ p + N) :
    Commute (chainL q l : A) (e (S a)) :=
  chainL_mul_e_of_const (isConstOn_serreSeq_right hpN ht₀ ht ha hq (by omega))

theorem commute_chainR_left_e {a q l : ℕ} (ha : a ≤ N) (hq : p ≤ q) (hl : q + l < p + a) :
    Commute (chainR q l : A) (e (S a)) :=
  chainR_mul_e_of_const (isConstOn_serreSeq_left hpN ht₀ ht ha hq (by omega))

theorem commute_chainL_left_e {a q l : ℕ} (ha : a ≤ N) (hq : p ≤ q) (hl : q + l < p + a) :
    Commute (chainL q l : A) (e (S a)) :=
  chainL_mul_e_of_const (isConstOn_serreSeq_left hpN ht₀ ht ha hq (by omega))

theorem commute_chainR_right_e {a q l : ℕ} (ha : a ≤ N) (hq : p + a < q) (hl : q + l ≤ p + N) :
    Commute (chainR q l : A) (e (S a)) :=
  chainR_mul_e_of_const (isConstOn_serreSeq_right hpN ht₀ ht ha hq (by omega))

/-- `α^+_{a,b} = e_{top} ψ_{p+a} ⋯ ψ_{p+N-1}`: the top of `α^+_{a,b}` is the idempotent
`e_{i,a+1} ⊗ 1_j ⊗ e_{i,b-1}`. -/
theorem aplus_eq {a : ℕ} (ha : a + 1 ≤ N) :
    (aplus t p N a : A) = etop t p N (a + 1) * chainL (p + a) (N - a) := by
  rw [aplus, etop, mul_assoc _ (chainL _ _), chainL_serre (k := k) (C := C) hpN ht₀ ht (by omega) (by omega),
    show p + (a + 1) + 1 = p + a + 2 by omega, show N - (a + 1) = N - a - 1 by omega]
  simp only [mul_assoc]

/-- `α^-_{a,b} = e_{top} ψ_{p+a-1} ⋯ ψ_p`. -/
theorem aminus_eq {a : ℕ} (ha1 : 1 ≤ a) (ha : a ≤ N) :
    (aminus t p N a : A) = etop t p N (a - 1) * chainR p a := by
  rw [aminus, etop, mul_assoc _ (chainR _ _), chainR_serre (k := k) (C := C) hpN ht₀ ht ha1 ha,
    show p + (a - 1) + 1 = p + a by omega, show N - (a - 1) = N - a + 1 by omega]
  simp only [mul_assoc]

/-- KL II, "Relations (10), (11) imply": `α^-_{a+1,b-1} α^+_{a,b} = (e_{i,a} ⊗ 1_j ⊗ e_{i,b})
ψ_{p+a} ⋯ ψ_p ψ_{p+a} ⋯ ψ_{p+N-1} 1_{S a}` (no idempotents in the middle). -/
theorem aminus_mul_aplus {a : ℕ} (ha : a + 1 ≤ N) :
    (aminus t p N (a + 1) * aplus t p N a : A) =
      blockElt p a * blockElt (p + a + 1) (N - a) * chainR p (a + 1) * chainL (p + a) (N - a) *
        e (S a) := by
  have hLc : (chainL (p + a) (N - a) * e (S a) : A) = e (S (a + 1)) * chainL (p + a) (N - a) :=
    chainL_serre hpN ht₀ ht (by omega) (by omega)
  have hR1 : (chainR p (a + 1) * e (S (a + 1)) : A) = e (S a) * chainR p (a + 1) := by
    have := chainR_serre (k := k) (C := C) hpN ht₀ ht (a := a + 1) (by omega) ha
    rwa [show a + 1 - 1 = a by omega] at this
  have hBL1 : Commute (blockElt p (a + 1) : A) (e (S (a + 1))) :=
    commute_blockElt_left_e hpN ht₀ ht ha le_rfl (by omega)
  have hBRs : Commute (blockElt (p + a + 2) (N - a - 1) : A) (e (S (a + 1))) :=
    commute_blockElt_right_e hpN ht₀ ht ha (by omega) (by omega)
  have hc1 : Commute (blockElt p (a + 1) : A) (blockElt (p + a + 2) (N - a - 1)) :=
    commute_blockElt_blockElt (by omega)
  have hc2 : Commute (chainR p (a + 1) : A) (blockElt (p + a + 2) (N - a - 1)) :=
    commute_chainR_blockElt (by omega)
  have hc3 : Commute (blockElt p a : A) (blockElt (p + a + 1) (N - a)) :=
    commute_blockElt_blockElt (by omega)
  have hc4 : Commute (blockElt p a : A) (ψ (p + a)) := (commute_ψ_blockElt (by omega)).symm
  -- the middle idempotent `1_{S (a+1)}` is absorbed
  have hK1 : (e (S (a + 1)) * (blockElt p (a + 1) * (blockElt (p + a + 2) (N - a - 1) *
      (chainL (p + a) (N - a) * e (S a)))) : A) = blockElt p (a + 1) *
        (blockElt (p + a + 2) (N - a - 1) * (chainL (p + a) (N - a) * e (S a))) := by
    rw [hLc, hBRs.left_comm, hBL1.left_comm, ← mul_assoc (e _) (e _), e_mul_self]
  -- KL II (10) on the right block
  have hK2 : (blockElt (p + a + 1) (N - a) * (blockElt (p + a + 2) (N - a - 1) *
      (chainR p (a + 1) * (blockElt p (a + 1) * (chainL (p + a) (N - a) * e (S a))))) : A) =
      blockElt (p + a + 1) (N - a) * (chainR p (a + 1) * (blockElt p (a + 1) *
        (chainL (p + a) (N - a) * e (S a)))) := by
    have hW : (chainR p (a + 1) * (blockElt p (a + 1) * (chainL (p + a) (N - a) * e (S a))) : A) =
        e (S a) * (chainR p (a + 1) * (blockElt p (a + 1) * chainL (p + a) (N - a))) := by
      rw [hLc, hBL1.left_comm, ← mul_assoc (chainR p (a + 1)), hR1, mul_assoc]
    have h10 := blockElt_mul_blockElt_right (k := k) (Q := klQ2 k C) (t := S a)
      (q := p + a + 1) (n := N - a - 1) (by omega)
      (isConstOn_serreSeq_right hpN ht₀ ht (a := a) (by omega) (by omega) (by omega))
    rw [show N - a - 1 + 1 = N - a by omega, show p + a + 1 + 1 = p + a + 2 by omega] at h10
    rw [hW, ← mul_assoc, ← mul_assoc, h10, mul_assoc]
  -- KL II (11) on the left block
  have hK3 : (blockElt p a * (chainR p a * (blockElt p (a + 1) * (chainL (p + a) (N - a) *
      e (S a)))) : A) = blockElt p a * (chainR p a * (chainL (p + a) (N - a) * e (S a))) := by
    have h11 := blockElt_mul_chainR_mul_blockElt (k := k) (Q := klQ2 k C) (t := S (a + 1))
      (q := p) (n := a) (by omega) (isConstOn_serreSeq_left hpN ht₀ ht ha le_rfl (by omega))
    rw [hLc, ← mul_assoc, ← mul_assoc, ← mul_assoc, h11]
    simp only [mul_assoc]
  rw [aminus, aplus, show a + 1 - 1 = a by omega, show p + (a + 1) = p + a + 1 by omega,
    show N - (a + 1) + 1 = N - a by omega]
  simp only [mul_assoc]
  rw [hK1, hc1.left_comm, hc2.left_comm, hK2, chainR_succ']
  simp only [mul_assoc]
  conv_lhs => rw [hc3.left_comm, hc4.left_comm, hK3]
  rw [hc3.left_comm, hc4.left_comm]

/-- KL II, "Furthermore": `α^+_{a-1,b+1} α^-_{a,b} = (e_{i,a} ⊗ 1_j ⊗ e_{i,b})
ψ_{p+a-1} ⋯ ψ_{p+N-1} ψ_{p+a-1} ⋯ ψ_p 1_{S a}`. -/
theorem aplus_mul_aminus {a : ℕ} (ha1 : 1 ≤ a) (ha : a ≤ N) :
    (aplus t p N (a - 1) * aminus t p N a : A) =
      blockElt p a * blockElt (p + a + 1) (N - a) * chainL (p + a - 1) (N - a + 1) * chainR p a *
        e (S a) := by
  have hRa : (chainR p a * e (S a) : A) = e (S (a - 1)) * chainR p a :=
    chainR_serre hpN ht₀ ht ha1 ha
  have hL1 : (chainL (p + a - 1) (N - a + 1) * e (S (a - 1)) : A) =
      e (S a) * chainL (p + a - 1) (N - a + 1) := by
    have := chainL_serre (k := k) (C := C) hpN ht₀ ht (a := a - 1) (l := N - a + 1) (by omega)
      (by omega)
    rwa [show p + (a - 1) = p + a - 1 by omega, show a - 1 + 1 = a by omega] at this
  have hBL1 : Commute (blockElt p (a - 1) : A) (e (S (a - 1))) :=
    commute_blockElt_left_e hpN ht₀ ht (by omega) le_rfl (by omega)
  have hBRb : Commute (blockElt (p + a) (N - a + 1) : A) (e (S (a - 1))) :=
    commute_blockElt_right_e hpN ht₀ ht (by omega) (by omega) (by omega)
  have hBRs : Commute (blockElt (p + a + 1) (N - a) : A) (e (S a)) :=
    commute_blockElt_right_e hpN ht₀ ht ha (by omega) (by omega)
  have hc1 : Commute (blockElt (p + a + 1) (N - a) : A) (blockElt p (a - 1)) :=
    commute_blockElt_blockElt (by omega)
  have hc2 : Commute (chainL (p + a - 1) (N - a + 1) : A) (blockElt p (a - 1)) :=
    commute_chainL_blockElt (by omega)
  have hc3 : Commute (blockElt (p + a + 1) (N - a) : A) (ψ (p + a - 1)) :=
    (commute_ψ_blockElt (by omega)).symm
  -- the middle idempotent `1_{S (a-1)}` is absorbed
  have hK1 : (e (S (a - 1)) * (blockElt p (a - 1) * (blockElt (p + a) (N - a + 1) *
      (chainR p a * e (S a)))) : A) = blockElt p (a - 1) * (blockElt (p + a) (N - a + 1) *
        (chainR p a * e (S a))) := by
    rw [hRa, hBRb.left_comm, hBL1.left_comm, ← mul_assoc (e _) (e _), e_mul_self]
  -- KL II (10) on the left block
  have hK2 : (blockElt p a * (blockElt p (a - 1) * (blockElt (p + a + 1) (N - a) *
      (chainL (p + a - 1) (N - a + 1) * (blockElt (p + a) (N - a + 1) * (chainR p a *
        e (S a)))))) : A) = blockElt p a * (blockElt (p + a + 1) (N - a) *
          (chainL (p + a - 1) (N - a + 1) * (blockElt (p + a) (N - a + 1) *
            (chainR p a * e (S a))))) := by
    have hW : (blockElt (p + a + 1) (N - a) * (chainL (p + a - 1) (N - a + 1) *
        (blockElt (p + a) (N - a + 1) * (chainR p a * e (S a)))) : A) =
        e (S a) * (blockElt (p + a + 1) (N - a) * (chainL (p + a - 1) (N - a + 1) *
          (blockElt (p + a) (N - a + 1) * chainR p a))) := by
      rw [hRa, hBRb.left_comm, ← mul_assoc (chainL _ _), hL1, mul_assoc, hBRs.left_comm]
    have h10 := blockElt_mul_blockElt_left (k := k) (Q := klQ2 k C) (t := S a)
      (q := p) (n := a - 1) (by omega)
      (isConstOn_serreSeq_left hpN ht₀ ht ha le_rfl (by omega))
    rw [show a - 1 + 1 = a by omega] at h10
    rw [hW, ← mul_assoc, ← mul_assoc, h10, mul_assoc]
  -- KL II (11) on the right block
  have hK3 : (blockElt (p + a + 1) (N - a) * (chainL (p + a) (N - a) *
      (blockElt (p + a) (N - a + 1) * (chainR p a * e (S a)))) : A) =
      blockElt (p + a + 1) (N - a) * (chainL (p + a) (N - a) * (chainR p a * e (S a))) := by
    have h11 := blockElt_mul_chainL_mul_blockElt (k := k) (Q := klQ2 k C) (t := S (a - 1))
      (q := p + a) (n := N - a) (by omega)
      (isConstOn_serreSeq_right hpN ht₀ ht (a := a - 1) (by omega) (by omega) (by omega))
    rw [hRa, ← mul_assoc, ← mul_assoc, ← mul_assoc, h11]
    simp only [mul_assoc]
  rw [aminus, aplus, show a - 1 + 1 = a by omega, show p + (a - 1) + 2 = p + a + 1 by omega,
    show N - (a - 1) - 1 = N - a by omega, show p + (a - 1) = p + a - 1 by omega,
    show N - (a - 1) = N - a + 1 by omega]
  simp only [mul_assoc]
  rw [hK1]
  conv_lhs => rw [hc2.left_comm, hc1.left_comm, hK2]
  rw [chainL_succ, show p + a - 1 + 1 = p + a by omega]
  simp only [mul_assoc]
  conv_lhs => rw [hc3.left_comm, hK3]
  rw [hc3.left_comm]

/-- One term of the sum produced by the relation `eq_r3_hard` in the proof of `serre_A`: by
KL II (12) and (13) only the term `c = a - 1` survives. -/
theorem serre_A_term {a c c' : ℕ} (ha1 : 1 ≤ a) (ha : a + 1 ≤ N) (hcc : c + c' = N - 2) :
    (blockElt p a * blockElt (p + a + 1) (N - a) *
        (x ⟨p + a - 1, by omega⟩ ^ c * x ⟨p + a + 1, by omega⟩ ^ c' * e (S a)) *
        (chainL (p + a + 1) (N - a - 1) * chainR p (a - 1)) : A) =
      if c = a - 1 then (-1) ^ (a - 1) * etop t p N a else 0 := by
  set X : A := x ⟨p + a - 1, by omega⟩ ^ c
  set X' : A := x ⟨p + a + 1, by omega⟩ ^ c'
  set Lr : A := chainL (p + a + 1) (N - a - 1)
  set Rl : A := chainR p (a - 1)
  set BL : A := blockElt p a
  set BR : A := blockElt (p + a + 1) (N - a)
  have hLRe : Commute (Lr * Rl) (e (S a)) :=
    (commute_chainL_right_e hpN ht₀ ht (by omega) (by omega) (by omega)).mul_left
      (commute_chainR_left_e hpN ht₀ ht (by omega) le_rfl (by omega))
  have c1 : Commute BR X := ((commute_x_blockElt (by simp only; omega)).pow_left c).symm
  have c2 : Commute Lr Rl := commute_chainL_chainR (by omega)
  have c3 : Commute X' Rl := (commute_x_chainR (by simp only; omega)).pow_left c'
  have c4 : Commute BR Rl := (commute_chainR_blockElt (by omega)).symm
  -- the two groups of strands
  have hG : Commute (BL * X * Rl) (BR * X' * Lr) := by
    have hBL : Commute BL (BR * X' * Lr) :=
      ((commute_blockElt_blockElt (by omega)).mul_right
        ((commute_x_blockElt (by simp only; omega)).pow_left c').symm).mul_right
        (commute_chainL_blockElt (by omega)).symm
    have hX : Commute X (BR * X' * Lr) :=
      (c1.symm.mul_right ((commute_x_x _ _).pow_pow c c')).mul_right
        ((commute_x_chainL (by simp only; omega)).pow_left c)
    have hR : Commute Rl (BR * X' * Lr) := (c4.symm.mul_right c3.symm).mul_right c2.symm
    exact (hBL.mul_left hX).mul_left hR
  have hform : (BL * BR * (X * X' * e (S a)) * (Lr * Rl) : A) = BL * X * Rl * (BR * X' * Lr *
      e (S a)) := by
    simp only [mul_assoc]
    rw [← hLRe.eq]
    simp only [mul_assoc]
    rw [c1.left_comm, c2.left_comm, c3.left_comm, c4.left_comm]
  rw [hform]
  have h12 : c' ≤ N - a - 1 → (BR * X' * Lr * e (S a) : A) =
      if c' = N - a - 1 then BR * e (S a) else 0 := fun hc' =>
    blockElt_mul_x_pow_mul_chainL' (k := k) (C := C) (s := S a) (q := p + a + 1)
      (b := N - a) (c := c') (by omega) (by omega)
      (isConstOn_serreSeq_right hpN ht₀ ht (by omega) (by omega) (by omega)) (by omega)
  rcases Nat.lt_or_ge (a - 1) c with hlt | hge
  · -- `c > a - 1`: the right group vanishes by (12)
    rw [if_neg (by omega)]
    rw [h12 (by omega), if_neg (by omega), mul_zero]
  · -- `c ≤ a - 1`: evaluate the left group by (13)
    have h13 := blockElt_mul_x_pow_mul_chainR' (k := k) (C := C) (s := S a) (q := p) (a := a)
      (c := c) (by omega) ha1 (isConstOn_serreSeq_left hpN ht₀ ht (by omega) le_rfl le_rfl) hge
    rw [← mul_assoc, hG.eq, mul_assoc]
    have h13' : (BL * X * Rl * e (S a) : A) =
        if c = a - 1 then (-1) ^ (a - 1) * (BL * e (S a)) else 0 := h13
    rw [h13']
    split_ifs with hca
    · subst hca
      have hBL : Commute BL (BR * X' * Lr) :=
        ((commute_blockElt_blockElt (by omega)).mul_right
          ((commute_x_blockElt (by simp only; omega)).pow_left c').symm).mul_right
          (commute_chainL_blockElt (by omega)).symm
      rw [← mul_assoc, ← ((Commute.neg_one_left _).pow_left (a - 1)).eq, mul_assoc,
        ← mul_assoc _ BL, ← hBL.eq, mul_assoc]
      have h12' : (BR * X' * Lr * e (S a) : A) = BR * e (S a) := by
        rw [h12 (by omega), if_pos (by omega)]
      rw [h12', etop]
      simp only [mul_assoc]
      rfl
    · rw [mul_zero]

/-- **KL II, §3** (the display before Proposition 6):
`α^+_{a-1,b+1} α^-_{a,b} - α^-_{a+1,b-1} α^+_{a,b} = (-1)^{a-1} e_{i,a} ⊗ 1_j ⊗ e_{i,b}` (as elements
of `R(ν)`, times `1_{…i^a j i^b…}`), for `1 ≤ a ≤ d`, `a + b = d + 1`, `d = d_ij`, `i · j ≠ 0`. -/
theorem serre_A (hij : i ≠ j) (hd : C.dot i j ≠ 0) (hN : N = C.dij i j + 1) {a : ℕ}
    (ha1 : 1 ≤ a) (ha : a + 1 ≤ N) :
    (aplus t p N (a - 1) * aminus t p N a - aminus t p N (a + 1) * aplus t p N a : A) =
      (-1) ^ (a - 1) * etop t p N a := by
  rw [aplus_mul_aminus hpN ht₀ ht ha1 (by omega), aminus_mul_aplus hpN ht₀ ht ha]
  set d := C.dij i j with hd_def
  -- the words
  set Lr : A := chainL (p + a + 1) (N - a - 1)
  set Rl : A := chainR p (a - 1)
  have hw2 : (chainL (p + a - 1) (N - a + 1) * chainR p a : A) =
      ψ (p + a - 1) * ψ (p + a) * ψ (p + a - 1) * (Lr * Rl) := by
    have e1 : (chainL (p + a - 1) (N - a + 1) : A) = ψ (p + a - 1) * ψ (p + a) * Lr := by
      rw [chainL_succ, show p + a - 1 + 1 = p + a by omega,
        show N - a = (N - a - 1) + 1 by omega, chainL_succ, mul_assoc]
    have e2 : (chainR p a : A) = ψ (p + a - 1) * Rl := chainR_eq_ψ_mul ha1
    have hc : Commute (ψ (p + a - 1) : A) Lr := commute_ψ_chainL (by omega)
    rw [e1, e2, mul_assoc (ψ (p + a - 1) * ψ (p + a)) Lr, ← mul_assoc Lr, ← hc.eq]
    simp only [mul_assoc]
  have hw1 : (chainR p (a + 1) * chainL (p + a) (N - a) : A) =
      ψ (p + a) * ψ (p + a - 1) * ψ (p + a) * (Lr * Rl) := by
    have e1 : (chainR p (a + 1) : A) = ψ (p + a) * ψ (p + a - 1) * Rl := by
      rw [chainR_succ', chainR_eq_ψ_mul ha1, mul_assoc]
    have e2 : (chainL (p + a) (N - a) : A) = ψ (p + a) * Lr := by
      rw [show N - a = (N - a - 1) + 1 by omega, chainL_succ]
    have hc : Commute (ψ (p + a) : A) Rl := commute_ψ_chainR (by omega)
    have hLR : Commute Lr Rl := commute_chainL_chainR (by omega)
    rw [e1, e2, mul_assoc (ψ (p + a) * ψ (p + a - 1)) Rl, ← mul_assoc Rl, ← hc.eq, hLR.eq]
    simp only [mul_assoc]
  have hLRe : Commute (Lr * Rl) (e (S a)) :=
    (commute_chainL_right_e hpN ht₀ ht (by omega) (by omega) (by omega)).mul_left
      (commute_chainR_left_e hpN ht₀ ht (by omega) le_rfl (by omega))
  -- the braid relation `eq_r3_hard` on `…i j i…`
  have hbr := braid_hard (k := k) (C := C) (p + a - 1) (by omega) (S a)
    (by rw [serreSeq_lbl_eq_i hpN ht₀ ht (by omega) _ (by simp only; omega) (by simp only; omega)
          (by simp only; omega), serreSeq_lbl_eq_i hpN ht₀ ht (by omega) _ (by simp only; omega)
          (by simp only; omega) (by simp only; omega)])
    (by rw [serreSeq_lbl_eq_i hpN ht₀ ht (by omega) _ (by simp only; omega) (by simp only; omega)
          (by simp only; omega), serreSeq_lbl_eq_j hpN ht₀ ht (by omega) _ (by simp only; omega)]
        exact hij)
    (by rw [serreSeq_lbl_eq_i hpN ht₀ ht (by omega) _ (by simp only; omega) (by simp only; omega)
          (by simp only; omega), serreSeq_lbl_eq_j hpN ht₀ ht (by omega) _ (by simp only; omega)]
        exact hd)
  rw [serreSeq_lbl_eq_i hpN ht₀ ht (by omega) _ (by simp only; omega) (by simp only; omega)
    (by simp only; omega), serreSeq_lbl_eq_j hpN ht₀ ht (by omega) _ (by simp only; omega),
    show p + a - 1 + 1 = p + a by omega] at hbr
  simp only [show p + a - 1 + 2 = p + a + 1 by omega] at hbr
  set B : A := blockElt p a * blockElt (p + a + 1) (N - a)
  have hLRe' : (Lr * (Rl * e (S a)) : A) = e (S a) * (Lr * Rl) := by
    rw [← mul_assoc]; exact hLRe.eq
  have h1 : (B * chainL (p + a - 1) (N - a + 1) * chainR p a * e (S a) : A) =
      B * (ψ (p + a - 1) * ψ (p + a) * ψ (p + a - 1) * e (S a)) * (Lr * Rl) := by
    rw [mul_assoc B, hw2]
    simp only [mul_assoc]
    rw [hLRe']
  have h2 : (B * chainR p (a + 1) * chainL (p + a) (N - a) * e (S a) : A) =
      B * (ψ (p + a) * ψ (p + a - 1) * ψ (p + a) * e (S a)) * (Lr * Rl) := by
    rw [mul_assoc B, hw1]
    simp only [mul_assoc]
    rw [hLRe']
  rw [h1, h2, ← sub_mul, ← mul_sub, hbr, Finset.sum_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_eq_single (a - 1)]
  · rw [serre_A_term hpN ht₀ ht ha1 ha (c := a - 1) (c' := C.dij i j - 1 - (a - 1)) (by omega),
      if_pos rfl]
  · intro c hc hca
    rw [Finset.mem_range] at hc
    rw [serre_A_term hpN ht₀ ht ha1 ha (c := c) (c' := C.dij i j - 1 - c) (by omega), if_neg hca]
  · intro h; exact absurd (Finset.mem_range.2 (by omega)) h

/-- **KL II, §3**: `α^-_{1,d} α^+_{0,d+1} = 1_j ⊗ e_{i,d+1}` (for `i · j = 0`, `d = 0`, this is
`ψ² 1_{…ji…} = 1_{…ji…}`). -/
theorem serre_B (hij : i ≠ j) (hN : N = C.dij i j + 1) :
    (aminus t p N 1 * aplus t p N 0 : A) = etop t p N 0 := by
  have hN1 : 1 ≤ N := by omega
  set L' : A := chainL (p + 1) (N - 1)
  set BR1 : A := blockElt (p + 1) N
  set BR2 : A := blockElt (p + 2) (N - 1)
  have hm : (aminus t p N 1 : A) = BR1 * ψ p * e (S 1) := by
    rw [aminus, Nat.sub_self, blockElt_zero, one_mul, show N - 1 + 1 = N by omega, chainR_one]
  have hp : (aplus t p N 0 : A) = BR2 * (ψ p * L') * e (S 0) := by
    rw [aplus, zero_add, blockElt_one, one_mul, add_zero, Nat.sub_zero,
      chainL_eq_ψ_mul hN1, show p + 0 + 2 = p + 2 by omega]
  have hA : (ψ p * (L' * e (S 0)) : A) = e (S 1) * (ψ p * L') := by
    have := chainL_serre (k := k) (C := C) hpN ht₀ ht (a := 0) (l := N) hN1 (by omega)
    rwa [add_zero, chainL_eq_ψ_mul hN1, mul_assoc] at this
  have hBR1 : Commute BR2 (e (S 1)) :=
    commute_blockElt_right_e hpN ht₀ ht hN1 (by omega) (by omega)
  have hL' : Commute L' (e (S 0)) :=
    commute_chainL_right_e hpN ht₀ ht (by omega) (by omega) (by omega)
  have hψ1 := ψ_serre_L (k := k) (C := C) hpN ht₀ ht (a := 0) (by omega)
  have hψ2 := ψ_serre_R (k := k) (C := C) hpN ht₀ ht (a := 1) le_rfl hN1
  rw [add_zero] at hψ1
  rw [show p + 1 - 1 = p by omega, Nat.sub_self] at hψ2
  have hB : (ψ p * (ψ p * (L' * e (S 0))) : A) = e (S 0) * (ψ p * (ψ p * L')) := by
    rw [hL'.eq, ← mul_assoc (ψ p) (e (S 0)), hψ1, mul_assoc, ← mul_assoc (ψ p) (e (S 1)), hψ2]
    simp only [mul_assoc]
  have hc : Commute (ψ p : A) BR2 := commute_ψ_blockElt (by omega)
  -- KL II (10) on the block `[p + 1, p + N + 1)`
  have h10 := blockElt_mul_blockElt_right (k := k) (Q := klQ2 k C) (t := S 0) (q := p + 1)
    (n := N - 1) (by omega) (isConstOn_serreSeq_right hpN ht₀ ht (by omega) (by omega) (by omega))
  rw [show N - 1 + 1 = N by omega, show p + 1 + 1 = p + 2 by omega] at h10
  have step : (aminus t p N 1 * aplus t p N 0 : A) = BR1 * (ψ p * ψ p * e (S 0)) * L' := by
    calc (aminus t p N 1 * aplus t p N 0 : A)
        = BR1 * (ψ p * (e (S 1) * (BR2 * (ψ p * (L' * e (S 0)))))) := by
          rw [hm, hp]; simp only [mul_assoc]
      _ = BR1 * (ψ p * (BR2 * (ψ p * (L' * e (S 0))))) := by
          rw [hA, hBR1.left_comm, ← mul_assoc (e (S 1)) (e (S 1)), e_mul_self,
            ← hBR1.left_comm, ← hA]
      _ = BR1 * (BR2 * (e (S 0) * (ψ p * (ψ p * L')))) := by rw [hc.left_comm, hB]
      _ = BR1 * (e (S 0) * (ψ p * (ψ p * L'))) := by
          rw [← mul_assoc, ← mul_assoc, h10, mul_assoc]
      _ = BR1 * (ψ p * ψ p * e (S 0)) * L' := by
          rw [← hB]; simp only [mul_assoc]; rw [hL'.eq]
  rw [step]
  by_cases hd : C.dot i j = 0
  · -- `i · j = 0`: `N = 1` and `ψ² 1_{ji} = 1_{ji}`
    have hN' : N = 1 := by rw [hN, (C.dij_eq_zero_iff hij).2 hd]
    have hsq := ψ_sq_of_dot_eq_zero (k := k) (C := C) p (by omega) (S 0)
      (by rw [serreSeq_lbl_eq_j hpN ht₀ ht (by omega) _ (by simp),
        serreSeq_lbl_eq_i hpN ht₀ ht (by omega) _ (by simp) (by simp only; omega)
          (by simp only; omega)]; exact Ne.symm hij)
      (by rw [serreSeq_lbl_eq_j hpN ht₀ ht (by omega) _ (by simp),
        serreSeq_lbl_eq_i hpN ht₀ ht (by omega) _ (by simp) (by simp only; omega)
          (by simp only; omega), C.symm]; exact hd)
    rw [hsq, etop, blockElt_zero, one_mul, add_zero, Nat.sub_zero]
    simp only [L', BR1, hN', Nat.sub_self, chainL_zero, mul_one, zero_add]
  · -- `i · j ≠ 0`: `ψ² 1_{ji} = (x_p^{d_ji} + x_{p+1}^{d_ij}) 1_{ji}`
    have hsq := ψ_sq_of_dot_ne_zero (k := k) (C := C) p (by omega) (S 0)
      (by rw [serreSeq_lbl_eq_j hpN ht₀ ht (by omega) _ (by simp),
        serreSeq_lbl_eq_i hpN ht₀ ht (by omega) _ (by simp) (by simp only; omega)
          (by simp only; omega)]; exact Ne.symm hij)
      (by rw [serreSeq_lbl_eq_j hpN ht₀ ht (by omega) _ (by simp),
        serreSeq_lbl_eq_i hpN ht₀ ht (by omega) _ (by simp) (by simp only; omega)
          (by simp only; omega), C.symm]; exact hd)
    rw [serreSeq_lbl_eq_j hpN ht₀ ht (by omega) _ (by simp),
      serreSeq_lbl_eq_i hpN ht₀ ht (by omega) _ (by simp) (by simp only; omega)
        (by simp only; omega)] at hsq
    rw [hsq]
    have h12 := fun c (hc : c ≤ N - 1) => blockElt_mul_x_pow_mul_chainL' (k := k) (C := C)
      (s := S 0) (q := p + 1) (b := N) (c := c) (by omega) hN1
      (isConstOn_serreSeq_right hpN ht₀ ht (by omega) (by omega) (by omega)) hc
    have hx0 : Commute (x ⟨p, by omega⟩ : A) BR1 := commute_x_blockElt (by simp only; omega)
    have hx0' : Commute (x ⟨p, by omega⟩ : A) L' := commute_x_chainL (by simp only; omega)
    have hdpos := C.dij_pos hij hd
    have hz := h12 0 (by omega)
    rw [pow_zero, mul_one, if_neg (by omega)] at hz
    have hd1 := h12 (C.dij i j) (by omega)
    rw [if_pos (by omega)] at hd1
    have t1 : (BR1 * (x ⟨p, by omega⟩ ^ C.dij j i * e (S 0)) * L' : A) = 0 := by
      simp only [mul_assoc]
      rw [← hL'.eq, ← (hx0.pow_left _).left_comm]
      have : (BR1 * (L' * e (S 0)) : A) = 0 := by rw [← hz]; simp only [mul_assoc]; rfl
      rw [this, mul_zero]
    have t2 : (BR1 * (x ⟨p + 1, by omega⟩ ^ C.dij i j * e (S 0)) * L' : A) =
        BR1 * e (S 0) := by
      rw [← hd1]; simp only [mul_assoc]; rw [hL'.eq]
    rw [add_mul, mul_add, add_mul, t1, t2, zero_add, etop, blockElt_zero, one_mul, add_zero,
      Nat.sub_zero]

/-- **KL II, §3**: `α^+_{d,1} α^-_{d+1,0} = (-1)^d e_{i,d+1} ⊗ 1_j` (for `i · j = 0`, `d = 0`, this
is `ψ² 1_{…ij…} = 1_{…ij…}`). -/
theorem serre_C (hij : i ≠ j) (hN : N = C.dij i j + 1) :
    (aplus t p N (N - 1) * aminus t p N N : A) = (-1) ^ (N - 1) * etop t p N N := by
  have hN1 : 1 ≤ N := by omega
  set R' : A := chainR p (N - 1)
  set BLN : A := blockElt p N
  set BLm : A := blockElt p (N - 1)
  have hp : (aplus t p N (N - 1) : A) = BLN * ψ (p + N - 1) * e (S (N - 1)) := by
    rw [aplus, show N - 1 + 1 = N by omega, show N - (N - 1) - 1 = 0 by omega, blockElt_zero,
      mul_one, show N - (N - 1) = 1 by omega, chainL_one, show p + (N - 1) = p + N - 1 by omega]
  have hm : (aminus t p N N : A) = BLm * (ψ (p + N - 1) * R') * e (S N) := by
    rw [aminus, Nat.sub_self, zero_add, blockElt_one, mul_one, chainR_eq_ψ_mul hN1]
  have hRN : (ψ (p + N - 1) * (R' * e (S N)) : A) = e (S (N - 1)) * (ψ (p + N - 1) * R') := by
    have := chainR_serre (k := k) (C := C) hpN ht₀ ht (a := N) hN1 le_rfl
    rwa [chainR_eq_ψ_mul hN1, mul_assoc] at this
  have hBLm : Commute BLm (e (S (N - 1))) :=
    commute_blockElt_left_e hpN ht₀ ht (by omega) le_rfl (by omega)
  have hR' : Commute R' (e (S N)) := commute_chainR_left_e hpN ht₀ ht le_rfl le_rfl (by omega)
  have hψ1 := ψ_serre_L (k := k) (C := C) hpN ht₀ ht (a := N - 1) (by omega)
  have hψ2 := ψ_serre_R (k := k) (C := C) hpN ht₀ ht (a := N) hN1 le_rfl
  rw [show p + (N - 1) = p + N - 1 by omega, show N - 1 + 1 = N by omega] at hψ1
  have hB : (ψ (p + N - 1) * (ψ (p + N - 1) * (R' * e (S N))) : A) =
      e (S N) * (ψ (p + N - 1) * (ψ (p + N - 1) * R')) := by
    rw [hR'.eq, ← mul_assoc (ψ (p + N - 1)) (e (S N)), hψ2, mul_assoc,
      ← mul_assoc (ψ (p + N - 1)) (e (S (N - 1))), hψ1]
    simp only [mul_assoc]
  have hc : Commute (ψ (p + N - 1) : A) BLm := commute_ψ_blockElt (by omega)
  have h10 := blockElt_mul_blockElt_left (k := k) (Q := klQ2 k C) (t := S N) (q := p)
    (n := N - 1) (by omega) (isConstOn_serreSeq_left hpN ht₀ ht le_rfl le_rfl (by omega))
  rw [show N - 1 + 1 = N by omega] at h10
  have step : (aplus t p N (N - 1) * aminus t p N N : A) =
      BLN * (ψ (p + N - 1) * ψ (p + N - 1) * e (S N)) * R' := by
    calc (aplus t p N (N - 1) * aminus t p N N : A)
        = BLN * (ψ (p + N - 1) * (e (S (N - 1)) * (BLm * (ψ (p + N - 1) * (R' * e (S N)))))) := by
          rw [hp, hm]; simp only [mul_assoc]
      _ = BLN * (ψ (p + N - 1) * (BLm * (ψ (p + N - 1) * (R' * e (S N))))) := by
          rw [hRN, hBLm.left_comm, ← mul_assoc (e (S (N - 1))) (e (S (N - 1))), e_mul_self,
            ← hBLm.left_comm, ← hRN]
      _ = BLN * (BLm * (e (S N) * (ψ (p + N - 1) * (ψ (p + N - 1) * R')))) := by
          rw [hc.left_comm, hB]
      _ = BLN * (e (S N) * (ψ (p + N - 1) * (ψ (p + N - 1) * R'))) := by
          rw [← mul_assoc, ← mul_assoc, h10, mul_assoc]
      _ = BLN * (ψ (p + N - 1) * ψ (p + N - 1) * e (S N)) * R' := by
          rw [← hB]; simp only [mul_assoc]; rw [hR'.eq]
  rw [step]
  have hlbl1 : (S N).lbl ⟨p + N - 1, by omega⟩ = i :=
    serreSeq_lbl_eq_i hpN ht₀ ht le_rfl _ (by simp only; omega) (by simp only; omega)
      (by simp only; omega)
  have hlbl2 : (S N).lbl ⟨p + N - 1 + 1, by omega⟩ = j :=
    serreSeq_lbl_eq_j hpN ht₀ ht le_rfl _ (by simp only; omega)
  by_cases hd : C.dot i j = 0
  · have hN' : N = 1 := by rw [hN, (C.dij_eq_zero_iff hij).2 hd]
    have hsq := ψ_sq_of_dot_eq_zero (k := k) (C := C) (p + N - 1) (by omega) (S N)
      (by rw [hlbl1, hlbl2]; exact hij) (by rw [hlbl1, hlbl2]; exact hd)
    rw [hsq, etop]
    simp only [BLN, R', hN', Nat.sub_self, chainR_zero, mul_one, blockElt_one, blockElt_zero,
      one_mul, pow_zero]
  · have hsq := ψ_sq_of_dot_ne_zero (k := k) (C := C) (p + N - 1) (by omega) (S N)
      (by rw [hlbl1, hlbl2]; exact hij) (by rw [hlbl1, hlbl2]; exact hd)
    rw [hlbl1, hlbl2] at hsq
    rw [hsq]
    have hdpos := C.dij_pos hij hd
    have h13 := fun c (hc : c ≤ N - 1) => blockElt_mul_x_pow_mul_chainR' (k := k) (C := C)
      (s := S N) (q := p) (a := N) (c := c) (by omega) hN1
      (isConstOn_serreSeq_left hpN ht₀ ht le_rfl le_rfl (by omega)) hc
    have hz := h13 0 (by omega)
    rw [pow_zero, mul_one, if_neg (by omega)] at hz
    have hd1 := h13 (C.dij i j) (by omega)
    rw [if_pos (by omega)] at hd1
    have hxN : Commute (x ⟨p + N - 1 + 1, by omega⟩ : A) BLN :=
      commute_x_blockElt (by simp only; omega)
    have hxR : Commute (x ⟨p + N - 1 + 1, by omega⟩ : A) R' :=
      commute_x_chainR (by simp only; omega)
    have t1 : (BLN * (x ⟨p + N - 1, by omega⟩ ^ C.dij i j * e (S N)) * R' : A) =
        (-1) ^ (N - 1) * (BLN * e (S N)) := by
      rw [← hd1]; simp only [mul_assoc]; rw [hR'.eq]
    have t2 : (BLN * (x ⟨p + N - 1 + 1, by omega⟩ ^ C.dij j i * e (S N)) * R' : A) = 0 := by
      simp only [mul_assoc]
      rw [← hR'.eq, ← (hxN.pow_left _).left_comm]
      have : (BLN * (R' * e (S N)) : A) = 0 := by rw [← hz]; simp only [mul_assoc]; rfl
      rw [this, mul_zero]
    rw [add_mul, mul_add, add_mul, t1, t2, add_zero, etop, show N - N = 0 by omega,
      blockElt_zero, mul_one]

/-- `α^+_{a+1,b-1} α^+_{a,b} = 0`: two strands `i` crossing the `j` from the right end up in the
same box `e_{i,a+2}` after crossing each other. -/
theorem serre_Dplus (hij : i ≠ j) {a : ℕ} (ha : a + 2 ≤ N) :
    (aplus t p N (a + 1) * aplus t p N a : A) = 0 := by
  set L0 : A := chainL (p + a) (N - a)
  set L1 : A := chainL (p + a + 1) (N - a - 1)
  set L2 : A := chainL (p + a + 2) (N - a - 2)
  set L3 : A := chainL (p + a + 1) (N - a - 2)
  set BLb : A := blockElt p (a + 2)
  set BLs : A := blockElt p (a + 1)
  set BRt : A := blockElt (p + a + 3) (N - a - 2)
  set BR : A := blockElt (p + a + 2) (N - a - 1)
  have hp1 : (aplus t p N (a + 1) : A) = BLb * BRt * L1 * e (S (a + 1)) := by
    rw [aplus, show p + (a + 1) + 2 = p + a + 3 by omega, show N - (a + 1) - 1 = N - a - 2 by omega,
      show p + (a + 1) = p + a + 1 by omega, show N - (a + 1) = N - a - 1 by omega]
  have hp0 : (aplus t p N a : A) = BLs * BR * L0 * e (S a) := rfl
  have hL0 : (L0 * e (S a) : A) = e (S (a + 1)) * L0 :=
    chainL_serre hpN ht₀ ht (by omega) (by omega)
  have hL1 : (L1 * e (S (a + 1)) : A) = e (S (a + 2)) * L1 := by
    have := chainL_serre (k := k) (C := C) hpN ht₀ ht (a := a + 1) (l := N - a - 1) (by omega)
      (by omega)
    rwa [show p + (a + 1) = p + a + 1 by omega] at this
  have hBR : Commute BR (e (S (a + 1))) :=
    commute_blockElt_right_e hpN ht₀ ht (by omega) (by omega) (by omega)
  have hBLs : Commute BLs (e (S (a + 1))) :=
    commute_blockElt_left_e hpN ht₀ ht (by omega) le_rfl (by omega)
  have hBRt : Commute BRt (e (S (a + 2))) :=
    commute_blockElt_right_e hpN ht₀ ht (by omega) (by omega) (by omega)
  have hc1 : Commute L1 BLs := commute_chainL_blockElt (by omega)
  have hc2 : Commute BRt BLs := commute_blockElt_blockElt (by omega)
  have hψt : Commute (ψ (p + a + 1) : A) BRt := commute_ψ_blockElt (by omega)
  have hψt' : Commute (ψ (p + a) : A) BRt := commute_ψ_blockElt (by omega)
  have hL1ψ : L1 = ψ (p + a + 1) * L2 := by
    simp only [L1, L2]
    rw [chainL_eq_ψ_mul (by omega), show p + a + 1 + 1 = p + a + 2 by omega,
      show N - a - 1 - 1 = N - a - 2 by omega]
  have hL0ψ : L0 = ψ (p + a) * L1 := by
    simp only [L0, L1]
    rw [chainL_eq_ψ_mul (by omega), show N - a - 1 = N - a - 1 by rfl]
  have h10 := blockElt_mul_blockElt_left (k := k) (Q := klQ2 k C) (t := S (a + 2)) (q := p)
    (n := a + 1) (by omega) (isConstOn_serreSeq_left hpN ht₀ ht (by omega) le_rfl (by omega))
  rw [show a + 1 + 1 = a + 2 by omega] at h10
  have h11 := blockElt_mul_chainL_mul_blockElt (k := k) (Q := klQ2 k C) (t := S (a + 1))
    (q := p + a + 2) (n := N - a - 2) (by omega)
    (isConstOn_serreSeq_right hpN ht₀ ht (by omega) (by omega) (by omega))
  rw [show p + a + 2 + 1 = p + a + 3 by omega, show N - a - 2 + 1 = N - a - 1 by omega] at h11
  -- the transported relation `L(q, q + l + 1) L(q, q + l) = L(q + 1, q + l + 1) L(q, q + l + 1)`
  have hC := chainL_mul_chainL_mul_e (k := k) (Q := klQ2 k C) (t := S a) (q := p + a + 1)
    (l := N - a - 2) (by omega)
    (isConstOn_serreSeq_right hpN ht₀ ht (by omega) (by omega) (by omega))
  rw [show N - a - 2 + 1 = N - a - 1 by omega, show p + a + 1 + 1 = p + a + 2 by omega] at hC
  have hY : Commute (L2 * L3) (e (S a)) :=
    (commute_chainL_right_e hpN ht₀ ht (by omega) (by omega) (by omega)).mul_left
      (commute_chainL_right_e hpN ht₀ ht (by omega) (by omega) (by omega))
  have hbr := braid_easy (k := k) (C := C) (p + a) (by omega) (S a) (by
    rw [serreSeq_lbl_eq_j hpN ht₀ ht (by omega) _ (by simp only),
      serreSeq_lbl_eq_i hpN ht₀ ht (by omega) _ (by simp only; omega) (by simp only; omega)
        (by simp only; omega)]
    exact fun h => hij h.1.symm)
  have hψ1 := ψ_serre_L (k := k) (C := C) hpN ht₀ ht (a := a) (by omega)
  have hψ2 := ψ_serre_L (k := k) (C := C) hpN ht₀ ht (a := a + 1) (by omega)
  rw [show p + (a + 1) = p + a + 1 by omega, show a + 1 + 1 = a + 2 by omega] at hψ2
  have hz := blockElt_mul_ψ_mul_e (k := k) (Q := klQ2 k C) (t := S (a + 2)) (q := p) (n := a + 2)
    (by omega) (isConstOn_serreSeq_left hpN ht₀ ht (by omega) le_rfl (by omega)) (j := p + a)
    (by omega) (by omega)
  -- the words: `L1 L0 = ψ ψ ψ L2 L3` after the relations
  have hW : (L1 * (L0 * e (S a)) : A) =
      ψ (p + a) * (ψ (p + a + 1) * (ψ (p + a) * (e (S a) * (L2 * L3)))) := by
    have hc : Commute (ψ (p + a) : A) L2 := commute_ψ_chainL (by omega)
    have e1 : (L1 * (L0 * e (S a)) : A) = ψ (p + a + 1) * (ψ (p + a) * (L2 * (L1 * e (S a)))) := by
      rw [hL0ψ]; nth_rewrite 1 [hL1ψ]; simp only [mul_assoc]; rw [← hc.left_comm]
    have e2 : (L2 * (L1 * e (S a)) : A) = L1 * (L3 * e (S a)) := by
      rw [← mul_assoc, ← mul_assoc, ← hC]
    have e3 : (L1 * (L3 * e (S a)) : A) = ψ (p + a + 1) * (e (S a) * (L2 * L3)) := by
      rw [hL1ψ, mul_assoc, ← mul_assoc L2, hY.eq]
    have hbr' : (ψ (p + a + 1) * (ψ (p + a) * (ψ (p + a + 1) * (e (S a) * (L2 * L3)))) : A) =
        ψ (p + a) * (ψ (p + a + 1) * (ψ (p + a) * (e (S a) * (L2 * L3)))) := by
      have := congrArg (· * (L2 * L3)) hbr
      simp only [mul_assoc] at this
      exact this.symm
    rw [e1, e2, e3, hbr']
  calc (aplus t p N (a + 1) * aplus t p N a : A)
      = BLb * (BRt * (L1 * (e (S (a + 1)) * (BLs * (BR * (L0 * e (S a))))))) := by
        rw [hp1, hp0]; simp only [mul_assoc]
    _ = BLb * (BLs * (BRt * (L1 * (BR * (L0 * e (S a)))))) := by
        rw [hL0, hBR.left_comm, hBLs.left_comm, ← mul_assoc (e (S (a + 1))) (e (S (a + 1))),
          e_mul_self, ← hBLs.left_comm, ← hBR.left_comm, ← hL0, hc1.left_comm, hc2.left_comm]
    _ = BLb * (BRt * (L1 * (BR * (L0 * e (S a))))) := by
        have hmv : (BRt * (L1 * (BR * (L0 * e (S a)))) : A) =
            e (S (a + 2)) * (BRt * (L1 * (BR * L0))) := by
          rw [hL0, hBR.left_comm, ← mul_assoc L1, hL1, mul_assoc, hBRt.left_comm]
        rw [hmv, ← mul_assoc, ← mul_assoc, h10, mul_assoc]
    _ = BLb * (BRt * (L1 * (L0 * e (S a)))) := by
        rw [hL1ψ]
        simp only [mul_assoc]
        rw [← hψt.left_comm, hL0]
        have : (BRt * (L2 * (BR * (e (S (a + 1)) * L0))) : A) =
            BRt * (L2 * (e (S (a + 1)) * L0)) := by
          rw [show (BRt * (L2 * (BR * (e (S (a + 1)) * L0))) : A) =
            BRt * L2 * BR * e (S (a + 1)) * L0 by simp only [mul_assoc], h11]
          simp only [mul_assoc]; rfl
        rw [this, hψt.left_comm]
    _ = 0 := by
        rw [hW, ← hψt'.left_comm]
        rw [← mul_assoc (ψ (p + a)) (e (S a)), hψ1, mul_assoc, ← mul_assoc (ψ (p + a + 1)),
          hψ2, mul_assoc, hBRt.left_comm, ← mul_assoc, ← mul_assoc, hz, zero_mul]

/-- `α^-_{a-1,b+1} α^-_{a,b} = 0`: two strands `i` crossing the `j` from the left end up in the
same box `e_{i,b+2}` after crossing each other. -/
theorem serre_Dminus (hij : i ≠ j) {a : ℕ} (ha2 : 2 ≤ a) (ha : a ≤ N) :
    (aminus t p N (a - 1) * aminus t p N a : A) = 0 := by
  set Ra : A := chainR p a
  set Ra1 : A := chainR p (a - 1)
  set Rp2 : A := chainR p (a - 2)
  set Rq : A := chainR (p + 1) (a - 2)
  set BLss : A := blockElt p (a - 2)
  set BLs : A := blockElt p (a - 1)
  set BRb : A := blockElt (p + a - 1) (N - a + 2)
  set BRc : A := blockElt (p + a) (N - a + 1)
  have hm1 : (aminus t p N (a - 1) : A) = BLss * BRb * Ra1 * e (S (a - 1)) := by
    rw [aminus, show a - 1 - 1 = a - 2 by omega, show p + (a - 1) = p + a - 1 by omega,
      show N - (a - 1) + 1 = N - a + 2 by omega]
  have hm0 : (aminus t p N a : A) = BLs * BRc * Ra * e (S a) := rfl
  have hRa : (Ra * e (S a) : A) = e (S (a - 1)) * Ra :=
    chainR_serre hpN ht₀ ht (by omega) ha
  have hRa1 : (Ra1 * e (S (a - 1)) : A) = e (S (a - 2)) * Ra1 := by
    have := chainR_serre (k := k) (C := C) hpN ht₀ ht (a := a - 1) (by omega) (by omega)
    rwa [show a - 1 - 1 = a - 2 by omega] at this
  have hBLs : Commute BLs (e (S (a - 1))) :=
    commute_blockElt_left_e hpN ht₀ ht (by omega) le_rfl (by omega)
  have hBRc : Commute BRc (e (S (a - 1))) :=
    commute_blockElt_right_e hpN ht₀ ht (by omega) (by omega) (by omega)
  have hBRb : Commute BRb (e (S (a - 2))) :=
    commute_blockElt_right_e hpN ht₀ ht (by omega) (by omega) (by omega)
  have hc1 : Commute BLs BRc := commute_blockElt_blockElt (by omega)
  have hc2 : Commute Ra1 BRc := commute_chainR_blockElt (by omega)
  have hc3 : Commute BLss BRb := commute_blockElt_blockElt (by omega)
  have hc4 : Commute BLss (ψ (p + a - 2)) := (commute_ψ_blockElt (by omega)).symm
  have hRa1ψ : Ra1 = ψ (p + a - 2) * Rp2 := by
    simp only [Ra1, Rp2]
    rw [chainR_eq_ψ_mul (by omega), show p + (a - 1) - 1 = p + a - 2 by omega,
      show a - 1 - 1 = a - 2 by omega]
  have hRaψ : Ra = ψ (p + a - 1) * Ra1 := by
    simp only [Ra, Ra1]
    rw [chainR_eq_ψ_mul (by omega)]
  have h10 := blockElt_mul_blockElt_right (k := k) (Q := klQ2 k C) (t := S (a - 2))
    (q := p + a - 1) (n := N - a + 1) (by omega)
    (isConstOn_serreSeq_right hpN ht₀ ht (by omega) (by omega) (by omega))
  rw [show N - a + 1 + 1 = N - a + 2 by omega, show p + a - 1 + 1 = p + a by omega] at h10
  have h11 := blockElt_mul_chainR_mul_blockElt (k := k) (Q := klQ2 k C) (t := S (a - 1))
    (q := p) (n := a - 2) (by omega)
    (isConstOn_serreSeq_left hpN ht₀ ht (by omega) le_rfl (by omega))
  rw [show a - 2 + 1 = a - 1 by omega] at h11
  have hC := chainR_mul_chainR_mul_e (k := k) (Q := klQ2 k C) (t := S a) (q := p) (l := a - 2)
    (by omega) (isConstOn_serreSeq_left hpN ht₀ ht (by omega) le_rfl (by omega))
  rw [show a - 2 + 1 = a - 1 by omega] at hC
  have hY : Commute (Rp2 * Rq) (e (S a)) :=
    (commute_chainR_left_e hpN ht₀ ht (by omega) le_rfl (by omega)).mul_left
      (commute_chainR_left_e hpN ht₀ ht (by omega) (by omega) (by omega))
  have hbr := braid_easy (k := k) (C := C) (p + a - 2) (by omega) (S a) (by
    rw [serreSeq_lbl_eq_i hpN ht₀ ht (by omega) _ (by simp only; omega) (by simp only; omega)
        (by simp only; omega), serreSeq_lbl_eq_j hpN ht₀ ht (by omega) _ (by simp only; omega)]
    exact fun h => hij h.1)
  rw [show p + a - 2 + 1 = p + a - 1 by omega] at hbr
  have hψ1 := ψ_serre_R (k := k) (C := C) hpN ht₀ ht (a := a) (by omega) ha
  have hψ2 := ψ_serre_R (k := k) (C := C) hpN ht₀ ht (a := a - 1) (by omega) (by omega)
  rw [show p + (a - 1) - 1 = p + a - 2 by omega, show a - 1 - 1 = a - 2 by omega] at hψ2
  have hz := blockElt_mul_ψ_mul_e (k := k) (Q := klQ2 k C) (t := S (a - 2)) (q := p + a - 1)
    (n := N - a + 2) (by omega)
    (isConstOn_serreSeq_right hpN ht₀ ht (by omega) (by omega) (by omega)) (j := p + a - 1)
    le_rfl (by omega)
  -- the words
  have hW : (Ra1 * (Ra * e (S a)) : A) =
      ψ (p + a - 1) * (ψ (p + a - 2) * (ψ (p + a - 1) * (e (S a) * (Rp2 * Rq)))) := by
    have hc : Commute (ψ (p + a - 1) : A) Rp2 := commute_ψ_chainR (by omega)
    have e1 : (Ra1 * (Ra * e (S a)) : A) =
        ψ (p + a - 2) * (ψ (p + a - 1) * (Rp2 * (Ra1 * e (S a)))) := by
      rw [hRaψ]; nth_rewrite 1 [hRa1ψ]; simp only [mul_assoc]; rw [← hc.left_comm]
    have e2 : (Rp2 * (Ra1 * e (S a)) : A) = Ra1 * (Rq * e (S a)) := by
      rw [← mul_assoc, ← mul_assoc, hC]
    have e3 : (Ra1 * (Rq * e (S a)) : A) = ψ (p + a - 2) * (e (S a) * (Rp2 * Rq)) := by
      rw [hRa1ψ, mul_assoc, ← mul_assoc Rp2, hY.eq]
    have hbr' : (ψ (p + a - 2) * (ψ (p + a - 1) * (ψ (p + a - 2) * (e (S a) * (Rp2 * Rq)))) :
        A) = ψ (p + a - 1) * (ψ (p + a - 2) * (ψ (p + a - 1) * (e (S a) * (Rp2 * Rq)))) := by
      have := congrArg (· * (Rp2 * Rq)) hbr
      simp only [mul_assoc] at this
      exact this
    rw [e1, e2, e3, hbr']
  calc (aminus t p N (a - 1) * aminus t p N a : A)
      = BLss * (BRb * (Ra1 * (e (S (a - 1)) * (BLs * (BRc * (Ra * e (S a))))))) := by
        rw [hm1, hm0]; simp only [mul_assoc]
    _ = BLss * (BRb * (BRc * (Ra1 * (BLs * (Ra * e (S a)))))) := by
        rw [hRa, hBRc.left_comm, hBLs.left_comm, ← mul_assoc (e (S (a - 1))) (e (S (a - 1))),
          e_mul_self, ← hBLs.left_comm, ← hBRc.left_comm, ← hRa, hc1.left_comm, hc2.left_comm]
    _ = BLss * (BRb * (Ra1 * (BLs * (Ra * e (S a))))) := by
        have hmv : (Ra1 * (BLs * (Ra * e (S a))) : A) = e (S (a - 2)) * (Ra1 * (BLs * Ra)) := by
          rw [hRa, hBLs.left_comm, ← mul_assoc Ra1, hRa1, mul_assoc]
        rw [hmv, ← mul_assoc BRb, ← mul_assoc BRb, ← mul_assoc (BRb * BRc), h10]
    _ = BLss * (BRb * (Ra1 * (Ra * e (S a)))) := by
        rw [hRa1ψ]
        simp only [mul_assoc]
        rw [hc3.left_comm, hc4.left_comm, hRa]
        have : (BLss * (Rp2 * (BLs * (e (S (a - 1)) * Ra))) : A) =
            BLss * (Rp2 * (e (S (a - 1)) * Ra)) := by
          rw [show (BLss * (Rp2 * (BLs * (e (S (a - 1)) * Ra))) : A) =
            BLss * Rp2 * BLs * e (S (a - 1)) * Ra by simp only [mul_assoc], h11]
          simp only [mul_assoc]; rfl
        rw [this, ← hc4.left_comm, ← hc3.left_comm]
    _ = 0 := by
        rw [hW, ← mul_assoc (ψ (p + a - 1)) (e (S a)), hψ1, mul_assoc,
          ← mul_assoc (ψ (p + a - 2)) (e (S (a - 1))), hψ2, mul_assoc, ← mul_assoc BRb,
          ← mul_assoc (BRb * ψ (p + a - 1)) (e (S (a - 2))), hz, zero_mul, mul_zero]

end maps

end Categorification.KLR.KL2
