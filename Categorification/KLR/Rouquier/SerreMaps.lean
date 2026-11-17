/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.KL2.SerreMaps

/-!
# Serre crossing maps for general KLR polynomials

R. Rouquier, *2-Kac–Moody algebras*, arXiv:0812.5023v1, §4.1.1, Proposition 4.2,
uses divided-power crossing maps and a contracting homotopy to establish the Serre relation.
This module supplies the polynomial-independent crossing identities for that proof, adapting
M. Khovanov and A. Lauda, *A diagrammatic approach to categorification of quantum groups II*,
arXiv:0804.2080v1, §3, equations (17)–(26). The nilHecke block identities hold over every
commutative ring and for arbitrary KLR polynomials. In particular, the two consecutive maps
in either direction compose to zero. The monomial evaluation below allows a total degree
bound, as needed to remove the lower terms in Rouquier's parameters.
-/

namespace Categorification.KLR.Rouquier

open Equiv MvPolynomial KLRAlgebra TypeA QuantumGroup KL2

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]

private theorem braid_easy {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I}
    (j : ℕ) (h : j + 2 < Multiset.card ν) (s : Seq ν)
    (hs : ¬ (s.lbl ⟨j, by omega⟩ = s.lbl ⟨j + 2, h⟩ ∧
      s.lbl ⟨j, by omega⟩ ≠ s.lbl ⟨j + 1, by omega⟩)) :
    (ψ j * ψ (j + 1) * ψ j * e s : KLRAlgebra k Q ν) =
      ψ (j + 1) * ψ j * ψ (j + 1) * e s := by
  rw [← sub_eq_zero, ← sub_mul, KLRAlgebra.braid j h s, ite_eq_right hs]

variable {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I}

local notation "m" => Multiset.card ν
local notation "A" => KLRAlgebra k Q ν

section helpers

/-- KL II (13) in the form used for `α^±`: the block `[p, p + a)`. -/
theorem blockElt_mul_x_pow_mul_chainR' {s : Seq ν} {q a c : ℕ} (h : q + a ≤ m) (ha1 : 1 ≤ a)
    (hc : IsConstOn s q a) (hca : c ≤ a - 1) :
    (blockElt q a * x ⟨q + a - 1, by omega⟩ ^ c * chainR q (a - 1) * e s : A) =
      if c = a - 1 then (-1) ^ (a - 1) * (blockElt q a * e s) else 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, a = n + 1 := ⟨a - 1, by omega⟩
  have := blockElt_mul_x_pow_mul_chainR (k := k) (Q := Q) (t := s) (q := q) (n := n)
    (a := c) h hc (by omega)
  simp only [Nat.add_sub_cancel] at hca ⊢
  convert this using 5
  congr 2

/-- KL II (12) in the form used for `α^±`: the block `[q, q + b)`. -/
theorem blockElt_mul_x_pow_mul_chainL' {s : Seq ν} {q b c : ℕ} (h : q + b ≤ m) (hb1 : 1 ≤ b)
    (hc : IsConstOn s q b) (hcb : c ≤ b - 1) :
    (blockElt q b * x ⟨q, by omega⟩ ^ c * chainL q (b - 1) * e s : A) =
      if c = b - 1 then blockElt q b * e s else 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
  exact blockElt_mul_x_pow_mul_chainL (k := k) (Q := Q) (t := s) (q := q) (n := n)
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
  have := chainR_mul_serre (k := k) (Q := Q) hpN ht₀ ht (a := a) (l := a) ha1 le_rfl ha
  rwa [show p + a - a = p by omega] at this

theorem ψ_serre_L {a : ℕ} (ha : a + 1 ≤ N) :
    (ψ (p + a) * e (S a) : A) = e (S (a + 1)) * ψ (p + a) := by
  have := chainL_serre (k := k) (Q := Q) hpN ht₀ ht (a := a) (l := 1) le_rfl ha
  rwa [chainL_one] at this

theorem ψ_serre_R {a : ℕ} (ha1 : 1 ≤ a) (ha : a ≤ N) :
    (ψ (p + a - 1) * e (S a) : A) = e (S (a - 1)) * ψ (p + a - 1) := by
  have := chainR_mul_serre (k := k) (Q := Q) hpN ht₀ ht (a := a) (l := 1) le_rfl ha1 ha
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
  rw [aplus, etop, mul_assoc _ (chainL _ _), chainL_serre (k := k) (Q := Q) hpN ht₀ ht (by omega) (by omega),
    show p + (a + 1) + 1 = p + a + 2 by omega, show N - (a + 1) = N - a - 1 by omega]
  simp only [mul_assoc]

/-- `α^-_{a,b} = e_{top} ψ_{p+a-1} ⋯ ψ_p`. -/
theorem aminus_eq {a : ℕ} (ha1 : 1 ≤ a) (ha : a ≤ N) :
    (aminus t p N a : A) = etop t p N (a - 1) * chainR p a := by
  rw [aminus, etop, mul_assoc _ (chainR _ _), chainR_serre (k := k) (Q := Q) hpN ht₀ ht ha1 ha,
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
    have := chainR_serre (k := k) (Q := Q) hpN ht₀ ht (a := a + 1) (by omega) ha
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
    have h10 := blockElt_mul_blockElt_right (k := k) (Q := Q) (t := S a)
      (q := p + a + 1) (n := N - a - 1) (by omega)
      (isConstOn_serreSeq_right hpN ht₀ ht (a := a) (by omega) (by omega) (by omega))
    rw [show N - a - 1 + 1 = N - a by omega, show p + a + 1 + 1 = p + a + 2 by omega] at h10
    rw [hW, ← mul_assoc, ← mul_assoc, h10, mul_assoc]
  -- KL II (11) on the left block
  have hK3 : (blockElt p a * (chainR p a * (blockElt p (a + 1) * (chainL (p + a) (N - a) *
      e (S a)))) : A) = blockElt p a * (chainR p a * (chainL (p + a) (N - a) * e (S a))) := by
    have h11 := blockElt_mul_chainR_mul_blockElt (k := k) (Q := Q) (t := S (a + 1))
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
    have := chainL_serre (k := k) (Q := Q) hpN ht₀ ht (a := a - 1) (l := N - a + 1) (by omega)
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
    have h10 := blockElt_mul_blockElt_left (k := k) (Q := Q) (t := S a)
      (q := p) (n := a - 1) (by omega)
      (isConstOn_serreSeq_left hpN ht₀ ht ha le_rfl (by omega))
    rw [show a - 1 + 1 = a by omega] at h10
    rw [hW, ← mul_assoc, ← mul_assoc, h10, mul_assoc]
  -- KL II (11) on the right block
  have hK3 : (blockElt (p + a + 1) (N - a) * (chainL (p + a) (N - a) *
      (blockElt (p + a) (N - a + 1) * (chainR p a * e (S a)))) : A) =
      blockElt (p + a + 1) (N - a) * (chainL (p + a) (N - a) * (chainR p a * e (S a))) := by
    have h11 := blockElt_mul_chainL_mul_blockElt (k := k) (Q := Q) (t := S (a - 1))
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
theorem serre_A_term {a c c' : ℕ} (ha1 : 1 ≤ a) (ha : a + 1 ≤ N) (hcc : c + c' ≤ N - 2) :
    (blockElt p a * blockElt (p + a + 1) (N - a) *
        (x ⟨p + a - 1, by omega⟩ ^ c * x ⟨p + a + 1, by omega⟩ ^ c' * e (S a)) *
        (chainL (p + a + 1) (N - a - 1) * chainR p (a - 1)) : A) =
      if c = a - 1 ∧ c' = N - a - 1 then (-1) ^ (a - 1) * etop t p N a else 0 := by
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
    blockElt_mul_x_pow_mul_chainL' (k := k) (Q := Q) (s := S a) (q := p + a + 1)
      (b := N - a) (c := c') (by omega) (by omega)
      (isConstOn_serreSeq_right hpN ht₀ ht (by omega) (by omega) (by omega)) (by omega)
  rcases Nat.lt_or_ge (a - 1) c with hlt | hge
  · -- `c > a - 1`: the right group vanishes by (12)
    rw [ite_eq_right (by omega)]
    rw [h12 (by omega), ite_eq_right (by omega), mul_zero]
  · -- `c ≤ a - 1`: evaluate the left group by (13)
    have h13 := blockElt_mul_x_pow_mul_chainR' (k := k) (Q := Q) (s := S a) (q := p) (a := a)
      (c := c) (by omega) ha1 (isConstOn_serreSeq_left hpN ht₀ ht (by omega) le_rfl le_rfl) hge
    rw [← mul_assoc, hG.eq, mul_assoc]
    have h13' : (BL * X * Rl * e (S a) : A) =
        if c = a - 1 then (-1) ^ (a - 1) * (BL * e (S a)) else 0 := h13
    rw [h13']
    by_cases hca : c = a - 1
    · rw [ite_eq_left hca]
      simp only [hca, true_and]
      have hBL : Commute BL (BR * X' * Lr) :=
        ((commute_blockElt_blockElt (by omega)).mul_right
          ((commute_x_blockElt (by simp only; omega)).pow_left c').symm).mul_right
          (commute_chainL_blockElt (by omega)).symm
      rw [← mul_assoc, ← ((Commute.neg_one_left _).pow_left (a - 1)).eq, mul_assoc,
        ← mul_assoc _ BL, ← hBL.eq, mul_assoc, h12 (by omega)]
      split_ifs with hc'
      · rw [etop]
        simp only [mul_assoc]
        rfl
      · rw [mul_zero, mul_zero]
    · rw [ite_eq_right hca, mul_zero, ite_eq_right (by simp [hca])]

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
    have := chainL_serre (k := k) (Q := Q) hpN ht₀ ht (a := a + 1) (l := N - a - 1) (by omega)
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
  have h10 := blockElt_mul_blockElt_left (k := k) (Q := Q) (t := S (a + 2)) (q := p)
    (n := a + 1) (by omega) (isConstOn_serreSeq_left hpN ht₀ ht (by omega) le_rfl (by omega))
  rw [show a + 1 + 1 = a + 2 by omega] at h10
  have h11 := blockElt_mul_chainL_mul_blockElt (k := k) (Q := Q) (t := S (a + 1))
    (q := p + a + 2) (n := N - a - 2) (by omega)
    (isConstOn_serreSeq_right hpN ht₀ ht (by omega) (by omega) (by omega))
  rw [show p + a + 2 + 1 = p + a + 3 by omega, show N - a - 2 + 1 = N - a - 1 by omega] at h11
  -- the transported relation `L(q, q + l + 1) L(q, q + l) = L(q + 1, q + l + 1) L(q, q + l + 1)`
  have hC := chainL_mul_chainL_mul_e (k := k) (Q := Q) (t := S a) (q := p + a + 1)
    (l := N - a - 2) (by omega)
    (isConstOn_serreSeq_right hpN ht₀ ht (by omega) (by omega) (by omega))
  rw [show N - a - 2 + 1 = N - a - 1 by omega, show p + a + 1 + 1 = p + a + 2 by omega] at hC
  have hY : Commute (L2 * L3) (e (S a)) :=
    (commute_chainL_right_e hpN ht₀ ht (by omega) (by omega) (by omega)).mul_left
      (commute_chainL_right_e hpN ht₀ ht (by omega) (by omega) (by omega))
  have hbr := braid_easy (k := k) (Q := Q) (p + a) (by omega) (S a) (by
    rw [serreSeq_lbl_eq_j hpN ht₀ ht (by omega) _ (by simp only),
      serreSeq_lbl_eq_i hpN ht₀ ht (by omega) _ (by simp only; omega) (by simp only; omega)
        (by simp only; omega)]
    exact fun h => hij h.1.symm)
  have hψ1 := ψ_serre_L (k := k) (Q := Q) hpN ht₀ ht (a := a) (by omega)
  have hψ2 := ψ_serre_L (k := k) (Q := Q) hpN ht₀ ht (a := a + 1) (by omega)
  rw [show p + (a + 1) = p + a + 1 by omega, show a + 1 + 1 = a + 2 by omega] at hψ2
  have hz := blockElt_mul_ψ_mul_e (k := k) (Q := Q) (t := S (a + 2)) (q := p) (n := a + 2)
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
    have := chainR_serre (k := k) (Q := Q) hpN ht₀ ht (a := a - 1) (by omega) (by omega)
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
  have h10 := blockElt_mul_blockElt_right (k := k) (Q := Q) (t := S (a - 2))
    (q := p + a - 1) (n := N - a + 1) (by omega)
    (isConstOn_serreSeq_right hpN ht₀ ht (by omega) (by omega) (by omega))
  rw [show N - a + 1 + 1 = N - a + 2 by omega, show p + a - 1 + 1 = p + a by omega] at h10
  have h11 := blockElt_mul_chainR_mul_blockElt (k := k) (Q := Q) (t := S (a - 1))
    (q := p) (n := a - 2) (by omega)
    (isConstOn_serreSeq_left hpN ht₀ ht (by omega) le_rfl (by omega))
  rw [show a - 2 + 1 = a - 1 by omega] at h11
  have hC := chainR_mul_chainR_mul_e (k := k) (Q := Q) (t := S a) (q := p) (l := a - 2)
    (by omega) (isConstOn_serreSeq_left hpN ht₀ ht (by omega) le_rfl (by omega))
  rw [show a - 2 + 1 = a - 1 by omega] at hC
  have hY : Commute (Rp2 * Rq) (e (S a)) :=
    (commute_chainR_left_e hpN ht₀ ht (by omega) le_rfl (by omega)).mul_left
      (commute_chainR_left_e hpN ht₀ ht (by omega) (by omega) (by omega))
  have hbr := braid_easy (k := k) (Q := Q) (p + a - 2) (by omega) (S a) (by
    rw [serreSeq_lbl_eq_i hpN ht₀ ht (by omega) _ (by simp only; omega) (by simp only; omega)
        (by simp only; omega), serreSeq_lbl_eq_j hpN ht₀ ht (by omega) _ (by simp only; omega)]
    exact fun h => hij h.1)
  rw [show p + a - 2 + 1 = p + a - 1 by omega] at hbr
  have hψ1 := ψ_serre_R (k := k) (Q := Q) hpN ht₀ ht (a := a) (by omega) ha
  have hψ2 := ψ_serre_R (k := k) (Q := Q) hpN ht₀ ht (a := a - 1) (by omega) (by omega)
  rw [show p + (a - 1) - 1 = p + a - 2 by omega, show a - 1 - 1 = a - 2 by omega] at hψ2
  have hz := blockElt_mul_ψ_mul_e (k := k) (Q := Q) (t := S (a - 2)) (q := p + a - 1)
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

end Categorification.KLR.Rouquier
