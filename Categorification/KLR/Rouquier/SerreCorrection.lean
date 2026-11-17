/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Rouquier.SerreMaps
import Categorification.KLR.Rouquier.Coefficient

/-!
# The braid correction in the Serre relation

Rouquier, *2-Kac–Moody algebras*, arXiv:0812.5023v1, §3.2.3,
Lemma 3.13 and §4.1.1, Proposition 4.2. The nilHecke blocks annihilate
all lower first-variable powers in the divided difference of the crossing
polynomial. Its leading pure coefficient is the scalar in the contracting
homotopy identity. This calculation uses arbitrary commutative coefficients.
-/

noncomputable section

namespace Categorification.KLR.Rouquier

open Equiv MvPolynomial KLRAlgebra TypeA QuantumGroup KL2

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I}
  {t : Seq ν} {p N a : ℕ}

local notation "A" => KLRAlgebra k Q ν
local notation "S" => serreSeq t p

/-- The divided difference sandwiched between the two nilHecke blocks. -/
def serreCorrection (hpN : p + N < Multiset.card ν) (ha1 : 1 ≤ a) (ha : a + 1 ≤ N) :
    MvPolynomial (Fin 2) k →ₗ[k] A where
  toFun f := blockElt p a * blockElt (p + a + 1) (N - a) *
    pol (rename ![⟨p + a - 1, by omega⟩, ⟨p + a, by omega⟩,
      ⟨p + a + 1, by omega⟩] (qbarLinear f)) * e (S a) *
    (chainL (p + a + 1) (N - a - 1) * chainR p (a - 1))
  map_add' f g := by simp [map_add, mul_add, add_mul]
  map_smul' c f := by simp [map_smul]

private theorem braid_correction (r : ℕ) (hr : r + 2 < Multiset.card ν) (s : Seq ν)
    (h₁ : s.lbl ⟨r, by omega⟩ = s.lbl ⟨r + 2, hr⟩)
    (h₂ : s.lbl ⟨r, by omega⟩ ≠ s.lbl ⟨r + 1, by omega⟩) :
    (ψ r * ψ (r + 1) * ψ r * e s - ψ (r + 1) * ψ r * ψ (r + 1) * e s : A) =
      pol (rename ![⟨r, by omega⟩, ⟨r + 1, by omega⟩, ⟨r + 2, hr⟩]
        (qbar (Q (s.lbl ⟨r, by omega⟩) (s.lbl ⟨r + 1, by omega⟩)))) * e s := by
  rw [← sub_mul, KLRAlgebra.braid r hr s, ite_eq_left ⟨h₁, h₂⟩, ncEval_x_three]


variable {i j : I} (hpN : p + N < Multiset.card ν)
  (ht₀ : ∀ r : Fin (Multiset.card ν), (r : ℕ) = p → t.lbl r = j)
  (ht : ∀ r : Fin (Multiset.card ν), p < r → (r : ℕ) ≤ p + N → t.lbl r = i)

include ht₀ ht in
/-- A nilHecke sandwich extracts the top first-variable degree of the braid correction. -/
theorem serreCorrection_monomial (ha1 : 1 ≤ a) (ha : a + 1 ≤ N)
    (s : Fin 2 →₀ ℕ) (hs : s 0 ≤ N - 1) :
    serreCorrection (Q := Q) (t := t) hpN ha1 ha (monomial s 1) =
      if s 0 = N - 1 then
        x ⟨p + a, by omega⟩ ^ s 1 * ((-1) ^ (a - 1) * etop t p N a) else 0 := by
  classical
  let B : A := blockElt p a * blockElt (p + a + 1) (N - a)
  let R : A := chainL (p + a + 1) (N - a - 1) * chainR p (a - 1)
  let z : A := x ⟨p + a, by omega⟩ ^ s 1
  have hz : Commute z B :=
    ((commute_x_blockElt (by simp only; omega)).mul_right
      (commute_x_blockElt (by simp only; omega))).pow_left _
  have heval : serreCorrection (Q := Q) (t := t) hpN ha1 ha (monomial s 1) =
      z * ∑ r ∈ Finset.range (s 0),
        B * (x ⟨p + a - 1, by omega⟩ ^ r *
          x ⟨p + a + 1, by omega⟩ ^ (s 0 - 1 - r) * e (S a)) * R := by
    simp only [serreCorrection, LinearMap.coe_mk, AddHom.coe_mk, qbarLinear_apply,
      qbar_monomial, map_mul, map_one, one_mul, map_pow, rename_X, pol_X,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      map_sum, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r _
    change B * (z * (_ * _)) * e (S a) * R = z * (B * (_ * e (S a)) * R)
    rw [← mul_assoc B z, ← hz.eq]
    simp only [mul_assoc]
    rfl
  rw [heval]
  have hterm (r : ℕ) (hr : r ∈ Finset.range (s 0)) :
      B * (x ⟨p + a - 1, by omega⟩ ^ r *
        x ⟨p + a + 1, by omega⟩ ^ (s 0 - 1 - r) * e (S a)) * R =
      if r = a - 1 ∧ s 0 - 1 - r = N - a - 1 then
        (-1) ^ (a - 1) * etop t p N a else 0 := by
    apply serre_A_term hpN ht₀ ht ha1 ha
    have := Finset.mem_range.1 hr
    omega
  rw [Finset.sum_congr rfl hterm]
  by_cases htop : s 0 = N - 1
  · rw [ite_eq_left htop]
    congr 1
    rw [Finset.sum_eq_single (a - 1)]
    · rw [ite_eq_left ⟨rfl, by omega⟩]
    · intro r _ hr
      rw [ite_eq_right (fun h => hr h.1)]
    · intro h
      exact (h (Finset.mem_range.2 (by omega))).elim
  · rw [ite_eq_right htop]
    have hzsum : ∑ r ∈ Finset.range (s 0),
        (if r = a - 1 ∧ s 0 - 1 - r = N - a - 1 then
          (-1 : A) ^ (a - 1) * etop t p N a else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro r hr
      rw [ite_eq_right]
      have := Finset.mem_range.1 hr
      omega
    rw [hzsum, mul_zero]


include ht₀ ht in
/-- The leading pure coefficient is the only contribution of the braid correction. -/
theorem serreCorrection_eq_coeff_smul (ha1 : 1 ≤ a) (ha : a + 1 ≤ N)
    (f : MvPolynomial (Fin 2) k)
    (hf : ∀ s ∈ f.support, s 0 ≤ N - 1 ∧ (s 0 = N - 1 → s 1 = 0)) :
    serreCorrection (Q := Q) (t := t) hpN ha1 ha f =
      f.coeff (Finsupp.single 0 (N - 1)) • ((-1) ^ (a - 1) * etop t p N a) := by
  classical
  apply map_eq_coeff_smul
  intro s hs
  rw [serreCorrection_monomial hpN ht₀ ht ha1 ha s (hf s hs).1]
  by_cases htop : s 0 = N - 1
  · have hzero : s 1 = 0 := (hf s hs).2 htop
    have heq : s = Finsupp.single 0 (N - 1) := by
      ext r
      fin_cases r <;> simp [htop, hzero]
    rw [ite_eq_left htop, ite_eq_left heq, hzero, pow_zero, one_mul]
  · have hne : s ≠ Finsupp.single 0 (N - 1) := by
      intro heq
      apply htop
      simp [heq]
    rw [ite_eq_right htop, ite_eq_right hne]

include hpN ht₀ ht in
/-- The interior Serre homotopy identity, with the leading coefficient of the crossing
polynomial. This is the coefficient calculation in Rouquier Lemma 3.13. -/
theorem serre_A (hij : i ≠ j) (ha1 : 1 ≤ a) (ha : a + 1 ≤ N)
    (hQ : ∀ s ∈ (Q i j).support, s 0 ≤ N - 1 ∧ (s 0 = N - 1 → s 1 = 0)) :
    (aplus t p N (a - 1) * aminus t p N a - aminus t p N (a + 1) * aplus t p N a : A) =
      (Q i j).coeff (Finsupp.single 0 (N - 1)) • ((-1) ^ (a - 1) * etop t p N a) := by
  rw [aplus_mul_aminus hpN ht₀ ht ha1 (by omega), aminus_mul_aplus hpN ht₀ ht ha]
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
  have hbr := braid_correction (Q := Q) (p + a - 1) (by omega) (S a)
    (by rw [serreSeq_lbl_eq_i hpN ht₀ ht (by omega) _ (by simp only; omega) (by simp only; omega)
          (by simp only; omega), serreSeq_lbl_eq_i hpN ht₀ ht (by omega) _ (by simp only; omega)
          (by simp only; omega) (by simp only; omega)])
    (by rw [serreSeq_lbl_eq_i hpN ht₀ ht (by omega) _ (by simp only; omega) (by simp only; omega)
          (by simp only; omega), serreSeq_lbl_eq_j hpN ht₀ ht (by omega) _ (by simp only; omega)]
        exact hij)
  rw [serreSeq_lbl_eq_i hpN ht₀ ht (by omega) _ (by simp only; omega) (by simp only; omega)
    (by simp only; omega), serreSeq_lbl_eq_j hpN ht₀ ht (by omega) _ (by simp only; omega)] at hbr
  simp only [show p + a - 1 + 1 = p + a by omega,
    show p + a - 1 + 2 = p + a + 1 by omega] at hbr
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
  rw [h1, h2, ← sub_mul, ← mul_sub, hbr]
  simpa only [serreCorrection, LinearMap.coe_mk, AddHom.coe_mk,
    qbarLinear_apply, B, Lr, Rl, mul_assoc] using
    serreCorrection_eq_coeff_smul (Q := Q) hpN ht₀ ht ha1 ha (Q i j) hQ

end Categorification.KLR.Rouquier
