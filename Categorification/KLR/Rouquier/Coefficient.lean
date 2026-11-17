/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Basic

/-!
# Coefficient extraction in the Serre calculation

Supporting polynomial algebra for Rouquier, *2-Kac–Moody algebras*,
arXiv:0812.5023v1, §3.2.3, Lemma 3.13. The nilHecke maps in that calculation
annihilate all monomials except the leading pure power. The following linear
coefficient-extraction lemma assembles those monomial calculations.
-/

noncomputable section

namespace Categorification.KLR.Rouquier

open MvPolynomial

variable {k : Type*} [CommRing k] {σ M : Type*} [AddCommGroup M] [Module k M]

/-- Assemble a monomial coefficient calculation under a linear map. -/
theorem map_eq_coeff_smul [DecidableEq σ] (F : MvPolynomial σ k →ₗ[k] M)
    (p : MvPolynomial σ k) (u : σ →₀ ℕ) (a : M)
    (hF : ∀ s ∈ p.support, F (monomial s 1) = if s = u then a else 0) :
    F p = p.coeff u • a := by
  classical
  rw [p.as_sum, map_sum]
  have hterm (s : σ →₀ ℕ) (hs : s ∈ p.support) :
      F (monomial s (p.coeff s)) = if s = u then p.coeff s • a else 0 := by
    rw [show monomial s (p.coeff s) = p.coeff s • monomial s 1 by simp [smul_monomial], map_smul, hF s hs]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hterm]
  by_cases hu : u ∈ p.support
  · simp [hu]
  · have hz : p.coeff u = 0 := by simpa only [mem_support_iff, not_not] using hu
    simp [hu, hz]

/-- The divided difference in the KLR braid correction is linear in its polynomial. -/
def qbarLinear : MvPolynomial (Fin 2) k →ₗ[k] MvPolynomial (Fin 3) k where
  toFun := qbar
  map_add' := qbar_add
  map_smul' c p := by
    induction p using MvPolynomial.induction_on' with
    | monomial s a =>
      simp only [smul_monomial, smul_eq_mul, qbar_monomial, map_mul]
      simp [smul_eq_C_mul, mul_assoc]
    | add p q hp hq =>
      simp only [smul_add, qbar_add, hp, hq]

@[simp] theorem qbarLinear_apply (p : MvPolynomial (Fin 2) k) : qbarLinear p = qbar p := rfl

end Categorification.KLR.Rouquier
