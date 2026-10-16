/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqCoproductNeg
import Categorification.TwoRep.RouqGrass
import Categorification.Algebra.DividedDifference
import Categorification.KLR.Basic

/-!
# Reparametrizing the dots of Rouquier's `sl₂` data

# Reparametrizing the dot of a Rouquier pair

Towards Webster, *Unfurling Khovanov-Lauda-Rouquier algebras*, arXiv:1603.06311v3, §2.3,
equation (a-auto): replacing the dots `x₁, x₂` of a `RouqLoc` datum by `f(x₁), f(x₂)`, for a
polynomial `f` with `f(0) = 0` and `f'(0) ≠ 0`, and the crossing `τ` by `τ` composed with the
inverse of the divided difference `∂f(E₁ ◁ x₂, x₁ ▷ E₂)`, gives again a `RouqLoc` datum.

This file currently contains the algebraic lemmas (inverting elements of a commutative
subalgebra with nilpotent generators and invertible constant term; divided differences of
`f(X₀)`; triangularity of the coefficients of `fᵗ`). The slide identities and the assembly of
the reparametrized `RouqLoc` datum are not yet in this file.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits Finset MvPolynomial

universe w v u

/-! ## Polynomials at nilpotent elements -/

section Algebra

variable {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A] {σ : Type*}

/-- A polynomial without constant term, evaluated at nilpotent elements, is nilpotent. -/
theorem isNilpotent_sub_constantCoeff (φ : MvPolynomial σ k →ₐ[k] A)
    (hφ : ∀ i, IsNilpotent (φ (X i))) (p : MvPolynomial σ k) :
    IsNilpotent (φ (p - C (constantCoeff p))) := by
  have hc : ∀ x y : MvPolynomial σ k, Commute (φ x) (φ y) := fun x y => by
    rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    rw [map_add, map_add, add_sub_add_comm, map_add]
    exact (hc _ _).isNilpotent_add hp hq
  | mul_X p i _ =>
    rw [map_mul, constantCoeff_X, mul_zero, map_zero, sub_zero, map_mul]
    exact (hc _ _).isNilpotent_mul_left (hφ i)

/-- A polynomial with nonzero constant term, evaluated at nilpotent elements, has a two-sided
inverse which is again a polynomial with nonzero constant term (the geometric series). -/
theorem exists_inv_of_constantCoeff_ne_zero (φ : MvPolynomial σ k →ₐ[k] A)
    (hφ : ∀ i, IsNilpotent (φ (X i))) (p : MvPolynomial σ k) (hp : constantCoeff p ≠ 0) :
    ∃ p' : MvPolynomial σ k, φ p * φ p' = 1 ∧ φ p' * φ p = 1 ∧ constantCoeff p' ≠ 0 := by
  set c := constantCoeff p
  obtain ⟨m, hm⟩ := isNilpotent_sub_constantCoeff φ hφ p
  replace hm : φ (p - C c) ^ (m + 1) = 0 := by rw [pow_succ, hm, zero_mul]
  set r : MvPolynomial σ k := -(C c⁻¹ * (p - C c))
  have hr : φ (r ^ (m + 1)) = 0 := by
    rw [show r ^ (m + 1) = (-C c⁻¹) ^ (m + 1) * (p - C c) ^ (m + 1) by simp only [r, ← mul_pow, neg_mul],
      map_mul, map_pow (f := φ) (p - C c), hm, mul_zero]
  have e : p * (C c⁻¹ * ∑ i ∈ range (m + 1), r ^ i) = 1 - r ^ (m + 1) := by
    rw [← mul_neg_geom_sum]
    have : p = C c * (1 - r) := by
      simp only [r, sub_neg_eq_add, mul_add, mul_one, ← mul_assoc, ← C_mul,
        mul_inv_cancel₀ hp, C_1, one_mul]
      ring
    rw [this, ← mul_assoc, mul_comm (C c), mul_assoc (1 - r), ← C_mul, mul_inv_cancel₀ hp, C_1,
      mul_one]
  refine ⟨C c⁻¹ * ∑ i ∈ range (m + 1), r ^ i, ?_, ?_, ?_⟩
  · rw [← map_mul, e, map_sub, hr, map_one, sub_zero]
  · rw [← map_mul, mul_comm, e, map_sub, hr, map_one, sub_zero]
  · rw [map_mul, constantCoeff_C, map_sum]
    have hr0 : constantCoeff r = 0 := by simp [r, c]
    rw [sum_range_succ', pow_zero, map_one]
    simp only [map_pow, hr0, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false,
      not_false_eq_true, zero_pow, sum_const_zero, zero_add, mul_one, inv_eq_zero]
    exact hp

variable [DecidableEq σ]

omit [Ring A] [Algebra k A] [DecidableEq σ] in
/-- The linear coefficient of a polynomial is the constant term of its divided difference. -/
theorem constantCoeff_ddiff_aeval (f : Polynomial k) :
    constantCoeff (ddiff 0 1 (Polynomial.aeval (X 0 : MvPolynomial (Fin 2) k) f)) = f.coeff 1 := by
  let ev : MvPolynomial (Fin 2) k →ₐ[k] Polynomial k := aeval ![Polynomial.X, 0]
  have hs : rename (Equiv.swap (0 : Fin 2) 1) (Polynomial.aeval (X 0) f) =
      Polynomial.aeval (X 1 : MvPolynomial (Fin 2) k) f := by
    rw [← Polynomial.aeval_algHom_apply, rename_X, Equiv.swap_apply_left]
  have hD := ddiff_spec (k := k) (σ := Fin 2) (a := 0) (b := 1) (by decide)
    (Polynomial.aeval (X 0) f)
  rw [hs] at hD
  have e0 : ev (Polynomial.aeval (X 0) f) = f := by
    rw [← Polynomial.aeval_algHom_apply]; simp [ev]
  have e1 : ev (Polynomial.aeval (X 1) f) = Polynomial.C (f.coeff 0) := by
    rw [← Polynomial.aeval_algHom_apply]
    simp [ev, Polynomial.aeval_def, Polynomial.eval₂_at_zero, Polynomial.coeff_zero_eq_eval_zero]
  have h1 := congrArg ev hD
  rw [map_mul, map_sub, map_sub, e0, e1] at h1
  generalize ddiff 0 1 (Polynomial.aeval (X 0 : MvPolynomial (Fin 2) k) f) = D at h1 ⊢
  have h2 := congrArg (fun q => Polynomial.coeff q 1) h1
  simp only [ev, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one, sub_zero,
    Polynomial.coeff_X_mul, Polynomial.coeff_sub, Polynomial.coeff_C, one_ne_zero, ite_false,
    sub_zero] at h2
  rw [← h2]
  have hc : (Polynomial.constantCoeff (R := k)).comp (ev : MvPolynomial (Fin 2) k →+* _) =
      constantCoeff := by
    refine MvPolynomial.ringHom_ext (fun r => by simp [ev]) (fun i => ?_)
    fin_cases i <;> simp [ev]
  have := congrArg (fun F : MvPolynomial (Fin 2) k →+* k => F D) hc
  exact this.symm.trans (Polynomial.constantCoeff_apply _)

omit [Ring A] [Algebra k A] [DecidableEq σ] in
/-- The powers of a polynomial without constant term are lower triangular in the monomial basis. -/
theorem coeff_pow_of_lt {f : Polynomial k} (hf : f.coeff 0 = 0) {t p : ℕ} (hp : p < t) :
    (f ^ t).coeff p = 0 := by
  obtain ⟨g, rfl⟩ := Polynomial.X_dvd_iff.mpr hf
  rw [mul_pow, Polynomial.coeff_X_pow_mul']
  simp [show ¬t ≤ p by omega]

omit [Ring A] [Algebra k A] [DecidableEq σ] in
/-- The diagonal coefficients of the powers of a polynomial without constant term. -/
theorem coeff_pow_self {f : Polynomial k} (hf : f.coeff 0 = 0) (t : ℕ) :
    (f ^ t).coeff t = f.coeff 1 ^ t := by
  obtain ⟨g, rfl⟩ := Polynomial.X_dvd_iff.mpr hf
  rw [mul_pow, Polynomial.coeff_X_pow_mul']
  simp only [le_refl, ↓reduceIte]
  rw [Nat.sub_self,
    Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_pow, ← Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.coeff_X_mul]

omit [DecidableEq σ] in
theorem rename_swap_aeval_X_zero (g : Polynomial k) :
    rename (Equiv.swap (0 : Fin 2) 1) (Polynomial.aeval (X 0) g) =
      Polynomial.aeval (X 1 : MvPolynomial (Fin 2) k) g := by
  rw [← Polynomial.aeval_algHom_apply, rename_X, Equiv.swap_apply_left]

omit [DecidableEq σ] in
/-- **Dots through a crossing**: if `τ x - y τ = 1`, then `τ g(x) - g(y) τ = ∂g(x, y)` for every
polynomial `g`, where `∂g = (g(x) - g(y)) / (x - y)` is the divided difference. -/
theorem mul_aeval_sub_aeval_mul (φ : MvPolynomial (Fin 2) k →ₐ[k] A) {τ : A}
    (hτ : τ * φ (X 0) - φ (X 1) * τ = 1) (g : Polynomial k) :
    τ * φ (Polynomial.aeval (X 0) g) - φ (Polynomial.aeval (X 1) g) * τ =
      φ (ddiff 0 1 (Polynomial.aeval (X 0) g)) := by
  induction g using Polynomial.induction_on with
  | C a =>
    simp only [Polynomial.aeval_C, algebraMap_eq, ddiff_C (by decide : (0 : Fin 2) ≠ 1),
      map_zero, AlgHom.commutes, Algebra.commutes, sub_self]
  | add p q hp hq =>
    simp only [map_add, mul_add, add_mul]
    rw [← hp, ← hq]
    abel
  | monomial n a ih =>
    have e : ∀ i : Fin 2, Polynomial.aeval (X i : MvPolynomial (Fin 2) k)
        (Polynomial.C a * Polynomial.X ^ (n + 1)) =
        Polynomial.aeval (X i) (Polynomial.C a * Polynomial.X ^ n) * X i := by
      intro i; rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X]
    rw [e, e, ddiff_mul (by decide), rename_swap_aeval_X_zero, ddiff_X_left (by decide), mul_one,
      map_add, map_mul, map_mul, map_mul, ← ih]
    calc τ * (φ (Polynomial.aeval (X 0) (Polynomial.C a * Polynomial.X ^ n)) * φ (X 0)) -
          φ (Polynomial.aeval (X 1) (Polynomial.C a * Polynomial.X ^ n)) * φ (X 1) * τ =
        (τ * φ (Polynomial.aeval (X 0) (Polynomial.C a * Polynomial.X ^ n)) -
          φ (Polynomial.aeval (X 1) (Polynomial.C a * Polynomial.X ^ n)) * τ) * φ (X 0) +
          φ (Polynomial.aeval (X 1) (Polynomial.C a * Polynomial.X ^ n)) *
            (τ * φ (X 0) - φ (X 1) * τ) := by noncomm_ring
      _ = _ := by rw [hτ, mul_one]

omit [DecidableEq σ] in
/-- **Dots through a crossing**, other side: if `x τ - τ y = 1`, then `g(x) τ - τ g(y) = ∂g(x, y)`. -/
theorem aeval_mul_sub_mul_aeval (φ : MvPolynomial (Fin 2) k →ₐ[k] A) {τ : A}
    (hτ : φ (X 0) * τ - τ * φ (X 1) = 1) (g : Polynomial k) :
    φ (Polynomial.aeval (X 0) g) * τ - τ * φ (Polynomial.aeval (X 1) g) =
      φ (ddiff 0 1 (Polynomial.aeval (X 0) g)) := by
  have hc : ∀ x y : MvPolynomial (Fin 2) k, φ x * φ y = φ y * φ x := fun x y => by
    rw [← map_mul, ← map_mul, mul_comm]
  induction g using Polynomial.induction_on with
  | C a =>
    simp only [Polynomial.aeval_C, algebraMap_eq, ddiff_C (by decide : (0 : Fin 2) ≠ 1),
      map_zero, AlgHom.commutes, Algebra.commutes, sub_self]
  | add p q hp hq =>
    simp only [map_add, mul_add, add_mul]
    rw [← hp, ← hq]
    abel
  | monomial n a ih =>
    have e : ∀ i : Fin 2, Polynomial.aeval (X i : MvPolynomial (Fin 2) k)
        (Polynomial.C a * Polynomial.X ^ (n + 1)) =
        X i * Polynomial.aeval (X i) (Polynomial.C a * Polynomial.X ^ n) := by
      intro i; rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, mul_comm]
    rw [e, e, ddiff_mul (by decide), rename_X, Equiv.swap_apply_left, ddiff_X_left (by decide),
      one_mul, map_add, map_mul, map_mul, map_mul, ← ih]
    calc φ (X 0) * φ (Polynomial.aeval (X 0) (Polynomial.C a * Polynomial.X ^ n)) * τ -
          τ * (φ (X 1) * φ (Polynomial.aeval (X 1) (Polynomial.C a * Polynomial.X ^ n))) =
        φ (Polynomial.aeval (X 0) (Polynomial.C a * Polynomial.X ^ n)) * (φ (X 0) * τ - τ * φ (X 1))
          + φ (X 1) * (φ (Polynomial.aeval (X 0) (Polynomial.C a * Polynomial.X ^ n)) * τ -
            τ * φ (Polynomial.aeval (X 1) (Polynomial.C a * Polynomial.X ^ n))) := by
          rw [hc (X 1) (Polynomial.aeval (X 1) _), hc (X 0) (Polynomial.aeval (X 0) _)]
          noncomm_ring
      _ = _ := by rw [hτ, mul_one]

end Algebra




end Categorification.TwoRep
