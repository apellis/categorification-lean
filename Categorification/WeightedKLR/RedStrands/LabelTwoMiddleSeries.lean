/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoUnknotGrading
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# The signed series of the label-two middle homology

Webster, arXiv:1309.3796v2, §8.2, printed page 81, Proposition 8.4.
The denominator of the middle contribution follows from its two-step
coefficient recurrence. Multiplying by the denominator gives a formal
power-series equality over the Laurent polynomial ring in the internal
variable.
-/

namespace Categorification.Webster.LabelTwo

open LaurentPolynomial PowerSeries

noncomputable section

local notation "L" => LaurentPolynomial ℤ
local notation "q[" j "]" => (LaurentPolynomial.T j : L)
local notation "t" => (PowerSeries.X : PowerSeries L)
local notation "Cₚ" => (PowerSeries.C : L →+* PowerSeries L)

/-- Coefficients of the signed middle homology series after removing
the degree-zero scalar class. -/
def middleTailCoeff (n : ℕ) : L :=
  if Even n then q[-2*(n:ℤ)-2] else -q[-2*(n:ℤ)]

private theorem middleTailCoeff_add_two (n : ℕ) :
    middleTailCoeff (n+2) = q[-4] * middleTailCoeff n := by
  have h : Even (n+2) ↔ Even n := by
    rw [Nat.even_add]
    simp
  unfold middleTailCoeff
  by_cases hn : Even n
  · rw [ite_eq_left (h.mpr hn),ite_eq_left hn,← LaurentPolynomial.T_add]
    congr 1
    omega
  · have he : -2*((n+2:ℕ):ℤ) = (-4:ℤ) + -2*(n:ℤ) := by omega
    rw [ite_eq_right (fun h' => hn (h.mp h')),ite_eq_right hn,mul_neg,
      ← LaurentPolynomial.T_add,he]

/-- The signed middle contribution, with its degree-zero scalar class. -/
def signedMiddleSeries : PowerSeries L := 1 + PowerSeries.mk middleTailCoeff

theorem signedMiddleSeries_coeff_zero : PowerSeries.coeff 0 signedMiddleSeries = 1 + q[-2] := by
  simp [signedMiddleSeries,middleTailCoeff]

theorem signedMiddleSeries_coeff_succ (n : ℕ) :
    PowerSeries.coeff (n+1) signedMiddleSeries =
      if Even n then -q[-2*((n+1:ℕ):ℤ)] else q[-2*((n+1:ℕ):ℤ)-2] := by
  by_cases h : Even n <;> simp [signedMiddleSeries,middleTailCoeff,Nat.even_add_one,h]

/-- In positive homological degree at an internal shift in the support,
the series coefficient is its Laurent monomial with the homological sign. -/
theorem signedMiddleSeries_coeff_of_support (n : ℕ) (q : ℤ)
    (hq : InternalSupport (n+1) q) :
    PowerSeries.coeff (n+1) signedMiddleSeries = if Even n then -q[q] else q[q] := by
  rw [signedMiddleSeries_coeff_succ]
  by_cases hn : Even n
  · have hq' : q = -2*((n+1:ℕ):ℤ) := by
      simpa only [InternalSupport,ite_eq_left hn] using hq
    simp only [hq',ite_eq_left hn]
  · have hq' : q = -2*((n+1:ℕ):ℤ)-2 := by
      simpa only [InternalSupport,ite_eq_right hn] using hq
    simp only [hq',ite_eq_right hn]

/-- The denominator of Webster's signed middle series. -/
def middleDenominator : PowerSeries L := 1 - Cₚ q[-4] * t^2

theorem middleDenominator_isUnit : IsUnit middleDenominator :=
  PowerSeries.isUnit_iff_constantCoeff.mpr (by simp [middleDenominator])

private theorem middleTail_relation :
    middleDenominator * PowerSeries.mk middleTailCoeff = Cₚ q[-2] * (1-t) := by
  apply PowerSeries.ext
  intro n
  rw [middleDenominator,sub_mul,one_mul,map_sub,mul_assoc,PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul',PowerSeries.coeff_mk,PowerSeries.coeff_C_mul,
    map_sub,PowerSeries.coeff_one,PowerSeries.coeff_X]
  cases n with
  | zero => simp [middleTailCoeff]
  | succ n =>
      cases n with
      | zero => simp [middleTailCoeff]
      | succ n =>
          simp [middleTailCoeff_add_two n]

/-- The signed two-periodic middle contribution of the label-two unknot
has numerator `q⁻²(1-t)` after subtracting the scalar constant term. -/
theorem signedMiddleSeries_relation :
    middleDenominator * signedMiddleSeries = middleDenominator + Cₚ q[-2] * (1-t) := by
  rw [signedMiddleSeries,mul_add,mul_one,middleTail_relation]

end

end Categorification.Webster.LabelTwo
