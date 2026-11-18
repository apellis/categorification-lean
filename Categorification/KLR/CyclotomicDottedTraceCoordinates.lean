/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicCornerTracePolynomial

/-!
# Dotted polynomial coordinates for the opposite cap

Kang–Kashiwara, arXiv:1102.4677v4, §5.2, Theorem 5.2. Moving successive
rightmost dots through the prescribed equal-colour crossing records the
dotted multiplication counits as successive polynomial coefficients.
-/

noncomputable section
namespace Categorification.KLR.KLRAlgebra.CornerTrace

open Polynomial
variable {I k : Type*} [DecidableEq I] [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (i : I) (γ : Multiset I)
  (a : I → Polynomial k) (hsym : KLRSymm Q)

local notation "β" => ((Singleton.singleton i : Multiset I) + γ)
local notation "R" => CycKLR k Q a β
local notation "H" => zero_lt_card_single_add i γ
local notation "Y" => lastDot0 i β a
local notation "CM" => cMap i β hsym a H

/-- The KK polynomial coordinate on a representative after right multiplication
by `N` dots on its last strand. -/
def dottedCapPolynomial (N : ℕ) : EIKZero Q i β a →ₗ[k] Polynomial R :=
  CM ∘ₗ ((Y ^ N).restrictScalars k) ∘ₗ eiZeroCoordinates Q i γ a

private theorem dotPow_section (N : ℕ) (p : Polynomial R) :
    (Y ^ N) (cSection i β a H p) = cSection i β a H (p * X ^ N) := by
  induction N with
  | zero => rw [pow_zero, Module.End.one_apply, pow_zero, mul_one]
  | succ N ih =>
    rw [pow_succ', Module.End.mul_apply, ih, lastDot0_cSection, pow_succ, mul_assoc]

/-- Dots on the polynomial summand multiply its coordinate by the corresponding monomial. -/
theorem dottedCapPolynomial_section (N : ℕ) (p : Polynomial R) :
    dottedCapPolynomial Q i γ a hsym N (eiCSection Q i γ a p) = p * X ^ N := by
  change CM ((Y ^ N) (eiZeroCoordinates Q i γ a _)) = _
  rw [eiCSection_coordinates, dotPow_section, cMap_cSection]

private theorem lowerDot_one_then (n : ℕ) (t : KZeroPrime Q i γ a) :
    lowerDot Q i γ a n (lowerDot Q i γ a 1 t) = lowerDot Q i γ a (n + 1) t := by
  induction n with
  | zero => rw [lowerDot_zero]
  | succ n ih => rw [lowerDot_succ, ih, ← lowerDot_succ]

/-- A dotted crossing contributes the `(N-1-j)`-dotted multiplication counit
in degree `j < N`, with the positive sign from the convention `τ = −ψ`. -/
theorem dottedCapPolynomial_crossing_coeff (N j : ℕ) (t : KZeroPrime Q i γ a) :
    (dottedCapPolynomial Q i γ a hsym N (lowerF Q i γ a t)).coeff j =
      if j < N then cyclotomicDotCounit Q i γ a (N - 1 - j) (lowerCyclotomicProj Q i γ a t) else 0 := by
  change (CM ((Y ^ N) (lowerFCoordinates Q i γ a t))).coeff j = _
  induction N generalizing t with
  | zero => rw [pow_zero, Module.End.one_apply, cMap_lowerF, coeff_zero, ite_eq_right (Nat.not_lt_zero j)]
  | succ N ih =>
    rw [pow_succ, Module.End.mul_apply, lastDot_lowerFCoordinates, map_add, dotPow_section,
      map_add, cMap_cSection, coeff_add, ih, C_mul_X_pow_eq_monomial, coeff_monomial]
    by_cases h : j < N
    · simp only [ite_eq_left h, ite_eq_left (Nat.lt_succ_of_lt h), ite_eq_right (Nat.ne_of_lt h).symm, add_zero,
        cyclotomicDotCounit_proj, lowerDot_one_then]
      rw [show N - 1 - j + 1 = N + 1 - 1 - j by omega]
    · rw [ite_eq_right h]
      by_cases he : N = j
      · subst j
        rw [ite_eq_left rfl, zero_add, ite_eq_left (Nat.lt_succ_self N), show N + 1 - 1 - N = 0 by omega, cyclotomicDotCounit_proj, lowerDot_zero]
      · rw [ite_eq_right he, ite_eq_right (show ¬j < N + 1 by omega), zero_add]

private theorem iter_pLift (n : ℕ) (p : Polynomial R) :
    (Y ^ n) (pLift i β a H (by simp) p) = pLift i β a H (by simp) (p * X ^ n) := by
  induction n with
  | zero => rw [pow_zero, Module.End.one_apply, pow_zero, mul_one]
  | succ n ih => rw [pow_succ', Module.End.mul_apply, ih, ← pLift_mul_X, pow_succ, mul_assoc]

/-- The section of the polynomial relation carries the same rightmost dots into
the input of the signed KK polynomial map. -/
theorem dottedCapPolynomial_relation (N : ℕ) (p : Polynomial R) :
    dottedCapPolynomial Q i γ a hsym N (eiP Q i γ a (eiBSection Q i γ a p)) =
      eiA Q i γ a hsym (p * X ^ N) := by
  have h : eiZeroCoordinates Q i γ a (eiP Q i γ a (eiBSection Q i γ a p)) =
      ((-1 : k) ^ Multiset.card β) • pLift i β a H (by simp) p := by
    rw [eiP_coordinates, eiBSection_coordinates]
    exact congrArg (((-1 : k) ^ Multiset.card β) • ·) (act0_one_pLift i β a H (by simp) p)
  change CM (((Y ^ N).restrictScalars k) (eiZeroCoordinates Q i γ a _)) = _
  rw [h, map_smul, LinearMap.restrictScalars_apply, iter_pLift, map_smul]
  rfl

end Categorification.KLR.KLRAlgebra.CornerTrace
