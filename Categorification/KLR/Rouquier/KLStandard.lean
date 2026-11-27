/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.KKScalarsStandard
import Categorification.KLR.Rouquier.PolynomialDegree

/-!
# The Khovanov–Lauda parameters are of Rouquier's form

The Khovanov–Lauda polynomials `Q_ij = u^{d_ij} + v^{d_ji}` (for `i · j ≠ 0`, and `Q_ij = 1`
otherwise), that is `qCL KL i j`, satisfy Rouquier's conditions: they are symmetric under
swapping the variables, weighted homogeneous of degree `-2 (i · j)`, and the coefficient of
`u^{d_ij}` is a unit (`isRouquierQ_qCL_kl`).
-/

namespace Categorification.KLR

open MvPolynomial QuantumGroup

variable {I : Type*} (C : CartanDatum I) {k : Type*} [CommRing k]

local notation "KL" => (KL3.Diagram.CL.CLScalars.kl : KL3.Diagram.CL.CLScalars C k)

/-- The Khovanov–Lauda polynomial in closed form. -/
theorem qCL_kl_eq (i j : I) :
    KL3.Diagram.CL.qCL KL i j =
      if C.dot i j = 0 then 1 else X 0 ^ C.dij i j + X 1 ^ C.dij j i := by
  unfold KL3.Diagram.CL.qCL
  split_ifs <;> simp

/-- **The Khovanov–Lauda parameters are of Rouquier's form.** -/
theorem isRouquierQ_qCL_kl : IsRouquierQ C (KL3.Diagram.CL.qCL KL) where
  symm i j hij := by
    rw [qCL_kl_eq, qCL_kl_eq, C.symm i j]
    split_ifs
    · simp
    · simp [add_comm]
  homogeneous i j hij := by
    rw [qCL_kl_eq]
    split_ifs with h
    · rw [h, mul_zero]
      exact isWeightedHomogeneous_one (R := k) _
    · refine IsWeightedHomogeneous.add ?_ ?_
      · convert (isWeightedHomogeneous_X (R := k) ![C.dot i i, C.dot j j] (0 : Fin 2)).pow (C.dij i j)
          using 1
        rw [← C.dij_mul hij]
        simp
      · convert (isWeightedHomogeneous_X (R := k) ![C.dot i i, C.dot j j] (1 : Fin 2)).pow (C.dij j i)
          using 1
        rw [C.symm i j, ← C.dij_mul (Ne.symm hij)]
        simp
  unit_coeff i j hij := by
    rw [coeff_qCL_kl]
    by_cases h : C.dot i j = 0
    · simp [h, (C.dij_eq_zero_iff hij).2 h]
    · have hp := C.dij_pos hij h
      simp [h, Finsupp.single_eq_single_iff, hp.ne']

variable {C} {Q : I → I → MvPolynomial (Fin 2) k}

/-- Polynomials equal to the Khovanov–Lauda ones off the diagonal are of Rouquier's form. -/
theorem isRouquierQ_of_kl (hstd : ∀ i j, i ≠ j → Q i j = KL3.Diagram.CL.qCL KL i j) :
    IsRouquierQ C Q where
  symm i j hij := by
    rw [hstd i j hij, hstd j i (Ne.symm hij)]
    exact (isRouquierQ_qCL_kl C).symm i j hij
  homogeneous i j hij := by
    rw [hstd i j hij]
    exact (isRouquierQ_qCL_kl C).homogeneous i j hij
  unit_coeff i j hij := by
    rw [hstd i j hij]
    exact (isRouquierQ_qCL_kl C).unit_coeff i j hij

end Categorification.KLR
