/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.KKScalars

/-!
# Kang–Kashiwara scalars of the Khovanov–Lauda parameters

If `Q_ij` is the Khovanov–Lauda polynomial `qCL KL i j` (with `t_ij = 1` and no mixed terms),
then the scalars `kkScalars` read off from `Q` are
the Khovanov–Lauda ones at `(i, j)`: `t_ij = 1` (`kkScalars_t_eq_one`), and `s_ij^{pq} = 0` in
the degrees `p < d_ij`, `q < d_ji` used by `qCL` (`kkScalars_s_eq_zero_of_kl`). The coefficients
`s_ij^{pq}` at the extremal degrees are those of `Q_ij` itself and need not vanish.
-/

namespace Categorification.KLR

open MvPolynomial QuantumGroup

variable {I : Type*} [DecidableEq I] (C : CartanDatum I) {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k}

local notation "KL" => (KL3.Diagram.CL.CLScalars.kl : KL3.Diagram.CL.CLScalars C k)

omit [DecidableEq I] in
/-- The coefficients of the Khovanov–Lauda polynomial `qCL KL i j`. -/
theorem coeff_qCL_kl (i j : I) (m : Fin 2 →₀ ℕ) :
    (KL3.Diagram.CL.qCL KL i j).coeff m =
      if C.dot i j = 0 then (if 0 = m then 1 else 0) else
      (if Finsupp.single 0 (C.dij i j) = m then 1 else 0) +
      (if Finsupp.single 1 (C.dij j i) = m then 1 else 0) := by
  rw [← TwoRep.brundanQ_eq_qCL KL (fun _ _ _ _ _ _ _ => rfl)]
  by_cases h : C.dot i j = 0
  · simp only [TwoRep.brundanQ, h, ↓reduceIte, coeff_C]
    simp
  · simp only [h, ↓reduceIte, coeff_brundanQ KL h]
    simp

variable {C} in
/-- If `Q_ij` is the Khovanov–Lauda polynomial for `i ≠ j`, the scalars `kkScalars` of `Q` are
the Khovanov–Lauda ones at `(i, j)` in the degrees used by `qCL`. -/
theorem kkScalars_t_eq_one (hQ : KLRSymm Q)
    (hunit : ∀ i j, i ≠ j → IsUnit (extremalCoeff C Q i j)) {i j : I}
    (hstd : i ≠ j → Q i j = KL3.Diagram.CL.qCL KL i j) :
    (kkScalars C hQ hunit).t i j = 1 := by
  by_cases hij : i = j
  · subst hij; exact (kkScalars C hQ hunit).t_self i
  refine Units.ext ?_
  change ((if h : i = j then 1 else (hunit i j h).unit : kˣ) : k) = 1
  rw [dite_eq_right hij, IsUnit.unit_spec, extremalCoeff, hstd hij, coeff_qCL_kl]
  by_cases h : C.dot i j = 0
  · simp [h, (C.dij_eq_zero_iff hij).2 h]
  · have hji : C.dot j i ≠ 0 := by rwa [C.symm]
    have hp := C.dij_pos (Ne.symm hij) hji
    simp [h, Finsupp.single_eq_single_iff, hp.ne']

variable {C} in
/-- If `Q_ij` is the Khovanov–Lauda polynomial for `i ≠ j`, the coefficients `s` of
`kkScalars` vanish at `(i, j)` in the degrees below the extremal ones. -/
theorem kkScalars_s_eq_zero_of_kl (hQ : KLRSymm Q)
    (hunit : ∀ i j, i ≠ j → IsUnit (extremalCoeff C Q i j)) {i j : I}
    (hstd : i ≠ j → Q i j = KL3.Diagram.CL.qCL KL i j) {p q : ℕ} (hp : p < C.dij i j)
    (hq : q < C.dij j i) : (kkScalars C hQ hunit).s i j p q = 0 := by
  change (if i = j then 0 else _) = 0
  split_ifs with hij
  · rfl
  rw [hstd hij, coeff_qCL_kl]
  have h : C.dot i j ≠ 0 := fun h => by
    rw [(C.dij_eq_zero_iff hij).2 h] at hp
    exact Nat.not_lt_zero _ hp
  simp only [h, ↓reduceIte, eq_comm (a := Finsupp.single _ _), single_add_single_eq_iff]
  simp [hp.ne', hq.ne']

end Categorification.KLR
