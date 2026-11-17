/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.KL2.Datum
import Categorification.KLR.Grading

/-!
# Rouquier crossing polynomials

R. Rouquier, *2-Kac–Moody algebras*, arXiv:0812.5023v1, §3.2.3, pp. 27–28:
the off-diagonal crossing polynomial has invertible pure-power coefficients,
and its mixed monomials have exponents strictly below the corresponding Cartan
exponents. The homogeneous specialization uses dot degrees `2 d_i`.

Here the Cartan datum supplies these dot degrees as `C.dot i i`, and the pure
`u` exponent is `C.dij i j`. The constant case `C.dij i j = 0` is a single
invertible constant; it is not expressed as a sum of two leading coefficients.
Only off-diagonal entries are constrained, as the library's KLR presentation
ignores the diagonal parameter. These polynomial conditions support roadmap B
for Webster arXiv:1209.2463v4, Theorem 2.19.
-/

noncomputable section

namespace Categorification.KLR

open MvPolynomial QuantumGroup

variable {I : Type*} {k : Type*} [CommRing k]

/-- The off-diagonal polynomial conditions of Rouquier arXiv:0812.5023v1,
§3.2.3, in the homogeneous specialization of pp. 27–28. Symmetry supplies the
pure `v` coefficient from the pure `u` coefficient with reversed indices. -/
structure IsRouquierQ (C : CartanDatum I) (Q : I → I → MvPolynomial (Fin 2) k) : Prop where
  symm : ∀ i j, i ≠ j → rename (![1, 0] : Fin 2 → Fin 2) (Q i j) = Q j i
  homogeneous : ∀ i j, i ≠ j →
    (Q i j).IsWeightedHomogeneous ![C.dot i i, C.dot j j] (-2 * C.dot i j)
  unit_coeff : ∀ i j, i ≠ j →
    IsUnit ((Q i j).coeff (Finsupp.single 0 (C.dij i j)))

namespace IsRouquierQ

variable {C : CartanDatum I} {Q : I → I → MvPolynomial (Fin 2) k}
  (hQ : IsRouquierQ C Q)

include hQ

/-- A monomial in a Rouquier polynomial has `u` exponent at most `d_ij`, and
only the pure `u` monomial can attain that bound (Rouquier §3.2.3, pp. 27–28). -/
theorem support_bound {i j : I} (hij : i ≠ j) {s : Fin 2 →₀ ℕ}
    (hs : s ∈ (Q i j).support) :
    s 0 ≤ C.dij i j ∧ (s 0 = C.dij i j → s 1 = 0) := by
  have hw := hQ.homogeneous i j hij (mem_support_iff.1 hs)
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at hw
  have he : (s 0 : ℤ) * C.dot i i + (s 1 : ℤ) * C.dot j j = -2 * C.dot i j := by
    simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, nsmul_eq_mul]
      using hw
  have hm := C.dij_mul hij
  have hn : 0 ≤ (s 1 : ℤ) * C.dot j j :=
    mul_nonneg (Nat.cast_nonneg _) (C.dot_self_pos j).le
  constructor
  · have hp : (s 0 : ℤ) * C.dot i i ≤ (C.dij i j : ℤ) * C.dot i i := by linarith
    have hh := (mul_le_mul_iff_of_pos_right (C.dot_self_pos i)).1 hp
    exact_mod_cast hh
  · intro hs0
    have hmul : (s 1 : ℤ) * C.dot j j = 0 := by
      rw [hs0] at he
      linarith
    have hz : (s 1 : ℤ) = 0 := (mul_eq_zero.1 hmul).resolve_right (C.dot_self_pos j).ne'
    exact_mod_cast hz

/-- The invertible leading coefficient, retained as a unit for arrow normalization. -/
def leadingUnit (i j : I) (hij : i ≠ j) : kˣ := (hQ.unit_coeff i j hij).unit

@[simp] theorem coe_leadingUnit (i j : I) (hij : i ≠ j) :
    (hQ.leadingUnit i j hij : k) = (Q i j).coeff (Finsupp.single 0 (C.dij i j)) :=
  (hQ.unit_coeff i j hij).unit_spec

/-- The zero Cartan exponent is Rouquier's separate constant-polynomial case. -/
theorem eq_C_of_dij_eq_zero {i j : I} (hij : i ≠ j) (hm : C.dij i j = 0) :
    Q i j = MvPolynomial.C ((Q i j).coeff 0) := by
  apply MvPolynomial.ext
  intro s
  by_cases hs : s = 0
  · subst s
    simp
  · have hz : (Q i j).coeff s = 0 := by
      by_contra hc
      have hb := hQ.support_bound hij (mem_support_iff.2 hc)
      have h₀ : s 0 = 0 := by omega
      have h₁ : s 1 = 0 := hb.2 (by omega)
      apply hs
      ext a
      fin_cases a <;> simp [h₀, h₁]
    simp [hz, Ne.symm hs]

/-- The grading from the homogeneous specialization in Rouquier §3.2.3, p. 28. -/
def gradingDatum : GradingDatum Q where
  degX i := C.dot i i
  degΨ i j := -C.dot i j
  degΨ_self _ := rfl
  isWeightedHomogeneous i j hij := by
    convert hQ.homogeneous i j hij using 1
    rw [C.symm j i]
    ring

@[simp] theorem gradingDatum_degX (i : I) :
    hQ.gradingDatum.degX i = C.dot i i := rfl

@[simp] theorem gradingDatum_degΨ (i j : I) :
    hQ.gradingDatum.degΨ i j = -C.dot i j := rfl

end IsRouquierQ

end Categorification.KLR
