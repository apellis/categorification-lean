/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Rouquier.Polynomial
import Categorification.KLR.KKScalars

/-!
# Leading terms of the Rouquier parameters

The homogeneous polynomial data of Rouquier, arXiv:0812.5023v1, §3.2.3,
satisfy the second-variable degree and unit-leading-coefficient conditions
in Kang–Kashiwara, arXiv:1102.4677v4, (3.1).
-/

namespace Categorification.KLR.IsRouquierQ

open MvPolynomial QuantumGroup QuantumGroup.UDot

variable {I k : Type*} [CommRing k] [Nontrivial k] {C : CartanDatum I}
    {Q : I → I → MvPolynomial (Fin 2) k} (hQ : IsRouquierQ C Q)

include hQ

omit [Nontrivial k] in
theorem klrSymm : KLRSymm Q := fun i j hij => (hQ.symm i j hij).symm

omit [Nontrivial k] in
private theorem polyInY_coeff_top {i j : I} (hij : i ≠ j) :
    (polyInY (Q j i)).coeff (C.dij i j) = Polynomial.C ((Q i j).coeff (Finsupp.single 0 (C.dij i j))) := by
  ext p
  rw [coeff_coeff_polyInY, coeff_swap hQ.klrSymm hij]
  cases p with
  | zero => simp
  | succ p =>
    rw [Polynomial.coeff_C_succ]
    by_contra hc
    have hb := hQ.support_bound hij (mem_support_iff.mpr hc)
    simpa using hb.2 (by simp)

theorem polyInY_natDegree {i j : I} (hij : i ≠ j) :
    (polyInY (Q j i)).natDegree = C.dij i j := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    ext p
    rw [coeff_coeff_polyInY, coeff_swap hQ.klrSymm hij, Polynomial.coeff_zero]
    by_contra hc
    have hb := (hQ.support_bound hij (mem_support_iff.mpr hc)).1
    simp at hb
    omega
  · rw [hQ.polyInY_coeff_top hij, ne_eq, Polynomial.C_eq_zero]
    exact (hQ.unit_coeff i j hij).ne_zero

theorem polyInY_leading (i j : I) (hij : i ≠ j) :
    ∃ c : k, IsUnit c ∧ (polyInY (Q i j)).leadingCoeff = Polynomial.C c :=
  ⟨_, hQ.unit_coeff j i hij.symm, by
    rw [Polynomial.leadingCoeff, hQ.polyInY_natDegree hij.symm, hQ.polyInY_coeff_top hij.symm]⟩

theorem polyInY_degree_pair {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (RD : WeightDatum C X Y) (i j : I) (hji : j ≠ i) :
    ((polyInY (Q j i)).natDegree : ℤ) = -RD.pair (RD.iY i) (RD.iX j) := by
  rw [hQ.polyInY_natDegree hji.symm, neg_pair_eq_dij C RD hji.symm]

end Categorification.KLR.IsRouquierQ
