/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAPhi
import Categorification.QuantumGroup.UDotBlock

/-!
# Cyclotomic polynomial degrees and the Cartan pairing

The polynomial degree gap in Kang–Kashiwara, arXiv:1102.4677v4, §5 equals
`⟨h_i, Λ - β⟩` when the parameters have the degrees specified in §2 and §4.1.
We make the needed parameter conditions explicit: the degree in the second
variable is bounded by the negative Cartan entry, and its extremal coefficient
is a unit. These are the consequences of the nonnegative coefficient grading
and extremal-unit condition in §2; arbitrary symmetric parameters need not
satisfy them. No grading of the quotient is assumed here.

Exact polynomial degrees require a nontrivial cyclotomic quotient. The
coefficient and degree-bound lemmas, and the injectivity/surjectivity statements
below, do not impose that restriction.
-/

namespace Categorification.KLR.KLRAlgebra
open MvPolynomial Polynomial QuantumGroup QuantumGroup.UDot

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} (i : I) (β : Multiset I)
  (a : I → Polynomial k)
  {C : CartanDatum I} {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (Λ : X)

/-- A degree bound and a unit extremal coefficient determine the parameter degree. -/
theorem natDegree_polyInY_of_bounds [Nontrivial k] (q : MvPolynomial (Fin 2) k) (d : ℕ)
    (hbound : (polyInY q).degree ≤ d) (htop : IsUnit ((polyInY q).coeff d)) :
    (polyInY q).natDegree = d :=
  Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (Polynomial.natDegree_le_of_degree_le hbound) htop.ne_zero

omit [DecidableEq I] in
/-- KK's second-variable degree follows from the degree bound and extremal-unit condition. -/
theorem polyInY_degree_eq_neg_pair [Nontrivial k] (j : I) (hji : j ≠ i)
    (hbound : (polyInY (Q j i)).degree ≤ (-RD.pair (RD.iY i) (RD.iX j)).toNat)
    (htop : IsUnit ((polyInY (Q j i)).coeff (-RD.pair (RD.iY i) (RD.iX j)).toNat)) :
    ((polyInY (Q j i)).natDegree : ℤ) = -RD.pair (RD.iY i) (RD.iX j) := by
  rw [natDegree_polyInY_of_bounds _ _ hbound htop, Int.toNat_of_nonneg]
  rw [RD.pair_iY_iX_eq_A]
  have := di_mul_A C i j
  have := di_pos C i
  have := C.dot_nonpos i j (Ne.symm hji)
  nlinarith

/-- The formal degree gap is the weight pairing under the actual parameter-degree conditions.
The second-variable degree of `Q j i` uses the Cartan entry with indices `i,j`. -/
theorem degA_sub_count_eq_pair
    (ha : ((a i).natDegree : ℤ) = RD.pair (RD.iY i) Λ)
    (hdeg : ∀ j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) =
      -RD.pair (RD.iY i) (RD.iX j)) :
    (degA Q i β a : ℤ) - 2 * β.count i =
      RD.pair (RD.iY i) (Λ - (β.map RD.iX).sum) := by
  have hf (j : I) : (degFac Q i j : ℤ) - (if j = i then 2 else 0) =
      -RD.pair (RD.iY i) (RD.iX j) := by
    by_cases h : j = i
    · subst j
      simp [degFac, RD.pair_iY_iX_self]
    · simp [degFac, h, hdeg j h]
  have hsum : ((β.map (degFac Q i)).sum : ℤ) - 2 * β.count i =
      -RD.pair (RD.iY i) ((β.map RD.iX).sum) := by
    induction β using Multiset.induction_on with
    | empty => simp
    | cons j β ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, Nat.cast_add, Multiset.map_cons,
        Multiset.sum_cons, map_add]
      by_cases h : j = i
      · subst j
        simp only [Multiset.count_cons_self, Nat.cast_add, Nat.cast_one]
        have := hf i
        simp only [ite_true] at this
        omega
      · rw [Multiset.count_cons_of_ne (Ne.symm h)]
        have := hf j
        simp only [h, ite_false, sub_zero] at this
        omega
  rw [degA, Nat.cast_add, map_sub, ← ha]
  omega

/-- The gap of the actual two monic polynomials, not only their formal expected degrees. -/
theorem aMonicL_degree_gap [Nontrivial (CycKLR k Q a β)]
    (hsym : KLRSymm Q)
    (hQ : ∀ a b : I, a ≠ b → ∃ c : k, IsUnit c ∧ (polyInY (Q a b)).leadingCoeff = Polynomial.C c)
    (ha : (a i).Monic)
    (hΛ : ((a i).natDegree : ℤ) = RD.pair (RD.iY i) Λ)
    (hdeg : ∀ j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) =
      -RD.pair (RD.iY i) (RD.iX j)) :
    ((aMonicL Q i β a).natDegree : ℤ) - (sPoly (Q := Q) i β a).natDegree =
      RD.pair (RD.iY i) (Λ - (β.map RD.iX).sum) := by
  rw [natDegree_aMonicL i β a hsym hQ ha, sPoly_natDegree, Nat.cast_mul, Nat.cast_ofNat]
  exact degA_sub_count_eq_pair i β a RD Λ hΛ hdeg

section ActualMap

variable
  (hsym : KLRSymm Q)
  (hβ : 0 < Multiset.card β)
  (hQ : ∀ i j : I, i ≠ j → ∃ c : k, IsUnit c ∧ (polyInY (Q i j)).leadingCoeff = Polynomial.C c)
  (ha : ∀ i, (a i).Monic)
  (h1 : 1 < Multiset.card ((Singleton.singleton i : Multiset I) + β))
  (hΛ : ((a i).natDegree : ℤ) = RD.pair (RD.iY i) Λ)
  (hdeg : ∀ j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) =
    -RD.pair (RD.iY i) (RD.iX j))

local notation "Rl" => CycKLR k Q a β
local notation "Amap" => aMap i β a h1 hβ hsym
local notation "wt" => RD.pair (RD.iY i) (Λ - Multiset.sum (Multiset.map RD.iX β))

include hQ ha hΛ hdeg in
/-- KK Proposition 5.3(a), also valid when the cyclotomic quotient is zero. -/
theorem aMap_X_pow_eq_zero_of_pair_neg (j : ℕ) (hj : wt + j < 0) :
    Amap (Polynomial.X ^ j) = 0 := by
  nontriviality Rl
  have hd := aMonicL_degree_gap i β a RD Λ hsym hQ (ha i) hΛ hdeg
  exact (aMap_phi_spec i β a hsym hβ hQ ha h1).1 j (by omega)

include hQ ha hΛ hdeg in
/-- KK Proposition 5.3(b) with the actual Cartan pairing and actual normalized polynomial. -/
theorem aMap_X_pow_monic_degree_of_pair_nonneg [Nontrivial Rl]
    (j : ℕ) (hj : 0 ≤ wt + j) :
    (Ring.inverse (lamA Q i β) • Amap (Polynomial.X ^ j)).Monic ∧
      ((Ring.inverse (lamA Q i β) • Amap (Polynomial.X ^ j)).natDegree : ℤ) = wt + j := by
  have hd := aMonicL_degree_gap i β a RD Λ hsym hQ (ha i) hΛ hdeg
  obtain ⟨hm, hmd⟩ := (aMap_phi_spec i β a hsym hβ hQ ha h1).2 j (by omega)
  exact ⟨hm, by omega⟩

include hQ ha hΛ hdeg in
/-- Nonnegative weight gives injectivity of the actual polynomial map, even for a zero quotient.
This is not yet the asserted inverse of the bimodule map in KK Theorem 5.2. -/
theorem aMap_injective_of_pair_nonneg (hwt : 0 ≤ wt) : Function.Injective Amap := by
  nontriviality Rl
  have hd := aMonicL_degree_gap i β a RD Λ hsym hQ (ha i) hΛ hdeg
  exact aMap_injective_of_degree_le i β a hsym hβ hQ ha h1 (by omega)

include hQ ha hΛ hdeg in
/-- Nonpositive weight gives surjectivity of the actual polynomial map, including a zero quotient. -/
theorem aMap_surjective_of_pair_nonpos (hwt : wt ≤ 0) : Function.Surjective Amap := by
  rcases subsingleton_or_nontrivial Rl with h | h
  · intro q
    exact ⟨0, Subsingleton.elim _ _⟩
  · have hd := aMonicL_degree_gap i β a RD Λ hsym hQ (ha i) hΛ hdeg
    exact aMap_surjective_of_degree_le i β a hsym hβ hQ ha h1 (by omega)

end ActualMap

end Categorification.KLR.KLRAlgebra
