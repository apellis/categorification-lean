/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicDegree
import Categorification.TwoRep.RouqUpKLR


/-!
# Kang–Kashiwara polynomials in Brundan's form

Kang–Kashiwara (arXiv:1102.4677v4, (3.1)) take KLR polynomials
`Q_ij(u, v) = ∑ t_{i,j;p,q} u^p v^q` (`i ≠ j`) with `Q_ij(u, v) = Q_ji(v, u)`, the extremal
coefficient `t_{i,j;-a_ij,0}` a unit, and `t_{i,j;p,q} = 0` above the line
`(i · i) p + (j · j) q = -2 (i · j)`. Any such family is Brundan's polynomial `brundanQ`
(arXiv:1501.00350v1, Definition 1.1, (1.3)) of explicit Cautis–Lauda scalars `kkScalars`
(`eq_brundanQ`):

* `t_ij` is the extremal coefficient of `u^{d_ij}` in `Q_ij` (`extremalCoeff`), a unit
  (`isUnit_extremalCoeff`, from the unit leading coefficient and degree hypotheses of the
  cyclotomic family);
* `s_ij^{pq}` is the coefficient of `u^p v^q` in `Q_ij`;
* `r_i = 1`.

When the `Q_ij` are moreover weighted homogeneous of degree `-2 (i · j)`, the scalars satisfy
the homogeneity restriction of the Cautis–Lauda presentation (`kkScalars_s_eq_zero`).

`coeff_coeff_polyInY` identifies the coefficients of `polyInY q` (`q` as a polynomial in the
second variable) with those of `q`.
-/

namespace Categorification.KLR

open MvPolynomial QuantumGroup QuantumGroup.UDot

noncomputable section

variable {k : Type*} [CommRing k]

/-- The coefficients of `polyInY q` are the coefficients of `q`. -/
theorem coeff_coeff_polyInY (q : MvPolynomial (Fin 2) k) (n p : ℕ) :
    ((polyInY q).coeff n).coeff p = q.coeff (Finsupp.single 0 p + Finsupp.single 1 n) := by
  induction q using MvPolynomial.induction_on' with
  | monomial m c =>
    have hm : polyInY (monomial m c) =
        Polynomial.C (Polynomial.C c * Polynomial.X ^ m 0) * Polynomial.X ^ m 1 := by
      simp only [polyInY, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
        Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, map_mul,
        map_pow]
      ring
    rw [hm, Polynomial.coeff_C_mul_X_pow, coeff_monomial]
    have key : m = Finsupp.single 0 p + Finsupp.single 1 n ↔ n = m 1 ∧ p = m 0 := by
      constructor
      · rintro rfl
        simp
      · rintro ⟨rfl, rfl⟩
        ext x
        fin_cases x <;> simp
    by_cases h : n = m 1 ∧ p = m 0
    · rw [ite_eq_left h.1, Polynomial.coeff_C_mul_X_pow, ite_eq_left h.2, ite_eq_left (key.2 h)]
    · rw [ite_eq_right (mt key.1 h)]
      by_cases h1 : n = m 1
      · rw [ite_eq_left h1, Polynomial.coeff_C_mul_X_pow, ite_eq_right (fun h2 => h ⟨h1, h2⟩)]
      · rw [ite_eq_right h1, Polynomial.coeff_zero]
  | add q q' hq hq' =>
    rw [show polyInY (q + q') = polyInY q + polyInY q' from map_add _ _ _,
      Polynomial.coeff_add, Polynomial.coeff_add, hq, hq']
    rfl

variable {I : Type*} [DecidableEq I] (C : CartanDatum I) (Q : I → I → MvPolynomial (Fin 2) k)

/-- Kang–Kashiwara's extremal coefficient `t_{i,j;-a_ij,0}` of `Q_ij`: the coefficient of
`u^{d_ij}`. -/
def extremalCoeff (i j : I) : k := (Q i j).coeff (Finsupp.single 0 (C.dij i j))

variable {Q}

omit [DecidableEq I] in
/-- Under `KLRSymm Q`, the coefficients of `Q_ji` are those of `Q_ij` with the variables
exchanged. -/
theorem coeff_swap (hQ : KLRSymm Q) {i j : I} (hij : i ≠ j) (p q : ℕ) :
    (Q j i).coeff (Finsupp.single 0 q + Finsupp.single 1 p) =
      (Q i j).coeff (Finsupp.single 0 p + Finsupp.single 1 q) := by
  have hinj : Function.Injective (![1, 0] : Fin 2 → Fin 2) := by decide
  have hm : Finsupp.single 0 q + Finsupp.single 1 p =
      Finsupp.mapDomain (![1, 0] : Fin 2 → Fin 2) (Finsupp.single 0 p + Finsupp.single 1 q) := by
    rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single, Finsupp.mapDomain_single, add_comm]
    rfl
  rw [hQ i j hij, hm, coeff_rename_mapDomain _ hinj]

omit [DecidableEq I] in
/-- The weight of `u^p v^q` for the weights `i · i`, `j · j`. -/
theorem weight_single_add (i j : I) (p q : ℕ) :
    Finsupp.weight (![C.dot i i, C.dot j j] : Fin 2 → ℤ)
      (Finsupp.single 0 p + Finsupp.single 1 q) = C.dot i i * p + C.dot j j * q := by
  rw [map_add, Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum_single_index (by simp),
    Finsupp.sum_single_index (by simp)]
  simp [mul_comm]

omit [DecidableEq I] in
/-- `-⟨h_i, α_j⟩ = d_ij` for `i ≠ j`. -/
theorem neg_pair_eq_dij {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (RD : RootDatum C X Y)
    {i j : I} (hij : i ≠ j) : -RD.pair (RD.iY i) (RD.iX j) = C.dij i j := by
  have h := C.dij_mul hij
  have hpos := C.dot_self_pos i
  rw [RD.pair_iY_iX, show 2 * C.dot i j = -(C.dij i j : ℤ) * C.dot i i by linarith,
    Int.mul_ediv_cancel _ hpos.ne', neg_neg]

omit [DecidableEq I] in
/-- **The extremal coefficient is a unit** under the hypotheses of the cyclotomic family. -/
theorem isUnit_extremalCoeff (hQ : KLRSymm Q)
    (hlead : ∀ j l, j ≠ l → ∃ c : k, IsUnit c ∧ (polyInY (Q j l)).leadingCoeff = Polynomial.C c)
    {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (RD : RootDatum C X Y)
    (hdeg : ∀ i j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) = -RD.pair (RD.iY i) (RD.iX j))
    {i j : I} (hij : i ≠ j) : IsUnit (extremalCoeff C Q i j) := by
  obtain ⟨c, hc, hlc⟩ := hlead j i (Ne.symm hij)
  have hd : (polyInY (Q j i)).natDegree = C.dij i j := by
    have := hdeg i j (Ne.symm hij)
    rw [neg_pair_eq_dij C RD hij] at this
    exact_mod_cast this
  have h0 := congrArg (fun r : Polynomial k => r.coeff 0) hlc
  simp only [Polynomial.leadingCoeff, hd, coeff_coeff_polyInY, Polynomial.coeff_C_zero,
    Finsupp.single_zero, zero_add] at h0
  have hs := coeff_swap hQ hij (C.dij i j) 0
  rw [Finsupp.single_zero, zero_add, Finsupp.single_zero, add_zero] at hs
  rw [extremalCoeff, ← hs, h0]
  exact hc

/-- **The Cautis–Lauda scalars of a Kang–Kashiwara polynomial family**: `t_ij` is the extremal
coefficient of `Q_ij`, `s_ij^{pq}` is the coefficient of `u^p v^q` in `Q_ij` (`i ≠ j`), and
`r_i = 1`. -/
def kkScalars (hQ : KLRSymm Q) (hunit : ∀ i j, i ≠ j → IsUnit (extremalCoeff C Q i j)) :
    KL3.Diagram.CL.CLScalars C k where
  t i j := if h : i = j then 1 else (hunit i j h).unit
  s i j p q := if i = j then 0 else (Q i j).coeff (Finsupp.single 0 p + Finsupp.single 1 q)
  r _ := 1
  t_self _ := dite_eq_left rfl
  t_symm i j h := by
    by_cases hij : i = j
    · subst hij; rfl
    rw [dite_eq_right hij, dite_eq_right (Ne.symm hij)]
    refine Units.ext ?_
    rw [IsUnit.unit_spec, IsUnit.unit_spec, extremalCoeff, extremalCoeff,
      (C.dij_eq_zero_iff hij).2 h, (C.dij_eq_zero_iff (Ne.symm hij)).2 (by rw [C.symm]; exact h)]
    have hs := coeff_swap hQ hij 0 0
    simp only [Finsupp.single_zero, add_zero] at hs
    simp only [Finsupp.single_zero]
    exact hs.symm
  s_symm i j p q := by
    by_cases hij : i = j
    · subst hij; simp
    rw [ite_eq_right hij, ite_eq_right (Ne.symm hij)]
    exact (coeff_swap hQ hij p q).symm

omit [DecidableEq I] in
/-- Coefficients of a weighted homogeneous `Q_ij` off the line of degree `-2 (i · j)`
vanish. -/
theorem coeff_eq_zero_of_weight {i j : I}
    (hhom : (Q i j).IsWeightedHomogeneous ![C.dot i i, C.dot j j] (-2 * C.dot i j)) (p q : ℕ)
    (h : C.dot i i * p + C.dot j j * q ≠ -2 * C.dot i j) :
    (Q i j).coeff (Finsupp.single 0 p + Finsupp.single 1 q) = 0 := by
  by_contra hne
  exact h ((weight_single_add C i j p q).symm.trans (hhom hne))

/-- The `kkScalars` satisfy the homogeneity restriction of the CL presentation. -/
theorem kkScalars_s_eq_zero (hQ : KLRSymm Q) (hunit : ∀ i j, i ≠ j → IsUnit (extremalCoeff C Q i j))
    (hhom : ∀ i j, i ≠ j →
      (Q i j).IsWeightedHomogeneous ![C.dot i i, C.dot j j] (-2 * C.dot i j))
    (i j : I) (p q : ℕ) (_ : p < C.dij i j) (_ : q < C.dij j i)
    (h : C.dot i i * p + C.dot j j * q ≠ -2 * C.dot i j) :
    (kkScalars C hQ hunit).s i j p q = 0 := by
  change (if i = j then 0 else _) = 0
  split_ifs with hij
  · rfl
  · exact coeff_eq_zero_of_weight C (hhom i j hij) p q h

omit [DecidableEq I] in
/-- A monomial in two variables is determined by its exponents. -/
theorem single_add_single_eq_iff (m : Fin 2 →₀ ℕ) (p q : ℕ) :
    Finsupp.single 0 p + Finsupp.single 1 q = m ↔ m 0 = p ∧ m 1 = q := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨h0, h1⟩
    ext x
    fin_cases x <;> simp [h0, h1]

variable {C} in
omit [DecidableEq I] in
/-- The coefficients of Brundan's polynomial `brundanQ` for `i · j ≠ 0`. -/
theorem coeff_brundanQ (Sc : KL3.Diagram.CL.CLScalars C k) {i j : I} (h : C.dot i j ≠ 0)
    (m : Fin 2 →₀ ℕ) :
    (TwoRep.brundanQ Sc i j).coeff m =
      (if Finsupp.single 0 (C.dij i j) = m then (Sc.t i j : k) else 0) +
      (if Finsupp.single 1 (C.dij j i) = m then (Sc.t j i : k) else 0) +
      (if m 0 < C.dij i j ∧ m 1 < C.dij j i then Sc.s i j (m 0) (m 1) else 0) := by
  have hmono : ∀ (p q : ℕ) (c : k), MvPolynomial.C c * X 0 ^ p * X 1 ^ q =
      monomial (Finsupp.single 0 p + Finsupp.single 1 q) c := by
    intro p q c
    rw [X_pow_eq_monomial, X_pow_eq_monomial, C_mul_monomial, monomial_mul_monomial, mul_one,
      mul_one]
  rw [TwoRep.brundanQ, ite_eq_right h]
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.coe_add, Pi.add_apply, coeff_sum, mul_assoc,
    coeff_C_mul, X_pow_eq_monomial,
    monomial_mul_monomial, coeff_monomial, mul_ite, mul_one, mul_zero]
  congr 1
  simp only [single_add_single_eq_iff, ite_and]
  by_cases hlt : m 0 < C.dij i j ∧ m 1 < C.dij j i
  · rw [ite_eq_left hlt.1, ite_eq_left hlt.2,
      Finset.sum_eq_single (m 0) (fun b _ hb => Finset.sum_eq_zero fun _ _ =>
        ite_eq_right (Ne.symm hb)) (fun hm => (hm (Finset.mem_range.2 hlt.1)).elim),
      Finset.sum_eq_single (m 1) (fun b _ hb => by rw [ite_eq_left rfl, ite_eq_right (Ne.symm hb)])
        (fun hm => (hm (Finset.mem_range.2 hlt.2)).elim), ite_eq_left rfl, ite_eq_left rfl]
  · rw [← ite_and, ite_eq_right hlt]
    refine Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun y hy => ?_
    split_ifs with h1 h2
    · subst h1 h2
      exact (hlt ⟨Finset.mem_range.1 hx, Finset.mem_range.1 hy⟩).elim
    · rfl
    · rfl

omit [DecidableEq I] in
/-- On or below the line of degree `-2 (i · j)`, the exponents are bounded by `d_ij` and `d_ji`,
and each bound is attained only at an extremal monomial. -/
theorem exponents_of_weight_le {i j : I} (hij : i ≠ j) {p q : ℕ}
    (hw : C.dot i i * p + C.dot j j * q ≤ -2 * C.dot i j) :
    (p < C.dij i j ∧ q < C.dij j i) ∨ (p = C.dij i j ∧ q = 0) ∨ (p = 0 ∧ q = C.dij j i) := by
  have hii := C.dot_self_pos i
  have hjj := C.dot_self_pos j
  have hd := C.dij_mul hij
  have hd' := C.dij_mul (Ne.symm hij)
  rw [C.symm j i] at hd'
  have hp0 := mul_nonneg hii.le (Nat.cast_nonneg (α := ℤ) p)
  have hq0 := mul_nonneg hjj.le (Nat.cast_nonneg (α := ℤ) q)
  have hp : (p : ℤ) ≤ C.dij i j := by
    refine le_of_not_gt fun hc => ?_
    nlinarith [mul_lt_mul_of_pos_left hc hii]
  have hq : (q : ℤ) ≤ C.dij j i := by
    refine le_of_not_gt fun hc => ?_
    nlinarith [mul_lt_mul_of_pos_left hc hjj]
  rcases hp.lt_or_eq with hp | hp
  · rcases hq.lt_or_eq with hq | hq
    · exact Or.inl ⟨by exact_mod_cast hp, by exact_mod_cast hq⟩
    · refine Or.inr (Or.inr ⟨?_, by exact_mod_cast hq⟩)
      have : C.dot i i * p = 0 := by rw [hq] at hw; linarith
      have := (mul_eq_zero.1 this).resolve_left hii.ne'
      exact_mod_cast this
  · refine Or.inr (Or.inl ⟨by exact_mod_cast hp, ?_⟩)
    have : C.dot j j * q = 0 := by rw [hp] at hw; linarith
    have := (mul_eq_zero.1 this).resolve_left hjj.ne'
    exact_mod_cast this

omit [DecidableEq I] in
/-- Weighted homogeneity of degree `-2 (i · j)` gives Kang–Kashiwara's support condition: the
coefficients above the line vanish. -/
theorem coeff_eq_zero_of_lt_of_hom {i j : I}
    (hhom : (Q i j).IsWeightedHomogeneous ![C.dot i i, C.dot j j] (-2 * C.dot i j)) (p q : ℕ)
    (h : -2 * C.dot i j < C.dot i i * p + C.dot j j * q) :
    (Q i j).coeff (Finsupp.single 0 p + Finsupp.single 1 q) = 0 :=
  coeff_eq_zero_of_weight C hhom p q h.ne'

/-- **A Kang–Kashiwara polynomial family is Brundan's polynomial of its scalars**: for `i ≠ j`,
`Q_ij = brundanQ (kkScalars Q) i j` when the coefficients of `Q_ij` above the line
`(i · i) p + (j · j) q = -2 (i · j)` vanish (Kang–Kashiwara, arXiv:1102.4677v4, (3.1)) and the
extremal coefficients are units. -/
theorem eq_brundanQ (hQ : KLRSymm Q) (hunit : ∀ i j, i ≠ j → IsUnit (extremalCoeff C Q i j))
    (hsupp : ∀ i j, i ≠ j → ∀ p q : ℕ, -2 * C.dot i j < C.dot i i * p + C.dot j j * q →
      (Q i j).coeff (Finsupp.single 0 p + Finsupp.single 1 q) = 0)
    {i j : I} (hij : i ≠ j) : Q i j = TwoRep.brundanQ (kkScalars C hQ hunit) i j := by
  have ht : ∀ {a b : I}, a ≠ b → ((kkScalars C hQ hunit).t a b : k) = extremalCoeff C Q a b :=
    fun h => by
      change ((if h' : _ = _ then 1 else (hunit _ _ h').unit : kˣ) : k) = _
      rw [dite_eq_right h, IsUnit.unit_spec]
  have hs : ∀ p q, (kkScalars C hQ hunit).s i j p q =
      (Q i j).coeff (Finsupp.single 0 p + Finsupp.single 1 q) := fun p q => by
    change (if i = j then 0 else _) = _
    rw [ite_eq_right hij]
  ext m
  have hm : Finsupp.single 0 (m 0) + Finsupp.single 1 (m 1) = m :=
    (single_add_single_eq_iff m _ _).2 ⟨rfl, rfl⟩
  have hzero : ¬ (m 0 < C.dij i j ∧ m 1 < C.dij j i) → Finsupp.single 0 (C.dij i j) ≠ m →
      Finsupp.single 1 (C.dij j i) ≠ m → (Q i j).coeff m = 0 := by
    intro hlt e1 e2
    rw [← hm]
    by_contra hne
    have hw := le_of_not_gt fun hgt => hne (hsupp i j hij _ _ hgt)
    rcases exponents_of_weight_le C hij hw with h | ⟨h0, h1⟩ | ⟨h0, h1⟩
    · exact hlt h
    · exact e1 (by rw [← hm, h0, h1, Finsupp.single_zero, add_zero])
    · exact e2 (by rw [← hm, h0, h1, Finsupp.single_zero, zero_add])
  by_cases h0 : C.dot i j = 0
  · have hdz : C.dij i j = 0 := (C.dij_eq_zero_iff hij).2 h0
    have hdz' : C.dij j i = 0 := (C.dij_eq_zero_iff (Ne.symm hij)).2 (by rw [C.symm]; exact h0)
    rw [TwoRep.brundanQ, ite_eq_left h0, coeff_C]
    by_cases hm0 : 0 = m
    · rw [ite_eq_left hm0, ht hij, extremalCoeff, hdz, Finsupp.single_zero, ← hm0]
    · rw [ite_eq_right hm0]
      refine hzero (by rw [hdz]; omega) (by rw [hdz, Finsupp.single_zero]; exact hm0)
        (by rw [hdz', Finsupp.single_zero]; exact hm0)
  · rw [coeff_brundanQ _ h0 m]
    have hdpos := C.dij_pos hij h0
    have hdpos' := C.dij_pos (Ne.symm hij) (by rw [C.symm]; exact h0)
    by_cases e1 : Finsupp.single 0 (C.dij i j) = m
    · subst e1
      have e2 : Finsupp.single 1 (C.dij j i) ≠ Finsupp.single 0 (C.dij i j) := fun e => by
        have := congrArg (· 1) e
        simp at this
        omega
      simp only [ht hij, extremalCoeff]
      simp only [↓reduceIte, Finsupp.single_eq_same, lt_irrefl, false_and, add_zero]
      split_ifs with hh
      · exfalso
        have := congrArg (fun f => f 1) hh
        simp at this
        omega
      · rw [add_zero]
    by_cases e2 : Finsupp.single 1 (C.dij j i) = m
    · subst e2
      simp only [e1, ↓reduceIte, ht (Ne.symm hij), extremalCoeff, zero_add, Finsupp.single_eq_same,
        lt_irrefl, and_false, add_zero]
      have hsw := coeff_swap hQ hij 0 (C.dij j i)
      rw [Finsupp.single_zero, add_zero, Finsupp.single_zero, zero_add] at hsw
      exact hsw.symm
    simp only [e1, e2, ↓reduceIte, zero_add]
    by_cases hlt : m 0 < C.dij i j ∧ m 1 < C.dij j i
    · rw [ite_eq_left hlt, hs, hm]
    · rw [ite_eq_right hlt]
      exact hzero hlt e1 e2

end

end Categorification.KLR
