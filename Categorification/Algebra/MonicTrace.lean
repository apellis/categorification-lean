/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic

/-!
# Remainder traces for central monic polynomials

For an arbitrary ring and a central monic polynomial `f` of degree `n`, the
coefficient of degree `n-1` in the monic remainder is a relative trace.
It is additive and left/right coefficient-linear; it is not the matrix trace.
The recursively constructed polynomials `D₀ = 1`,
`Dₛ₊₁ = Dₛ X + C(f[n-1-s])` recover every coefficient:
`tr(Dₛ p) = (p %ₘ f)[n-1-s]` for `s < n`.
Both dual-basis identities and both nondegeneracy statements are proved.

No domain, field, nontriviality, separability, Frobenius, or basis hypothesis
is required. Centrality is explicit and necessary for the left-coefficient
linearity used by the recursion; right-coefficient linearity only needs monicity.
Degree zero is included. This is the polynomial prerequisite for cyclotomic
relative duality, not a trace on a general KLR corner or a categorical adjunction.
-/

noncomputable section
namespace Categorification.MonicTrace
open Polynomial
variable {R : Type*} [Ring R] (f : Polynomial R) (hf : f.Monic)
include hf

theorem remainder_add (p q : Polynomial R) :
    (p + q) %ₘ f = p %ₘ f + q %ₘ f := by
  nontriviality R
  exact (div_modByMonic_unique (p /ₘ f + q /ₘ f) (p %ₘ f + q %ₘ f) hf
    ⟨by
      conv_rhs => rw [← modByMonic_add_div p f, ← modByMonic_add_div q f]
      rw [mul_add]; abel,
      (degree_add_le _ _).trans_lt
        (max_lt (degree_modByMonic_lt p hf) (degree_modByMonic_lt q hf))⟩).2

theorem remainder_eq_of_sub (p q : Polynomial R) (h : ∃ d, p - q = f * d) :
    p %ₘ f = q %ₘ f := by
  nontriviality R
  obtain ⟨d, hd⟩ := h
  exact (div_modByMonic_unique (q /ₘ f + d) (q %ₘ f) hf
    ⟨by
      rw [mul_add, ← add_assoc, modByMonic_add_div, ← hd]
      abel,
      degree_modByMonic_lt q hf⟩).2

theorem remainder_mul_right (p q : Polynomial R) :
    (p * q) %ₘ f = ((p %ₘ f) * q) %ₘ f := by
  apply remainder_eq_of_sub f hf
  refine ⟨(p /ₘ f) * q, ?_⟩
  rw [modByMonic_eq_sub_mul_div]
  noncomm_ring

theorem remainder_mul_left (hcentral : ∀ p, Commute p f) (p q : Polynomial R) :
    (p * q) %ₘ f = (p * (q %ₘ f)) %ₘ f := by
  apply remainder_eq_of_sub f hf
  refine ⟨p * (q /ₘ f), ?_⟩
  rw [modByMonic_eq_sub_mul_div, mul_sub, sub_sub_cancel, ← mul_assoc,
    (hcentral p).eq, mul_assoc]

theorem remainder_mul_C (p : Polynomial R) (r : R) :
    (p * C r) %ₘ f = (p %ₘ f) * C r := by
  nontriviality R
  refine (div_modByMonic_unique ((p /ₘ f) * C r) ((p %ₘ f) * C r) hf ?_).2
  constructor
  · rw [← mul_assoc, ← add_mul, modByMonic_add_div]
  · apply lt_of_le_of_lt (degree_mul_le _ _) _
    exact (add_le_add_right (degree_C_le (a := r)) _).trans_lt (by simpa using degree_modByMonic_lt p hf)

theorem remainder_C_mul (hcentral : ∀ p, Commute p f) (r : R) (p : Polynomial R) :
    (C r * p) %ₘ f = C r * (p %ₘ f) := by
  nontriviality R
  refine (div_modByMonic_unique (C r * (p /ₘ f)) (C r * (p %ₘ f)) hf ?_).2
  constructor
  · rw [← mul_assoc, ← (hcentral (C r)).eq, mul_assoc, ← mul_add, modByMonic_add_div]
  · apply lt_of_le_of_lt (degree_mul_le _ _) _
    exact (add_le_add_left (degree_C_le (a := r)) _).trans_lt (by simpa using degree_modByMonic_lt p hf)

/-- The top coefficient of the monic remainder, not the matrix trace. -/
def trace (p : Polynomial R) : R := (p %ₘ f).coeff (f.natDegree - 1)

theorem trace_add (p q : Polynomial R) : trace f (p + q) = trace f p + trace f q := by
  simp only [trace, remainder_add f hf, coeff_add]

theorem trace_mul_C (p : Polynomial R) (r : R) : trace f (p * C r) = trace f p * r := by
  simp only [trace, remainder_mul_C f hf, coeff_mul_C]

theorem trace_C_mul (hcentral : ∀ p, Commute p f) (r : R) (p : Polynomial R) :
    trace f (C r * p) = r * trace f p := by
  simp only [trace, remainder_C_mul f hf hcentral, coeff_C_mul]

/-- Recursion producing the trace-dual family in reverse power order. -/
def dual : ℕ → Polynomial R
  | 0 => 1
  | s + 1 => dual s * X + C (f.coeff (f.natDegree - 1 - s))

theorem remainder_X_mul_of_degree_lt [Nontrivial R] (hn : 0 < f.natDegree)
    (p : Polynomial R) (hp : p.degree < f.degree) :
    (X * p) %ₘ f = X * p - f * C (p.coeff (f.natDegree - 1)) := by
  refine (div_modByMonic_unique (C (p.coeff (f.natDegree - 1)))
    (X * p - f * C (p.coeff (f.natDegree - 1))) hf ⟨by abel, ?_⟩).2
  rw [degree_eq_natDegree hf.ne_zero, degree_lt_iff_coeff_zero]
  intro j hj
  rw [coeff_sub, coeff_mul_C]
  have hj0 : j ≠ 0 := by omega
  have hx : (X * p).coeff j = p.coeff (j - 1) := by
    obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
    simp only [coeff_X_mul, Nat.succ_sub_one]
  rw [hx]
  by_cases he : j = f.natDegree
  · subst j
    rw [hf.coeff_natDegree, one_mul, sub_self]
  · have hpj : p.coeff (j - 1) = 0 := coeff_eq_zero_of_degree_lt
      (hp.trans_le (by rw [degree_eq_natDegree hf.ne_zero]; exact_mod_cast (show f.natDegree ≤ j - 1 by omega)))
    rw [hpj, coeff_eq_zero_of_natDegree_lt (show f.natDegree < j by omega), zero_mul, sub_self]

theorem remainder_X_coeff_succ [Nontrivial R] (hcentral : ∀ p, Commute p f)
    (p : Polynomial R) (j : ℕ)
    (hj : j + 1 < f.natDegree) :
    ((X * p) %ₘ f).coeff (j + 1) =
      (p %ₘ f).coeff j - f.coeff (j + 1) * trace f p := by
  rw [remainder_mul_left f hf hcentral,
    remainder_X_mul_of_degree_lt f hf (by omega) _ (degree_modByMonic_lt p hf)]
  simp only [coeff_sub, coeff_X_mul, coeff_mul_C, trace]

/-- The recursion recovers every coefficient, over noncommutative coefficient rings. -/
theorem trace_dual_mul (hcentral : ∀ p, Commute p f) (s : ℕ)
    (hs : s < f.natDegree) (p : Polynomial R) :
    trace f (dual f s * p) = (p %ₘ f).coeff (f.natDegree - 1 - s) := by
  nontriviality R
  induction s generalizing p with
  | zero => simp only [dual, one_mul, Nat.sub_zero, trace]
  | succ s ih =>
    have hs' : s < f.natDegree := by omega
    have hi : f.natDegree - 1 - s = (f.natDegree - 1 - (s + 1)) + 1 := by omega
    rw [dual, add_mul, trace_add f hf, mul_assoc, ih hs', trace_C_mul f hf hcentral]
    rw [hi, remainder_X_coeff_succ f hf hcentral p _ (by omega), sub_add_cancel]

omit hf in
theorem coeff_commute (hcentral : ∀ p, Commute p f) (j : ℕ) (r : R) :
    Commute (f.coeff j) r := by
  have h := congrArg (fun p : Polynomial R => p.coeff j) (hcentral (C r)).eq
  change f.coeff j * r = r * f.coeff j
  simpa only [coeff_C_mul, coeff_mul_C] using h.symm

omit hf in
theorem dual_commute (hcentral : ∀ p, Commute p f) (s : ℕ) (p : Polynomial R) :
    Commute (dual f s) p := by
  induction s with
  | zero => exact Commute.one_left p
  | succ s ih =>
    apply Commute.add_left (ih.mul_left (commute_X p))
    change C (f.coeff (f.natDegree - 1 - s)) * p = p * C (f.coeff (f.natDegree - 1 - s))
    ext j
    simp only [coeff_C_mul, coeff_mul_C]
    exact (coeff_commute f hcentral _ _).eq

theorem trace_mul_dual (hcentral : ∀ p, Commute p f) (s : ℕ)
    (hs : s < f.natDegree) (p : Polynomial R) :
    trace f (p * dual f s) = (p %ₘ f).coeff (f.natDegree - 1 - s) := by
  rw [← (dual_commute f hcentral s p).eq, trace_dual_mul f hf hcentral s hs]

/-- Explicit left dual-basis reconstruction, including degree zero. -/
theorem dual_basis (hcentral : ∀ p, Commute p f) (p : Polynomial R) :
    ∑ j : Fin f.natDegree, monomial j (trace f (dual f (f.natDegree - 1 - j) * p)) = p %ₘ f := by
  have he (j : Fin f.natDegree) :
      trace f (dual f (f.natDegree - 1 - j) * p) = (p %ₘ f).coeff j := by
    rw [trace_dual_mul f hf hcentral _ (by omega)]
    congr 1
    omega
  simp_rw [he]
  exact sum_modByMonic_coeff hf degree_le_natDegree

/-- Explicit right dual-basis reconstruction, preserving coefficient order. -/
theorem dual_basis_right (hcentral : ∀ p, Commute p f) (p : Polynomial R) :
    ∑ j : Fin f.natDegree, monomial j (trace f (p * dual f (f.natDegree - 1 - j))) = p %ₘ f := by
  simp_rw [← (dual_commute f hcentral _ p).eq]
  exact dual_basis f hf hcentral p

theorem trace_nondegenerate (hcentral : ∀ p, Commute p f) (p : Polynomial R)
    (hp : ∀ q, trace f (q * p) = 0) : p %ₘ f = 0 := by
  rw [← dual_basis f hf hcentral p]
  simp only [hp, monomial_zero_right, Finset.sum_const_zero]

theorem trace_nondegenerate_right (hcentral : ∀ p, Commute p f) (p : Polynomial R)
    (hp : ∀ q, trace f (p * q) = 0) : p %ₘ f = 0 := by
  rw [← dual_basis_right f hf hcentral p]
  simp only [hp, monomial_zero_right, Finset.sum_const_zero]

/-- Trace-duality against every power below the monic degree. -/
theorem trace_dual_pow (hcentral : ∀ p, Commute p f) (i j : Fin f.natDegree) :
    trace f (dual f (f.natDegree - 1 - i) * X ^ (j : ℕ)) = if i = j then 1 else 0 := by
  nontriviality R
  rw [trace_dual_mul f hf hcentral _ (by omega)]
  have hi : f.natDegree - 1 - (f.natDegree - 1 - i) = i := by omega
  rw [hi, (modByMonic_eq_self_iff hf).2 (by
    rw [degree_X_pow, degree_eq_natDegree hf.ne_zero]; exact_mod_cast j.isLt), coeff_X_pow]
  simp only [Fin.ext_iff]

/-- Additive packaging permits coefficient-ordered finite sums. -/
def traceAddHom : Polynomial R →+ R where
  toFun := trace f
  map_zero' := by simp [trace]
  map_add' := trace_add f hf

theorem trace_mul_expansion (hcentral : ∀ p, Commute p f) (q p : Polynomial R) :
    trace f (q * p) = ∑ j : Fin f.natDegree, (q %ₘ f).coeff j * trace f (X ^ (j : ℕ) * p) := by
  have hq := sum_modByMonic_coeff (p := q) hf degree_le_natDegree
  have hr : trace f (q * p) = trace f ((q %ₘ f) * p) :=
    congrArg (fun t : Polynomial R => t.coeff (f.natDegree - 1)) (remainder_mul_right f hf q p)
  rw [hr]
  conv_lhs => rw [← hq, Finset.sum_mul]
  change traceAddHom f hf _ = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  change trace f (monomial (j : ℕ) ((q %ₘ f).coeff j) * p) = _
  rw [← C_mul_X_pow_eq_monomial, mul_assoc, trace_C_mul f hf hcentral]

/-- The second dual-basis reconstruction; its coefficients stay on the right. -/
theorem dual_basis_swapped (hcentral : ∀ p, Commute p f) (p : Polynomial R) :
    (∑ j : Fin f.natDegree,
      dual f (f.natDegree - 1 - j) * C (trace f (X ^ (j : ℕ) * p))) %ₘ f = p %ₘ f := by
  apply remainder_eq_of_sub f hf
  apply (modByMonic_eq_zero_iff_dvd hf).1
  apply trace_nondegenerate f hf hcentral
  intro q
  rw [mul_sub]
  change traceAddHom f hf _ = _
  rw [map_sub]
  apply sub_eq_zero.mpr
  change trace f _ = trace f _
  rw [Finset.mul_sum]
  change traceAddHom f hf _ = _
  rw [map_sum, trace_mul_expansion f hf hcentral q p]
  apply Finset.sum_congr rfl
  intro j _
  change trace f (q * (dual f (f.natDegree - 1 - j) * C _)) = _
  rw [← mul_assoc, trace_mul_C f hf, trace_mul_dual f hf hcentral _ (by omega)]
  congr 2
  omega

end Categorification.MonicTrace
