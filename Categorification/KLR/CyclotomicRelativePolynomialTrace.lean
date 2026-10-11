/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.MonicTrace
import Categorification.KLR.CyclotomicSplit

/-!
# Relative polynomial trace over the actual cyclotomic coefficient ring

For arbitrary beta, including nonzero beta, this applies `MonicTrace` to the
source-defined central monic polynomial `aMonicL` in `CycKLR k Q a beta[t]`.
The value lies in the actual, generally noncommutative, cyclotomic algebra.
Left/right coefficient linearity and dual-basis recovery modulo `aMonicL`
are theorems. They do not assume relative Frobenius identities.

The specialization retains the domain, nonzero factorization, unit-leading-
coefficient and monicity assumptions of the existing `CyclotomicSplit` proofs
of monicity and centrality. The underlying polynomial theorem only needs a ring,
monicity and centrality and permits zero divisors and the zero ring.

Kang–Kashiwara §4.2 supplies the polynomial-coordinate splitting, not an
identification of this polynomial quotient with the entire induction corner.
The remaining nonzero-beta step is to descend a trace through the actual corner
presentation, including its crossing/lower-tensor summand, and prove duality for
the actual induction/restriction bimodules. No such descent, adjunction, grading,
or prescribed-mixed-map compatibility is asserted here.
-/

noncomputable section
namespace Categorification.KLR.KLRAlgebra.RelativePolynomialTrace
open Polynomial
variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} (i : I) (β : Multiset I) (a : I → Polynomial k)
local notation "R" => CycKLR k Q a β

def trace (p : Polynomial R) : R := MonicTrace.trace (aMonicL Q i β a) p

variable [IsDomain k] {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ c d, c ≠ d → Q c d = P d c * MvPolynomial.rename ![1, 0] (P c d))
  (hP : ∀ c d, c ≠ d → P c d ≠ 0)
  (hQ : ∀ c d, c ≠ d → IsUnit (polyInY (Q c d)).leadingCoeff)
  (ha : (a i).Monic)
include hPQ hP hQ ha

theorem trace_C_mul (r : R) (p : Polynomial R) :
    trace i β a (C r * p) = r * trace i β a p :=
  MonicTrace.trace_C_mul _ (monic_aMonicL i β a (sym_of_factor hPQ) hQ ha)
    (aMonicL_comm hPQ hP i β a) r p

omit hP in
theorem trace_mul_C (p : Polynomial R) (r : R) :
    trace i β a (p * C r) = trace i β a p * r :=
  MonicTrace.trace_mul_C _ (monic_aMonicL i β a (sym_of_factor hPQ) hQ ha) p r

theorem dual_basis (p : Polynomial R) :
    ∑ j : Fin (aMonicL Q i β a).natDegree,
      monomial j (trace i β a (MonicTrace.dual (aMonicL Q i β a)
        ((aMonicL Q i β a).natDegree - 1 - j) * p)) = p %ₘ aMonicL Q i β a :=
  MonicTrace.dual_basis _ (monic_aMonicL i β a (sym_of_factor hPQ) hQ ha)
    (aMonicL_comm hPQ hP i β a) p

theorem dual_basis_swapped (p : Polynomial R) :
    (∑ j : Fin (aMonicL Q i β a).natDegree,
      MonicTrace.dual (aMonicL Q i β a) ((aMonicL Q i β a).natDegree - 1 - j) *
        C (trace i β a (X ^ (j : ℕ) * p))) %ₘ aMonicL Q i β a = p %ₘ aMonicL Q i β a :=
  MonicTrace.dual_basis_swapped _ (monic_aMonicL i β a (sym_of_factor hPQ) hQ ha)
    (aMonicL_comm hPQ hP i β a) p

theorem trace_nondegenerate (p : Polynomial R) (hp : ∀ q, trace i β a (q * p) = 0) :
    p %ₘ aMonicL Q i β a = 0 :=
  MonicTrace.trace_nondegenerate _ (monic_aMonicL i β a (sym_of_factor hPQ) hQ ha)
    (aMonicL_comm hPQ hP i β a) p hp

end Categorification.KLR.KLRAlgebra.RelativePolynomialTrace
