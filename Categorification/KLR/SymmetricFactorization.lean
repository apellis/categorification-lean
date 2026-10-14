/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.BaseChange
import Categorification.KLR.CyclotomicFinite

/-!
# Symmetric KLR data admit a factorization

Kang–Kashiwara, arXiv:1102.4677v4, §3, assume `Q_{ij}(u,v) = Q_{ji}(v,u)` for `i ≠ j`
(`KLRSymm Q`). Several results of this library are proved through the polynomial
representation and are stated under a factorization

`Q_{ij}(u, v) = P_{ji}(u, v) · P_{ij}(v, u)` with all `P_{ij} ≠ 0`.

Over any commutative ring this factorization follows from the symmetry: choose a well-order
`<` on `I` and put `P_{ij} = Q_{ij}(v, u)` for `i < j` and `P_{ij} = 1` otherwise
(`symmP`). The factors are nonzero as soon as the off-diagonal `Q_{ij}` are, which holds
when `polyInY (Q_{ij})` has a unit leading coefficient over a nontrivial ring.

So every statement of the library carrying the factorization hypotheses `hPQ`, `hP` holds
under `KLRSymm Q` and unit leading coefficients, which are Kang–Kashiwara's hypotheses.
-/

namespace Categorification.KLR

open MvPolynomial

variable {I : Type*} {k : Type*} [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k)

open Classical in
/-- The factor `P_{ab}`: `Q_{ab}(v, u)` when `a < b` in the well-order `univLt`, and `1`
otherwise. -/
noncomputable def symmP (a b : I) : MvPolynomial (Fin 2) k :=
  if univLt a b then rename ![1, 0] (Q a b) else 1

/-- Symmetric KLR data factor as `Q_{ab}(u, v) = P_{ba}(u, v) P_{ab}(v, u)`. -/
theorem symmP_factor (hsym : KLRSymm Q) (a b : I) (hab : a ≠ b) :
    Q a b = symmP Q b a * rename ![1, 0] (symmP Q a b) := by
  rcases univLt_total hab with h | h
  · simp only [symmP, h, univLt_asymm h, ↓reduceIte, one_mul, rename_swap_rename_swap]
  · simp only [symmP, h, univLt_asymm h, ↓reduceIte, map_one, mul_one]
    rw [hsym a b hab, rename_swap_rename_swap]

/-- The factors are nonzero when the off-diagonal `Q_{ab}` are. -/
theorem symmP_ne_zero [Nontrivial k] (hQ : ∀ a b : I, a ≠ b → Q a b ≠ 0) (a b : I) (hab : a ≠ b) :
    symmP Q a b ≠ 0 := by
  unfold symmP
  split_ifs
  · exact fun h => hQ a b hab
      (rename_injective _ (fun s t hst => by fin_cases s <;> fin_cases t <;> simp_all)
        (h.trans (map_zero _).symm))
  · exact one_ne_zero

/-- Over a nontrivial ring, a unit leading coefficient of `polyInY q` forces `q ≠ 0`. -/
theorem ne_zero_of_isUnit_leadingCoeff [Nontrivial k] {q : MvPolynomial (Fin 2) k}
    (hq : IsUnit (polyInY q).leadingCoeff) : q ≠ 0 := by
  rintro rfl
  simp [polyInY] at hq

/-- Kang–Kashiwara's hypotheses on `Q` (symmetry and unit leading coefficients) give the
factorization hypotheses used by the polynomial-representation arguments of this library. -/
theorem factorization_of_symm [Nontrivial k] (hsym : KLRSymm Q)
    (hQ : ∀ a b : I, a ≠ b → IsUnit (polyInY (Q a b)).leadingCoeff) :
    (∀ a b, a ≠ b → Q a b = symmP Q b a * rename ![1, 0] (symmP Q a b)) ∧
      ∀ a b, a ≠ b → symmP Q a b ≠ 0 :=
  ⟨symmP_factor Q hsym, symmP_ne_zero Q fun a b hab =>
    ne_zero_of_isUnit_leadingCoeff (hQ a b hab)⟩

omit Q in
/-- Kang–Kashiwara's hypothesis that the leading coefficient of `Q_{ij}` in the second variable
is a unit constant `t_{i,j;−a_{ij},0} ∈ kˣ` gives a unit leading coefficient of `polyInY`. -/
theorem isUnit_of_leadConst {q : MvPolynomial (Fin 2) k}
    (hq : ∃ c : k, IsUnit c ∧ (polyInY q).leadingCoeff = Polynomial.C c) :
    IsUnit (polyInY q).leadingCoeff := by
  obtain ⟨c, hc, h⟩ := hq
  rw [h]
  exact hc.map Polynomial.C

/-- Over an integral domain, a unit leading coefficient of `polyInY q` is a unit constant. -/
theorem leadConst_of_isUnit [IsDomain k] {q : MvPolynomial (Fin 2) k}
    (hq : IsUnit (polyInY q).leadingCoeff) :
    ∃ c : k, IsUnit c ∧ (polyInY q).leadingCoeff = Polynomial.C c := by
  obtain ⟨c, hc, h⟩ := Polynomial.isUnit_iff.1 hq
  exact ⟨c, hc, h.symm⟩

end Categorification.KLR
