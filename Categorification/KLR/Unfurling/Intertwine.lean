/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Unfurling.Cover
import Categorification.KLR.Unfurling.Substitution
import Categorification.KLR.Unfurling.Target

/-!
# Unfurling: crossings and the substitution map

For an unfurling datum `D` (Webster, arXiv:1603.06311v3, §3.3), the substitution
`γ_P : Pol_ν → Pol_ν̃` (`Unfurling.polySubst`) relates the crossing `ψ_j` of `R(ν)` to the
crossing `ψ_j` of the unfurled KLR algebra (parameters `unfP D.arrows`) on each summand `t`
of the output, in the three cases of Webster's formulas (labels `com0newer`,
`com0newerer`):

* labels `π t_j ≠ π t_{j+1}`: `γ_P ψ = P°(y_j, y_{j+1}) · ψ̃ γ_P` (`polySubst_opΨ_of_ne_colour`);
* `t_j = t_{j+1}`: `h(y_j, y_{j+1}) · γ_P ψ = ψ̃ γ_P`, where `ϖ(x) - ϖ(y) = (x - y) h(x, y)`
  (`polySubst_opΨ_of_eq_label`);
* `π t_j = π t_{j+1}`, `t_j ≠ t_{j+1}`:
  `(ϖ_{t_j}(y_j) - ϖ_{t_{j+1}}(y_{j+1})) · γ_P ψ = γ_P - ψ̃ γ_P` (`polySubst_opΨ_of_ne_label`).

In the completion the factors `h` and `ϖ_a(x) - ϖ_b(y)` (`a ≠ b`) are invertible: their
constant terms are `ϖ'(0) ≠ 0` and `ϖ_a(0) - ϖ_b(0) ≠ 0`.
-/

namespace Categorification.KLR.Unfurling

open MvPolynomial TypeA PolyRep

variable {I J : Type*} {k : Type*} [Field k]
  {P : I → I → MvPolynomial (Fin 2) k} (D : UnfurlingDatum k P J)

/-- The divided difference `h_j(x, y) = (ϖ_j(x) - ϖ_j(y)) / (x - y)`. -/
noncomputable def pwDiff (j : J) : MvPolynomial (Fin 2) k := ddiff 0 1 (pwAt D.pw j 0)

theorem X_sub_X_mul_pwDiff (j : J) :
    (X 0 - X 1) * pwDiff D j = pwAt D.pw j 0 - pwAt D.pw j 1 := by
  rw [pwDiff, ddiff_spec (by decide), pwAt, pwAt, ← Polynomial.aeval_algHom_apply, rename_X,
    Equiv.swap_apply_left]

theorem coeff_single_aeval_X {σ : Type*} [DecidableEq σ] (a b : σ) (q : Polynomial k) :
    (Polynomial.aeval (X b : MvPolynomial σ k) q).coeff (Finsupp.single a 1) =
      if b = a then q.coeff 1 else 0 := by
  rw [Polynomial.aeval_eq_sum_range, coeff_sum]
  simp only [coeff_smul, X_pow_eq_monomial, coeff_monomial, Finsupp.single_eq_single_iff,
    smul_eq_mul]
  by_cases hb : b = a
  · subst hb
    simp only [true_and, one_ne_zero, and_false, or_false, mul_ite, mul_one, mul_zero, ite_true]
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · have : q.natDegree < 1 := by simpa using h
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt this]
  · simp [hb]

/-- The constant term of `h_j` is the linear coefficient of `ϖ_j`. -/
theorem constantCoeff_pwDiff (j : J) : constantCoeff (pwDiff D j) = (D.pw j).coeff 1 := by
  have key : ((X 0 - X 1) * pwDiff D j).coeff (Finsupp.single 0 1) =
      (pwAt D.pw j 0 - pwAt D.pw j 1 : MvPolynomial (Fin 2) k).coeff (Finsupp.single 0 1) := by
    rw [X_sub_X_mul_pwDiff]
  rw [pwAt, pwAt, coeff_sub, coeff_single_aeval_X, coeff_single_aeval_X, sub_mul, coeff_sub,
    coeff_X_mul', coeff_X_mul'] at key
  rw [constantCoeff_eq]
  simpa [Finsupp.single_apply] using key

variable {ν : Multiset I} {ν' : Multiset J} (hν : ν'.map D.π = ν)

theorem lt_card_of_lt (hν : ν'.map D.π = ν) {j : ℕ} (h : j + 1 < Multiset.card ν) :
    j + 1 < Multiset.card ν' := by
  rwa [← card_eq D.π hν]

/-- Substituting into a polynomial in the two variables `x_j, x_{j+1}`. -/
theorem substAt_rename_pair (t : Seq ν') {j : ℕ} (h : j + 1 < Multiset.card ν)
    (F : MvPolynomial (Fin 2) k) :
    substAt D.π D.pw hν t (rename ![(⟨j, by omega⟩ : Fin (Multiset.card ν)), ⟨j + 1, h⟩] F) =
      rename ![(⟨j, by have := lt_card_of_lt D hν h; omega⟩ : Fin (Multiset.card ν')),
          ⟨j + 1, lt_card_of_lt D hν h⟩]
        (aeval ![Polynomial.aeval (X 0) (D.pw (t.lbl ⟨j, by have := lt_card_of_lt D hν h; omega⟩)),
          Polynomial.aeval (X 1) (D.pw (t.lbl ⟨j + 1, lt_card_of_lt D hν h⟩))] F) := by
  rw [substAt, aeval_rename, ← AlgHom.comp_apply, comp_aeval]
  congr 1
  ext1 c
  fin_cases c <;>
  · simp only [aeval_X, Function.comp_apply, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    rw [← Polynomial.aeval_algHom_apply, rename_X]
    rfl

variable [DecidableEq I] [DecidableEq J]

/-- Webster's (label `com0newerer`): a crossing of strands of distinct colours. -/
theorem polySubst_opΨ_of_ne_colour {j : ℕ} (h : j + 1 < Multiset.card ν) (p : Pol k ν)
    (t : Seq ν')
    (hne : D.π (t.lbl ⟨j, by have := lt_card_of_lt D hν h; omega⟩) ≠
      D.π (t.lbl ⟨j + 1, lt_card_of_lt D hν h⟩)) :
    polySubst D.π D.pw hν (opΨ P j p) t =
      rename ![(⟨j, by have := lt_card_of_lt D hν h; omega⟩ : Fin (Multiset.card ν')),
          ⟨j + 1, lt_card_of_lt D hν h⟩]
        (D.unit (t.lbl ⟨j, by have := lt_card_of_lt D hν h; omega⟩)
          (t.lbl ⟨j + 1, lt_card_of_lt D hν h⟩)) *
      opΨ (unfP D.arrows) j (polySubst D.π D.pw hν p) t := by
  have h' := lt_card_of_lt D hν h
  rw [polySubst_opΨ_of_ne D.π D.pw hν P h p t hne, substAt_rename_pair D hν t h]
  erw [D.factor _ _ hne]
  rw [opΨ_apply _ j h', crossComp, ite_eq_right_of_eq_false _ _ (eq_false (by
      rw [GradingDatum.lbl_sadj_smul, GradingDatum.lbl_sadj_smul, sadj_apply_left h',
        sadj_apply_right h']
      intro e; exact hne (by rw [e]))),
    LinearMap.comp_apply, LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply,
    GradingDatum.lbl_sadj_smul, GradingDatum.lbl_sadj_smul, sadj_apply_left h',
    sadj_apply_right h', map_mul, unfP, mul_assoc, mul_left_comm]

end Categorification.KLR.Unfurling
