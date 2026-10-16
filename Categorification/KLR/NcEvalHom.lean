/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Basic

/-!
# Evaluating polynomials at commuting elements

For pairwise commuting elements `y` of a `k`-algebra, the noncommutative evaluation
`KLR.ncEval y` (used to write down the relations of `R(ν)`) is an algebra homomorphism out of the
polynomial ring (`exists_algHom_ncEval`).
-/

namespace Categorification.KLR

open MvPolynomial

variable {k : Type*} [CommRing k] {A : Type*} [Ring A] [Algebra k A]

open scoped IsMulCommutative in
/-- Evaluation of polynomials at pairwise commuting elements is an algebra homomorphism. -/
theorem exists_algHom_ncEval {n : ℕ} (y : Fin n → A) (hc : ∀ a b, Commute (y a) (y b)) :
    ∃ φ : MvPolynomial (Fin n) k →ₐ[k] A, (∀ a, φ (X a) = y a) ∧ ∀ p, ncEval y p = φ p := by
  set R := Algebra.adjoin k (Set.range y)
  have := Algebra.isMulCommutative_adjoin k (s := Set.range y)
    (by rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ _; exact hc a b)
  let y' : Fin n → R := fun a => ⟨y a, Algebra.subset_adjoin ⟨a, rfl⟩⟩
  refine ⟨R.val.comp (aeval y'), fun a => by simp [y'], fun p => ?_⟩
  have hval : ncEval y p = R.val (ncEval y' p) := by
    simp only [ncEval, Finsupp.sum, map_sum, map_mul, AlgHom.commutes, map_list_prod,
      List.map_ofFn, Function.comp_def, map_pow]
    rfl
  have haeval : ncEval y' p = aeval y' p := by
    simp only [ncEval, aeval_def, eval₂]
    refine Finsupp.sum_congr fun s _ => ?_
    rw [List.prod_ofFn, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rw [hval, haeval]
  rfl

end Categorification.KLR
