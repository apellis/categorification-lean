/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicMixedMate.MixedCrossing

/-!
# The quadratic relation for two appended strands of different colours

Khovanov–Lauda I, §2.1 (the relation `ψ_k² 1_i = Q_{i_k i_{k+1}}(x_k, x_{k+1}) 1_i` for
`i_k ≠ i_{k+1}`), read on the two strands appended last. For `doubleLast Q γ i j`
(append `j`, then `i`):

* `doubleLast_e`: the image of `1_s` is `1_{s j i}`;
* `psi_sq_mul_doubleLast_one`: `ψ_n² · D_{ij}(1) = Q_{ji}(x_n, x_{n+1}) · D_{ij}(1)` for `i ≠ j`,
  where `n = |γ|`;
* `cast_doubleLast_one_mul_psi`: the reverse intertwining `D_{ji}(1) ψ_n = ψ_n D_{ij}(1)`,
  transported to the content of `D_{ij}`.
-/

noncomputable section
namespace Categorification.KLR.KLRAlgebra.AbsentColour.MixedCrossing

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (γ : Multiset I) (i j : I)

theorem doubleLast_e (s : Seq γ) : doubleLast Q γ i j (e s) = e (doubleSeq γ i j s) := by
  change cL Q i ({j} + γ) (cL Q j γ (e s)) = _
  rw [cL_e, cL_e]
  rfl

omit [DecidableEq I] in
theorem card_double : Multiset.card (({i} : Multiset I) + ({j} + γ)) = Multiset.card γ + 2 := by
  simp only [Multiset.card_add, Multiset.card_singleton]
  omega

/-- **The quadratic relation on the two appended strands** (KL I, §2.1): for `i ≠ j`,
`ψ_n² D_{ij}(1) = Q_{ji}(x_n, x_{n+1}) D_{ij}(1)`. -/
theorem psi_sq_mul_doubleLast_one (hij : i ≠ j) :
    (ψ (Multiset.card γ) * ψ (Multiset.card γ) * doubleLast Q γ i j 1 :
        KLRAlgebra k Q ({i} + ({j} + γ))) =
      ncEval ![x ⟨Multiset.card γ, by rw [card_double]; omega⟩,
        x ⟨Multiset.card γ + 1, by rw [card_double]; omega⟩] (Q j i) * doubleLast Q γ i j 1 := by
  rw [← sum_e (k := k) (Q := Q) (ν := γ), map_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hn : Multiset.card γ + 1 < Multiset.card (({i} : Multiset I) + ({j} + γ)) := by
    rw [card_double]; omega
  have h1 : (doubleSeq γ i j s).lbl ⟨Multiset.card γ, by omega⟩ = j :=
    doubleSeq_apply_mid γ i j s _ rfl
  have h2 : (doubleSeq γ i j s).lbl ⟨Multiset.card γ + 1, hn⟩ = i :=
    doubleSeq_apply_last γ i j s _ rfl
  rw [doubleLast_e, ψ_sq _ hn]
  simp only [h1, h2, hij.symm, ite_false]

theorem castKLR_castKLR {μ μ' μ'' : Multiset I} (h : μ = μ') (h' : μ' = μ'')
    (z : KLRAlgebra k Q μ) : castKLR Q h' (castKLR Q h z) = castKLR Q (h.trans h') z := by
  subst h; subst h'; rfl

/-- **The reverse intertwining** on the content of `D_{ij}`: `D_{ji}(1) ψ_n = ψ_n D_{ij}(1)`. -/
theorem cast_doubleLast_one_mul_psi :
    castKLR Q (square γ i j) (doubleLast Q γ j i 1) * ψ (Multiset.card γ) =
      ψ (Multiset.card γ) * doubleLast Q γ i j 1 := by
  have h := congrArg (castKLR Q (square γ i j)) (doubleLast_one_intertwine Q γ j i)
  rwa [map_mul, map_mul, castKLR_ψ, castKLR_castKLR, castKLR_rfl] at h

theorem doubleLast_one_mul_self :
    (doubleLast Q γ i j 1 * doubleLast Q γ i j 1 : KLRAlgebra k Q ({i} + ({j} + γ))) =
      doubleLast Q γ i j 1 := by
  rw [← map_mul, one_mul]


theorem x_commute_doubleLast_one (a : Fin (Multiset.card (({i} : Multiset I) + ({j} + γ)))) :
    Commute (x a : KLRAlgebra k Q ({i} + ({j} + γ))) (doubleLast Q γ i j 1) := by
  rw [← sum_e (k := k) (Q := Q) (ν := γ), map_sum]
  exact Commute.sum_right _ _ _ fun s _ => by rw [doubleLast_e]; exact x_mul_e a _


/-- **Dot slides on the two appended strands** (KL I, §2.1, (2.4) for `i_k ≠ i_{k+1}`):
`(x_n ψ_n - ψ_n x_{n+1}) D_{ij}(1) = 0` for `i ≠ j`. -/
theorem dot_cross_left_mul_doubleLast_one (hij : i ≠ j) :
    ((x ⟨Multiset.card γ, by rw [card_double]; omega⟩ * ψ (Multiset.card γ) -
        ψ (Multiset.card γ) * x ⟨Multiset.card γ + 1, by rw [card_double]; omega⟩) *
        doubleLast Q γ i j 1 : KLRAlgebra k Q ({i} + ({j} + γ))) = 0 := by
  rw [← sum_e (k := k) (Q := Q) (ν := γ), map_sum, Finset.mul_sum]
  refine Finset.sum_eq_zero fun s _ => ?_
  have hn : Multiset.card γ + 1 < Multiset.card (({i} : Multiset I) + ({j} + γ)) := by
    rw [card_double]; omega
  have h1 : (doubleSeq γ i j s).lbl ⟨Multiset.card γ, by omega⟩ = j :=
    doubleSeq_apply_mid γ i j s _ rfl
  have h2 : (doubleSeq γ i j s).lbl ⟨Multiset.card γ + 1, hn⟩ = i :=
    doubleSeq_apply_last γ i j s _ rfl
  rw [doubleLast_e, dot_cross_left _ hn]
  simp only [h1, h2, hij.symm, ite_false]

/-- **Dot slides on the two appended strands** (KL I, §2.1, (2.4) for `i_k ≠ i_{k+1}`):
`(ψ_n x_n - x_{n+1} ψ_n) D_{ij}(1) = 0` for `i ≠ j`. -/
theorem dot_cross_right_mul_doubleLast_one (hij : i ≠ j) :
    ((ψ (Multiset.card γ) * x ⟨Multiset.card γ, by rw [card_double]; omega⟩ -
        x ⟨Multiset.card γ + 1, by rw [card_double]; omega⟩ * ψ (Multiset.card γ)) *
        doubleLast Q γ i j 1 : KLRAlgebra k Q ({i} + ({j} + γ))) = 0 := by
  rw [← sum_e (k := k) (Q := Q) (ν := γ), map_sum, Finset.mul_sum]
  refine Finset.sum_eq_zero fun s _ => ?_
  have hn : Multiset.card γ + 1 < Multiset.card (({i} : Multiset I) + ({j} + γ)) := by
    rw [card_double]; omega
  have h1 : (doubleSeq γ i j s).lbl ⟨Multiset.card γ, by omega⟩ = j :=
    doubleSeq_apply_mid γ i j s _ rfl
  have h2 : (doubleSeq γ i j s).lbl ⟨Multiset.card γ + 1, hn⟩ = i :=
    doubleSeq_apply_last γ i j s _ rfl
  rw [doubleLast_e, dot_cross_right _ hn]
  simp only [h1, h2, hij.symm, ite_false]

end Categorification.KLR.KLRAlgebra.AbsentColour.MixedCrossing
