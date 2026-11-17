/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Mackey.Swap
import Categorification.KLR.KL2.Datum

/-!
# Cartan data from Webster's standing multiplicities

Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4,
§2.1, assigns positive symmetrizers `d_i` and edge multiplicities satisfying
`d_{h(e)} c_e = d_{t(e)} c_ē`. The off-diagonal sums give the Cartan datum
used by the quantum-group map in §2.4, Theorem 2.19, for loop-free graphs.
The construction records the loop-deleted edge data; loop-freeness is imposed
when identifying it with the weighted diagram grading.

The normalization is `i · i = 2 d_i`, `i · j = -d_i m_ij` for `i ≠ j`.
Thus the dots have degree `i · i`, crossings have degree `-i · j`, and the
polynomial `Q_ij` has weighted degree `-2 (i · j)`. The Serre parameter is
`m_ij = -2 (i · j)/(i · i)`, as in KL II arXiv:0804.2080v1, §1.1.
-/

noncomputable section

namespace Categorification.WeightedKLR.WeightedGraph.Standing

open MvPolynomial

variable {I 𝕜 k : Type*} [DecidableEq I] [CommRing k] {Γ : WeightedGraph I 𝕜 k}

/-- The reverse multiplicity `c_ē`, chosen together with the existing `c_e`. -/
def edgeMultRev (hS : Γ.Standing) (e : Γ.E) : ℕ := (hS.isUnitHomogeneous_Q e).choose

omit [DecidableEq I] in
theorem isUnitHomogeneous_Q_rev (hS : Γ.Standing) (e : Γ.E) :
    IsUnitHomogeneous (hS.symm (Γ.head e)) (hS.symm (Γ.tail e))
      (hS.edgeMult e) (hS.edgeMultRev e) (Γ.Q e) :=
  (hS.isUnitHomogeneous_Q e).choose_spec

omit [DecidableEq I] in
theorem symm_pos (hS : Γ.Standing) (i : I) : 0 < hS.symm i := hS.choose_spec.1 i

omit [DecidableEq I] in
theorem edgeMult_balance (hS : Γ.Standing) (e : Γ.E) :
    hS.symm (Γ.head e) * hS.edgeMult e = hS.symm (Γ.tail e) * hS.edgeMultRev e :=
  (hS.isUnitHomogeneous_Q_rev e).1

/-- The pure first-variable exponent of `Q_ij`, summed over both edge directions. -/
def rootMultiplicity (hS : Γ.Standing) (i j : I) : ℕ :=
  (∑ e, if Γ.head e = i ∧ Γ.tail e = j then hS.edgeMult e else 0) +
    ∑ e, if Γ.tail e = i ∧ Γ.head e = j then hS.edgeMultRev e else 0

/-- The standing edge balance makes the total multiplicities symmetrizable. -/
theorem symm_mul_rootMultiplicity (hS : Γ.Standing) (i j : I) :
    hS.symm i * hS.rootMultiplicity i j = hS.symm j * hS.rootMultiplicity j i := by
  classical
  simp only [rootMultiplicity, mul_add, Finset.mul_sum, mul_ite, mul_zero]
  rw [add_comm (∑ e, if Γ.head e = j ∧ Γ.tail e = i then _ else 0)]
  congr 1
  · apply Finset.sum_congr rfl
    intro e _
    by_cases he : Γ.head e = i ∧ Γ.tail e = j
    · simpa [he.1, he.2] using hS.edgeMult_balance e
    · have hf : ¬(Γ.tail e = j ∧ Γ.head e = i) := fun hf => he ⟨hf.2, hf.1⟩
      simp only [he, hf, ite_false]
  · apply Finset.sum_congr rfl
    intro e _
    by_cases he : Γ.tail e = i ∧ Γ.head e = j
    · simpa [he.1, he.2] using (hS.edgeMult_balance e).symm
    · have hf : ¬(Γ.head e = j ∧ Γ.tail e = i) := fun hf => he ⟨hf.2, hf.1⟩
      simp only [he, hf, ite_false]

/-- The Cartan datum of the standing edge multiplicities, with loops omitted.
For a loop-free graph this is the datum in Webster Theorem 2.19. -/
def cartanDatum (hS : Γ.Standing) : QuantumGroup.CartanDatum I where
  dot i j := if i = j then 2 * (hS.symm i : ℤ) else
    -((hS.symm i : ℤ) * hS.rootMultiplicity i j)
  symm i j := by
    by_cases h : i = j
    · subst h; rfl
    · simp only [h, Ne.symm h, ite_false]
      exact congrArg (fun n : ℕ => -(n : ℤ)) (hS.symm_mul_rootMultiplicity i j)
  dot_self_pos i := by simp only [ite_true]; exact mul_pos (by norm_num) (by exact_mod_cast hS.symm_pos i)
  dot_self_even i := by simp only [ite_true]; exact even_two_mul _
  dot_nonpos i j hij := by
    simp only [hij, ite_false]
    exact neg_nonpos.mpr (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  dvd_two_mul i j := by
    simp only [ite_true]
    by_cases hij : i = j
    · subst hij
      simp only [ite_true]
      exact dvd_mul_left _ _
    · simp only [hij, ite_false]
      refine ⟨-(hS.rootMultiplicity i j : ℤ), ?_⟩
      ring

@[simp] theorem cartanDatum_dot_self (hS : Γ.Standing) (i : I) :
    hS.cartanDatum.dot i i = 2 * (hS.symm i : ℤ) := by simp [cartanDatum]

theorem cartanDatum_dot_of_ne (hS : Γ.Standing) {i j : I} (hij : i ≠ j) :
    hS.cartanDatum.dot i j = -((hS.symm i : ℤ) * hS.rootMultiplicity i j) := by
  simp only [cartanDatum, hij, ite_false]

/-- KL II's Serre parameter is the total pure first-variable exponent. -/
theorem cartanDatum_dij (hS : Γ.Standing) {i j : I} (hij : i ≠ j) :
    hS.cartanDatum.dij i j = hS.rootMultiplicity i j := by
  have h := hS.cartanDatum.dij_mul hij
  rw [hS.cartanDatum_dot_self, hS.cartanDatum_dot_of_ne hij] at h
  have hd : (hS.symm i : ℤ) ≠ 0 := by exact_mod_cast (hS.symm_pos i).ne'
  have he : (hS.cartanDatum.dij i j : ℤ) = hS.rootMultiplicity i j := by
    apply mul_right_cancel₀ (mul_ne_zero (by norm_num : (2 : ℤ) ≠ 0) hd)
    nlinarith [h]
  exact_mod_cast he

/-- The standing polynomial degree is the sum of the degrees of its individual
edge walls, in both orientations. -/
theorem symm_mul_rootMultiplicity_eq_wall_sum (hS : Γ.Standing) (i j : I) :
    (hS.symm i : ℤ) * hS.rootMultiplicity i j =
      (∑ e, if i = Γ.head e ∧ j = Γ.tail e then hS.gradingDatum.wall e else 0) +
        ∑ e, if j = Γ.head e ∧ i = Γ.tail e then hS.gradingDatum.wall e else 0 := by
  classical
  simp only [rootMultiplicity, Nat.cast_add, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero,
    mul_add, Finset.mul_sum, mul_ite, mul_zero]
  congr 1
  · apply Finset.sum_congr rfl
    intro e _
    by_cases he : Γ.head e = i ∧ Γ.tail e = j
    · simp [he.1, he.2, gradingDatum_wall]
    · have hf : ¬(i = Γ.head e ∧ j = Γ.tail e) := fun hf => he ⟨hf.1.symm, hf.2.symm⟩
      simp only [he, hf, ite_false]
  · apply Finset.sum_congr rfl
    intro e _
    by_cases he : Γ.tail e = i ∧ Γ.head e = j
    · have hbalance := congrArg (fun n : ℕ => (n : ℤ)) (hS.edgeMult_balance e)
      simpa [he.1, he.2, gradingDatum_wall] using hbalance.symm
    · have hf : ¬(j = Γ.head e ∧ i = Γ.tail e) := fun hf => he ⟨hf.2.symm, hf.1.symm⟩
      simp only [he, hf, ite_false]

/-- For a loop-free graph, crossing degrees in the standing grading are the
negatives of the Cartan pairing, with the canonical dot degree `2 d_i`. -/
theorem pairDeg_eq_neg_cartanDatum_dot (hS : Γ.Standing)
    (hE : ∀ e, Γ.head e ≠ Γ.tail e) (hl : ∀ i, Γ.loop i = none) (i j : I) :
    hS.gradingDatum.pairDeg i j = -hS.cartanDatum.dot i j := by
  classical
  by_cases hij : i = j
  · subst j
    have hn : ∀ e : Γ.E, ¬(i = Γ.head e ∧ i = Γ.tail e) :=
      fun e he => hE e (he.1.symm.trans he.2)
    simp only [GradingDatum.pairDeg, hn, ite_false, Finset.sum_const_zero,
      zero_add, ite_true, gradingDatum_cross_of_none hS (hl i), cartanDatum_dot_self]
  · rw [cartanDatum_dot_of_ne hS hij, neg_neg,
      symm_mul_rootMultiplicity_eq_wall_sum]
    simp only [GradingDatum.pairDeg, hij, ite_false, add_zero]

end Categorification.WeightedKLR.WeightedGraph.Standing
