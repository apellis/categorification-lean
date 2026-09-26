/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Crystal.SimpleTensor
import Categorification.KLR.Simple

/-!
# Graded modules satisfy the hypotheses of the crystal lemmas

Khovanov–Lauda I (arXiv:0803.4121v2), §3.2 works with graded finite-dimensional `R(ν)`-modules.
The ungraded results of `Categorification.KLR.Crystal` (Lemmas 3.6–3.8, Proposition 3.10,
Corollary 3.12) assume that the module is finite-dimensional, simple as an ungraded module, and
that the dots act nilpotently. This file records that these hypotheses hold for the simple graded
modules of the paper:

* `KLRAlgebra.smulNilpotent_x_of_graded` : on a finite-dimensional graded `R(ν)`-module the dots
  act nilpotently, for any grading datum with dots of positive degree (`x_a 1_i` raises the degree
  by `degX(i_a) > 0` and the module is bounded);
* simple graded modules are finite-dimensional and simple as ungraded modules (KL I Proposition
  2.12, `KLRAlgebra.finiteDimensional_of_isGradedSimple`,
  `KLRAlgebra.isSimpleModule_of_isGradedSimple`), recalled in `crystal_hypotheses_of_isGradedSimple`.
-/

noncomputable section

namespace Categorification.KLR

open Graded DirectSum MvPolynomial

variable {I : Type*} [DecidableEq I]

namespace KLRAlgebra

variable {K : Type*} [Field K] {Q : I → I → MvPolynomial (Fin 2) K} {ν : Multiset I}
  (G : GradingDatum Q) (hG : ∀ a, 0 < G.degX a)
  {M : Type*} [AddCommGroup M] [Module K M] [Module (KLRAlgebra K Q ν) M]
  [IsScalarTower K (KLRAlgebra K Q ν) M]
  (ℳ : ℤ → Submodule K M) [Decomposition ℳ] [SetLike.GradedSMul (G.grade ν) ℳ]

omit [IsScalarTower K (KLRAlgebra K Q ν) M] in
include hG ℳ in
/-- **The dots act nilpotently on a finite-dimensional graded `R(ν)`-module** (for a grading
datum with dots of positive degree). -/
theorem smulNilpotent_x_of_graded [FiniteDimensional K M] (a : Fin (Multiset.card ν)) :
    SmulNilpotent (x a : KLRAlgebra K Q ν) M := by
  obtain ⟨L, U, hLU⟩ := Graded.exists_bounds (ℳ := ℳ)
  refine ⟨(U - L + 1).toNat, fun v => ?_⟩
  set N := (U - L + 1).toNat
  -- homogeneous vectors
  have hhom : ∀ (d : ℤ) (w : M), w ∈ ℳ d → (x a : KLRAlgebra K Q ν) ^ N • w = 0 := by
    intro d w hw
    by_cases hd : L ≤ d ∧ d ≤ U
    · have hN1 : N ≠ 0 := by simp only [N]; omega
      have hNZ : ((N : ℕ) : ℤ) = U - L + 1 := by simp only [N]; omega
      rw [← one_smul (KLRAlgebra K Q ν) w, ← sum_e, Finset.sum_smul, Finset.smul_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      have hpow : (x a : KLRAlgebra K Q ν) ^ N * e i = (x a * e i) ^ N := by
        have hc : Commute (x a : KLRAlgebra K Q ν) (e i) := x_mul_e a i
        have hi : IsIdempotentElem (e i : KLRAlgebra K Q ν) := e_mul_self i
        obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hN1
        rw [hc.mul_pow, hn, hi.pow_succ_eq]
      rw [smul_smul, hpow]
      have hmem := SetLike.GradedSMul.smul_mem
        (SetLike.pow_mem_graded N (G.x_mul_e_mem_grade a i)) hw
      have hdeg := hG (i.lbl a)
      rw [hLU _ (Or.inr (by rw [vadd_eq_add, nsmul_eq_mul]; nlinarith)), Submodule.mem_bot] at hmem
      exact hmem
    · have : ℳ d = ⊥ := hLU d (by omega)
      rw [this, Submodule.mem_bot] at hw
      rw [hw, smul_zero]
  induction v using DirectSum.Decomposition.inductionOn ℳ with
  | zero => rw [smul_zero]
  | homogeneous w => exact hhom _ w w.2
  | add v w hv hw => rw [smul_add, hv, hw, add_zero]

variable {P : I → I → MvPolynomial (Fin 2) K}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)

include hPQ hP hG in
/-- A simple graded `R(ν)`-module (grading datum with dots of positive degree) satisfies the
hypotheses of the ungraded crystal lemmas: it is finite-dimensional, simple as an ungraded module,
and the dots act nilpotently. -/
theorem crystal_hypotheses_of_isGradedSimple (hS : IsGradedSimple (G.grade ν) ℳ) :
    FiniteDimensional K M ∧ IsSimpleModule (KLRAlgebra K Q ν) M ∧
      ∀ a, SmulNilpotent (x a : KLRAlgebra K Q ν) M := by
  haveI := finiteDimensional_of_isGradedSimple hPQ hP G hG ℳ hS
  exact ⟨this, isSimpleModule_of_isGradedSimple hPQ hP G hG ℳ hS,
    fun a => smulNilpotent_x_of_graded G hG ℳ a⟩

end KLRAlgebra

end Categorification.KLR
