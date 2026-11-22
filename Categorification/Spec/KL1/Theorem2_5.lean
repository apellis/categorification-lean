/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.KL1Basis
import Categorification.KLR.Grading

/-! # The integral graded corner basis (KL I, arXiv:0803.4121v2, Theorem 2.5) -/

namespace Categorification.Spec.KL1

open Equiv MvPolynomial TypeA KLR KLRAlgebra

/-- Fix the graph and strand content of §2.1, then a minimal presentation of each
permutation as in §2.3. In each corner the indicated bottom-dotted diagrams form
an integral basis consisting of homogeneous elements for the graph grading. -/
theorem theorem_2_5 {I : Type*} [DecidableEq I] (Γ : SimpleGraph I) [DecidableRel Γ.Adj]
    (ν : Multiset I) (ρ : Perm (Fin ν.card) → List ℕ)
    (hρ : ∀ w, IsReduced ν.card (ρ w) ∧ wordProd ν.card (ρ w) = w) (i j : Seq ν) :
    ∃ B : Module.Basis (CornerIdx j i) ℤ (corner (Q := klQ (k := ℤ) Γ) j i),
      ∀ b, (B b : R1 ℤ Γ ν) = ψw (ρ b.1.1) * pol (monomial b.2 1) * e i ∧
        ∃ d : ℤ, (B b : R1 ℤ Γ ν) ∈ (klGradingDatum ℤ Γ).grade ν d := by
  refine ⟨KLR.KL1.cornerBasis ρ hρ j i, fun b => ?_⟩
  have h := KLR.KL1.cornerBasis_apply (k := ℤ) (Γ := Γ) ρ hρ j i b
  refine ⟨h, ?_⟩
  exact ⟨_, Eq.subst (motive := fun z : R1 ℤ Γ ν => z ∈ (klGradingDatum ℤ Γ).grade ν _)
    h.symm ((klGradingDatum ℤ Γ).ψw_mul_pol_monomial_mul_e_mem_grade _ _ _)⟩

end Categorification.Spec.KL1
