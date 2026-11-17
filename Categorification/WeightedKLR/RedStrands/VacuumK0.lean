/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.ScalarK0
import Categorification.WeightedKLR.RedStrands.StendhalGrading
import Categorification.WeightedKLR.RedStrands.Vacuum

/-!
# The highest-weight summand in Webster's tensor product categorification

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
§4.7, Lemma 4.36 and Theorem 4.38. The tensor product of the highest weight lines
corresponds to the projective with all red strands and no black strands.
-/

namespace Categorification.Stendhal

open Categorification.Graded

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type*} [DecidableEq I] {k : Type*} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}
  (G : KLR.GradingDatum (stendhalQ Q Λ))

local notation "R" => LaurentPolynomial ℤ

/-- The vacuum block in Webster, arXiv:1309.3796v2, §4.7, proof of Lemma 4.36:
the graded projective class of its identity freely generates its Grothendieck group. -/
noncomputable def tensorProductVacuumK0Equiv :
    K0 (tensorProductGrade G (0 : Multiset I)) ≃ₗ[R] R :=
  scalarK0Equiv _ (tensorProductAlgebraZeroEquiv Q Λ).symm

@[simp] theorem tensorProductVacuumK0Equiv_regular :
    tensorProductVacuumK0Equiv G (K0.of (GProj.regular (tensorProductGrade G 0))) = 1 := by
  apply (tensorProductVacuumK0Equiv G).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  change _ = (scalarK0Equiv _ _).symm 1
  rw [scalarK0Equiv_symm_apply, one_smul]

end Categorification.Stendhal
