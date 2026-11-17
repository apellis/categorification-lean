/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.KrullSchmidt
import Categorification.KLR.CyclotomicFinite
import Categorification.KLR.CyclotomicGrading
import Mathlib.LinearAlgebra.DirectSum.Basis

/-!
# Freeness of the cyclotomic projective Grothendieck group

Kang–Kashiwara, arXiv:1102.4677v4, §6, proof of Theorem 6.2, and Webster,
arXiv:1309.3796v2, §3.4, proof of Proposition 3.21. The graded projective
Grothendieck group of the cyclotomic algebra, summed over every root content,
is free over the Laurent polynomials. Its basis consists of indecomposable
graded projectives up to shift in each summand.
-/

noncomputable section

namespace Categorification.KLR.CycKLR

open Categorification.Graded Polynomial
open scoped DirectSum

section Ring

variable {k I : Type*} [CommRing k] [DecidableEq I] {Q : I → I → MvPolynomial (Fin 2) k}
    (G : GradingDatum Q) (Λ : I → ℕ)


/-- The graded projective Grothendieck group in Webster, arXiv:1309.3796v2,
Proposition 3.21, with the summands indexed by black-strand root content. -/
abbrev projectiveK0 := ⨁ ν : Multiset I, K0 (grade G Λ ν)

end Ring

variable {k I : Type*} [Field k] [DecidableEq I] {Q : I → I → MvPolynomial (Fin 2) k}
    (G : GradingDatum Q) (Λ : I → ℕ)

local notation "LP" => LaurentPolynomial ℤ

/-- The indecomposable basis of the total cyclotomic projective Grothendieck group,
as used in Kang–Kashiwara, arXiv:1102.4677v4, §6, proof of Theorem 6.2. -/
def projectiveK0Basis (hQ : ∀ i j, i ≠ j → IsUnit (polyInY (Q i j)).leadingCoeff) :
    Module.Basis (Σ ν : Multiset I, GProj.IndecClass (grade G Λ ν)) LP (projectiveK0 G Λ) := by
  apply DFinsupp.basis
  intro ν
  letI := module_finite (ν := ν) hQ (fun i => monic_X_pow (R := k) (Λ i))
  letI := HasGdim.of_finiteDimensional (grade G Λ ν)
  exact K0.indecBasis _

theorem projectiveK0Basis_apply (hQ : ∀ i j, i ≠ j → IsUnit (polyInY (Q i j)).leadingCoeff)
    (ν : Multiset I) (b : GProj.IndecClass (grade G Λ ν)) :
    projectiveK0Basis G Λ hQ ⟨ν, b⟩ =
      DirectSum.of (fun μ => K0 (grade G Λ μ)) ν (K0.of b.rep) := by
  classical
  let (μ : Multiset I) := module_finite (ν := μ) hQ (fun i => monic_X_pow (R := k) (Λ i))
  let (μ : Multiset I) := HasGdim.of_finiteDimensional (grade G Λ μ)
  simp [projectiveK0Basis, DFinsupp.basis, Module.Basis.coe_ofRepr, DirectSum.of]
  rfl

theorem projectiveK0_free (hQ : ∀ i j, i ≠ j → IsUnit (polyInY (Q i j)).leadingCoeff) :
    Module.Free LP (projectiveK0 G Λ) :=
  Module.Free.of_basis (projectiveK0Basis G Λ hQ)

end Categorification.KLR.CycKLR
