/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.IdempotentLift
import Categorification.KLR.CyclotomicGrading

/-!
# Lifting graded cyclotomic projectives to affine idempotents

Webster, arXiv:1309.3796v2, proof of Proposition 3.21. For the generation of
cyclotomic projective classes, every indecomposable projective is a shift of
the image of a principal affine projective. Its degree-zero idempotent lifts by
the Fitting decomposition in the finite-dimensional degree-zero affine algebra.
-/

namespace Categorification.KLR.CycKLR

open Categorification.Graded

variable {k I : Type*} [Field k] [DecidableEq I] {Q : I → I → MvPolynomial (Fin 2) k}
    (G : GradingDatum Q) (Λ : I → ℕ) (ν : Multiset I)

local notation "R" => KLRAlgebra k Q ν
local notation "π" => mk k Q (fun i => Polynomial.X ^ Λ i) ν

/-- A degree-zero idempotent of the monomial cyclotomic quotient lifts to a
degree-zero idempotent of the affine algebra. Symmetry of the parameters and
positive dot degrees give finite dimensionality of the affine degree-zero part. -/
theorem exists_idempotent_preimage (hsym : KLRSymm Q) (hX : ∀ i, 0 < G.degX i)
    {e : CycKLR k Q (fun i => Polynomial.X ^ Λ i) ν} (he : IsIdempotentElem e)
    (he0 : e ∈ grade G Λ ν 0) :
    ∃ p : R, IsIdempotentElem p ∧ p ∈ G.grade ν 0 ∧ π p = e := by
  let := (G.hasGdim_grade' (ν := ν) hsym hX).finiteDimensional 0
  exact exists_graded_idempotent_preimage (G.grade ν) (grade G Λ ν) π
    (fun _ _ hx => Graded.mem_map_of_mem _ _ hx) mk_surjective he he0

/-- Every indecomposable graded projective in a cyclotomic block comes from
a degree-zero affine idempotent, up to a grading shift. -/
theorem exists_iso_of_affineIdempotent (hsym : KLRSymm Q) (hX : ∀ i, 0 < G.degX i)
    [HasGdim (grade G Λ ν)] (P : GProj (grade G Λ ν)) (hP : P.IsIndec _) :
    ∃ (p : R) (hp : IsIdempotentElem p) (hp0 : p ∈ G.grade ν 0) (j : ℤ),
      Nonempty (P.Iso ((GProj.ofIdempotent (π p) (hp.map π)
        (Graded.mem_map_of_mem _ _ hp0)).shift j)) := by
  obtain ⟨e, he, he0, j, h⟩ := hP.exists_iso_ofIdempotent
  obtain ⟨p, hp, hp0, rfl⟩ := exists_idempotent_preimage G Λ ν hsym hX he he0
  exact ⟨p, hp, hp0, j, h⟩

end Categorification.KLR.CycKLR
