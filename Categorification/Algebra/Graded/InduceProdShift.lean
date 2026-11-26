/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.BalancedInduction
import Categorification.Algebra.Graded.ProjectiveCharacter

/-!
# Induction along a graded bimodule: direct sums and shifts

Tensoring with a finite-dimensional graded bimodule `M` commutes with direct sums and grading
shifts (`GFin.induceProdIso`, `GFin.induceShiftIso`), and Hom polynomials into a shifted module
are multiplied by `q^a` (`projectiveHomPolynomial_shift`). These are the inputs for reading the
braiding functors of B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v2, §6.1, on Grothendieck groups.

## Main definitions and results

* `GFin.induceProdIso` : `M ⊗_A (N ⊕ N') ≅ (M ⊗_A N) ⊕ (M ⊗_A N')`.
* `GFin.induceShiftIso` : `M ⊗_A (N{a}) ≅ (M ⊗_A N){a}`.
* `projectiveHomPolynomial_shift` : `gdim HOM(x, M{a}) = q^a gdim HOM(x, M)`.
-/

noncomputable section

namespace Categorification.Graded

open DirectSum MulOpposite BalancedTensor

universe u v

section Induce

variable {k : Type*} [Field k] {A B : Type u} [Ring A] [Algebra k A] [Ring B] [Algebra k B]
  (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜] (ℬ : ℤ → Submodule k B)
  {M : Type u} [AddCommGroup M] [Module k M] [Module B M] [IsScalarTower k B M]
  [Module Aᵐᵒᵖ M] [SMulCommClass B Aᵐᵒᵖ M] [IsScalarTower k Aᵐᵒᵖ M]
  (ℳ : ℤ → Submodule k M) [Decomposition ℳ] [SetLike.GradedSMul ℬ ℳ]
  [SetLike.GradedSMul (oppositeGrade 𝒜) ℳ] [Module.Finite k M]

/-- `M ⊗_A (N ⊕ N') ≅ (M ⊗_A N) ⊕ (M ⊗_A N')`. -/
def GFin.induceProdIso (N N' : GFin 𝒜) :
    (GFin.induce 𝒜 ℬ ℳ (N.prod N')).Iso ((GFin.induce 𝒜 ℬ ℳ N).prod (GFin.induce 𝒜 ℬ ℳ N')) :=
  GradedEquiv.ofPreserves (prodRight k B A M N.carrier N'.carrier) fun _ _ hy =>
    balancedGrading_map_mem
      (fun d => ((GFin.induce 𝒜 ℬ ℳ N).prod (GFin.induce 𝒜 ℬ ℳ N')).grading d)
      ((prodRight k B A M N.carrier N'.carrier).toLinearMap.restrictScalars k)
      (fun _ j _ n hm (hn : n ∈ Graded.prod N.grading N'.grading j) =>
        ⟨tmul_mem_balancedGrading (B := B) (A := A) hm (mem_prod.1 hn).1,
          tmul_mem_balancedGrading (B := B) (A := A) hm (mem_prod.1 hn).2⟩) hy

/-- `M ⊗_A (N{a}) ≅ (M ⊗_A N){a}`. -/
def GFin.induceShiftIso (N : GFin 𝒜) (a : ℤ) :
    (GFin.induce 𝒜 ℬ ℳ (N.shift a)).Iso ((GFin.induce 𝒜 ℬ ℳ N).shift a) :=
  GradedEquiv.ofPreserves (LinearEquiv.refl _ _) fun _ _ hy =>
    balancedGrading_map_mem (fun d => ((GFin.induce 𝒜 ℬ ℳ N).shift a).grading d)
      (LinearMap.id (R := k)) (fun i j _ _ hm hn => by
        change _ ∈ balancedGrading B A ℳ N.grading (i + j - a)
        rw [show i + j - a = i + (j - a) by ring]
        exact tmul_mem_balancedGrading hm hn) hy

end Induce

section Shift

variable {k : Type v} [Field k] {A : Type u} [Ring A] [Algebra k A]
    [Module.Finite k A] (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜]

/-- Shifting the target: `gdim HOM(x, M{a}) = q^a gdim HOM(x, M)`. -/
theorem projectiveHomPolynomial_shift (M : GFin 𝒜) (a : ℤ) (x : K0 𝒜) :
    projectiveHomPolynomial 𝒜 (M.shift a) x =
      LaurentPolynomial.T a * projectiveHomPolynomial 𝒜 M x := by
  induction x using K0.induction_on with
  | of P =>
    apply toLaurentSeries_injective
    rw [toLaurentSeries_projectiveHomPolynomial, toLaurentSeries_T_mul,
      toLaurentSeries_projectiveHomPolynomial, pairingRight_of, pairingRight_of]
    unfold pairingGdim
    rw [← gdim_shift]
    congr 1
    funext d
    exact homGrade_shift_right a d
  | zero => simp
  | add _ _ hx hy => rw [map_add, map_add, hx, hy, mul_add]
  | neg _ hx => rw [map_neg, map_neg, hx, mul_neg]

end Shift

end Categorification.Graded
