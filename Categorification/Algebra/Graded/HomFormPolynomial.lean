/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.Duality
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

/-!
# The graded Hom form of a finite-dimensional algebra is Laurent polynomial

Finite generation gives the homogeneous decomposition of the Hom between
two projectives. Finite-dimensionality of the algebra makes its support
finite. The same conclusion holds on all virtual classes by additivity.
-/

noncomputable section
namespace Categorification.Graded
universe u v
variable {k : Type v} [Field k] {A : Type u} [Ring A] [Algebra k A] [Module.Finite k A]
    (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜] [HasGdim 𝒜]

omit [HasGdim 𝒜] in
/-- The actual Hom polynomial expands to the graded Hom dimension. -/
theorem GProj.toLaurentSeries_homGdimPoly (P Q : GProj 𝒜) :
    toLaurentSeries (gdimPoly (homGrade A P.grading Q.grading)) = P.homGdim Q := by
  let : Module.Finite k P.carrier := Module.Finite.trans A P.carrier
  let : Module.Finite k Q.carrier := Module.Finite.trans A Q.carrier
  let := (isInternal_homGrade 𝒜 P.grading Q.grading).chooseDecomposition
  exact toLaurentSeries_gdimPoly _

/-- Every pair of virtual projectives over a finite-dimensional graded
algebra has an integral Laurent polynomial for its Euler pairing. -/
theorem K0.exists_homForm_polynomial (x y : K0 𝒜) :
    ∃ p : LaurentPolynomial ℤ, toLaurentSeries p = K0.homForm 𝒜 x y := by
  let S := (toLaurentSeries (R := ℤ)).range
  change K0.homForm 𝒜 x y ∈ S
  induction y using K0.induction_on with
  | of Q =>
    induction x using K0.induction_on with
    | of P =>
      rw [K0.homForm_of]
      exact ⟨_, GProj.toLaurentSeries_homGdimPoly 𝒜 P Q⟩
    | zero => simpa only [map_zero, AddMonoidHom.zero_apply] using S.zero_mem
    | add x y hx hy => simpa only [map_add, AddMonoidHom.add_apply] using S.add_mem hx hy
    | neg x hx => simpa only [map_neg, AddMonoidHom.neg_apply] using S.neg_mem hx
  | zero => simpa only [map_zero] using S.zero_mem
  | add _ _ h h' => simpa only [map_add] using S.add_mem h h'
  | neg _ h => simpa only [map_neg] using S.neg_mem h

end Categorification.Graded
