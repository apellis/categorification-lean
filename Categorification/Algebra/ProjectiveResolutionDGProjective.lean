/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.OrdinaryProjectiveResolutionDG
import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# The dg model of a projective resolution has projective underlying module

The dg model `projectiveResolutionDGModel P` of an ordinary projective resolution
(Webster, arXiv:1309.3796v2, §6.1, p. 65) has underlying module the direct sum of the terms of
the resolution, hence is a projective module. This is the hypothesis under which tensoring
with it is exact in the coefficient (`coefficientTensor_shortExact`).
-/

open CategoryTheory CategoryTheory.Limits ComplexShape DG

noncomputable section

namespace Categorification

universe u

variable {R : Type u} [Ring R] {X : ModuleCat.{u} R} (P : ProjectiveResolution X)

/-- The terms of the extended resolution are projective modules. -/
theorem projectiveResolution_extend_X_projective (n : ℤ) :
    Module.Projective R ((P.complex.extend embeddingDownNat).X n) := by
  let K : CochainComplex (ModuleCat.{u} R) ℤ := P.complex.extend embeddingDownNat
  have : Projective (K.X n) := by
    by_cases hn : n ≤ 0
    · let j := (-n).toNat
      have hj : embeddingDownNat.f j = n := by
        change -(j : ℤ) = n
        dsimp [j]
        omega
      exact Projective.of_iso (P.complex.extendXIso embeddingDownNat hj).symm (P.projective j)
    · exact IsZero.projective (P.complex.isZero_extend_X embeddingDownNat n (by
        intro j hj
        change -(j : ℤ) = n at hj
        omega))
  exact (IsProjective.iff_projective (K.X n)).2 this

/-- **The dg model of a projective resolution is a projective module.** -/
instance projectiveResolutionDGModel_projective :
    Module.Projective R (projectiveResolutionDGModel P) := by
  have := projectiveResolution_extend_X_projective P
  exact Module.Projective.directSum (M := fun n => (P.complex.extend embeddingDownNat).X n)

end Categorification
