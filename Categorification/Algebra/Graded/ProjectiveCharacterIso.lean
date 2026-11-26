/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.ProjectiveCharacter

/-!
# Projective characters of isomorphic modules

The Laurent-polynomial coordinates `[P] ↦ dim_q Hom(P, M)` depend only on the graded
isomorphism class of the finite-dimensional module `M`.
-/

noncomputable section
namespace Categorification.Graded

universe u v
variable {k : Type v} [Field k] {A : Type u} [Ring A] [Algebra k A]
    [Module.Finite k A] (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜]

theorem projectiveHomPolynomial_congr {M N : GFin 𝒜} (e : M.Iso N) :
    projectiveHomPolynomial 𝒜 M = projectiveHomPolynomial 𝒜 N :=
  AddMonoidHom.ext fun x => toLaurentSeries_injective (by
    rw [toLaurentSeries_projectiveHomPolynomial, toLaurentSeries_projectiveHomPolynomial,
      pairingRight_hiso e])

theorem projectiveCharacter_congr {M N : GFin 𝒜} (e : M.Iso N) :
    projectiveCharacter 𝒜 M = projectiveCharacter 𝒜 N :=
  LinearMap.ext fun x => by
    change LaurentPolynomial.invert (projectiveHomPolynomial 𝒜 M x) =
      LaurentPolynomial.invert (projectiveHomPolynomial 𝒜 N x)
    rw [projectiveHomPolynomial_congr 𝒜 e]

end Categorification.Graded
