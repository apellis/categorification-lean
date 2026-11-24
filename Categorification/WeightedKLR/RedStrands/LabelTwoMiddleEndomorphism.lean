/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoMiddleDetection
import Categorification.WeightedKLR.RedStrands.LabelTwoPolynomialPresentation

/-!
# The diagrammatic endomorphism algebra of the label-two middle standard

Webster, arXiv:1309.3796v2, §8.2, preceding Proposition 8.4. The algebra
of endomorphisms of the standard at red–black–red–black is
`k[y₁,y₂]/(y₁²,y₂²)`, with its two generators acting by the actual dots.
-/

noncomputable section

namespace Categorification.Stendhal.LabelTwo

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable (k : Type) [Field k]

local notation "ν₂" => (({()} : Multiset Unit) + {()})
local notation "A" => TensorProductAlgebra k (parameter k) weights ν₂
local notation "U" => (MvPolynomial (Fin 2) k) ⧸ middleDotIdeal k
local notation "V" => Module.End A (Standard k)

private theorem quotient_finrank : Module.finrank k U = 4 :=
  Webster.LabelTwo.finrank_squareQuotient k

private theorem end_finrank : Module.finrank k V = 4 := by
  have : Module.Finite k U := Module.finite_of_finrank_pos (by rw [quotient_finrank]; decide)
  have hf := middleDotQuotientAction_surjective k
  have : Module.Finite k V :=
    Module.Finite.of_surjective (middleDotQuotientAction k).toLinearMap hf
  have h₁ := LinearMap.finrank_le_finrank_of_surjective
    (f := (middleDotQuotientAction k).toLinearMap) hf
  have h₂ := LinearMap.finrank_le_finrank_of_surjective
    (f := standardEnd_detectFactors k) (standardEnd_detectFactors_surjective k)
  rw [quotient_finrank] at h₁
  rw [separatedFactors_finrank] at h₂
  exact le_antisymm h₁ h₂

/-- Webster, arXiv:1309.3796v2, §8.2, Proposition 8.4 input. The
two-variable square-zero quotient is the endomorphism algebra of
the actual middle standard, via the two black dots. -/
def middleEndomorphismEquiv : U ≃ₐ[k] V := by
  have : Module.Finite k U := Module.finite_of_finrank_pos (by rw [quotient_finrank]; decide)
  have hf := middleDotQuotientAction_surjective k
  have : Module.Finite k V :=
    Module.Finite.of_surjective (middleDotQuotientAction k).toLinearMap hf
  have hdim : Module.finrank k U = Module.finrank k V := by
    rw [quotient_finrank, end_finrank]
  refine AlgEquiv.ofBijective (middleDotQuotientAction k) ⟨?_, hf⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := (middleDotQuotientAction k).toLinearMap) hdim).mpr hf

/-- Webster's sum-of-dots relation is transported by the algebra
isomorphism to the sum of the diagrammatic dot endomorphisms. -/
theorem middleEndomorphismEquiv_sum :
    middleEndomorphismEquiv k (Ideal.Quotient.mk (middleDotIdeal k)
      (MvPolynomial.X 0 + MvPolynomial.X 1)) = dotEnd k 0 + dotEnd k 1 :=
  middleDotQuotientAction_sum k

end Categorification.Stendhal.LabelTwo
