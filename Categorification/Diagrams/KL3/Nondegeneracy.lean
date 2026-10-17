/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Unfurling.GenericNondeg
import Categorification.Diagrams.KL3.IntegralFamily
import Categorification.Diagrams.KL3.GammaAlgebra

/-!
# Nondegeneracy of the KL diagrammatic calculus

Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3,
Theorem 3.6, proves the diagram basis theorem for general Cartan data.
Khovanov–Lauda, *A categorification of quantum sl(n)*, arXiv:0807.3250v1,
§6.4, “Simple nondegeneracy observations”, supplies the rational-to-integral
and arbitrary-ring passage. KL III's nondegeneracy theorem is stated in type A;
the general Cartan-datum conclusion here uses Webster's representation argument.

`calculusNondeg` proves the graded dimension statement over every field.
`canonicalBasis` gives the canonical KL spanning diagrams as a basis of the
presented Hom over every commutative ring, including rings with zero divisors.
Both consume the characteristic-zero theorem and integral descent with no
scalar-law, evaluation, independence, or descent assumption. The colour type
is finite, as in the headline Cartan-datum convention.
-/

noncomputable section
namespace Categorification.KL3.Diagram
open CategoryTheory StringDiagrams QuantumGroup UDot Module
universe u v w
variable {I : Type u} [Finite I] {C : CartanDatum I}
  {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y)

/-- KL nondegeneracy over every field, without a characteristic restriction.
The direct unfurling construction is used only over `ℚ`; integral spanning
and presentation base change then give the result in every characteristic. -/
theorem calculusNondeg (k : Type w) [Field k] : CalculusNondeg RD k := by
  classical
  exact calculusNondeg_of_rational k (KLR.Unfurling.GenericFields.calculusNondeg_charZero ℚ RD)

/-- The canonical KL diagram basis over every commutative ring. This is a
basis of the actual presented Hom, not of a replacement free module. -/
def canonicalBasis (k : Type w) [CommRing k] (μ : X) (s t : List (Letter I)) :
    Basis (SpanIdx s t) k ((pres RD k).obj (ob RD μ s) ⟶ (pres RD k).obj (ob RD μ t)) := by
  classical
  exact integralNondegBasis k (calculusNondeg RD ℚ) μ s t

/-- The basis vectors are the canonical integral spanning diagrams with
coefficients in the given ring. -/
@[simp] theorem canonicalBasis_apply (k : Type w) [CommRing k] (μ : X)
    (s t : List (Letter I)) (x : SpanIdx s t) :
    canonicalBasis RD k μ s t x = IntegralSpanning.twoB RD k μ s t x := by
  classical
  exact integralNondegBasis_apply k (calculusNondeg RD ℚ) μ s t x

section Gamma

attribute [local instance] KLR.KLGamma.vAlgebra
variable [DecidableEq I] (k : Type w) [Field k]

/-- KL III Theorem 1.2 with nondegeneracy supplied: every integral weight-block
map is bijective, for an arbitrary finite Cartan datum and every field. -/
theorem gammaUA'_bijective_unconditional (lam ρ : X) :
    Function.Bijective (gammaUA' (RD := RD) (k := k) homGdim lam ρ) :=
  gammaUA'_bijective_of_calculusNondeg (calculusNondeg RD k) lam ρ

/-- KL III Theorem 1.2 with its nondegeneracy hypothesis discharged by Webster's
basis theorem and integral descent. -/
theorem gammaAlg_injective_unconditional :
    Function.Injective (gammaAlg (RD := RD) k (torsionFreeK0_of_homGdim homGdim)) :=
  gammaAlg_injective_of_calculusNondeg (calculusNondeg RD k)

/-- The KL categorification equivalence for every finite Cartan datum over
any field, with no nondegeneracy premise. -/
def gammaAlgEquiv_unconditional : AUD RD vQ ≃+* K0All RD k :=
  gammaAlgEquiv_of_calculusNondeg (calculusNondeg RD k)

end Gamma

end Categorification.KL3.Diagram
