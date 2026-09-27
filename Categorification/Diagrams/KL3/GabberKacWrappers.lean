/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.QuantumGroup.GabberKacStatement
import Categorification.Diagrams.KL3.Injectivity

/-!
# KL III bijectivity from the canonical Gabber–Kac statement

Thin wrappers around `KL3.Diagram.gammaUA'_bijective` and `KL3.Diagram.gammaUA'Equiv`
(Khovanov–Lauda III, arXiv:0807.3250v1), replacing the hypothesis `UDot.KL3.FormNondeg RD`
(KL III Proposition 2.5) by the canonical quantum Gabber–Kac statement
`CartanDatum.QuantumGabberKac` (Lusztig, *Introduction to quantum groups*, Theorem 33.1.3(a)),
via `UDot.KL3.formNondeg_of_quantumGabberKac`. The calculus nondegeneracy hypothesis `hnd` is
unchanged.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open QuantumGroup UDot

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {k : Type w} [Field k]

attribute [local instance] KLR.KLGamma.vAlgebra

variable [DecidableEq I] [Finite I] (hSL : SimplyLaced C)

include hSL in
/-- `γ : 1_ρ (_𝒜 U̇) 1_λ → K₀(U̇(λ, ρ))` is bijective if the calculus is nondegenerate, assuming
the canonical quantum Gabber–Kac statement (which gives KL III Prop. 2.5). -/
theorem gammaUA'_bijective_of_quantumGabberKac (hnd : CalculusNondeg RD k)
    (hGK : C.QuantumGabberKac) (lam ρ : X) :
    Function.Bijective (gammaUA' (RD := RD) (k := k) hSL lam ρ) :=
  gammaUA'_bijective hSL hnd (KL3.formNondeg_of_quantumGabberKac RD hGK) lam ρ

/-- `γ` as an isomorphism `1_ρ (_𝒜 U̇) 1_λ ≅ K₀(U̇(λ, ρ))` under the hypotheses of
`gammaUA'_bijective_of_quantumGabberKac`. -/
def gammaUA'Equiv_of_quantumGabberKac (hnd : CalculusNondeg RD k) (hGK : C.QuantumGabberKac)
    (lam ρ : X) :
    LinearMap.range (dpComb (RD := RD) lam ρ) ≃ₗ[LaurentPolynomial ℤ] K0Kar RD k ρ lam :=
  gammaUA'Equiv hSL hnd (KL3.formNondeg_of_quantumGabberKac RD hGK) lam ρ

end Categorification.KL3.Diagram

end
