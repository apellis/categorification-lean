/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.QuantumGroup.GabberKacBridge
import Categorification.Diagrams.KL3.Injectivity

/-!
# KL III bijectivity from the canonical Gabber–Kac statement

Thin wrappers around `KL3.Diagram.gammaUA'_bijective` and `KL3.Diagram.gammaUA'Equiv`
(Khovanov–Lauda III, arXiv:0807.3250v1), replacing the hypothesis `UDot.KL3.FormNondeg RD`
(KL III Proposition 2.5) by the canonical quantum Gabber–Kac statement
`CartanDatum.QuantumGabberKac` (Lusztig, *Introduction to quantum groups*, Theorem 33.1.3(a)),
via `UDot.KL3.formNondeg_of_quantumGabberKac`. The calculus nondegeneracy hypothesis `hnd` is
unchanged. Since the canonical statement is proved (`CartanDatum.quantumGabberKac`), the
`_unconditional` versions assume only the calculus nondegeneracy.

For an arbitrary root datum, `gammaUA'_injective_unconditional` (Theorem 1.2) and
`gammaUA'_bijective_of_sortedSpan_unconditional` are stated under the hom-finiteness and spanning
hypotheses `HomGdim`, `SortedSpan`, which follow from KL III Proposition 3.11 and its proof.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open Categorification.QuantumGroup UDot

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {k : Type w} [Field k]

attribute [local instance] KLR.KLGamma.vAlgebra

/-! ## Arbitrary root data, given hom-finiteness -/

section General

variable [DecidableEq I] (hG : HomGdim RD k)

include hG in
/-- **KL III Theorem 1.2 for an arbitrary root datum** (`k` a field), given hom-finiteness
`HomGdim RD k` (under which `γ` is defined): if the graphical calculus is nondegenerate,
`γ : 1_ρ (_𝒜 U̇) 1_λ → K₀(U̇(λ, ρ))` is injective. Proposition 2.5 is no longer a hypothesis. -/
theorem gammaUA'_injective_unconditional (hnd : CalculusNondeg RD k) (lam ρ : X) :
    Function.Injective (gammaUA' hG lam ρ) :=
  gammaUA'_injective hG hnd (KL3.formNondeg_unconditional RD) lam ρ

include hG in
/-- **KL III Theorems 1.1 and 1.2 for an arbitrary root datum** (`I` finite, `k` a field), given
hom-finiteness `HomGdim RD k` and the spanning hypothesis `SortedSpan RD k` (both consequences of
KL III Proposition 3.11 and its proof; both proved for simply-laced Cartan data): if the graphical
calculus is nondegenerate, `γ : 1_ρ (_𝒜 U̇) 1_λ → K₀(U̇(λ, ρ))` is bijective. -/
theorem gammaUA'_bijective_of_sortedSpan_unconditional [Finite I] (hspan : SortedSpan RD k)
    (hnd : CalculusNondeg RD k) (lam ρ : X) : Function.Bijective (gammaUA' hG lam ρ) :=
  gammaUA'_bijective_of_sortedSpan hG hspan hnd (KL3.formNondeg_unconditional RD) lam ρ

end General

/-! ## Simply-laced Cartan data -/

variable [DecidableEq I] [Finite I] (hSL : SimplyLaced C)

include hSL in
/-- `γ : 1_ρ (_𝒜 U̇) 1_λ → K₀(U̇(λ, ρ))` is bijective if the calculus is nondegenerate, assuming
the canonical quantum Gabber–Kac statement (which gives KL III Prop. 2.5). -/
theorem gammaUA'_bijective_of_quantumGabberKac (hnd : CalculusNondeg RD k)
    (hGK : C.QuantumGabberKac) (lam ρ : X) :
    Function.Bijective (gammaUA' (RD := RD) (k := k) (homGdim_of_simplyLaced hSL) lam ρ) :=
  gammaUA'_bijective hSL hnd (KL3.formNondeg_of_quantumGabberKac RD hGK) lam ρ

/-- `γ` as an isomorphism `1_ρ (_𝒜 U̇) 1_λ ≅ K₀(U̇(λ, ρ))` under the hypotheses of
`gammaUA'_bijective_of_quantumGabberKac`. -/
def gammaUA'Equiv_of_quantumGabberKac (hnd : CalculusNondeg RD k) (hGK : C.QuantumGabberKac)
    (lam ρ : X) :
    LinearMap.range (dpComb (RD := RD) lam ρ) ≃ₗ[LaurentPolynomial ℤ] K0Kar RD k ρ lam :=
  gammaUA'Equiv hSL hnd (KL3.formNondeg_of_quantumGabberKac RD hGK) lam ρ

include hSL in
/-- `γ : 1_ρ (_𝒜 U̇) 1_λ → K₀(U̇(λ, ρ))` is bijective if the calculus is nondegenerate. -/
theorem gammaUA'_bijective_unconditional (hnd : CalculusNondeg RD k) (lam ρ : X) :
    Function.Bijective (gammaUA' (RD := RD) (k := k) (homGdim_of_simplyLaced hSL) lam ρ) :=
  gammaUA'_bijective hSL hnd (KL3.formNondeg_unconditional RD) lam ρ

/-- `γ` as an isomorphism `1_ρ (_𝒜 U̇) 1_λ ≅ K₀(U̇(λ, ρ))` if the calculus is nondegenerate. -/
def gammaUA'Equiv_unconditional (hnd : CalculusNondeg RD k) (lam ρ : X) :
    LinearMap.range (dpComb (RD := RD) lam ρ) ≃ₗ[LaurentPolynomial ℤ] K0Kar RD k ρ lam :=
  gammaUA'Equiv hSL hnd (KL3.formNondeg_unconditional RD) lam ρ

end Categorification.KL3.Diagram

end
