/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackRouqVacuum

/-!
# Strongly equivariant endofunctors of `D(T^λ)` on the image of `Ř^λ-pmod`

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 7.22: "any choice of isomorphism induces isomorphisms between functors", the
uniqueness of Corollary 3.27. For strongly equivariant endofunctors `σ`, `σ'` of the derived
action `blackPresCL` (Theorem 4.31), an isomorphism `σ(C₀) ≅ σ'(C₀)` at the vacuum object `C₀`
induces an isomorphism `Φ ≫ σ ≅ Φ ≫ σ'` of strongly equivariant functors out of `Ř^λ-pmod`,
where `Φ = blackVacuumFunctor C₀` (`blackVacuumImageIso`); in particular `σ(C₀) ≅ C₀` gives
`Φ ≫ σ ≅ Φ` (`blackVacuumImageIsoSelf`). So `σ` and `σ'` agree, equivariantly, on the image of
`Ř^λ-pmod`.

This is the part of Proposition 7.22 (b) on projective modules. The extension from this image
to all of `D(T^λ)` is not here: a natural isomorphism on projective modules does not by itself
determine a triangulated functor, so it needs a presentation of the functors as derived tensor
products with complexes of bimodules.

The hypotheses are those of `blackVacuumFunctor`, including the route hypothesis `hΛ₀` of
`blackRouqFamily`.
-/

namespace Categorification.Stendhal

open CategoryTheory CategoryTheory.Limits KLR TwoRep QuantumGroup KL3.Diagram CyclotomicAction
  DoubleDiagram StringDiagrams
open scoped Classical ZeroObject
open Pseudofunctor.StrongTrans

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe u w u₁

noncomputable section

variable {I : Type u} {k : Type u} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {C : CartanDatum I}
  {hQ : IsRouquierQ C Q}
  {P : Presentation.{u, u}
    (signature (coordinateDatum Λ C) (redWeight (cyclotomicCoverWeightDatum Λ C))) k}
  (hP : CoverRelsNegligible.{u, u, w} Λ C hQ (coverDotCentral Λ C hQ)
    (blockWeight (cyclotomicCoverWeightDatum Λ C) (cyclotomicCoverHighest (I := I) (ℓ := ℓ)) 0 :
      I ⊕ Fin ℓ → ℤ) P)
  (hwf : P.WFDom)
  [∀ β : Multiset I,
    _root_.HasDerivedCategory.{u} (ModuleCat.{u} (TensorProductAlgebra k Q Λ β)ᵐᵒᵖ)]
  {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y] {RD : UDot.WeightDatum C X Y} {Λ₀ : X}
  (hΛ₀ : ∀ i, RD.pair (RD.iY i) Λ₀ = ∑ r : Fin ℓ, (Λ r i : ℤ))
  (hsym : KLRSymm Q)

set_option hygiene false in
local notation "D" β => _root_.DerivedCategory (ModuleCat.{u} (TensorProductAlgebra k Q Λ β)ᵐᵒᵖ)

variable (C₀ : ∀ β : WeightBlocks RD Λ₀ (blockWeight RD Λ₀ 0), D β.1)
  (hC₀ : ∀ β, β.1 ≠ 0 → IsZero (C₀ β))

/-- **Strongly equivariant endofunctors of `D(T^λ)` agreeing at the vacuum agree on the image of
`Ř^λ-pmod`** (Webster, arXiv:1309.3796v3, proof of Proposition 7.22, by the uniqueness of
Corollary 3.27): an isomorphism `σ(C₀) ≅ σ'(C₀)` induces `Φ ≫ σ ≅ Φ ≫ σ'` for
`Φ = blackVacuumFunctor C₀`, extending the given isomorphism at `P_∅`
(`blackVacuumImageIso_hom_app`). Route hypothesis (tracked): `hΛ₀`. -/
def blackVacuumImageIso (σ σ' : blackPresCL hP hwf hΛ₀ hsym ⟶ blackPresCL hP hwf hΛ₀ hsym)
    (e : (σ.app (vacRegion hQ RD Λ₀)).obj.obj C₀ ≅ (σ'.app (vacRegion hQ RD Λ₀)).obj.obj C₀) :
    (blackVacuumFunctor hP hwf hΛ₀ hsym C₀ hC₀ :
        univCyclotomicPresCLPmod.{u, u, u} hQ RD Λ₀ (blackLam_pair hΛ₀) ⟶
          blackPresCL hP hwf hΛ₀ hsym) ≫ σ ≅
      (blackVacuumFunctor hP hwf hΛ₀ hsym C₀ hC₀ :
        univCyclotomicPresCLPmod.{u, u, u} hQ RD Λ₀ (blackLam_pair hΛ₀) ⟶
          blackPresCL hP hwf hΛ₀ hsym) ≫ σ' :=
  vacuumFunctorIso hQ RD Λ₀ (blackLam_pair hΛ₀)
    ((σ.app (vacRegion hQ RD Λ₀)).obj.mapIso (blackVacuumFunctorAppIso hP hwf hΛ₀ hsym C₀ hC₀) ≪≫
      e ≪≫ ((σ'.app (vacRegion hQ RD Λ₀)).obj.mapIso
        (blackVacuumFunctorAppIso hP hwf hΛ₀ hsym C₀ hC₀)).symm)

theorem blackVacuumImageIso_hom_app
    (σ σ' : blackPresCL hP hwf hΛ₀ hsym ⟶ blackPresCL hP hwf hΛ₀ hsym)
    (e : (σ.app (vacRegion hQ RD Λ₀)).obj.obj C₀ ≅ (σ'.app (vacRegion hQ RD Λ₀)).obj.obj C₀) :
    ((blackVacuumImageIso hP hwf hΛ₀ hsym C₀ hC₀ σ σ' e).hom.as.app
        (vacRegion hQ RD Λ₀)).hom.app (univVacuum hQ RD Λ₀ (blackLam_pair hΛ₀)) =
      (σ.app (vacRegion hQ RD Λ₀)).obj.map
          (blackVacuumFunctorAppIso hP hwf hΛ₀ hsym C₀ hC₀).hom ≫ e.hom ≫
        (σ'.app (vacRegion hQ RD Λ₀)).obj.map
          (blackVacuumFunctorAppIso hP hwf hΛ₀ hsym C₀ hC₀).inv :=
  vacuumFunctorIso_hom_app hQ RD Λ₀ _ _

/-- **A strongly equivariant endofunctor of `D(T^λ)` fixing the vacuum is the identity on the
image of `Ř^λ-pmod`** (Webster, arXiv:1309.3796v3, proof of Proposition 7.22): `σ(C₀) ≅ C₀`
induces `Φ ≫ σ ≅ Φ` for `Φ = blackVacuumFunctor C₀`. Route hypothesis (tracked): `hΛ₀`. -/
def blackVacuumImageIsoSelf (σ : blackPresCL hP hwf hΛ₀ hsym ⟶ blackPresCL hP hwf hΛ₀ hsym)
    (e : (σ.app (vacRegion hQ RD Λ₀)).obj.obj C₀ ≅ C₀) :
    (blackVacuumFunctor hP hwf hΛ₀ hsym C₀ hC₀ :
        univCyclotomicPresCLPmod.{u, u, u} hQ RD Λ₀ (blackLam_pair hΛ₀) ⟶
          blackPresCL hP hwf hΛ₀ hsym) ≫ σ ≅
      (blackVacuumFunctor hP hwf hΛ₀ hsym C₀ hC₀ :
        univCyclotomicPresCLPmod.{u, u, u} hQ RD Λ₀ (blackLam_pair hΛ₀) ⟶
          blackPresCL hP hwf hΛ₀ hsym) :=
  blackVacuumFunctorIso hP hwf hΛ₀ hsym C₀ hC₀ _
    ((σ.app (vacRegion hQ RD Λ₀)).obj.mapIso (blackVacuumFunctorAppIso hP hwf hΛ₀ hsym C₀ hC₀) ≪≫
      e)

end

end Categorification.Stendhal
