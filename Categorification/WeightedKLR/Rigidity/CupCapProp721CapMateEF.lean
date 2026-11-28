/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721CapMateModuleDerived
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapEFAdjoint

/-!
# Compatibility of `K ∘ 𝔈_i ≅ 𝔈_i ∘ K` with the cups and caps of `𝔈_i ⊣ 𝔉_i`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, with the adjunction `𝔈_i ⊣ 𝔉_i` of Theorem 4.31. For `𝔉_i ⊣ 𝔈_i` the
compatibility of the two commutation isomorphisms with the units and counits is
`CupCap.capFOrdIso_inv_mate`. For `𝔈_i ⊣ 𝔉_i` (`CupCap.blackEFAdjunction`,
`CupCap.plusEFAdjunction`) the corresponding statement is that the mate of the inverse of
`K ∘ 𝔈_i ≅ 𝔈_i ∘ K` (`CupCap.capEOrdIso`) is `K ∘ 𝔉_i ≅ 𝔉_i ∘ K` (`CupCap.capFOrdIso`). The
adjunction of Theorem 4.31 is transported from the matrix rings of the categorical action, and
no closed formula for its unit or counit on right `T^λ`-modules is available in the library, so
this statement is recorded as the route hypothesis `CupCap.CapEFMateCompatible`; by
`CupCap.capEFMateCompatible_of_counit` it reduces to one equation for the counits.

Under this hypothesis, the statement passes to Mathlib's derived categories of modules
(`CupCap.capEDerivedOrdIso_inv_mateEF`), through `CupCap.mateEquiv_mapDerivedCategory`;
`derivedBlackResIndAdjunction` is by definition the derived adjunction.

## Main definitions

* `CupCap.CapEFMateCompatible`: the route hypothesis (mate of `capEOrdIso.inv` along
  `𝔈_i ⊣ 𝔉_i` on both sides is `capFOrdIso.hom`).

## Main results

* `CupCap.capEFMateCompatible_of_counit`: the route hypothesis from the counit equation.
* `CupCap.capEDerivedOrdIso_inv_mateEF`: the derived form.

Route hypotheses (tracked): `CupCap.CapEFMateCompatible`; `K_ν`, `K_{{i} + ν}` projective as left
modules; `IsRouquierQ C Q` over a field, Webster's setting for Theorem 4.31.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open CategoryTheory Limits KLR KLRAlgebra MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance] OpBimodule.projective_opOp

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} {ν₀ : Multiset I}
  {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  {ν : Multiset I} {i : I}

set_option hygiene false in
local notation "TA" => TensorProductAlgebra k Q Λ ν
set_option hygiene false in
local notation "TAᵢ" => TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν)
set_option hygiene false in
local notation "TPp" => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
set_option hygiene false in
local notation "TPpᵢ" =>
  TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (((Singleton.singleton i : Multiset I) + ν) + ν₀)
set_option hygiene false in
local notation "CB" => CapBimodule k Q Λ Λc j hj ν ν₀ L
set_option hygiene false in
local notation "CBᵢ" => CapBimodule k Q Λ Λc j hj ((Singleton.singleton i : Multiset I) + ν) ν₀ L
set_option hygiene false in
local notation "aT" => appendBlackTPAOp k Q Λ Λc j hj ν ν₀ i
set_option hygiene false in
local notation "OrdK" => ordTensor TPpᵐᵒᵖ TAᵐᵒᵖ (OpBimodule TA CB)
set_option hygiene false in
local notation "OrdKᵢ" => ordTensor TPpᵢᵐᵒᵖ TAᵢᵐᵒᵖ (OpBimodule TAᵢ CBᵢ)

section Module

variable (C : QuantumGroup.CartanDatum I) (hRq : IsRouquierQ C Q)
  (D : CapAppendData k Q Λ Λc j hj ν₀ L ν i) (D' : CapFData k Q Λ Λc j hj ν₀ L ν i)

/-- **Compatibility of the cap bimodule with the cups and caps of `𝔈_i ⊣ 𝔉_i`** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.21, with Theorem 4.31), on right modules: along
`𝔈_i ⊣ 𝔉_i` on both sides (`blackEFAdjunction`, `plusEFAdjunction`), the mate of the inverse of
`K ∘ 𝔈_i ≅ 𝔈_i ∘ K` is `K ∘ 𝔉_i ≅ 𝔉_i ∘ K`.

This is a route hypothesis (tracked): Webster's proof uses it, and its proof needs the unit and
counit of the adjunction of Theorem 4.31 on right `T^λ`-modules. -/
def CapEFMateCompatible : Prop :=
  (mateEquiv (blackEFAdjunction Q Λ i ν C hRq) (plusEFAdjunction k Q Λ Λc j hj ν₀ ν i C hRq)
    (TwoSquare.mk _ _ _ _ (capEOrdIso D).inv)).natTrans = (capFOrdIso D').hom

variable {C hRq D D'} in
/-- **The route hypothesis from the counits**: `CupCap.CapEFMateCompatible` holds as soon as, for
every right `T^λ_ν`-module `N`, restricting `K ∘ 𝔉_i ≅ 𝔉_i ∘ K` at `N` and applying the counit of
`𝔈_i ⊣ 𝔉_i` on the `λ⁺` side equals the inverse of `K ∘ 𝔈_i ≅ 𝔈_i ∘ K` at `𝔉_i N` followed by
`K` of the counit of `𝔈_i ⊣ 𝔉_i` on the `λ` side (Webster, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21). -/
theorem capEFMateCompatible_of_counit
    (h : ∀ N : ModuleCat.{0} TAᵐᵒᵖ,
      (resFunctor.{0, 0} aT).map ((capFOrdIso D').hom.app N) ≫
          (plusEFAdjunction k Q Λ Λc j hj ν₀ ν i C hRq).counit.app ((OrdK).obj N) =
        (capEOrdIso D).inv.app ((blackF Q Λ i ν).obj N) ≫
          (OrdK).map ((blackEFAdjunction Q Λ i ν C hRq).counit.app N)) :
    CapEFMateCompatible C hRq D D' :=
  congrArg TwoSquare.natTrans (mateEquiv_eq_of_counit (blackEFAdjunction Q Λ i ν C hRq)
    (plusEFAdjunction k Q Λ Λc j hj ν₀ ν i C hRq) _ (TwoSquare.mk _ _ _ _ _) h)

end Module

private theorem blackE_additive_capMateEF : (blackE Q Λ i ν).Additive :=
  inferInstanceAs (resFunctor.{0, 0} (appendBlackOp Q Λ i ν)).Additive

private theorem blackF_additive_capMateEF : (blackF Q Λ i ν).Additive :=
  inferInstanceAs (InductionAlong.functor.{0, 0} (appendBlackOp Q Λ i ν)).Additive

attribute [local instance] blackE_additive_capMateEF blackF_additive_capMateEF

variable [HasDerivedCategory.{0} (ModuleCat.{0} TAᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} TAᵢᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} TPpᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} TPpᵢᵐᵒᵖ)]
  (C : QuantumGroup.CartanDatum I) (hRq : IsRouquierQ C Q)
  (D : CapAppendData k Q Λ Λc j hj ν₀ L ν i) (D' : CapFData k Q Λ Λc j hj ν₀ L ν i)
  [Module.Projective TA CB] [Module.Projective TAᵢ CBᵢ]

/-- **Compatibility with the cups and caps of `𝔈_i ⊣ 𝔉_i` on derived categories of modules**
(Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21, with Theorem 4.31): along the
derived adjunctions `𝔈_i ⊣ 𝔉_i` on both sides, the mate of the inverse of `capEDerivedOrdIso` is
`capFDerivedOrdIso`, under the route hypothesis `CupCap.CapEFMateCompatible`. -/
theorem capEDerivedOrdIso_inv_mateEF (hEF : CapEFMateCompatible C hRq D D') :
    letI := blackF_preservesFiniteLimits Q Λ i ν C hRq
    letI := blackF_preservesFiniteColimits Q Λ i ν C hRq
    letI := projective_plusCorner k Q Λ Λc j hj ν₀ ν i C hRq
    letI := functor_preservesFiniteLimits aT
    letI := functor_preservesFiniteColimits aT
    (mateEquiv (derivedBlackResIndAdjunction.{0} Q Λ i ν C hRq
        (blackEFAdjunction Q Λ i ν C hRq))
      (plusEFAdjunction k Q Λ Λc j hj ν₀ ν i C hRq).mapDerivedCategory
      (TwoSquare.mk _ _ _ _ (capEDerivedOrdIso.{0} D).inv)).natTrans =
      (capFDerivedOrdIso.{0} C hRq D').hom := by
  let := blackF_preservesFiniteLimits Q Λ i ν C hRq
  let := blackF_preservesFiniteColimits Q Λ i ν C hRq
  let := projective_plusCorner k Q Λ Λc j hj ν₀ ν i C hRq
  let := functor_preservesFiniteLimits aT
  let := functor_preservesFiniteColimits aT
  have h := mateEquiv_mapDerivedCategory (blackEFAdjunction Q Λ i ν C hRq)
    (plusEFAdjunction k Q Λ Λc j hj ν₀ ν i C hRq) (capEOrdIso D).inv (capFOrdIso D').hom hEF
  simp only [capFDerivedOrdIso, capEDerivedOrdIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, mapDerivedCategoryIsoOfIso_hom_eq, mapDerivedCategoryIsoOfIso_inv_eq,
    Category.assoc]
  exact h

end Categorification.Stendhal.CupCap
