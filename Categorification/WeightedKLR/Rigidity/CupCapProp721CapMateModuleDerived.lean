/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721CapMate
import Categorification.WeightedKLR.Rigidity.CupCapProp721CapMateDerived
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapFDerived
import Categorification.WeightedKLR.Rigidity.CupCapProp721DerivedSquare

/-!
# The mate of `K ∘ 𝔉_i ≅ 𝔉_i ∘ K` on Mathlib's derived categories of modules

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21: the compatibility of the two commutation isomorphisms with the units and counits
of `𝔉_i ⊣ 𝔈_i`, on Mathlib's derived categories of right modules. Along the derived adjunctions
(`derivedBlackAdjunction` and the derived induction-restriction adjunction on the `λ⁺` side), the
mate of the inverse of `CupCap.capFDerivedOrdIso` is `CupCap.capEDerivedOrdIso`
(`CupCap.capFDerivedOrdIso_inv_mate`). This is the module-level statement
`CupCap.capFOrdIso_inv_mate` passed through `CupCap.mateEquiv_mapDerivedCategory`.

Route hypotheses (tracked), as for `CupCap.capFOrdIso_inv_mate`: the compatibility `hD` of the
two bimodule data (discharged for both positions of the cap by `CupCap.capFImageEquivMid_unitGen`
and `CupCap.capFImageEquivTop_unitGen`); `K_ν`, `K_{{i} + ν}` projective as left modules and
`IsRouquierQ C Q` (Theorem 4.31), as for `CupCap.capFDerivedOrdIso`.

## Main results

* `CupCap.mapDerivedCategoryIsoOfIso_inv_eq`.
* `CupCap.capFDerivedOrdIso_inv_mate`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open CategoryTheory Limits KLR KLRAlgebra MulOpposite InductionAlong

section Iso

variable {C₁ C₂ : Type*} [Category* C₁] [Abelian C₁] [HasDerivedCategory C₁]
  [Category* C₂] [Abelian C₂] [HasDerivedCategory C₂]
  {F G : C₁ ⥤ C₂} [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- The inverse of `mapDerivedCategoryIsoOfIso e` is the derived natural transformation of
`e.inv`. -/
theorem mapDerivedCategoryIsoOfIso_inv_eq (e : F ≅ G) :
    (mapDerivedCategoryIsoOfIso e).inv = e.inv.mapDerivedCategory :=
  congrArg Iso.inv (Iso.ext (mapDerivedCategoryIsoOfIso_hom_eq e) :
    mapDerivedCategoryIsoOfIso e = NatTrans.mapDerivedCategoryIso e)

end Iso

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

private theorem blackE_additive_capMate : (blackE Q Λ i ν).Additive :=
  inferInstanceAs (resFunctor.{0, 0} (appendBlackOp Q Λ i ν)).Additive

private theorem blackF_additive_capMate : (blackF Q Λ i ν).Additive :=
  inferInstanceAs (InductionAlong.functor.{0, 0} (appendBlackOp Q Λ i ν)).Additive

attribute [local instance] blackE_additive_capMate blackF_additive_capMate

variable [HasDerivedCategory.{0} (ModuleCat.{0} TAᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} TAᵢᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} TPpᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} TPpᵢᵐᵒᵖ)]
  (C : QuantumGroup.CartanDatum I) (hRq : IsRouquierQ C Q)
  (D : CapAppendData k Q Λ Λc j hj ν₀ L ν i) (D' : CapFData k Q Λ Λc j hj ν₀ L ν i)
  [Module.Projective TA CB] [Module.Projective TAᵢ CBᵢ]

/-- **The mate of `K ∘ 𝔉_i ≅ 𝔉_i ∘ K` is `K ∘ 𝔈_i ≅ 𝔈_i ∘ K` on derived categories of
modules** (Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21): along the derived
adjunctions `𝔉_i ⊣ 𝔈_i` on both sides, the mate of the inverse of `capFDerivedOrdIso` is
`capEDerivedOrdIso`, provided `D'.bwd (1 ⊗ c) = D.iota c`. -/
theorem capFDerivedOrdIso_inv_mate
    (hD : ∀ c : CB, D'.bwd (Ind.tmul (unitGen aT) c) = D.iota c) :
    letI := blackF_preservesFiniteLimits Q Λ i ν C hRq
    letI := blackF_preservesFiniteColimits Q Λ i ν C hRq
    letI := projective_plusCorner k Q Λ Λc j hj ν₀ ν i C hRq
    letI := functor_preservesFiniteLimits aT
    letI := functor_preservesFiniteColimits aT
    (mateEquiv (derivedBlackAdjunction.{0} Q Λ i ν C hRq)
      (InductionAlong.adjunction.{0, 0} aT).mapDerivedCategory
      (TwoSquare.mk _ _ _ _ (capFDerivedOrdIso.{0} C hRq D').inv)).natTrans =
      (capEDerivedOrdIso.{0} D).hom := by
  let := blackF_preservesFiniteLimits Q Λ i ν C hRq
  let := blackF_preservesFiniteColimits Q Λ i ν C hRq
  let := projective_plusCorner k Q Λ Λc j hj ν₀ ν i C hRq
  let := functor_preservesFiniteLimits aT
  let := functor_preservesFiniteColimits aT
  have h := mateEquiv_mapDerivedCategory (blackAdjunction.{0} Q Λ i ν)
    (InductionAlong.adjunction.{0, 0} aT) (capFOrdIso D').inv (capEOrdIso D).hom
    (capFOrdIso_inv_mate D D' hD)
  simp only [capFDerivedOrdIso, capEDerivedOrdIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, mapDerivedCategoryIsoOfIso_hom_eq, mapDerivedCategoryIsoOfIso_inv_eq,
    Category.assoc]
  exact h

end Categorification.Stendhal.CupCap
