/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapFDerived
import Categorification.WeightedKLR.Rigidity.CupCapProp721Adjoint
import Categorification.WeightedKLR.RedStrands.BlackDerivedTwoMorphisms

/-!
# `𝔉_i ⊣ 𝔈_i` on derived categories of dg modules, and `𝔈_i 𝕋 ≅ 𝕋 𝔈_i`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21. Webster obtains the commutation of `RHom(K, -)` (and of the quantum trace `𝕋`)
with the categorical action from that of the coevaluation `𝕂` by taking adjoints
(`CupCap.coevaluationRightAdjointCommIso`). Applied to `𝔉_i` with `𝔉_i ⊣ 𝔈_i` on both sides, the
isomorphism `𝕂 ⋙ 𝔉_i ≅ 𝔉_i ⋙ 𝕂` (`CupCap.capFDerivedIsoMid`, `CupCap.capFDerivedIsoTop`) gives
`𝔈_i ⋙ RHom(K, -) ≅ RHom(K, -) ⋙ 𝔈_i`.

The adjunction `𝔉_i ⊣ 𝔈_i` (induction left adjoint to restriction) is known on Mathlib's derived
categories of modules (`derivedBlackAdjunction`, and `Adjunction.mapDerivedCategory` on the `λ⁺`
side). It is transported to the derived categories of dg modules along the comparison
equivalences and the identifications of the derived tensor products with the derived functors
(`CupCap.adjunctionOfComparison`).

## Main definitions

* `CupCap.adjunctionOfComparison`: an adjunction transported along equivalences.
* `CupCap.derivedBlackFEAdjunction`: `derivedBlackF ⊣ derivedBlackE`.
* `CupCap.derivedPlusFEAdjunction`: `derivedPlusF ⊣ derivedPlusE`.
* `CupCap.capERightAdjointIsoMid`, `CupCap.capERightAdjointIsoTop`:
  `𝔈_i ⋙ RHom(K_ν, -) ≅ RHom(K_{{i} + ν}, -) ⋙ 𝔈_i`.

Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`, as for
`CupCap.capFDerivedIsoMid`; `IsRouquierQ C Q` is Webster's setting for Theorem 4.31.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open CategoryTheory KLR KLRAlgebra MulOpposite InductionAlong DG.DegreeZero

/-! ### Transport of adjunctions along equivalences -/

section Generic

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {DA : Type u₁} {DB : Type u₂} {MA : Type u₃} {MB : Type u₄}
  [Category.{v₁} DA] [Category.{v₂} DB] [Category.{v₃} MA] [Category.{v₄} MB]
  (eA : DA ≌ MA) (eB : DB ≌ MB) {F : DA ⥤ DB} {G : DB ⥤ DA} {F' : MA ⥤ MB} {G' : MB ⥤ MA}

/-- **An adjunction transported along equivalences**: if `F' ⊣ G'` and `F`, `G` correspond to
`F'`, `G'` under equivalences, then `F ⊣ G`. -/
def adjunctionOfComparison (adj : F' ⊣ G') (iF : F ⋙ eB.functor ≅ eA.functor ⋙ F')
    (iG : G ⋙ eA.functor ≅ eB.functor ⋙ G') : F ⊣ G :=
  (((eA.toAdjunction.comp adj).comp eB.symm.toAdjunction).ofNatIsoLeft
    ((Functor.rightUnitor F).symm ≪≫ Functor.isoWhiskerLeft F eB.unitIso ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight iF eB.inverse).symm).ofNatIsoRight
    ((Functor.rightUnitor G).symm ≪≫ Functor.isoWhiskerLeft G eA.unitIso ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight iG eA.inverse ≪≫
      Functor.associator _ _ _).symm

end Generic

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance] OpBimodule.projective_opOp

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} {ν₀ : Multiset I}
  {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

variable (ν : Multiset I) (i : I)

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
local notation "aT" => appendBlackTPAOp k Q Λ Λc j hj ν ν₀ i

private theorem blackF_additive_capAdj : (blackF Q Λ i ν).Additive :=
  inferInstanceAs (InductionAlong.functor.{0, 0} (appendBlackOp Q Λ i ν)).Additive

private theorem blackE_additive_capAdj : (blackE Q Λ i ν).Additive :=
  inferInstanceAs (resFunctor.{0, 0} (appendBlackOp Q Λ i ν)).Additive

attribute [local instance] blackF_additive_capAdj blackE_additive_capAdj

/-! ### `𝔉_i ⊣ 𝔈_i` on derived categories of dg modules -/

section Adjunctions

variable [DG.HasDerivedCategory.{0, 0} TAᵐᵒᵖ] [DG.HasDerivedCategory.{0, 0} TAᵢᵐᵒᵖ]
  [DG.HasDerivedCategory.{0, 0} TPpᵐᵒᵖ] [DG.HasDerivedCategory.{0, 0} TPpᵢᵐᵒᵖ]
  [HasDerivedCategory.{0} (ModuleCat.{0} TAᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} TAᵢᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} TPpᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} TPpᵢᵐᵒᵖ)]
  (C : QuantumGroup.CartanDatum I) (hRq : IsRouquierQ C Q)

/-- **`𝔉_i ⊣ 𝔈_i` on derived categories of dg modules** over `T^λ` (Webster, arXiv:1309.3796v3,
§4.6), from `derivedBlackAdjunction` on Mathlib's derived categories, for Rouquier polynomials
over a field (Theorem 4.31). -/
def derivedBlackFEAdjunction : derivedBlackF.{0} Q Λ i ν ⊣ derivedBlackE.{0} Q Λ i ν :=
  letI := blackF_preservesFiniteLimits Q Λ i ν C hRq
  letI := blackF_preservesFiniteColimits Q Λ i ν C hRq
  adjunctionOfComparison (derivedComparisonEquivalence.{0, 0} TAᵐᵒᵖ)
    (derivedComparisonEquivalence.{0, 0} TAᵢᵐᵒᵖ) (derivedBlackAdjunction.{0} Q Λ i ν C hRq)
    (derivedBlackFComparisonIso.{0, 0} Q Λ i ν C hRq) (derivedBlackEComparisonIso.{0, 0} Q Λ i ν)

/-- **`𝔉_i ⊣ 𝔈_i` on derived categories of dg modules** over `T^{λ⁺}`, the derived form of
induction left adjoint to restriction along appending a black strand, for Rouquier polynomials
over a field (Theorem 4.31 on the `λ⁺` side, `CupCap.projective_plusCorner`). -/
def derivedPlusFEAdjunction :
    derivedPlusF.{0} k Q Λ Λc j hj ν₀ ν i ⊣ derivedPlusE.{0} k Q Λ Λc j hj ν₀ ν i :=
  letI := projective_plusCorner k Q Λ Λc j hj ν₀ ν i C hRq
  letI := functor_preservesFiniteLimits aT
  letI := functor_preservesFiniteColimits aT
  adjunctionOfComparison (derivedComparisonEquivalence.{0, 0} TPpᵐᵒᵖ)
    (derivedComparisonEquivalence.{0, 0} TPpᵢᵐᵒᵖ)
    (InductionAlong.adjunction.{0, 0} aT).mapDerivedCategory
    (derivedPlusFComparisonIso.{0, 0} k Q Λ Λc j hj ν₀ ν i C hRq)
    (derivedPlusEComparisonIso.{0, 0} k Q Λ Λc j hj ν₀ ν i)

end Adjunctions

/-! ### `𝔈_i ⋙ RHom(K, -) ≅ RHom(K, -) ⋙ 𝔈_i` -/

section Cases

variable [DG.HasDerivedCategory.{0, 0} TAᵐᵒᵖ] [DG.HasDerivedCategory.{0, 0} TAᵢᵐᵒᵖ]
  [DG.HasDerivedCategory.{0, 0} TPpᵐᵒᵖ] [DG.HasDerivedCategory.{0, 0} TPpᵢᵐᵒᵖ]
  [HasDerivedCategory.{0} (ModuleCat.{0} TAᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} TAᵢᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} TPpᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} TPpᵢᵐᵒᵖ)]
  [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
  (hQ : KLRSymm Q) (hκ : ∀ i', IsUnit (cupScalar Q ν₀ i')) (hP : PullOff k Q Λc ν₀ L)
  (hPL : PullOffLeft k Q Λc ν₀ L)
  (hfin : ∀ (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t), Module.Finite k
    (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht))))
  (hproj : ∀ (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t), Module.Projective k
    (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht))))
  (C : QuantumGroup.CartanDatum I) (hRq : IsRouquierQ C Q)

/-- **`𝔈_i ⋙ RHom(K_ν, -) ≅ RHom(K_{{i} + ν}, -) ⋙ 𝔈_i` for `j < ℓ`** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.21, by taking adjoints of the part for `𝔉_i`).

Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`; `hRq` is
Webster's setting for Theorem 4.31. -/
def capERightAdjointIsoMid (h : j < ℓ) :
    derivedPlusE.{0} k Q Λ Λc j hj ν₀ ν i ⋙ coevaluationRightAdjoint k Q Λ Λc j hj ν ν₀ L ≅
      coevaluationRightAdjoint k Q Λ Λc j hj ((Singleton.singleton i : Multiset I) + ν) ν₀ L ⋙
        derivedBlackE.{0} Q Λ i ν :=
  coevaluationRightAdjointCommIso (derivedBlackFEAdjunction ν i C hRq)
    (derivedPlusFEAdjunction ν i C hRq)
    (capFDerivedIsoMid.{0, 0} ν i hL hQ hκ hP hPL hfin hproj C hRq h)

/-- **`𝔈_i ⋙ RHom(K_ν, -) ≅ RHom(K_{{i} + ν}, -) ⋙ 𝔈_i` for `j = ℓ`** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.21, by taking adjoints of the part for `𝔉_i`).

Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`; `hRq` is
Webster's setting for Theorem 4.31. -/
def capERightAdjointIsoTop (h : ¬ j < ℓ) :
    derivedPlusE.{0} k Q Λ Λc j hj ν₀ ν i ⋙ coevaluationRightAdjoint k Q Λ Λc j hj ν ν₀ L ≅
      coevaluationRightAdjoint k Q Λ Λc j hj ((Singleton.singleton i : Multiset I) + ν) ν₀ L ⋙
        derivedBlackE.{0} Q Λ i ν :=
  coevaluationRightAdjointCommIso (derivedBlackFEAdjunction ν i C hRq)
    (derivedPlusFEAdjunction ν i C hRq)
    (capFDerivedIsoTop.{0, 0} ν i hL hQ hκ hP hPL hfin hproj C hRq h)

end Cases

end Categorification.Stendhal.CupCap
