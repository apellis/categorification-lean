/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapEFunctor
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KDerivedCoe
import Categorification.WeightedKLR.RedStrands.BlackDerivedFunctors

/-!
# `𝕂 ∘ 𝔈_i ≅ 𝔈_i ∘ 𝕂` on derived categories

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, the part for `𝔈_i`, on derived categories. On modules the isomorphism
`K_ν ⊗ M e' ≅ (K_{{i} + ν} ⊗ M) e'⁺` is `CupCap.capEOrdIso`. All functors involved are exact:
restriction (`𝔈_i`, and appending a black strand on the `λ⁺` side) with no hypothesis, and the
tensor products with `K_ν` and `K_{{i} + ν}` because these bimodules are projective as left
modules (`projective_midCapBimodule`). Hence the module isomorphism passes to Mathlib's derived
categories of modules (`CupCap.capEDerivedOrdIso`) and, through the comparison of derived
categories of dg modules over a ring with Mathlib's derived categories of modules, to the
coevaluation functor `𝕂 = - ⊗ᴸ K` of Definition 7.18 (`CupCap.capEDerivedIso`):
`𝕂_{{i} + ν} ⋙ 𝔈_i ≅ 𝔈_i ⋙ 𝕂_ν`, the input `c` of `CupCap.coevaluationRightAdjointCommIso`.

## Main definitions

* `CupCap.derivedPlusE`: `𝔈_i` on derived categories of right `T^{λ⁺}`-modules, the derived
  tensor product with the right ideal of appending a black strand.
* `CupCap.coevaluationComparisonOrdIso`: `𝕂` followed by the comparison is the comparison
  followed by the derived functor of `- ⊗ K`.
* `CupCap.capEDerivedOrdIso`: the module isomorphism on Mathlib's derived categories.
* `CupCap.capEDerivedIso`: `𝕂 ⋙ 𝔈_i ≅ 𝔈_i ⋙ 𝕂` for the coevaluation functor.
* `CupCap.capEDerivedIsoMid`, `CupCap.capEDerivedIsoTop`: the two cases `j < ℓ` and `j = ℓ`.

Route hypotheses (tracked): `hL` (violated idempotents act by zero on `L`), `hQ` (symmetric
`Q`), `hκ` (the cup scalars are units), `hP`, `hPL` (the pull-off identities), `hfin`, `hproj`
(the pieces `L e(t)` are finitely generated projective `k`-modules). They are used for the
module isomorphism (`CupCap.capEEquivMid`, `CupCap.capEEquivTop`) and for the projectivity of
`K` (`projective_midCapBimodule`). The ground ring is a field, as in Webster's paper.
-/

set_option backward.isDefEq.respectTransparency false

universe w w'

noncomputable section

namespace Categorification.Stendhal.CupCap

open CategoryTheory KLR KLRAlgebra MulOpposite InductionAlong DG.DegreeZero

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
local notation "CB" => CapBimodule k Q Λ Λc j hj ν ν₀ L
set_option hygiene false in
local notation "CBᵢ" => CapBimodule k Q Λ Λc j hj ((Singleton.singleton i : Multiset I) + ν) ν₀ L
set_option hygiene false in
local notation "aT" => appendBlackTPAOp k Q Λ Λc j hj ν ν₀ i
set_option hygiene false in
local notation "OrdK" => ordTensor TPpᵐᵒᵖ TAᵐᵒᵖ (OpBimodule TA CB)
set_option hygiene false in
local notation "OrdKᵢ" => ordTensor TPpᵢᵐᵒᵖ TAᵢᵐᵒᵖ (OpBimodule TAᵢ CBᵢ)

private theorem blackE_additive_capE : (blackE Q Λ i ν).Additive :=
  inferInstanceAs (resFunctor.{0, 0} (appendBlackOp Q Λ i ν)).Additive

attribute [local instance] blackE_additive_capE

/-! ### Mathlib's derived categories of modules -/

section ModuleDerived

variable [HasDerivedCategory.{w'} (ModuleCat.{0} TAᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} TAᵢᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} TPpᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} TPpᵢᵐᵒᵖ)]

variable {ν i}

/-- **`K ∘ 𝔈_i ≅ 𝔈_i ∘ K` on Mathlib's derived categories of right modules** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.21): the derived functors of the two sides of
`CupCap.capEOrdIso`, for `K_ν` and `K_{{i} + ν}` projective as left modules. -/
def capEDerivedOrdIso (D : CapAppendData k Q Λ Λc j hj ν₀ L ν i) [Module.Projective TA CB]
    [Module.Projective TAᵢ CBᵢ] :
    (blackE Q Λ i ν).mapDerivedCategory ⋙ (OrdK).mapDerivedCategory ≅
      (OrdKᵢ).mapDerivedCategory ⋙ (resFunctor.{0, 0} aT).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫ mapDerivedCategoryIsoOfIso (capEOrdIso D) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

end ModuleDerived

/-! ### Derived categories of dg modules -/

section DGDerived

variable [DG.HasDerivedCategory.{w, 0} TAᵐᵒᵖ] [DG.HasDerivedCategory.{w, 0} TAᵢᵐᵒᵖ]
  [DG.HasDerivedCategory.{w, 0} TPpᵐᵒᵖ] [DG.HasDerivedCategory.{w, 0} TPpᵢᵐᵒᵖ]
  [HasDerivedCategory.{w'} (ModuleCat.{0} TAᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} TAᵢᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} TPpᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} TPpᵢᵐᵒᵖ)]

variable (k Q Λ Λc j hj ν₀ L)

/-- **`𝔈_i` on derived categories of right `T^{λ⁺}`-modules**, `N ↦ N ⊗ᴸ T^{λ⁺} e'⁺`: the
derived tensor product with the right ideal `e'⁺ T^{λ⁺}` of appending a black strand
(`appendBlackTPAOp`) in the opposite ring. -/
def derivedPlusE : DG.DerivedCategory.{w} TPpᵢᵐᵒᵖ ⥤ DG.DerivedCategory.{w} TPpᵐᵒᵖ :=
  derivedTensor.{w} TPpᵐᵒᵖ TPpᵢᵐᵒᵖ (RCorner aT)

/-- **`derivedPlusE` is the derived functor of the exact restriction functor**, with no
hypothesis: the bimodule is a summand of the regular module. -/
def derivedPlusEComparisonIso :
    derivedPlusE.{w} k Q Λ Λc j hj ν₀ ν i ⋙ derivedComparison.{w, w'} TPpᵐᵒᵖ ≅
      derivedComparison.{w, w'} TPpᵢᵐᵒᵖ ⋙ (resFunctor.{0, 0} aT).mapDerivedCategory :=
  derivedTensorComparisonIso.{w, w'} TPpᵐᵒᵖ TPpᵢᵐᵒᵖ (RCorner aT) ≪≫
    Functor.isoWhiskerLeft _ (mapDerivedCategoryIsoOfIso (resOrdIso aT))

/-- **`𝕂` followed by the comparison is the comparison followed by the derived functor of
`- ⊗ K`**, for `K_ν` projective as a left `T^λ_ν`-module. -/
def coevaluationComparisonOrdIso [Module.Projective TA CB] :
    coevaluationFunctor.{0, w} k Q Λ Λc j hj ν ν₀ L ⋙ derivedComparison.{w, w'} TPpᵐᵒᵖ ≅
      derivedComparison.{w, w'} TAᵐᵒᵖ ⋙ (OrdK).mapDerivedCategory :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (derivedComparisonEquivalence.{w, w'} TAᵐᵒᵖ).unitIso _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (coevaluationOrdIso j hj Q Λ Λc ν ν₀ L)

variable {k Q Λ Λc j hj ν₀ L ν i}

/-- **`𝕂 ⋙ 𝔈_i ≅ 𝔈_i ⋙ 𝕂` on derived categories** (Webster, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.21, the part for `𝔈_i`), for the coevaluation functor `𝕂` of Definition 7.18,
from a map `ι : K_ν → K_{{i} + ν}` as in `CupCap.CapAppendData` and the projectivity of `K_ν`
and `K_{{i} + ν}` as left modules. -/
def capEDerivedIsoOfData (D : CapAppendData k Q Λ Λc j hj ν₀ L ν i) [Module.Projective TA CB]
    [Module.Projective TAᵢ CBᵢ] :
    coevaluationFunctor.{0, w} k Q Λ Λc j hj ((Singleton.singleton i : Multiset I) + ν) ν₀ L ⋙
        derivedPlusE.{w} k Q Λ Λc j hj ν₀ ν i ≅
      derivedBlackE.{w} Q Λ i ν ⋙ coevaluationFunctor.{0, w} k Q Λ Λc j hj ν ν₀ L :=
  ((Functor.FullyFaithful.ofFullyFaithful (derivedComparison.{w, w'} TPpᵐᵒᵖ)).whiskeringRight
      _).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (derivedPlusEComparisonIso.{w, w'} k Q Λ Λc j hj ν₀ ν i) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (coevaluationComparisonOrdIso.{w, w'} k Q Λ Λc j hj ν₀ L _) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (capEDerivedOrdIso.{w'} D).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (derivedBlackEComparisonIso.{w, w'} Q Λ i ν).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (coevaluationComparisonOrdIso.{w, w'} k Q Λ Λc j hj ν₀ L ν).symm ≪≫
      (Functor.associator _ _ _).symm)

/-! ### The two cases -/

section Cases

variable [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
  (hQ : KLRSymm Q) (hκ : ∀ i', IsUnit (cupScalar Q ν₀ i')) (hP : PullOff k Q Λc ν₀ L)
  (hPL : PullOffLeft k Q Λc ν₀ L)
  (hfin : ∀ (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t), Module.Finite k
    (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht))))
  (hproj : ∀ (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t), Module.Projective k
    (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht))))

variable (ν i)

/-- **`𝕂 ⋙ 𝔈_i ≅ 𝔈_i ⋙ 𝕂` on derived categories for `j < ℓ`** (Webster, arXiv:1309.3796v3,
§7.3, proof of Proposition 7.21, the part for `𝔈_i`).

Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`. -/
def capEDerivedIsoMid (h : j < ℓ) :
    coevaluationFunctor.{0, w} k Q Λ Λc j hj ((Singleton.singleton i : Multiset I) + ν) ν₀ L ⋙
        derivedPlusE.{w} k Q Λ Λc j hj ν₀ ν i ≅
      derivedBlackE.{w} Q Λ i ν ⋙ coevaluationFunctor.{0, w} k Q Λ Λc j hj ν ν₀ L :=
  have := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := ν) hL hQ hκ hP hPL hfin
    hproj
  have := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ)
    (ν := (Singleton.singleton i : Multiset I) + ν) hL hQ hκ hP hPL hfin hproj
  capEDerivedIsoOfData.{w, w'}
    (capAppendDataMid (hL := hL) ν i (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP hPL hκ hQ
      hfin h)

/-- **`𝕂 ⋙ 𝔈_i ≅ 𝔈_i ⋙ 𝕂` on derived categories for `j = ℓ`** (Webster, arXiv:1309.3796v3,
§7.3, proof of Proposition 7.21, the part for `𝔈_i`).

Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`. -/
def capEDerivedIsoTop (h : ¬ j < ℓ) :
    coevaluationFunctor.{0, w} k Q Λ Λc j hj ((Singleton.singleton i : Multiset I) + ν) ν₀ L ⋙
        derivedPlusE.{w} k Q Λ Λc j hj ν₀ ν i ≅
      derivedBlackE.{w} Q Λ i ν ⋙ coevaluationFunctor.{0, w} k Q Λ Λc j hj ν ν₀ L :=
  have := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := ν) hL hQ hκ hP hPL hfin
    hproj
  have := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ)
    (ν := (Singleton.singleton i : Multiset I) + ν) hL hQ hκ hP hPL hfin hproj
  capEDerivedIsoOfData.{w, w'}
    (capAppendDataTop (hL := hL) ν i (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP hPL hκ hQ
      hfin h)

end Cases

end DGDerived

end Categorification.Stendhal.CupCap
