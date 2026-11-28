/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapEDerivedTwo
import Categorification.WeightedKLR.Rigidity.CupCapProp721ComparisonSquare

/-!
# `𝕂 ∘ 𝔈_i ≅ 𝔈_i ∘ 𝕂` and the 2-morphisms, on derived categories of dg modules

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, the part for `𝔈_i`. The isomorphism `𝕂 ⋙ 𝔈_i ≅ 𝔈_i ⋙ 𝕂` of functors between
derived categories of dg modules (`CupCap.capEDerivedIsoOfData`) is conjugate, along the fully
faithful comparisons with Mathlib's derived categories of modules, to the derived functor of the
module isomorphism `CupCap.capEOrdIso` (`CupCap.capEDerivedIsoOfData_isComparisonSquare`), and,
after the identification of restriction along `appendBlackTPAOp` with `blackEOfEq`
(`resFunctorIsoOfEq`), to the derived functor of `CupCap.capEOrdIsoOfEq`
(`CupCap.capEDerivedIsoOfData_isComparisonSquareOfEq`).

The dot and the crossing on the dg derived functors `derivedBlackE`, `CupCap.derivedPlusE` are
defined as the conjugates of the derived dot and crossing (`CupCap.dgBlackDot`,
`CupCap.dgPlusDot`, `CupCap.dgBlackCross`, `CupCap.dgPlusCross`); `CupCap.dgBlackCross` is the
conjugate of `derivedBlackCross` on `E^D ⋙ E^D`. The module-level compatibilities then pass to
the dg side (`CupCap.capEDerivedIsoOfData_dot`, `CupCap.capEDerivedIsoPaste_cross`, and the
cases `Mid` (`j < ℓ`) and `Top` (`j = ℓ`)).

Route hypotheses (tracked): as for `CupCap.capEDerivedIsoMid`: `hL`, `hQ`, `hκ`, `hP`, `hPL`,
`hfin`, `hproj` (through `MidKLRRel` and `projective_midCapBimodule`).
-/

set_option backward.isDefEq.respectTransparency false

universe w w'

noncomputable section

namespace Categorification.Stendhal.CupCap

open CategoryTheory KLR KLRAlgebra MulOpposite InductionAlong DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance] OpBimodule.projective_opOp

section Exact

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {n : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ' : Fin n → I →₀ ℕ) (i : I) {μ β : Multiset I}
  (h : ({i} : Multiset I) + μ = β)

private theorem blackE_additive_capEDG (ν : Multiset I) : (blackE Q Λ' i ν).Additive :=
  inferInstanceAs (resFunctor.{0, 0} (appendBlackOp Q Λ' i ν)).Additive

private theorem blackEOfEq_additive_capEDG : (blackEOfEq Q Λ' i h).Additive :=
  inferInstanceAs (resFunctor.{0, 0} (appendBlackOpOfEq Q Λ' i h)).Additive

private theorem blackEOfEq_limits_capEDG :
    Limits.PreservesFiniteLimits (blackEOfEq Q Λ' i h) :=
  inferInstanceAs (Limits.PreservesFiniteLimits (resFunctor.{0, 0} (appendBlackOpOfEq Q Λ' i h)))

private theorem blackEOfEq_colimits_capEDG :
    Limits.PreservesFiniteColimits (blackEOfEq Q Λ' i h) :=
  inferInstanceAs
    (Limits.PreservesFiniteColimits (resFunctor.{0, 0} (appendBlackOpOfEq Q Λ' i h)))

end Exact

attribute [local instance] blackE_additive_capEDG blackEOfEq_additive_capEDG
  blackEOfEq_limits_capEDG blackEOfEq_colimits_capEDG

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} {ν₀ : Multiset I}
  {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

/-! ### One step -/

section One

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

variable [DG.HasDerivedCategory.{w, 0} TAᵐᵒᵖ] [DG.HasDerivedCategory.{w, 0} TAᵢᵐᵒᵖ]
  [DG.HasDerivedCategory.{w, 0} TPpᵐᵒᵖ] [DG.HasDerivedCategory.{w, 0} TPpᵢᵐᵒᵖ]
  [HasDerivedCategory.{w'} (ModuleCat.{0} TAᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} TAᵢᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} TPpᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} TPpᵢᵐᵒᵖ)]

variable (k Q Λ Λc j hj ν₀) in
/-- `derivedPlusE` followed by the comparison is the comparison followed by the derived functor
of `blackEOfEq` along `plusWeight_assoc`: `CupCap.derivedPlusEComparisonIso` composed with
the derived functor of `resFunctorIsoOfEq`. -/
def derivedPlusEComparisonIsoOfEq :
    derivedPlusE.{w} k Q Λ Λc j hj ν₀ ν i ⋙ derivedComparison.{w, w'} TPpᵐᵒᵖ ≅
      derivedComparison.{w, w'} TPpᵢᵐᵒᵖ ⋙
        (blackEOfEq Q (plusLabels Λ Λc j hj) i (plusWeight_assoc ν ν₀ i)).mapDerivedCategory :=
  derivedPlusEComparisonIso.{w, w'} k Q Λ Λc j hj ν₀ ν i ≪≫
    Functor.isoWhiskerLeft _ (mapDerivedCategoryIsoOfIso
      (resFunctorIsoOfEq.{0, 0} (appendBlackTPAOp_eq_ofEq k Q Λ Λc j hj ν₀ ν i)))

variable {ν i}

/-- **`CupCap.capEDerivedIsoOfData` is conjugate to the derived `CupCap.capEOrdIso`** along the
comparisons of derived categories (Webster, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21). -/
theorem capEDerivedIsoOfData_isComparisonSquare (D : CapAppendData k Q Λ Λc j hj ν₀ L ν i)
    [Module.Projective TA CB] [Module.Projective TAᵢ CBᵢ] :
    IsComparisonSquare (derivedBlackEComparisonIso.{w, w'} Q Λ i ν)
      (coevaluationComparisonOrdIso.{w, w'} k Q Λ Λc j hj ν₀ L ν)
      (coevaluationComparisonOrdIso.{w, w'} k Q Λ Λc j hj ν₀ L _)
      (derivedPlusEComparisonIso.{w, w'} k Q Λ Λc j hj ν₀ ν i)
      (derivedSquareIso (capEOrdIso D)) (capEDerivedIsoOfData.{w, w'} D) := fun x => by
  refine (congrArg (fun t => NatTrans.app t x)
    (((Functor.FullyFaithful.ofFullyFaithful (derivedComparison.{w, w'} TPpᵐᵒᵖ)).whiskeringRight
      _).map_preimage _)).trans ?_
  simp [derivedSquareIso, capEDerivedOrdIso]

/-- **`CupCap.capEDerivedIsoOfData` is conjugate to the derived `CupCap.capEOrdIsoOfEq`**, with
`𝔈⁺_i = blackEOfEq` along `plusWeight_assoc` on the module side (Webster, arXiv:1309.3796v3,
§7.3, proof of Proposition 7.21). This links `CupCap.capEOrdIsoOfEq`, used by the module-level
2-morphism compatibilities, with `CupCap.capEOrdIso`, from which `CupCap.capEDerivedIsoOfData`
is built, through `resFunctorIsoOfEq`. -/
theorem capEDerivedIsoOfData_isComparisonSquareOfEq (D : CapAppendData k Q Λ Λc j hj ν₀ L ν i)
    [Module.Projective TA CB] [Module.Projective TAᵢ CBᵢ] :
    IsComparisonSquare (derivedBlackEComparisonIso.{w, w'} Q Λ i ν)
      (coevaluationComparisonOrdIso.{w, w'} k Q Λ Λc j hj ν₀ L ν)
      (coevaluationComparisonOrdIso.{w, w'} k Q Λ Λc j hj ν₀ L _)
      (derivedPlusEComparisonIsoOfEq.{w, w'} k Q Λ Λc j hj ν₀ ν i)
      (derivedSquareIso (capEOrdIsoOfEq D)) (capEDerivedIsoOfData.{w, w'} D) :=
  (capEDerivedIsoOfData_isComparisonSquare D).changeY _
    ((derivedSquareIso_trans_whiskerLeft _ _).trans (by rw [mapDerivedCategoryIsoOfIso_hom_eq]))

variable (ν i)

/-- **The dot on the dg derived `𝔈_i`** of right `T^λ`-modules: the conjugate of
`derivedBlackDot` along `derivedBlackEComparisonIso`. -/
def dgBlackDot : derivedBlackE.{w} Q Λ i ν ⟶ derivedBlackE.{w} Q Λ i ν :=
  comparisonConj (Functor.FullyFaithful.ofFullyFaithful (derivedComparison.{w, w'} TAᵐᵒᵖ))
    (derivedBlackEComparisonIso.{w, w'} Q Λ i ν) (derivedBlackEComparisonIso.{w, w'} Q Λ i ν)
    (derivedBlackDot.{w'} Q Λ i ν)

variable (k Q Λ Λc j hj ν₀) in
/-- **The dot on the dg derived `𝔈⁺_i`** of right `T^{λ⁺}`-modules: the conjugate of the
derived dot `resDotOfEq` along `CupCap.derivedPlusEComparisonIsoOfEq`. -/
def dgPlusDot : derivedPlusE.{w} k Q Λ Λc j hj ν₀ ν i ⟶ derivedPlusE.{w} k Q Λ Λc j hj ν₀ ν i :=
  comparisonConj (Functor.FullyFaithful.ofFullyFaithful (derivedComparison.{w, w'} TPpᵐᵒᵖ))
    (derivedPlusEComparisonIsoOfEq.{w, w'} k Q Λ Λc j hj ν₀ ν i)
    (derivedPlusEComparisonIsoOfEq.{w, w'} k Q Λ Λc j hj ν₀ ν i)
    (resDotOfEq Q (plusLabels Λ Λc j hj) i (plusWeight_assoc ν ν₀ i)).mapDerivedCategory

variable {ν i}

/-- **`𝕂 ⋙ 𝔈_i ≅ 𝔈_i ⋙ 𝕂` carries the dot to the dot on derived categories of dg modules**
(Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21), from the module-level
compatibility for `CupCap.capEOrdIsoOfEq D`. -/
theorem capEDerivedIsoOfData_dot (D : CapAppendData k Q Λ Λc j hj ν₀ L ν i)
    [Module.Projective TA CB] [Module.Projective TAᵢ CBᵢ]
    (hdot : Functor.whiskerRight (blackDot Q Λ i ν) OrdK ≫ (capEOrdIsoOfEq D).hom =
      (capEOrdIsoOfEq D).hom ≫ Functor.whiskerLeft OrdKᵢ
        (resDotOfEq Q (plusLabels Λ Λc j hj) i (plusWeight_assoc ν ν₀ i))) :
    Functor.whiskerLeft (coevaluationFunctor.{0, w} k Q Λ Λc j hj _ ν₀ L)
        (dgPlusDot.{w, w'} k Q Λ Λc j hj ν₀ ν i) ≫ (capEDerivedIsoOfData.{w, w'} D).hom =
      (capEDerivedIsoOfData.{w, w'} D).hom ≫
        Functor.whiskerRight (dgBlackDot.{w, w'} ν i)
          (coevaluationFunctor.{0, w} k Q Λ Λc j hj ν ν₀ L) :=
  (capEDerivedIsoOfData_isComparisonSquareOfEq D).whisker
    (capEDerivedIsoOfData_isComparisonSquareOfEq D) (isComparisonConj_comparisonConj _ _ _ _)
    (isComparisonConj_comparisonConj _ _ _ _) (derivedSquareIso_whisker _ _ hdot)

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

/-- **`𝕂 ⋙ 𝔈_i ≅ 𝔈_i ⋙ 𝕂` carries the dot to the dot on derived categories of dg modules, for
`j < ℓ`** (Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21).
Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`. -/
theorem capEDerivedIsoMid_dot (h : j < ℓ) :
    Functor.whiskerLeft (coevaluationFunctor.{0, w} k Q Λ Λc j hj _ ν₀ L)
        (dgPlusDot.{w, w'} k Q Λ Λc j hj ν₀ ν i) ≫
        (capEDerivedIsoMid.{w, w'} ν i hL hQ hκ hP hPL hfin hproj h).hom =
      (capEDerivedIsoMid.{w, w'} ν i hL hQ hκ hP hPL hfin hproj h).hom ≫
        Functor.whiskerRight (dgBlackDot.{w, w'} ν i)
          (coevaluationFunctor.{0, w} k Q Λ Λc j hj ν ν₀ L) :=
  have := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := ν) hL hQ hκ hP hPL hfin
    hproj
  have := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ)
    (ν := (Singleton.singleton i : Multiset I) + ν) hL hQ hκ hP hPL hfin hproj
  capEDerivedIsoOfData_dot _
    (capEOrdIsoOfEqMid_dot ν i (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP hPL hκ hQ hfin h)

/-- **`𝕂 ⋙ 𝔈_i ≅ 𝔈_i ⋙ 𝕂` carries the dot to the dot on derived categories of dg modules, for
`j = ℓ`** (Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21).
Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`. -/
theorem capEDerivedIsoTop_dot (h : ¬ j < ℓ) :
    Functor.whiskerLeft (coevaluationFunctor.{0, w} k Q Λ Λc j hj _ ν₀ L)
        (dgPlusDot.{w, w'} k Q Λ Λc j hj ν₀ ν i) ≫
        (capEDerivedIsoTop.{w, w'} ν i hL hQ hκ hP hPL hfin hproj h).hom =
      (capEDerivedIsoTop.{w, w'} ν i hL hQ hκ hP hPL hfin hproj h).hom ≫
        Functor.whiskerRight (dgBlackDot.{w, w'} ν i)
          (coevaluationFunctor.{0, w} k Q Λ Λc j hj ν ν₀ L) :=
  have := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := ν) hL hQ hκ hP hPL hfin
    hproj
  have := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ)
    (ν := (Singleton.singleton i : Multiset I) + ν) hL hQ hκ hP hPL hfin hproj
  capEDerivedIsoOfData_dot _
    (capEOrdIsoOfEqTop_dot ν i (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP hPL hκ hQ hfin h)

end Cases

end One

/-! ### Two steps: the crossing -/

section Two

variable (ν : Multiset I) (i : I)

set_option hygiene false in
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
set_option hygiene false in
local notation "νᵢᵢ" =>
  ((Singleton.singleton i : Multiset I) + ((Singleton.singleton i : Multiset I) + ν))
set_option hygiene false in
local notation "TA" μ:max => TensorProductAlgebra k Q Λ μ
set_option hygiene false in
local notation "TPp" μ:max => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (μ + ν₀)
set_option hygiene false in
local notation "CB" μ:max => CapBimodule k Q Λ Λc j hj μ ν₀ L
set_option hygiene false in
local notation "OrdK" μ:max => ordTensor (TPp μ)ᵐᵒᵖ (TA μ)ᵐᵒᵖ (OpBimodule (TA μ) (CB μ))

variable [DG.HasDerivedCategory.{w, 0} (TA ν)ᵐᵒᵖ] [DG.HasDerivedCategory.{w, 0} (TA νᵢ)ᵐᵒᵖ]
  [DG.HasDerivedCategory.{w, 0} (TA νᵢᵢ)ᵐᵒᵖ]
  [DG.HasDerivedCategory.{w, 0} (TPp ν)ᵐᵒᵖ] [DG.HasDerivedCategory.{w, 0} (TPp νᵢ)ᵐᵒᵖ]
  [DG.HasDerivedCategory.{w, 0} (TPp νᵢᵢ)ᵐᵒᵖ]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TA ν)ᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TA νᵢ)ᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TA νᵢᵢ)ᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TPp ν)ᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TPp νᵢ)ᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TPp νᵢᵢ)ᵐᵒᵖ)]

/-- **The crossing on the dg derived `𝔈_i²`** of right `T^λ`-modules: the conjugate of
`derivedBlackCross` along the pasted comparison isomorphisms. -/
def dgBlackCross :
    derivedBlackE.{w} Q Λ i νᵢ ⋙ derivedBlackE.{w} Q Λ i ν ⟶
      derivedBlackE.{w} Q Λ i νᵢ ⋙ derivedBlackE.{w} Q Λ i ν :=
  comparisonConj (Functor.FullyFaithful.ofFullyFaithful (derivedComparison.{w, w'} (TA ν)ᵐᵒᵖ))
    (squarePaste (derivedBlackEComparisonIso.{w, w'} Q Λ i ν)
      (derivedBlackEComparisonIso.{w, w'} Q Λ i νᵢ))
    (squarePaste (derivedBlackEComparisonIso.{w, w'} Q Λ i ν)
      (derivedBlackEComparisonIso.{w, w'} Q Λ i νᵢ))
    (derivedBlackCross.{w'} Q Λ i ν)

variable (k Q Λ Λc j hj ν₀) in
/-- **The crossing on the dg derived `𝔈⁺_i²`** of right `T^{λ⁺}`-modules: the conjugate of the
derived crossing `resCrossOfEq` (through `Functor.mapDerivedCategoryCompIso`) along the pasted
comparison isomorphisms `CupCap.derivedPlusEComparisonIsoOfEq`. -/
def dgPlusCross (hQ : KLRSymm Q) :
    derivedPlusE.{w} k Q Λ Λc j hj ν₀ νᵢ i ⋙ derivedPlusE.{w} k Q Λ Λc j hj ν₀ ν i ⟶
      derivedPlusE.{w} k Q Λ Λc j hj ν₀ νᵢ i ⋙ derivedPlusE.{w} k Q Λ Λc j hj ν₀ ν i :=
  comparisonConj (Functor.FullyFaithful.ofFullyFaithful (derivedComparison.{w, w'} (TPp ν)ᵐᵒᵖ))
    (squarePaste (derivedPlusEComparisonIsoOfEq.{w, w'} k Q Λ Λc j hj ν₀ ν i)
      (derivedPlusEComparisonIsoOfEq.{w, w'} k Q Λ Λc j hj ν₀ νᵢ i))
    (squarePaste (derivedPlusEComparisonIsoOfEq.{w, w'} k Q Λ Λc j hj ν₀ ν i)
      (derivedPlusEComparisonIsoOfEq.{w, w'} k Q Λ Λc j hj ν₀ νᵢ i))
    ((Functor.mapDerivedCategoryCompIso _ _).hom ≫
      (resCrossOfEq (plusLabels Λ Λc j hj) hQ i i (plusWeight_assoc ν ν₀ i)
        (plusWeight_assoc νᵢ ν₀ i) (plusWeight_assoc ν ν₀ i)
        (plusWeight_assoc νᵢ ν₀ i)).mapDerivedCategory ≫
      (Functor.mapDerivedCategoryCompIso _ _).inv)

variable {ν i}

/-- **`𝕂 ⋙ 𝔈_i² ≅ 𝔈_i² ⋙ 𝕂` on derived categories of dg modules**, the pasting of two copies
of `CupCap.capEDerivedIsoOfData` (Webster, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21). -/
def capEDerivedIsoPaste (D₁ : CapAppendData k Q Λ Λc j hj ν₀ L ν i)
    (D₂ : CapAppendData k Q Λ Λc j hj ν₀ L νᵢ i) [Module.Projective (TA ν) (CB ν)]
    [Module.Projective (TA νᵢ) (CB νᵢ)] [Module.Projective (TA νᵢᵢ) (CB νᵢᵢ)] :
    coevaluationFunctor.{0, w} k Q Λ Λc j hj νᵢᵢ ν₀ L ⋙
        (derivedPlusE.{w} k Q Λ Λc j hj ν₀ νᵢ i ⋙ derivedPlusE.{w} k Q Λ Λc j hj ν₀ ν i) ≅
      (derivedBlackE.{w} Q Λ i νᵢ ⋙ derivedBlackE.{w} Q Λ i ν) ⋙
        coevaluationFunctor.{0, w} k Q Λ Λc j hj ν ν₀ L :=
  (squarePaste (capEDerivedIsoOfData.{w, w'} D₁).symm
    (capEDerivedIsoOfData.{w, w'} D₂).symm).symm

/-- **`CupCap.capEDerivedIsoPaste` is conjugate to the derived `CupCap.capECompIsoOfEq`**, with
the composites of the derived functors identified with the derived functors of the composites
by `Functor.mapDerivedCategoryCompIso`. -/
theorem capEDerivedIsoPaste_isComparisonSquare (D₁ : CapAppendData k Q Λ Λc j hj ν₀ L ν i)
    (D₂ : CapAppendData k Q Λ Λc j hj ν₀ L νᵢ i) [Module.Projective (TA ν) (CB ν)]
    [Module.Projective (TA νᵢ) (CB νᵢ)] [Module.Projective (TA νᵢᵢ) (CB νᵢᵢ)] :
    IsComparisonSquare
      (squarePaste (derivedBlackEComparisonIso.{w, w'} Q Λ i ν)
        (derivedBlackEComparisonIso.{w, w'} Q Λ i νᵢ) ≪≫
        Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso _ _))
      (coevaluationComparisonOrdIso.{w, w'} k Q Λ Λc j hj ν₀ L ν)
      (coevaluationComparisonOrdIso.{w, w'} k Q Λ Λc j hj ν₀ L νᵢᵢ)
      (squarePaste (derivedPlusEComparisonIsoOfEq.{w, w'} k Q Λ Λc j hj ν₀ ν i)
        (derivedPlusEComparisonIsoOfEq.{w, w'} k Q Λ Λc j hj ν₀ νᵢ i) ≪≫
        Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso _ _))
      (derivedSquareIso (capECompIsoOfEq D₁ D₂)) (capEDerivedIsoPaste.{w, w'} D₁ D₂) :=
  (((capEDerivedIsoOfData_isComparisonSquareOfEq D₁).paste
      (capEDerivedIsoOfData_isComparisonSquareOfEq D₂)).changeX
      (Functor.mapDerivedCategoryCompIso _ _) (eh' := Functor.isoWhiskerRight
        (Functor.mapDerivedCategoryCompIso _ _).symm _ ≪≫ squarePaste _ _) rfl).changeY
    (Functor.mapDerivedCategoryCompIso _ _) (by
      rw [Iso.trans_hom, Category.assoc, ← derivedSquareIso_squarePaste, ← Category.assoc,
        Functor.isoWhiskerRight_hom, ← Functor.whiskerRight_comp, Iso.symm_hom, Iso.inv_hom_id,
        Functor.whiskerRight_id', Category.id_comp]
      rfl)

/-- **`𝕂 ⋙ 𝔈_i² ≅ 𝔈_i² ⋙ 𝕂` carries the crossing to the crossing on derived categories of dg
modules** (Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21), from the
module-level compatibility for `CupCap.capECompIsoOfEq D₁ D₂`. -/
theorem capEDerivedIsoPaste_cross (hQ : KLRSymm Q) (D₁ : CapAppendData k Q Λ Λc j hj ν₀ L ν i)
    (D₂ : CapAppendData k Q Λ Λc j hj ν₀ L νᵢ i) [Module.Projective (TA ν) (CB ν)]
    [Module.Projective (TA νᵢ) (CB νᵢ)] [Module.Projective (TA νᵢᵢ) (CB νᵢᵢ)]
    (hcross : Functor.whiskerRight (blackCross Q Λ i ν) (OrdK ν) ≫
        (capECompIsoOfEq D₁ D₂).hom =
      (capECompIsoOfEq D₁ D₂).hom ≫ Functor.whiskerLeft (OrdK νᵢᵢ)
        (resCrossOfEq (plusLabels Λ Λc j hj) hQ i i (plusWeight_assoc ν ν₀ i)
          (plusWeight_assoc νᵢ ν₀ i) (plusWeight_assoc ν ν₀ i) (plusWeight_assoc νᵢ ν₀ i))) :
    Functor.whiskerLeft (coevaluationFunctor.{0, w} k Q Λ Λc j hj νᵢᵢ ν₀ L)
        (dgPlusCross.{w, w'} k Q Λ Λc j hj ν₀ ν i hQ) ≫ (capEDerivedIsoPaste.{w, w'} D₁ D₂).hom =
      (capEDerivedIsoPaste.{w, w'} D₁ D₂).hom ≫
        Functor.whiskerRight (dgBlackCross.{w, w'} ν i)
          (coevaluationFunctor.{0, w} k Q Λ Λc j hj ν ν₀ L) :=
  (capEDerivedIsoPaste_isComparisonSquare D₁ D₂).whisker
    (capEDerivedIsoPaste_isComparisonSquare D₁ D₂)
    ((isComparisonConj_comparisonConj _ _ _ _).trans_whiskerLeft _ _ (by
      simp only [derivedBlackCross, Category.assoc, Iso.inv_hom_id, Category.comp_id]))
    ((isComparisonConj_comparisonConj _ _ _ _).trans_whiskerLeft _ _ (by
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]))
    (derivedSquareIso_whisker _ _ hcross)

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

/-- **`𝕂 ⋙ 𝔈_i² ≅ 𝔈_i² ⋙ 𝕂` carries the crossing to the crossing on derived categories of dg
modules, for
`j < ℓ`** (Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21), for the
pasting of the isomorphisms of `CupCap.capAppendDataMid` at `ν` and at `{i} + ν`.
Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`. -/
theorem capEDerivedIsoPasteMid_cross (h : j < ℓ) :
    letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := ν) hL hQ hκ hP hPL
      hfin hproj
    letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := νᵢ) hL hQ hκ hP hPL
      hfin hproj
    letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := νᵢᵢ) hL hQ hκ hP hPL
      hfin hproj
    Functor.whiskerLeft (coevaluationFunctor.{0, w} k Q Λ Λc j hj νᵢᵢ ν₀ L)
        (dgPlusCross.{w, w'} k Q Λ Λc j hj ν₀ ν i hQ) ≫
        (capEDerivedIsoPaste.{w, w'}
          (capAppendDataMid (hL := hL) ν i (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP hPL hκ
            hQ hfin h)
          (capAppendDataMid (hL := hL) νᵢ i (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP hPL
            hκ hQ hfin h)).hom =
      (capEDerivedIsoPaste.{w, w'}
          (capAppendDataMid (hL := hL) ν i (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP hPL hκ
            hQ hfin h)
          (capAppendDataMid (hL := hL) νᵢ i (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP hPL
            hκ hQ hfin h)).hom ≫
        Functor.whiskerRight (dgBlackCross.{w, w'} ν i)
          (coevaluationFunctor.{0, w} k Q Λ Λc j hj ν ν₀ L) :=
  have := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := ν) hL hQ hκ hP hPL
    hfin hproj
  have := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := νᵢ) hL hQ hκ hP hPL
    hfin hproj
  have := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := νᵢᵢ) hL hQ hκ hP hPL
    hfin hproj
  capEDerivedIsoPaste_cross hQ _ _
    (capECompIsoOfEqMid_cross ν i (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL)
      (midKLRRel hκ hP hPL) hP hPL hκ hQ hfin h)

/-- **`𝕂 ⋙ 𝔈_i² ≅ 𝔈_i² ⋙ 𝕂` carries the crossing to the crossing on derived categories of dg
modules, for
`j = ℓ`** (Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21), for the
pasting of the isomorphisms of `CupCap.capAppendDataTop` at `ν` and at `{i} + ν`.
Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`. -/
theorem capEDerivedIsoPasteTop_cross (h : ¬ j < ℓ) :
    letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := ν) hL hQ hκ hP hPL
      hfin hproj
    letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := νᵢ) hL hQ hκ hP hPL
      hfin hproj
    letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := νᵢᵢ) hL hQ hκ hP hPL
      hfin hproj
    Functor.whiskerLeft (coevaluationFunctor.{0, w} k Q Λ Λc j hj νᵢᵢ ν₀ L)
        (dgPlusCross.{w, w'} k Q Λ Λc j hj ν₀ ν i hQ) ≫
        (capEDerivedIsoPaste.{w, w'}
          (capAppendDataTop (hL := hL) ν i (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP hPL hκ
            hQ hfin h)
          (capAppendDataTop (hL := hL) νᵢ i (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP hPL
            hκ hQ hfin h)).hom =
      (capEDerivedIsoPaste.{w, w'}
          (capAppendDataTop (hL := hL) ν i (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP hPL hκ
            hQ hfin h)
          (capAppendDataTop (hL := hL) νᵢ i (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP hPL
            hκ hQ hfin h)).hom ≫
        Functor.whiskerRight (dgBlackCross.{w, w'} ν i)
          (coevaluationFunctor.{0, w} k Q Λ Λc j hj ν ν₀ L) :=
  have := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := ν) hL hQ hκ hP hPL
    hfin hproj
  have := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := νᵢ) hL hQ hκ hP hPL
    hfin hproj
  have := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := νᵢᵢ) hL hQ hκ hP hPL
    hfin hproj
  capEDerivedIsoPaste_cross hQ _ _
    (capECompIsoOfEqTop_cross ν i (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL)
      (midKLRRel hκ hP hPL) hP hPL hκ hQ hfin h)

end Cases

end Two

end Categorification.Stendhal.CupCap
