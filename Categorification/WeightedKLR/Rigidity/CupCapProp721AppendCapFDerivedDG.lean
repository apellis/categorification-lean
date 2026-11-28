/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapFDerived
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapFDotCap
import Categorification.WeightedKLR.Rigidity.CupCapProp721ComparisonSquare

/-!
# `𝕂 ∘ 𝔉_i ≅ 𝔉_i ∘ 𝕂` and the dot, on derived categories of dg modules

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, the part for `𝔉_i`. The isomorphism `𝕂 ⋙ 𝔉_i ≅ 𝔉_i ⋙ 𝕂` of functors between
derived categories of dg modules (`CupCap.capFDerivedIsoOfData`) is conjugate, along the fully
faithful comparisons with Mathlib's derived categories of modules, to the derived functor of
`CupCap.capFOrdIso` (`CupCap.capFDerivedIsoOfData_isComparisonSquare`), and, after the
identification of induction along `appendBlackTPAOp` with `blackFOfEq`
(`CupCap.indFunctorIsoOfEq`), to the derived functor of `CupCap.capFOrdIsoOfEq`
(`CupCap.capFDerivedIsoOfData_isComparisonSquareOfEq`).

The dots on the dg derived functors `derivedBlackF` and `CupCap.derivedPlusF` are the
conjugates of the derived dots `indDotOfEq` (`CupCap.dgBlackFDot`, `CupCap.dgPlusFDot`), and the
module-level compatibility passes to the dg side (`CupCap.capFDerivedIsoOfData_dot`,
`CupCap.capFDerivedIsoMid_dot`, `CupCap.capFDerivedIsoTop_dot`).

The exactness of `𝔉_i` and `𝔉⁺_i` (Theorem 4.31, from `C` and `IsRouquierQ C Q`) enters as
instance arguments in the generic statements and is supplied in the two cases.

Route hypotheses (tracked): as for `CupCap.capFDerivedIsoMid`: `hL`, `hQ`, `hκ`, `hP`, `hPL`,
`hfin`, `hproj`; `hRq : IsRouquierQ C Q` is Webster's setting for Theorem 4.31.
-/

set_option backward.isDefEq.respectTransparency false

universe w w'

noncomputable section

namespace Categorification.Stendhal.CupCap

open CategoryTheory KLR KLRAlgebra MulOpposite InductionAlong DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance] OpBimodule.projective_opOp

section Additive

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {n : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ' : Fin n → I →₀ ℕ) (i : I) {μ β : Multiset I}
  (h : ({i} : Multiset I) + μ = β)

private theorem blackF_additive_capFDG (ν : Multiset I) : (blackF Q Λ' i ν).Additive :=
  inferInstanceAs (InductionAlong.functor.{0, 0} (appendBlackOp Q Λ' i ν)).Additive

private theorem blackFOfEq_additive_capFDG : (blackFOfEq Q Λ' i h).Additive :=
  inferInstanceAs (InductionAlong.functor.{0, 0} (appendBlackOpOfEq Q Λ' i h)).Additive

end Additive

attribute [local instance] blackF_additive_capFDG blackFOfEq_additive_capFDG

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
set_option hygiene false in
local notation "Fᵖ" => blackFOfEq Q (plusLabels Λ Λc j hj) i (plusWeight_assoc ν ν₀ i)

variable (k Q Λ Λc j hj ν₀) in
/-- `𝔉⁺_i` along `plusWeight_assoc` is exact once induction along `appendBlackTPAOp` is. -/
theorem blackFOfEqPlus_preservesFiniteLimits
    [Limits.PreservesFiniteLimits (InductionAlong.functor.{0, 0} aT)] :
    Limits.PreservesFiniteLimits Fᵖ :=
  Limits.preservesFiniteLimits_of_natIso
    (indFunctorIsoOfEq (appendBlackTPAOp_eq_ofEq k Q Λ Λc j hj ν₀ ν i))

variable (k Q Λ Λc j hj ν₀) in
/-- `𝔉⁺_i` along `plusWeight_assoc` is exact once induction along `appendBlackTPAOp` is. -/
theorem blackFOfEqPlus_preservesFiniteColimits
    [Limits.PreservesFiniteColimits (InductionAlong.functor.{0, 0} aT)] :
    Limits.PreservesFiniteColimits Fᵖ :=
  Limits.preservesFiniteColimits_of_natIso
    (indFunctorIsoOfEq (appendBlackTPAOp_eq_ofEq k Q Λ Λc j hj ν₀ ν i))

section Generic

variable [DG.HasDerivedCategory.{w, 0} TAᵐᵒᵖ] [DG.HasDerivedCategory.{w, 0} TAᵢᵐᵒᵖ]
  [DG.HasDerivedCategory.{w, 0} TPpᵐᵒᵖ] [DG.HasDerivedCategory.{w, 0} TPpᵢᵐᵒᵖ]
  [HasDerivedCategory.{w'} (ModuleCat.{0} TAᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} TAᵢᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} TPpᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} TPpᵢᵐᵒᵖ)]
  [hFl : Limits.PreservesFiniteLimits (blackF Q Λ i ν)]
  [hFc : Limits.PreservesFiniteColimits (blackF Q Λ i ν)]
  [Limits.PreservesFiniteLimits (InductionAlong.functor.{0, 0} aT)]
  [Limits.PreservesFiniteColimits (InductionAlong.functor.{0, 0} aT)]
  [Limits.PreservesFiniteLimits Fᵖ] [Limits.PreservesFiniteColimits Fᵖ]

variable (C : QuantumGroup.CartanDatum I) (hRq : IsRouquierQ C Q)

variable (k Q Λ Λc j hj ν₀) in
/-- `derivedPlusF` followed by the comparison is the comparison followed by the derived functor
of `blackFOfEq` along `plusWeight_assoc`: `CupCap.derivedPlusFComparisonIso` composed with the
derived functor of `CupCap.indFunctorIsoOfEq`. -/
def derivedPlusFComparisonIsoOfEq :
    derivedPlusF.{w} k Q Λ Λc j hj ν₀ ν i ⋙ derivedComparison.{w, w'} TPpᵢᵐᵒᵖ ≅
      derivedComparison.{w, w'} TPpᵐᵒᵖ ⋙ Fᵖ.mapDerivedCategory :=
  derivedPlusFComparisonIso.{w, w'} k Q Λ Λc j hj ν₀ ν i C hRq ≪≫
    Functor.isoWhiskerLeft _ (mapDerivedCategoryIsoOfIso
      (indFunctorIsoOfEq (appendBlackTPAOp_eq_ofEq k Q Λ Λc j hj ν₀ ν i)))

variable {ν i}

omit [Limits.PreservesFiniteLimits (blackF Q Λ i ν)]
  [Limits.PreservesFiniteColimits (blackF Q Λ i ν)]
  [Limits.PreservesFiniteLimits (InductionAlong.functor.{0, 0} aT)]
  [Limits.PreservesFiniteColimits (InductionAlong.functor.{0, 0} aT)]
  [Limits.PreservesFiniteLimits Fᵖ] [Limits.PreservesFiniteColimits Fᵖ] in
/-- **`CupCap.capFDerivedIsoOfData` is conjugate to the derived `CupCap.capFOrdIso`** along the
comparisons of derived categories (Webster, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21). -/
theorem capFDerivedIsoOfData_isComparisonSquare (D : CapFData k Q Λ Λc j hj ν₀ L ν i)
    [Module.Projective TA CB] [Module.Projective TAᵢ CBᵢ] :
    IsComparisonSquare (derivedBlackFComparisonIso.{w, w'} Q Λ i ν C hRq)
      (coevaluationComparisonOrdIso.{w, w'} k Q Λ Λc j hj ν₀ L _)
      (coevaluationComparisonOrdIso.{w, w'} k Q Λ Λc j hj ν₀ L ν)
      (derivedPlusFComparisonIso.{w, w'} k Q Λ Λc j hj ν₀ ν i C hRq)
      (derivedSquareIso (capFOrdIso D)) (capFDerivedIsoOfData.{w, w'} C hRq D) := fun x => by
  refine (congrArg (fun t => NatTrans.app t x)
    (((Functor.FullyFaithful.ofFullyFaithful (derivedComparison.{w, w'} TPpᵢᵐᵒᵖ)).whiskeringRight
      _).map_preimage _)).trans ?_
  simp [derivedSquareIso, capFDerivedOrdIso]

set_option linter.unusedSectionVars false in
/-- **`CupCap.capFDerivedIsoOfData` is conjugate to the derived `CupCap.capFOrdIsoOfEq`**, with
`𝔉⁺_i = blackFOfEq` along `plusWeight_assoc` on the module side (Webster, arXiv:1309.3796v3,
§7.3, proof of Proposition 7.21). This links `CupCap.capFOrdIsoOfEq` with `CupCap.capFOrdIso`
through `CupCap.indFunctorIsoOfEq`. -/
theorem capFDerivedIsoOfData_isComparisonSquareOfEq (D : CapFData k Q Λ Λc j hj ν₀ L ν i)
    [Module.Projective TA CB] [Module.Projective TAᵢ CBᵢ] :
    IsComparisonSquare (derivedBlackFComparisonIso.{w, w'} Q Λ i ν C hRq)
      (coevaluationComparisonOrdIso.{w, w'} k Q Λ Λc j hj ν₀ L _)
      (coevaluationComparisonOrdIso.{w, w'} k Q Λ Λc j hj ν₀ L ν)
      (derivedPlusFComparisonIsoOfEq.{w, w'} k Q Λ Λc j hj ν₀ ν i C hRq)
      (derivedSquareIso (capFOrdIsoOfEq D)) (capFDerivedIsoOfData.{w, w'} C hRq D) :=
  (capFDerivedIsoOfData_isComparisonSquare C hRq D).changeY _
    ((derivedSquareIso_trans_whiskerLeft _ _).trans (by rw [mapDerivedCategoryIsoOfIso_hom_eq]))

variable (ν i)

/-- **The dot on the dg derived `𝔉_i`** of right `T^λ`-modules: the conjugate of the derived
dot `indDotOfEq` along `derivedBlackFComparisonIso`. -/
def dgBlackFDot : derivedBlackF.{w} Q Λ i ν ⟶ derivedBlackF.{w} Q Λ i ν :=
  comparisonConj (Functor.FullyFaithful.ofFullyFaithful (derivedComparison.{w, w'} TAᵢᵐᵒᵖ))
    (derivedBlackFComparisonIso.{w, w'} Q Λ i ν C hRq)
    (derivedBlackFComparisonIso.{w, w'} Q Λ i ν C hRq)
    (NatTrans.mapDerivedCategory
      (indDotOfEq Q Λ i (rfl : ({i} : Multiset I) + ν = _) : blackF Q Λ i ν ⟶ blackF Q Λ i ν))

variable (k Q Λ Λc j hj ν₀) in
/-- **The dot on the dg derived `𝔉⁺_i`** of right `T^{λ⁺}`-modules: the conjugate of the
derived dot `indDotOfEq` along `CupCap.derivedPlusFComparisonIsoOfEq`. -/
def dgPlusFDot : derivedPlusF.{w} k Q Λ Λc j hj ν₀ ν i ⟶ derivedPlusF.{w} k Q Λ Λc j hj ν₀ ν i :=
  comparisonConj (Functor.FullyFaithful.ofFullyFaithful (derivedComparison.{w, w'} TPpᵢᵐᵒᵖ))
    (derivedPlusFComparisonIsoOfEq.{w, w'} k Q Λ Λc j hj ν₀ ν i C hRq)
    (derivedPlusFComparisonIsoOfEq.{w, w'} k Q Λ Λc j hj ν₀ ν i C hRq)
    (indDotOfEq Q (plusLabels Λ Λc j hj) i (plusWeight_assoc ν ν₀ i)).mapDerivedCategory

variable {ν i}

set_option linter.unusedSectionVars false in
/-- **`𝕂 ⋙ 𝔉_i ≅ 𝔉_i ⋙ 𝕂` carries the dot to the dot on derived categories of dg modules**
(Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21), from the module-level
compatibility for `CupCap.capFOrdIsoOfEq D`. -/
theorem capFDerivedIsoOfData_dot (D : CapFData k Q Λ Λc j hj ν₀ L ν i)
    [Module.Projective TA CB] [Module.Projective TAᵢ CBᵢ]
    (hdot : (Functor.whiskerRight (indDotOfEq Q Λ i (rfl : ({i} : Multiset I) + ν = _)) OrdKᵢ :
        blackF Q Λ i ν ⋙ OrdKᵢ ⟶ blackF Q Λ i ν ⋙ OrdKᵢ) ≫ (capFOrdIsoOfEq D).hom =
      (capFOrdIsoOfEq D).hom ≫ Functor.whiskerLeft OrdK
        (indDotOfEq Q (plusLabels Λ Λc j hj) i (plusWeight_assoc ν ν₀ i))) :
    Functor.whiskerLeft (coevaluationFunctor.{0, w} k Q Λ Λc j hj ν ν₀ L)
        (dgPlusFDot.{w, w'} k Q Λ Λc j hj ν₀ ν i C hRq) ≫
        (capFDerivedIsoOfData.{w, w'} C hRq D).hom =
      (capFDerivedIsoOfData.{w, w'} C hRq D).hom ≫
        Functor.whiskerRight (dgBlackFDot.{w, w'} ν i C hRq)
          (coevaluationFunctor.{0, w} k Q Λ Λc j hj _ ν₀ L) :=
  (capFDerivedIsoOfData_isComparisonSquareOfEq C hRq D).whisker
    (capFDerivedIsoOfData_isComparisonSquareOfEq C hRq D)
    (isComparisonConj_comparisonConj _ _ _ _) (isComparisonConj_comparisonConj _ _ _ _)
    (derivedSquareIso_whisker _ _ hdot)

end Generic

section Cases

variable [DG.HasDerivedCategory.{w, 0} TAᵐᵒᵖ] [DG.HasDerivedCategory.{w, 0} TAᵢᵐᵒᵖ]
  [DG.HasDerivedCategory.{w, 0} TPpᵐᵒᵖ] [DG.HasDerivedCategory.{w, 0} TPpᵢᵐᵒᵖ]
  [HasDerivedCategory.{w'} (ModuleCat.{0} TAᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} TAᵢᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} TPpᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} TPpᵢᵐᵒᵖ)]
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

/-- **`𝕂 ⋙ 𝔉_i ≅ 𝔉_i ⋙ 𝕂` carries the dot to the dot on derived categories of dg modules, for
`j < ℓ`** (Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21). Route hypotheses
(tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`; `hRq` is Webster's setting for
Theorem 4.31. -/
theorem capFDerivedIsoMid_dot (h : j < ℓ) :
    letI := blackF_preservesFiniteLimits Q Λ i ν C hRq
    letI := blackF_preservesFiniteColimits Q Λ i ν C hRq
    letI := projective_plusCorner k Q Λ Λc j hj ν₀ ν i C hRq
    letI := functor_preservesFiniteLimits aT
    letI := functor_preservesFiniteColimits aT
    letI := blackFOfEqPlus_preservesFiniteLimits k Q Λ Λc j hj ν₀ ν i
    letI := blackFOfEqPlus_preservesFiniteColimits k Q Λ Λc j hj ν₀ ν i
    Functor.whiskerLeft (coevaluationFunctor.{0, w} k Q Λ Λc j hj ν ν₀ L)
        (dgPlusFDot.{w, w'} k Q Λ Λc j hj ν₀ ν i C hRq) ≫
        (capFDerivedIsoMid.{w, w'} ν i hL hQ hκ hP hPL hfin hproj C hRq h).hom =
      (capFDerivedIsoMid.{w, w'} ν i hL hQ hκ hP hPL hfin hproj C hRq h).hom ≫
        Functor.whiskerRight (dgBlackFDot.{w, w'} ν i C hRq)
          (coevaluationFunctor.{0, w} k Q Λ Λc j hj _ ν₀ L) :=
  letI := blackF_preservesFiniteLimits Q Λ i ν C hRq
  letI := blackF_preservesFiniteColimits Q Λ i ν C hRq
  letI := projective_plusCorner k Q Λ Λc j hj ν₀ ν i C hRq
  letI := functor_preservesFiniteLimits aT
  letI := functor_preservesFiniteColimits aT
  letI := blackFOfEqPlus_preservesFiniteLimits k Q Λ Λc j hj ν₀ ν i
  letI := blackFOfEqPlus_preservesFiniteColimits k Q Λ Λc j hj ν₀ ν i
  have := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := ν) hL hQ hκ hP hPL hfin
    hproj
  have := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ)
    (ν := (Singleton.singleton i : Multiset I) + ν) hL hQ hκ hP hPL hfin hproj
  capFDerivedIsoOfData_dot C hRq _
    (capFOrdIsoOfEqMid_dot (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP hPL hκ h)

/-- **`𝕂 ⋙ 𝔉_i ≅ 𝔉_i ⋙ 𝕂` carries the dot to the dot on derived categories of dg modules, for
`j = ℓ`** (Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21). Route hypotheses
(tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`; `hRq` is Webster's setting for
Theorem 4.31. -/
theorem capFDerivedIsoTop_dot (h : ¬ j < ℓ) :
    letI := blackF_preservesFiniteLimits Q Λ i ν C hRq
    letI := blackF_preservesFiniteColimits Q Λ i ν C hRq
    letI := projective_plusCorner k Q Λ Λc j hj ν₀ ν i C hRq
    letI := functor_preservesFiniteLimits aT
    letI := functor_preservesFiniteColimits aT
    letI := blackFOfEqPlus_preservesFiniteLimits k Q Λ Λc j hj ν₀ ν i
    letI := blackFOfEqPlus_preservesFiniteColimits k Q Λ Λc j hj ν₀ ν i
    Functor.whiskerLeft (coevaluationFunctor.{0, w} k Q Λ Λc j hj ν ν₀ L)
        (dgPlusFDot.{w, w'} k Q Λ Λc j hj ν₀ ν i C hRq) ≫
        (capFDerivedIsoTop.{w, w'} ν i hL hQ hκ hP hPL hfin hproj C hRq h).hom =
      (capFDerivedIsoTop.{w, w'} ν i hL hQ hκ hP hPL hfin hproj C hRq h).hom ≫
        Functor.whiskerRight (dgBlackFDot.{w, w'} ν i C hRq)
          (coevaluationFunctor.{0, w} k Q Λ Λc j hj _ ν₀ L) :=
  letI := blackF_preservesFiniteLimits Q Λ i ν C hRq
  letI := blackF_preservesFiniteColimits Q Λ i ν C hRq
  letI := projective_plusCorner k Q Λ Λc j hj ν₀ ν i C hRq
  letI := functor_preservesFiniteLimits aT
  letI := functor_preservesFiniteColimits aT
  letI := blackFOfEqPlus_preservesFiniteLimits k Q Λ Λc j hj ν₀ ν i
  letI := blackFOfEqPlus_preservesFiniteColimits k Q Λ Λc j hj ν₀ ν i
  have := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := ν) hL hQ hκ hP hPL hfin
    hproj
  have := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ)
    (ν := (Singleton.singleton i : Multiset I) + ν) hL hQ hκ hP hPL hfin hproj
  capFDerivedIsoOfData_dot C hRq _
    (capFOrdIsoOfEqTop_dot (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP hPL hκ h)

end Cases

end Categorification.Stendhal.CupCap
