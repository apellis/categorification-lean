/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721MateTransport
import Categorification.WeightedKLR.Rigidity.CupCapProp721CapMateModuleDerived

/-!
# The mate of `𝕂 ⋙ 𝔉_i ≅ 𝔉_i ⋙ 𝕂` on derived categories of dg modules

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21: the commutation isomorphisms of the coevaluation functor `𝕂` (Definition 7.18)
with `𝔉_i` and `𝔈_i` are compatible with the units and counits of `𝔉_i ⊣ 𝔈_i`. Along the
adjunctions `𝔉_i ⊣ 𝔈_i` on derived categories of dg modules over `T^λ` and `T^{λ⁺}`
(`CupCap.derivedBlackFEAdjunction`, `CupCap.derivedPlusFEAdjunction`), the mate of
`𝕂 ⋙ 𝔉_i ≅ 𝔉_i ⋙ 𝕂` is the inverse of `𝕂 ⋙ 𝔈_i ≅ 𝔈_i ⋙ 𝕂`. This is the statement on
Mathlib's derived categories (`CupCap.capFDerivedOrdIso_inv_mate`) passed through
`CupCap.mateEquiv_eq_of_comparison`; the two defining `preimageIso`s are characterised under the
comparison functors (`CupCap.capFDerivedIsoOfData_hom_comparison`,
`CupCap.capEDerivedIsoOfData_inv_comparison`).

Route hypotheses (tracked): for `CupCap.capFDerivedIsoOfData_hom_mate`, the compatibility `hD`
of the two bimodule data and projectivity of `K_ν`, `K_{{i} + ν}` as left modules; for the two
positions of the cap, `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`, as for
`CupCap.capFDerivedIsoMid` (`hD` is discharged by `CupCap.capFImageEquivMid_unitGen`,
`CupCap.capFImageEquivTop_unitGen`). `IsRouquierQ C Q` is Webster's setting for Theorem 4.31.

## Main results

* `CupCap.capFDerivedIsoOfData_hom_mate`.
* `CupCap.capFDerivedIsoMid_hom_mate`, `CupCap.capFDerivedIsoTop_hom_mate`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open CategoryTheory Limits KLR KLRAlgebra MulOpposite InductionAlong DG.DegreeZero

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

private theorem blackE_additive_capMateDG : (blackE Q Λ i ν).Additive :=
  inferInstanceAs (resFunctor.{0, 0} (appendBlackOp Q Λ i ν)).Additive

private theorem blackF_additive_capMateDG : (blackF Q Λ i ν).Additive :=
  inferInstanceAs (InductionAlong.functor.{0, 0} (appendBlackOp Q Λ i ν)).Additive

attribute [local instance] blackE_additive_capMateDG blackF_additive_capMateDG

variable [DG.HasDerivedCategory.{0, 0} TAᵐᵒᵖ] [DG.HasDerivedCategory.{0, 0} TAᵢᵐᵒᵖ]
  [DG.HasDerivedCategory.{0, 0} TPpᵐᵒᵖ] [DG.HasDerivedCategory.{0, 0} TPpᵢᵐᵒᵖ]
  [HasDerivedCategory.{0} (ModuleCat.{0} TAᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} TAᵢᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} TPpᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} TPpᵢᵐᵒᵖ)]

section Data

variable (C : QuantumGroup.CartanDatum I) (hRq : IsRouquierQ C Q)
  (D : CapAppendData k Q Λ Λc j hj ν₀ L ν i) (D' : CapFData k Q Λ Λc j hj ν₀ L ν i)
  [Module.Projective TA CB] [Module.Projective TAᵢ CBᵢ]

/-- Under the comparison functor, `capFDerivedIsoOfData` is the composite of the comparison
isomorphisms with the inverse of `capFDerivedOrdIso`. -/
theorem capFDerivedIsoOfData_hom_comparison (a : DG.DerivedCategory.{0} TAᵐᵒᵖ) :
    letI := blackF_preservesFiniteLimits Q Λ i ν C hRq
    letI := blackF_preservesFiniteColimits Q Λ i ν C hRq
    letI := projective_plusCorner k Q Λ Λc j hj ν₀ ν i C hRq
    letI := functor_preservesFiniteLimits aT
    letI := functor_preservesFiniteColimits aT
    (derivedComparison.{0, 0} TPpᵢᵐᵒᵖ).map ((capFDerivedIsoOfData.{0, 0} C hRq D').hom.app a) =
      (derivedPlusFComparisonIso.{0, 0} k Q Λ Λc j hj ν₀ ν i C hRq).hom.app
          ((coevaluationFunctor.{0, 0} k Q Λ Λc j hj ν ν₀ L).obj a) ≫
        ((InductionAlong.functor.{0, 0} aT).mapDerivedCategory).map
          ((coevaluationComparisonOrdIso.{0, 0} k Q Λ Λc j hj ν₀ L ν).hom.app a) ≫
        (capFDerivedOrdIso.{0} C hRq D').inv.app (derivedComparison.{0, 0} TAᵐᵒᵖ |>.obj a) ≫
        ((OrdKᵢ).mapDerivedCategory).map
          ((derivedBlackFComparisonIso.{0, 0} Q Λ i ν C hRq).inv.app a) ≫
        (coevaluationComparisonOrdIso.{0, 0} k Q Λ Λc j hj ν₀ L _).inv.app
          ((derivedBlackF.{0} Q Λ i ν).obj a) := by
  let := blackF_preservesFiniteLimits Q Λ i ν C hRq
  let := blackF_preservesFiniteColimits Q Λ i ν C hRq
  let := projective_plusCorner k Q Λ Λc j hj ν₀ ν i C hRq
  let := functor_preservesFiniteLimits aT
  let := functor_preservesFiniteColimits aT
  have key : ∀ {G₁ G₂ : DG.DerivedCategory.{0} TAᵐᵒᵖ ⥤ DG.DerivedCategory.{0} TPpᵢᵐᵒᵖ}
      (f : G₁ ⋙ derivedComparison.{0, 0} TPpᵢᵐᵒᵖ ⟶ G₂ ⋙ derivedComparison.{0, 0} TPpᵢᵐᵒᵖ),
      (derivedComparison.{0, 0} TPpᵢᵐᵒᵖ).map ((((Functor.FullyFaithful.ofFullyFaithful
        (derivedComparison.{0, 0} TPpᵢᵐᵒᵖ)).whiskeringRight
          (DG.DerivedCategory.{0} TAᵐᵒᵖ)).preimage f).app a) = f.app a := fun f =>
    NatTrans.congr_app (((Functor.FullyFaithful.ofFullyFaithful
      (derivedComparison.{0, 0} TPpᵢᵐᵒᵖ)).whiskeringRight
        (DG.DerivedCategory.{0} TAᵐᵒᵖ)).map_preimage f) a
  simp only [capFDerivedIsoOfData, Functor.FullyFaithful.preimageIso_hom, key, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id]

/-- Under the comparison functor, the inverse of `capEDerivedIsoOfData` is the composite of the
comparison isomorphisms with `capEDerivedOrdIso`. -/
theorem capEDerivedIsoOfData_inv_comparison
    (d : DG.DerivedCategory.{0} TAᵢᵐᵒᵖ) :
    (derivedComparison.{0, 0} TPpᵐᵒᵖ).map ((capEDerivedIsoOfData.{0, 0} D).inv.app d) =
      (coevaluationComparisonOrdIso.{0, 0} k Q Λ Λc j hj ν₀ L ν).hom.app
          ((derivedBlackE.{0} Q Λ i ν).obj d) ≫
        ((OrdK).mapDerivedCategory).map
          ((derivedBlackEComparisonIso.{0, 0} Q Λ i ν).hom.app d) ≫
        (capEDerivedOrdIso.{0} D).hom.app (derivedComparison.{0, 0} TAᵢᵐᵒᵖ |>.obj d) ≫
        ((resFunctor.{0, 0} aT).mapDerivedCategory).map
          ((coevaluationComparisonOrdIso.{0, 0} k Q Λ Λc j hj ν₀ L _).inv.app d) ≫
        (derivedPlusEComparisonIso.{0, 0} k Q Λ Λc j hj ν₀ ν i).inv.app
          ((coevaluationFunctor.{0, 0} k Q Λ Λc j hj ((Singleton.singleton i : Multiset I) + ν)
            ν₀ L).obj d) := by
  have key : ∀ {G₁ G₂ : DG.DerivedCategory.{0} TAᵢᵐᵒᵖ ⥤ DG.DerivedCategory.{0} TPpᵐᵒᵖ}
      (f : G₁ ⋙ derivedComparison.{0, 0} TPpᵐᵒᵖ ⟶ G₂ ⋙ derivedComparison.{0, 0} TPpᵐᵒᵖ),
      (derivedComparison.{0, 0} TPpᵐᵒᵖ).map ((((Functor.FullyFaithful.ofFullyFaithful
        (derivedComparison.{0, 0} TPpᵐᵒᵖ)).whiskeringRight
          (DG.DerivedCategory.{0} TAᵢᵐᵒᵖ)).preimage f).app d) = f.app d := fun f =>
    NatTrans.congr_app (((Functor.FullyFaithful.ofFullyFaithful
      (derivedComparison.{0, 0} TPpᵐᵒᵖ)).whiskeringRight
        (DG.DerivedCategory.{0} TAᵢᵐᵒᵖ)).map_preimage f) d
  simp only [capEDerivedIsoOfData, Functor.FullyFaithful.preimageIso_inv, key, Iso.trans_inv,
    Iso.symm_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id, Category.assoc]

/-- **The mate of `𝕂 ⋙ 𝔉_i ≅ 𝔉_i ⋙ 𝕂` is `𝔈_i ⋙ 𝕂 ≅ 𝕂 ⋙ 𝔈_i` on derived categories of dg
modules** (Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21), along `𝔉_i ⊣ 𝔈_i` on
both sides, provided `D'.bwd (1 ⊗ c) = D.iota c`. -/
theorem capFDerivedIsoOfData_hom_mate
    (hD : ∀ c : CB, D'.bwd (Ind.tmul (unitGen aT) c) = D.iota c) :
    (mateEquiv (derivedBlackFEAdjunction ν i C hRq) (derivedPlusFEAdjunction ν i C hRq)
      (TwoSquare.mk _ _ _ _ (capFDerivedIsoOfData.{0, 0} C hRq D').hom)).natTrans =
      (capEDerivedIsoOfData.{0, 0} D).inv := by
  let := blackF_preservesFiniteLimits Q Λ i ν C hRq
  let := blackF_preservesFiniteColimits Q Λ i ν C hRq
  let := projective_plusCorner k Q Λ Λc j hj ν₀ ν i C hRq
  let := functor_preservesFiniteLimits aT
  let := functor_preservesFiniteColimits aT
  exact mateEquiv_eq_of_comparison
    (derivedBlackFComparisonIso.{0, 0} Q Λ i ν C hRq) (derivedBlackEComparisonIso.{0, 0} Q Λ i ν)
    (derivedPlusFComparisonIso.{0, 0} k Q Λ Λc j hj ν₀ ν i C hRq)
    (derivedPlusEComparisonIso.{0, 0} k Q Λ Λc j hj ν₀ ν i)
    (coevaluationComparisonOrdIso.{0, 0} k Q Λ Λc j hj ν₀ L ν)
    (coevaluationComparisonOrdIso.{0, 0} k Q Λ Λc j hj ν₀ L _)
    (adj' := derivedBlackAdjunction.{0} Q Λ i ν C hRq)
    (adjP' := (InductionAlong.adjunction.{0, 0} aT).mapDerivedCategory)
    (fun d => adjunctionOfComparison_counit_map (derivedComparisonEquivalence.{0, 0} TAᵐᵒᵖ)
      (derivedComparisonEquivalence.{0, 0} TAᵢᵐᵒᵖ) (derivedBlackAdjunction.{0} Q Λ i ν C hRq)
      (derivedBlackFComparisonIso.{0, 0} Q Λ i ν C hRq)
      (derivedBlackEComparisonIso.{0, 0} Q Λ i ν) d)
    (fun d => adjunctionOfComparison_counit_map (derivedComparisonEquivalence.{0, 0} TPpᵐᵒᵖ)
      (derivedComparisonEquivalence.{0, 0} TPpᵢᵐᵒᵖ)
      (InductionAlong.adjunction.{0, 0} aT).mapDerivedCategory
      (derivedPlusFComparisonIso.{0, 0} k Q Λ Λc j hj ν₀ ν i C hRq)
      (derivedPlusEComparisonIso.{0, 0} k Q Λ Λc j hj ν₀ ν i) d)
    _ _ (capFDerivedOrdIso_inv_mate C hRq D D' hD) _ _
    (capFDerivedIsoOfData_hom_comparison C hRq D')
    (capEDerivedIsoOfData_inv_comparison D)

end Data

/-! ### The two positions of the cap -/

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
  (C : QuantumGroup.CartanDatum I) (hRq : IsRouquierQ C Q)

variable (ν i)

/-- **The mate of `𝕂 ⋙ 𝔉_i ≅ 𝔉_i ⋙ 𝕂` is `𝔈_i ⋙ 𝕂 ≅ 𝕂 ⋙ 𝔈_i` for `j < ℓ`** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.21), on derived categories of dg modules, along
`𝔉_i ⊣ 𝔈_i` on both sides.

Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`; `hRq` is
Webster's setting for Theorem 4.31. -/
theorem capFDerivedIsoMid_hom_mate (h : j < ℓ) :
    (mateEquiv (derivedBlackFEAdjunction (Λ := Λ) ν i C hRq)
      (derivedPlusFEAdjunction (Λc := Λc) (hj := hj) (ν₀ := ν₀) ν i C hRq)
      (TwoSquare.mk _ _ _ _
        (capFDerivedIsoMid.{0, 0} (Λ := Λ) (hj := hj) ν i hL hQ hκ hP hPL hfin hproj C hRq
          h).hom)).natTrans =
      (capEDerivedIsoMid.{0, 0} ν i hL hQ hκ hP hPL hfin hproj h).inv := by
  have := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := ν) hL hQ hκ hP hPL hfin
    hproj
  have := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ)
    (ν := (Singleton.singleton i : Multiset I) + ν) hL hQ hκ hP hPL hfin hproj
  exact capFDerivedIsoOfData_hom_mate C hRq _ _
    (capFImageEquivMid_unitGen (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP hPL hκ h)

/-- **The mate of `𝕂 ⋙ 𝔉_i ≅ 𝔉_i ⋙ 𝕂` is `𝔈_i ⋙ 𝕂 ≅ 𝕂 ⋙ 𝔈_i` for `j = ℓ`** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.21), on derived categories of dg modules, along
`𝔉_i ⊣ 𝔈_i` on both sides.

Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`; `hRq` is
Webster's setting for Theorem 4.31. -/
theorem capFDerivedIsoTop_hom_mate (h : ¬ j < ℓ) :
    (mateEquiv (derivedBlackFEAdjunction (Λ := Λ) ν i C hRq)
      (derivedPlusFEAdjunction (Λc := Λc) (hj := hj) (ν₀ := ν₀) ν i C hRq)
      (TwoSquare.mk _ _ _ _
        (capFDerivedIsoTop.{0, 0} (Λ := Λ) (hj := hj) ν i hL hQ hκ hP hPL hfin hproj C hRq
          h).hom)).natTrans =
      (capEDerivedIsoTop.{0, 0} ν i hL hQ hκ hP hPL hfin hproj h).inv := by
  have := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := ν) hL hQ hκ hP hPL hfin
    hproj
  have := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ)
    (ν := (Singleton.singleton i : Multiset I) + ν) hL hQ hκ hP hPL hfin hproj
  exact capFDerivedIsoOfData_hom_mate C hRq _ _
    (capFImageEquivTop_unitGen (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP hPL hκ h)

end Cases

end Categorification.Stendhal.CupCap
