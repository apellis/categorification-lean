/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721CapMateEF
import Categorification.WeightedKLR.Rigidity.CupCapProp721CapMateTrace
import Categorification.WeightedKLR.Rigidity.CupCapProp721TraceShiftF

/-!
# `𝕂 ⋙ 𝔈_i ≅ 𝔈_i ⋙ 𝕂` and the cups and caps of `𝔈_i ⊣ 𝔉_i` on dg modules

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21 and Definition 7.18, with the adjunction `𝔈_i ⊣ 𝔉_i` of Theorem 4.31. Along
`𝔈_i ⊣ 𝔉_i` on derived categories of dg modules over `T^λ` and `T^{λ⁺}`
(`CupCap.derivedBlackEFAdjunction`, `CupCap.derivedPlusEFAdjunction`), the mate of
`𝕂 ⋙ 𝔈⁺_i ≅ 𝔈_i ⋙ 𝕂` is the inverse of `𝕂 ⋙ 𝔉⁺_i ≅ 𝔉_i ⋙ 𝕂`
(`CupCap.capEDerivedIsoOfData_hom_mateEF`), under the module-level route hypothesis
`CupCap.CapEFMateCompatible`. The proof is the transport `CupCap.mateEquiv_eq_of_comparison` of
`CupCap.capEDerivedOrdIso_inv_mateEF`, with the two `preimageIso`s read off under the comparison
functors (`CupCap.capEDerivedIsoOfData_hom_comparison`,
`CupCap.capFDerivedIsoOfData_inv_comparison`).

Consequently the isomorphism `𝔉⁺_i ⋙ RHom(K, -) ≅ RHom(K, -) ⋙ 𝔉_i`, defined by taking adjoints
along `𝔈_i ⊣ 𝔉_i` (`CupCap.capFRightAdjointIso`), is the mate of the inverse of
`𝕂 ⋙ 𝔉⁺_i ≅ 𝔉_i ⋙ 𝕂` along the coevaluation adjunctions `𝕂 ⊣ RHom(K, -)`
(`CupCap.capFRightAdjointIso_inv_eq_mate`), and likewise on the quantum trace `𝕋`
(`CupCap.capFQuantumTraceShiftIso_inv_eq_mate`).

## Main definitions

* `CupCap.CapEFMateCompatibleCases`: the route hypothesis `CupCap.CapEFMateCompatible` for the
  data of both positions of the cap (`j < ℓ` and `j = ℓ`).

## Main results

* `CupCap.capEDerivedIsoOfData_hom_mateEF`.
* `CupCap.capEDerivedIso_hom_mateEF` (every `j ≤ ℓ`).
* `CupCap.capFRightAdjointIso_inv_eq_mate`, `CupCap.capFQuantumTraceShiftIso_inv_eq_mate`.

Route hypotheses (tracked): `CupCap.CapEFMateCompatible` (in the cases,
`CupCap.CapEFMateCompatibleCases`); `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`, as for
`CupCap.capEDerivedIso`; `C`, `hRq : IsRouquierQ C Q` is Webster's setting for Theorem 4.31.
-/

set_option backward.isDefEq.respectTransparency false

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
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
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

private theorem blackE_additive_capMateEFDG : (blackE Q Λ i ν).Additive :=
  inferInstanceAs (resFunctor.{0, 0} (appendBlackOp Q Λ i ν)).Additive

private theorem blackF_additive_capMateEFDG : (blackF Q Λ i ν).Additive :=
  inferInstanceAs (InductionAlong.functor.{0, 0} (appendBlackOp Q Λ i ν)).Additive

attribute [local instance] blackE_additive_capMateEFDG blackF_additive_capMateEFDG

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

/-- Under the comparison functor, the inverse of `capFDerivedIsoOfData` is the composite of the
comparison isomorphisms with `capFDerivedOrdIso`. -/
theorem capFDerivedIsoOfData_inv_comparison (a : DG.DerivedCategory.{0} TAᵐᵒᵖ) :
    letI := blackF_preservesFiniteLimits Q Λ i ν C hRq
    letI := blackF_preservesFiniteColimits Q Λ i ν C hRq
    letI := projective_plusCorner k Q Λ Λc j hj ν₀ ν i C hRq
    letI := functor_preservesFiniteLimits aT
    letI := functor_preservesFiniteColimits aT
    (derivedComparison.{0, 0} TPpᵢᵐᵒᵖ).map ((capFDerivedIsoOfData.{0, 0} C hRq D').inv.app a) =
      (coevaluationComparisonOrdIso.{0, 0} k Q Λ Λc j hj ν₀ L _).hom.app
          ((derivedBlackF.{0} Q Λ i ν).obj a) ≫
        ((OrdKᵢ).mapDerivedCategory).map
          ((derivedBlackFComparisonIso.{0, 0} Q Λ i ν C hRq).hom.app a) ≫
        (capFDerivedOrdIso.{0} C hRq D').hom.app (derivedComparison.{0, 0} TAᵐᵒᵖ |>.obj a) ≫
        ((InductionAlong.functor.{0, 0} aT).mapDerivedCategory).map
          ((coevaluationComparisonOrdIso.{0, 0} k Q Λ Λc j hj ν₀ L ν).inv.app a) ≫
        (derivedPlusFComparisonIso.{0, 0} k Q Λ Λc j hj ν₀ ν i C hRq).inv.app
          ((coevaluationFunctor.{0, 0} k Q Λ Λc j hj ν ν₀ L).obj a) := by
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
  simp only [capFDerivedIsoOfData, Functor.FullyFaithful.preimageIso_inv, key, Iso.trans_inv,
    Iso.symm_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id, Category.assoc]

/-- Under the comparison functor, `capEDerivedIsoOfData` is the composite of the comparison
isomorphisms with the inverse of `capEDerivedOrdIso`. -/
theorem capEDerivedIsoOfData_hom_comparison (d : DG.DerivedCategory.{0} TAᵢᵐᵒᵖ) :
    (derivedComparison.{0, 0} TPpᵐᵒᵖ).map ((capEDerivedIsoOfData.{0, 0} D).hom.app d) =
      (derivedPlusEComparisonIso.{0, 0} k Q Λ Λc j hj ν₀ ν i).hom.app
          ((coevaluationFunctor.{0, 0} k Q Λ Λc j hj ((Singleton.singleton i : Multiset I) + ν)
            ν₀ L).obj d) ≫
        ((resFunctor.{0, 0} aT).mapDerivedCategory).map
          ((coevaluationComparisonOrdIso.{0, 0} k Q Λ Λc j hj ν₀ L _).hom.app d) ≫
        (capEDerivedOrdIso.{0} D).inv.app (derivedComparison.{0, 0} TAᵢᵐᵒᵖ |>.obj d) ≫
        ((OrdK).mapDerivedCategory).map
          ((derivedBlackEComparisonIso.{0, 0} Q Λ i ν).inv.app d) ≫
        (coevaluationComparisonOrdIso.{0, 0} k Q Λ Λc j hj ν₀ L ν).inv.app
          ((derivedBlackE.{0} Q Λ i ν).obj d) := by
  have key : ∀ {G₁ G₂ : DG.DerivedCategory.{0} TAᵢᵐᵒᵖ ⥤ DG.DerivedCategory.{0} TPpᵐᵒᵖ}
      (f : G₁ ⋙ derivedComparison.{0, 0} TPpᵐᵒᵖ ⟶ G₂ ⋙ derivedComparison.{0, 0} TPpᵐᵒᵖ),
      (derivedComparison.{0, 0} TPpᵐᵒᵖ).map ((((Functor.FullyFaithful.ofFullyFaithful
        (derivedComparison.{0, 0} TPpᵐᵒᵖ)).whiskeringRight
          (DG.DerivedCategory.{0} TAᵢᵐᵒᵖ)).preimage f).app d) = f.app d := fun f =>
    NatTrans.congr_app (((Functor.FullyFaithful.ofFullyFaithful
      (derivedComparison.{0, 0} TPpᵐᵒᵖ)).whiskeringRight
        (DG.DerivedCategory.{0} TAᵢᵐᵒᵖ)).map_preimage f) d
  simp only [capEDerivedIsoOfData, Functor.FullyFaithful.preimageIso_hom, key, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id]

/-- **The mate of `𝕂 ⋙ 𝔈⁺_i ≅ 𝔈_i ⋙ 𝕂` along `𝔈_i ⊣ 𝔉_i` is the inverse of
`𝕂 ⋙ 𝔉⁺_i ≅ 𝔉_i ⋙ 𝕂`** on derived categories of dg modules (Webster, arXiv:1309.3796v3, §7.3,
proof of Proposition 7.21, with Theorem 4.31), under the route hypothesis
`CupCap.CapEFMateCompatible`. -/
theorem capEDerivedIsoOfData_hom_mateEF (hEF : CapEFMateCompatible C hRq D D') :
    (mateEquiv (derivedBlackEFAdjunction ν i C hRq) (derivedPlusEFAdjunction ν i C hRq)
      (TwoSquare.mk _ _ _ _ (capEDerivedIsoOfData.{0, 0} D).hom)).natTrans =
      (capFDerivedIsoOfData.{0, 0} C hRq D').inv := by
  let := blackF_preservesFiniteLimits Q Λ i ν C hRq
  let := blackF_preservesFiniteColimits Q Λ i ν C hRq
  let := projective_plusCorner k Q Λ Λc j hj ν₀ ν i C hRq
  let := functor_preservesFiniteLimits aT
  let := functor_preservesFiniteColimits aT
  exact mateEquiv_eq_of_comparison
    (derivedBlackEComparisonIso.{0, 0} Q Λ i ν) (derivedBlackFComparisonIso.{0, 0} Q Λ i ν C hRq)
    (derivedPlusEComparisonIso.{0, 0} k Q Λ Λc j hj ν₀ ν i)
    (derivedPlusFComparisonIso.{0, 0} k Q Λ Λc j hj ν₀ ν i C hRq)
    (coevaluationComparisonOrdIso.{0, 0} k Q Λ Λc j hj ν₀ L _)
    (coevaluationComparisonOrdIso.{0, 0} k Q Λ Λc j hj ν₀ L ν)
    (adj' := derivedBlackResIndAdjunction.{0} Q Λ i ν C hRq (blackEFAdjunction Q Λ i ν C hRq))
    (adjP' := (plusEFAdjunction k Q Λ Λc j hj ν₀ ν i C hRq).mapDerivedCategory)
    (fun d => adjunctionOfComparison_counit_map (derivedComparisonEquivalence.{0, 0} TAᵢᵐᵒᵖ)
      (derivedComparisonEquivalence.{0, 0} TAᵐᵒᵖ)
      (derivedBlackResIndAdjunction.{0} Q Λ i ν C hRq (blackEFAdjunction Q Λ i ν C hRq))
      (derivedBlackEComparisonIso.{0, 0} Q Λ i ν)
      (derivedBlackFComparisonIso.{0, 0} Q Λ i ν C hRq) d)
    (fun d => adjunctionOfComparison_counit_map (derivedComparisonEquivalence.{0, 0} TPpᵢᵐᵒᵖ)
      (derivedComparisonEquivalence.{0, 0} TPpᵐᵒᵖ)
      (plusEFAdjunction k Q Λ Λc j hj ν₀ ν i C hRq).mapDerivedCategory
      (derivedPlusEComparisonIso.{0, 0} k Q Λ Λc j hj ν₀ ν i)
      (derivedPlusFComparisonIso.{0, 0} k Q Λ Λc j hj ν₀ ν i C hRq) d)
    _ _ (capEDerivedOrdIso_inv_mateEF C hRq D D' hEF) _ _
    (capEDerivedIsoOfData_hom_comparison D)
    (capFDerivedIsoOfData_inv_comparison C hRq D')

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
  (C : QuantumGroup.CartanDatum I) (hRq : IsRouquierQ C Q) (shift : ℤ)

variable (ν i)

/-- **The route hypothesis `CupCap.CapEFMateCompatible` for both positions of the cap**
(Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21, with Theorem 4.31): for `j < ℓ`
for the data `capAppendDataMid`, `capFDataMid`, and for `j = ℓ` for `capAppendDataTop`,
`capFDataTop`. Route hypothesis (tracked). -/
def CapEFMateCompatibleCases : Prop :=
  (∀ h : j < ℓ, CapEFMateCompatible (Λ := Λ) (hj := hj) C hRq
    (capAppendDataMid (hL := hL) ν i (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP hPL hκ hQ
      hfin h)
    (capFDataMid (hL := hL) (ν := ν) (i := i) (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP
      hPL hκ h)) ∧
  (∀ h : ¬ j < ℓ, CapEFMateCompatible (Λ := Λ) (hj := hj) C hRq
    (capAppendDataTop (hL := hL) ν i (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP hPL hκ hQ
      hfin h)
    (capFDataTop (hL := hL) (ν := ν) (i := i) (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP
      hPL hκ h))

variable {ν i hL hQ hκ hP hPL hfin C hRq} in
/-- **The mate of `𝕂 ⋙ 𝔈⁺_i ≅ 𝔈_i ⋙ 𝕂` along `𝔈_i ⊣ 𝔉_i` is the inverse of
`𝕂 ⋙ 𝔉⁺_i ≅ 𝔉_i ⋙ 𝕂`** (Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21, with
Theorem 4.31), for every `j ≤ ℓ`, on derived categories of dg modules.
Route hypotheses (tracked): `hEF`; `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`; `C`,
`hRq`. -/
theorem capEDerivedIso_hom_mateEF
    (hEF : CapEFMateCompatibleCases (Λ := Λ) (hj := hj) ν i hL hQ hκ hP hPL hfin C hRq) :
    (mateEquiv (derivedBlackEFAdjunction (Λ := Λ) ν i C hRq)
      (derivedPlusEFAdjunction (Λc := Λc) (hj := hj) (ν₀ := ν₀) ν i C hRq)
      (TwoSquare.mk _ _ _ _
        (capEDerivedIso ν i hL hQ hκ hP hPL hfin hproj).hom)).natTrans =
      (capFDerivedIso ν i hL hQ hκ hP hPL hfin hproj C hRq).inv := by
  have := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := ν) hL hQ hκ hP hPL hfin
    hproj
  have := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ)
    (ν := (Singleton.singleton i : Multiset I) + ν) hL hQ hκ hP hPL hfin hproj
  unfold capEDerivedIso capFDerivedIso
  split_ifs with h
  · exact capEDerivedIsoOfData_hom_mateEF C hRq _ _ (hEF.1 h)
  · exact capEDerivedIsoOfData_hom_mateEF C hRq _ _ (hEF.2 h)

variable {ν i hL hQ hκ hP hPL hfin C hRq} in
/-- **`𝔉⁺_i ⋙ RHom(K, -) ≅ RHom(K, -) ⋙ 𝔉_i` is the mate of `𝕂 ⋙ 𝔉⁺_i ≅ 𝔉_i ⋙ 𝕂`**
(Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21), for every `j ≤ ℓ`: the inverse
of `CupCap.capFRightAdjointIso`, defined by taking adjoints along `𝔈_i ⊣ 𝔉_i`, is the mate of
the inverse of `CupCap.capFDerivedIso` along the coevaluation adjunctions `𝕂 ⊣ RHom(K, -)`.
Route hypotheses (tracked): `hEF`; `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`; `C`,
`hRq`. -/
theorem capFRightAdjointIso_inv_eq_mate
    (hEF : CapEFMateCompatibleCases (Λ := Λ) (hj := hj) ν i hL hQ hκ hP hPL hfin C hRq) :
    (capFRightAdjointIso ν i hL hQ hκ hP hPL hfin hproj C hRq).inv =
      (mateEquiv (coevaluationAdjunction k Q Λ Λc j hj ν ν₀ L)
        (coevaluationAdjunction k Q Λ Λc j hj νᵢ ν₀ L)
        (TwoSquare.mk _ _ _ _
          (capFDerivedIso ν i hL hQ hκ hP hPL hfin hproj C hRq).inv)).natTrans := by
  have h := rightAdjointCommIso_inv_eq_mate (coevaluationAdjunction k Q Λ Λc j hj νᵢ ν₀ L)
    (coevaluationAdjunction k Q Λ Λc j hj ν ν₀ L) (derivedBlackEFAdjunction ν i C hRq)
    (derivedPlusEFAdjunction ν i C hRq) _ _ (capEDerivedIso_hom_mateEF hproj hEF)
  refine Eq.trans ?_ h
  unfold capFRightAdjointIso capEDerivedIso
  split_ifs <;> rfl

variable {ν i hL hQ hκ hP hPL hfin C hRq} in
/-- **`𝔉⁺_i ⋙ 𝕋 ≅ 𝕋 ⋙ 𝔉_i` through the mate of `𝕂 ⋙ 𝔉⁺_i ≅ 𝔉_i ⋙ 𝕂`** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.21 and Definition 7.18), for every `j ≤ ℓ` and
the quantum trace with homological shift `shift`, with the shift of `𝔉_i` induced by
`𝔈_i ⊣ 𝔉_i`: the inverse of `CupCap.capFQuantumTraceShiftIso` is the shift compatibility of
`𝔉_i` followed by the shift of the mate of the inverse of `CupCap.capFDerivedIso` along the
coevaluation adjunctions.
Route hypotheses (tracked): `hEF`; `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`; `C`,
`hRq`. -/
theorem capFQuantumTraceShiftIso_inv_eq_mate
    (hEF : CapEFMateCompatibleCases (Λ := Λ) (hj := hj) ν i hL hQ hκ hP hPL hfin C hRq) :
    letI := derivedBlackFAdjointCommShift (Λ := Λ) ν i C hRq
    (capFQuantumTraceShiftIso ν i C hRq hL hQ hκ hP hPL hfin hproj shift).inv =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (coevaluationRightAdjoint k Q Λ Λc j hj ν ν₀ L)
          ((derivedBlackF.{0} Q Λ i ν).commShiftIso shift).hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (mateEquiv (coevaluationAdjunction k Q Λ Λc j hj ν ν₀ L)
          (coevaluationAdjunction k Q Λ Λc j hj νᵢ ν₀ L)
          (TwoSquare.mk _ _ _ _
            (capFDerivedIso ν i hL hQ hκ hP hPL hfin hproj C hRq).inv)).natTrans
          (shiftFunctor _ shift) ≫ (Functor.associator _ _ _).hom := by
  let := derivedBlackFAdjointCommShift (Λ := Λ) ν i C hRq
  exact rightAdjointShiftCommIso_inv_eq_mate (coevaluationAdjunction k Q Λ Λc j hj νᵢ ν₀ L)
    (coevaluationAdjunction k Q Λ Λc j hj ν ν₀ L) (derivedBlackEFAdjunction ν i C hRq)
    (derivedPlusEFAdjunction ν i C hRq) _ _ (capEDerivedIso_hom_mateEF hproj hEF) shift

end Cases

end Categorification.Stendhal.CupCap
