/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapFDerivedDG
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapFCross

/-!
# `𝕂 ∘ 𝔉_i² ≅ 𝔉_i² ∘ 𝕂` and the crossing, on derived categories of dg modules

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, the part for `𝔉_i`. The pasting of two copies of `CupCap.capFDerivedIsoOfData`
(`CupCap.capFDerivedIsoPaste`) is conjugate to the derived functor of `CupCap.capFCompIsoOfEq`
(`CupCap.capFDerivedIsoPaste_isComparisonSquare`). With the crossings on the dg derived functors
`derivedBlackF²` and `CupCap.derivedPlusF²` defined as conjugates of the derived crossings
`indCrossOfEq` (`CupCap.dgBlackFCross`, `CupCap.dgPlusFCross`), the module-level compatibility
(`CupCap.capFCompIsoOfEq_cross`) passes to the dg side (`CupCap.capFDerivedIsoPaste_cross`).

The exactness of `𝔉_i` and `𝔉⁺_i` (Theorem 4.31) enters as instance arguments.
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

private theorem blackF_additive_capFDGTwo (ν : Multiset I) : (blackF Q Λ' i ν).Additive :=
  inferInstanceAs (InductionAlong.functor.{0, 0} (appendBlackOp Q Λ' i ν)).Additive

private theorem blackFOfEq_additive_capFDGTwo : (blackFOfEq Q Λ' i h).Additive :=
  inferInstanceAs (InductionAlong.functor.{0, 0} (appendBlackOpOfEq Q Λ' i h)).Additive

end Additive

attribute [local instance] blackF_additive_capFDGTwo blackFOfEq_additive_capFDGTwo

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} {ν₀ : Multiset I}
  {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

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
set_option hygiene false in
local notation "aT" μ:max => appendBlackTPAOp k Q Λ Λc j hj μ ν₀ i
set_option hygiene false in
local notation "Fᵖ" μ:max => blackFOfEq Q (plusLabels Λ Λc j hj) i (plusWeight_assoc μ ν₀ i)

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
  [Limits.PreservesFiniteLimits (blackF Q Λ i ν)]
  [Limits.PreservesFiniteColimits (blackF Q Λ i ν)]
  [Limits.PreservesFiniteLimits (blackF Q Λ i νᵢ)]
  [Limits.PreservesFiniteColimits (blackF Q Λ i νᵢ)]
  [Limits.PreservesFiniteLimits (InductionAlong.functor.{0, 0} (aT ν))]
  [Limits.PreservesFiniteColimits (InductionAlong.functor.{0, 0} (aT ν))]
  [Limits.PreservesFiniteLimits (InductionAlong.functor.{0, 0} (aT νᵢ))]
  [Limits.PreservesFiniteColimits (InductionAlong.functor.{0, 0} (aT νᵢ))]
  [Limits.PreservesFiniteLimits (Fᵖ ν)] [Limits.PreservesFiniteColimits (Fᵖ ν)]
  [Limits.PreservesFiniteLimits (Fᵖ νᵢ)] [Limits.PreservesFiniteColimits (Fᵖ νᵢ)]
  (C : QuantumGroup.CartanDatum I) (hRq : IsRouquierQ C Q)

/-- **The crossing on the dg derived `𝔉_i²`** of right `T^λ`-modules: the conjugate of the
derived crossing `indCrossOfEq` (through `Functor.mapDerivedCategoryCompIso`) along the pasted
comparison isomorphisms. -/
def dgBlackFCross (hQ : KLRSymm Q) :
    derivedBlackF.{w} Q Λ i ν ⋙ derivedBlackF.{w} Q Λ i νᵢ ⟶
      derivedBlackF.{w} Q Λ i ν ⋙ derivedBlackF.{w} Q Λ i νᵢ :=
  comparisonConj (Functor.FullyFaithful.ofFullyFaithful (derivedComparison.{w, w'} (TA νᵢᵢ)ᵐᵒᵖ))
    (squarePaste (derivedBlackFComparisonIso.{w, w'} Q Λ i νᵢ C hRq)
      (derivedBlackFComparisonIso.{w, w'} Q Λ i ν C hRq))
    (squarePaste (derivedBlackFComparisonIso.{w, w'} Q Λ i νᵢ C hRq)
      (derivedBlackFComparisonIso.{w, w'} Q Λ i ν C hRq))
    ((Functor.mapDerivedCategoryCompIso _ _).hom ≫
      NatTrans.mapDerivedCategory (F := blackF Q Λ i ν ⋙ blackF Q Λ i νᵢ)
        (G := blackF Q Λ i ν ⋙ blackF Q Λ i νᵢ) (indCrossOfEq Λ hQ i i rfl rfl rfl rfl) ≫
      (Functor.mapDerivedCategoryCompIso _ _).inv)

variable (k Q Λ Λc j hj ν₀) in
/-- **The crossing on the dg derived `𝔉⁺_i²`** of right `T^{λ⁺}`-modules: the conjugate of the
derived crossing `indCrossOfEq` along the pasted comparison isomorphisms
`CupCap.derivedPlusFComparisonIsoOfEq`. -/
def dgPlusFCross (hQ : KLRSymm Q) :
    derivedPlusF.{w} k Q Λ Λc j hj ν₀ ν i ⋙ derivedPlusF.{w} k Q Λ Λc j hj ν₀ νᵢ i ⟶
      derivedPlusF.{w} k Q Λ Λc j hj ν₀ ν i ⋙ derivedPlusF.{w} k Q Λ Λc j hj ν₀ νᵢ i :=
  comparisonConj
    (Functor.FullyFaithful.ofFullyFaithful (derivedComparison.{w, w'} (TPp νᵢᵢ)ᵐᵒᵖ))
    (squarePaste (derivedPlusFComparisonIsoOfEq.{w, w'} k Q Λ Λc j hj ν₀ νᵢ i C hRq)
      (derivedPlusFComparisonIsoOfEq.{w, w'} k Q Λ Λc j hj ν₀ ν i C hRq))
    (squarePaste (derivedPlusFComparisonIsoOfEq.{w, w'} k Q Λ Λc j hj ν₀ νᵢ i C hRq)
      (derivedPlusFComparisonIsoOfEq.{w, w'} k Q Λ Λc j hj ν₀ ν i C hRq))
    ((Functor.mapDerivedCategoryCompIso _ _).hom ≫
      (indCrossOfEq (plusLabels Λ Λc j hj) hQ i i (plusWeight_assoc ν ν₀ i)
        (plusWeight_assoc νᵢ ν₀ i) (plusWeight_assoc ν ν₀ i)
        (plusWeight_assoc νᵢ ν₀ i)).mapDerivedCategory ≫
      (Functor.mapDerivedCategoryCompIso _ _).inv)

variable {ν i}

/-- **`𝕂 ⋙ 𝔉_i² ≅ 𝔉_i² ⋙ 𝕂` on derived categories of dg modules**, the pasting of two copies
of `CupCap.capFDerivedIsoOfData` (Webster, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21). -/
def capFDerivedIsoPaste (D₁ : CapFData k Q Λ Λc j hj ν₀ L ν i)
    (D₂ : CapFData k Q Λ Λc j hj ν₀ L νᵢ i) [Module.Projective (TA ν) (CB ν)]
    [Module.Projective (TA νᵢ) (CB νᵢ)] [Module.Projective (TA νᵢᵢ) (CB νᵢᵢ)] :
    coevaluationFunctor.{0, w} k Q Λ Λc j hj ν ν₀ L ⋙
        (derivedPlusF.{w} k Q Λ Λc j hj ν₀ ν i ⋙ derivedPlusF.{w} k Q Λ Λc j hj ν₀ νᵢ i) ≅
      (derivedBlackF.{w} Q Λ i ν ⋙ derivedBlackF.{w} Q Λ i νᵢ) ⋙
        coevaluationFunctor.{0, w} k Q Λ Λc j hj νᵢᵢ ν₀ L :=
  (squarePaste (capFDerivedIsoOfData.{w, w'} C hRq D₂).symm
    (capFDerivedIsoOfData.{w, w'} C hRq D₁).symm).symm

/-- **`CupCap.capFDerivedIsoPaste` is conjugate to the derived `CupCap.capFCompIsoOfEq`.** -/
theorem capFDerivedIsoPaste_isComparisonSquare (D₁ : CapFData k Q Λ Λc j hj ν₀ L ν i)
    (D₂ : CapFData k Q Λ Λc j hj ν₀ L νᵢ i) [Module.Projective (TA ν) (CB ν)]
    [Module.Projective (TA νᵢ) (CB νᵢ)] [Module.Projective (TA νᵢᵢ) (CB νᵢᵢ)] :
    IsComparisonSquare
      (squarePaste (derivedBlackFComparisonIso.{w, w'} Q Λ i νᵢ C hRq)
        (derivedBlackFComparisonIso.{w, w'} Q Λ i ν C hRq) ≪≫
        Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso _ _))
      (coevaluationComparisonOrdIso.{w, w'} k Q Λ Λc j hj ν₀ L νᵢᵢ)
      (coevaluationComparisonOrdIso.{w, w'} k Q Λ Λc j hj ν₀ L ν)
      (squarePaste (derivedPlusFComparisonIsoOfEq.{w, w'} k Q Λ Λc j hj ν₀ νᵢ i C hRq)
        (derivedPlusFComparisonIsoOfEq.{w, w'} k Q Λ Λc j hj ν₀ ν i C hRq) ≪≫
        Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso _ _))
      (derivedSquareIso (capFCompIsoOfEq D₁ D₂)) (capFDerivedIsoPaste.{w, w'} C hRq D₁ D₂) :=
  (((capFDerivedIsoOfData_isComparisonSquareOfEq C hRq D₂).paste
      (capFDerivedIsoOfData_isComparisonSquareOfEq C hRq D₁)).changeX
      (Functor.mapDerivedCategoryCompIso _ _) (eh' := Functor.isoWhiskerRight
        (Functor.mapDerivedCategoryCompIso _ _).symm _ ≪≫ squarePaste _ _) rfl).changeY
    (Functor.mapDerivedCategoryCompIso _ _) (by
      rw [Iso.trans_hom, Category.assoc, ← derivedSquareIso_squarePaste, ← Category.assoc,
        Functor.isoWhiskerRight_hom, ← Functor.whiskerRight_comp, Iso.symm_hom, Iso.inv_hom_id,
        Functor.whiskerRight_id', Category.id_comp]
      rfl)

/-- **`𝕂 ⋙ 𝔉_i² ≅ 𝔉_i² ⋙ 𝕂` carries the crossing to the crossing on derived categories of dg
modules** (Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21), from the
module-level compatibility for `CupCap.capFCompIsoOfEq D₁ D₂`. -/
theorem capFDerivedIsoPaste_cross (hQ : KLRSymm Q) (D₁ : CapFData k Q Λ Λc j hj ν₀ L ν i)
    (D₂ : CapFData k Q Λ Λc j hj ν₀ L νᵢ i) [Module.Projective (TA ν) (CB ν)]
    [Module.Projective (TA νᵢ) (CB νᵢ)] [Module.Projective (TA νᵢᵢ) (CB νᵢᵢ)]
    (hcross : (Functor.whiskerRight (indCrossOfEq Λ hQ i i rfl rfl rfl rfl) (OrdK νᵢᵢ) :
        (blackF Q Λ i ν ⋙ blackF Q Λ i νᵢ) ⋙ OrdK νᵢᵢ ⟶
          (blackF Q Λ i ν ⋙ blackF Q Λ i νᵢ) ⋙ OrdK νᵢᵢ) ≫ (capFCompIsoOfEq D₁ D₂).hom =
      (capFCompIsoOfEq D₁ D₂).hom ≫ Functor.whiskerLeft (OrdK ν)
        (indCrossOfEq (plusLabels Λ Λc j hj) hQ i i (plusWeight_assoc ν ν₀ i)
          (plusWeight_assoc νᵢ ν₀ i) (plusWeight_assoc ν ν₀ i) (plusWeight_assoc νᵢ ν₀ i))) :
    Functor.whiskerLeft (coevaluationFunctor.{0, w} k Q Λ Λc j hj ν ν₀ L)
        (dgPlusFCross.{w, w'} k Q Λ Λc j hj ν₀ ν i C hRq hQ) ≫
        (capFDerivedIsoPaste.{w, w'} C hRq D₁ D₂).hom =
      (capFDerivedIsoPaste.{w, w'} C hRq D₁ D₂).hom ≫
        Functor.whiskerRight (dgBlackFCross.{w, w'} ν i C hRq hQ)
          (coevaluationFunctor.{0, w} k Q Λ Λc j hj νᵢᵢ ν₀ L) :=
  (capFDerivedIsoPaste_isComparisonSquare C hRq D₁ D₂).whisker
    (capFDerivedIsoPaste_isComparisonSquare C hRq D₁ D₂)
    ((isComparisonConj_comparisonConj _ _ _ _).trans_whiskerLeft _ _ (by
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]))
    ((isComparisonConj_comparisonConj _ _ _ _).trans_whiskerLeft _ _ (by
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]))
    (derivedSquareIso_whisker _ _ hcross)

end Categorification.Stendhal.CupCap
