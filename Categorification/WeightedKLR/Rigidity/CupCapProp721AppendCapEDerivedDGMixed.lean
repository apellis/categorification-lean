/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapEDerivedDG
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendMixedCap
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendMixedTopCap

/-!
# `𝕂 ∘ 𝔈_a 𝔈_b ≅ 𝔈_a 𝔈_b ∘ 𝕂` and the mixed crossing, on derived categories of dg modules

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, the part for `𝔈_i`. The crossing of two strands of different colours `a ≠ b`
relates `𝔈_a 𝔈_b` and `𝔈_b 𝔈_a`, whose contents `{b} + ({a} + ν)` and `{a} + ({b} + ν)` agree
only up to the equality `mixedSwap`. On the dg side, `𝔈_i` along a content equality
`h : {i} + ν = β` is `derivedBlackE` transported along `h` (`CupCap.derivedBlackEOfEq`), and
likewise on the `λ⁺` side (`CupCap.derivedPlusEOfEq`); the isomorphism
`CupCap.capEDerivedIsoOfData'` is `CupCap.capEDerivedIsoOfData` transported along `h`, conjugate
to the derived `CupCap.capEOrdIsoOfEq'`. The mixed crossings on the dg side are the conjugates
of the derived crossings `resCrossOfEq` (`CupCap.dgMixedCross`, `CupCap.dgPlusMixedCross`), and
the module-level compatibility passes to the dg side
(`CupCap.capEDerivedIsoPaste'_mixedCross`, with the cases
`CupCap.capEDerivedIsoPaste'Mid_mixedCross`, `CupCap.capEDerivedIsoPaste'Top_mixedCross`).

Route hypotheses (tracked): as for `CupCap.capEDerivedIsoMid`: `hL`, `hQ`, `hκ`, `hP`, `hPL`,
`hfin`, `hproj`.
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

private theorem blackE_additive_capEMix (ν : Multiset I) : (blackE Q Λ' i ν).Additive :=
  inferInstanceAs (resFunctor.{0, 0} (appendBlackOp Q Λ' i ν)).Additive

private theorem blackEOfEq_additive_capEMix : (blackEOfEq Q Λ' i h).Additive :=
  inferInstanceAs (resFunctor.{0, 0} (appendBlackOpOfEq Q Λ' i h)).Additive

private theorem blackEOfEq_limits_capEMix :
    Limits.PreservesFiniteLimits (blackEOfEq Q Λ' i h) :=
  inferInstanceAs (Limits.PreservesFiniteLimits (resFunctor.{0, 0} (appendBlackOpOfEq Q Λ' i h)))

private theorem blackEOfEq_colimits_capEMix :
    Limits.PreservesFiniteColimits (blackEOfEq Q Λ' i h) :=
  inferInstanceAs
    (Limits.PreservesFiniteColimits (resFunctor.{0, 0} (appendBlackOpOfEq Q Λ' i h)))

end Exact

attribute [local instance] blackE_additive_capEMix blackEOfEq_additive_capEMix
  blackEOfEq_limits_capEMix blackEOfEq_colimits_capEMix

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} {ν₀ : Multiset I}
  {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

set_option hygiene false in
local notation "TA" μ:max => TensorProductAlgebra k Q Λ μ
set_option hygiene false in
local notation "TPp" μ:max => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (μ + ν₀)
set_option hygiene false in
local notation "CB" μ:max => CapBimodule k Q Λ Λc j hj μ ν₀ L
set_option hygiene false in
local notation "OrdK" μ:max => ordTensor (TPp μ)ᵐᵒᵖ (TA μ)ᵐᵒᵖ (OpBimodule (TA μ) (CB μ))

/-! ### `𝔈_i` along a content equality -/

section OfEq

variable {ν : Multiset I} {i : I} {β : Multiset I} (h : ({i} : Multiset I) + ν = β)
  [DG.HasDerivedCategory.{w, 0} (TA ν)ᵐᵒᵖ] [DG.HasDerivedCategory.{w, 0} (TA β)ᵐᵒᵖ]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TA ν)ᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TA β)ᵐᵒᵖ)]

variable (Q Λ) in
/-- **`𝔈_i` on derived categories of dg modules along a content equality** `{i} + ν = β`:
`derivedBlackE` transported along the equality. -/
def derivedBlackEOfEq :
    DG.DerivedCategory.{w} (TA β)ᵐᵒᵖ ⥤ DG.DerivedCategory.{w} (TA ν)ᵐᵒᵖ := by
  subst h
  exact derivedBlackE.{w} Q Λ i ν

variable (Q Λ) in
/-- The comparison isomorphism of `CupCap.derivedBlackEOfEq` with the derived `blackEOfEq`. -/
def derivedBlackEOfEqComparisonIso :
    derivedBlackEOfEq.{w} Q Λ h ⋙ derivedComparison.{w, w'} (TA ν)ᵐᵒᵖ ≅
      derivedComparison.{w, w'} (TA β)ᵐᵒᵖ ⋙ (blackEOfEq Q Λ i h).mapDerivedCategory := by
  subst h
  exact derivedBlackEComparisonIso.{w, w'} Q Λ i ν

variable
  [DG.HasDerivedCategory.{w, 0} (TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀))ᵐᵒᵖ]
  [DG.HasDerivedCategory.{w, 0} (TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (β + ν₀))ᵐᵒᵖ]
  [HasDerivedCategory.{w'}
    (ModuleCat.{0} (TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀))ᵐᵒᵖ)]
  [HasDerivedCategory.{w'}
    (ModuleCat.{0} (TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (β + ν₀))ᵐᵒᵖ)]

variable (k Q Λ Λc j hj ν₀) in
/-- **`𝔈⁺_i` on derived categories of dg modules along a content equality** `{i} + ν = β`:
`CupCap.derivedPlusE` transported along the equality. -/
def derivedPlusEOfEq :
    DG.DerivedCategory.{w} (TPp β)ᵐᵒᵖ ⥤ DG.DerivedCategory.{w} (TPp ν)ᵐᵒᵖ := by
  subst h
  exact derivedPlusE.{w} k Q Λ Λc j hj ν₀ ν i

variable (k Q Λ Λc j hj ν₀) in
/-- The comparison isomorphism of `CupCap.derivedPlusEOfEq` with the derived `blackEOfEq` for
any `hp : {i} + (ν + ν₀) = β + ν₀`. -/
def derivedPlusEOfEqComparisonIso (hp : ({i} : Multiset I) + (ν + ν₀) = β + ν₀) :
    derivedPlusEOfEq.{w} k Q Λ Λc j hj ν₀ h ⋙ derivedComparison.{w, w'} (TPp ν)ᵐᵒᵖ ≅
      derivedComparison.{w, w'} (TPp β)ᵐᵒᵖ ⋙
        (blackEOfEq Q (plusLabels Λ Λc j hj) i hp).mapDerivedCategory := by
  subst h
  exact derivedPlusEComparisonIsoOfEq.{w, w'} k Q Λ Λc j hj ν₀ ν i

/-- **`𝕂 ⋙ 𝔈_i ≅ 𝔈_i ⋙ 𝕂` along a content equality** (Webster, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.21): `CupCap.capEDerivedIsoOfData` transported along `h`. -/
def capEDerivedIsoOfData' (D : CapAppendData k Q Λ Λc j hj ν₀ L ν i)
    [Module.Projective (TA ν) (CB ν)] [Module.Projective (TA β) (CB β)] :
    coevaluationFunctor.{0, w} k Q Λ Λc j hj β ν₀ L ⋙
        derivedPlusEOfEq.{w} k Q Λ Λc j hj ν₀ h ≅
      derivedBlackEOfEq.{w} Q Λ h ⋙ coevaluationFunctor.{0, w} k Q Λ Λc j hj ν ν₀ L := by
  subst h
  exact capEDerivedIsoOfData.{w, w'} D

/-- `CupCap.capEDerivedIsoOfData'` is conjugate to the derived `CupCap.capEOrdIsoOfEq'`. -/
theorem capEDerivedIsoOfData'_isComparisonSquare (D : CapAppendData k Q Λ Λc j hj ν₀ L ν i)
    (hp : ({i} : Multiset I) + (ν + ν₀) = β + ν₀)
    [Module.Projective (TA ν) (CB ν)] [Module.Projective (TA β) (CB β)] :
    IsComparisonSquare (derivedBlackEOfEqComparisonIso.{w, w'} Q Λ h)
      (coevaluationComparisonOrdIso.{w, w'} k Q Λ Λc j hj ν₀ L ν)
      (coevaluationComparisonOrdIso.{w, w'} k Q Λ Λc j hj ν₀ L β)
      (derivedPlusEOfEqComparisonIso.{w, w'} k Q Λ Λc j hj ν₀ h hp)
      (derivedSquareIso (capEOrdIsoOfEq' D h hp)) (capEDerivedIsoOfData'.{w, w'} h D) := by
  subst h
  exact capEDerivedIsoOfData_isComparisonSquareOfEq D

end OfEq

/-! ### Pasting along a content equality -/

section Paste

variable {ν : Multiset I} {a b : I} {δ : Multiset I}
  (h : ({b} : Multiset I) + (({a} : Multiset I) + ν) = δ)
  [DG.HasDerivedCategory.{w, 0} (TA ν)ᵐᵒᵖ]
  [DG.HasDerivedCategory.{w, 0} (TA (({a} : Multiset I) + ν))ᵐᵒᵖ]
  [DG.HasDerivedCategory.{w, 0} (TA δ)ᵐᵒᵖ]
  [DG.HasDerivedCategory.{w, 0} (TPp ν)ᵐᵒᵖ]
  [DG.HasDerivedCategory.{w, 0} (TPp (({a} : Multiset I) + ν))ᵐᵒᵖ]
  [DG.HasDerivedCategory.{w, 0} (TPp δ)ᵐᵒᵖ]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TA ν)ᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TA (({a} : Multiset I) + ν))ᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TA δ)ᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TPp ν)ᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TPp (({a} : Multiset I) + ν))ᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TPp δ)ᵐᵒᵖ)]

/-- **`𝕂 ⋙ 𝔈_b 𝔈_a ≅ 𝔈_b 𝔈_a ⋙ 𝕂` on derived categories of dg modules** along a content
equality `{b} + ({a} + ν) = δ` (Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21):
the pasting of `CupCap.capEDerivedIsoOfData` and `CupCap.capEDerivedIsoOfData'`. -/
def capEDerivedIsoPaste' (D₁ : CapAppendData k Q Λ Λc j hj ν₀ L ν a)
    (D₂ : CapAppendData k Q Λ Λc j hj ν₀ L (({a} : Multiset I) + ν) b)
    [Module.Projective (TA ν) (CB ν)]
    [Module.Projective (TA (({a} : Multiset I) + ν)) (CB (({a} : Multiset I) + ν))]
    [Module.Projective (TA δ) (CB δ)] :
    coevaluationFunctor.{0, w} k Q Λ Λc j hj δ ν₀ L ⋙
        (derivedPlusEOfEq.{w} k Q Λ Λc j hj ν₀ h ⋙ derivedPlusE.{w} k Q Λ Λc j hj ν₀ ν a) ≅
      (derivedBlackEOfEq.{w} Q Λ h ⋙ derivedBlackE.{w} Q Λ a ν) ⋙
        coevaluationFunctor.{0, w} k Q Λ Λc j hj ν ν₀ L :=
  (squarePaste (capEDerivedIsoOfData.{w, w'} D₁).symm
    (capEDerivedIsoOfData'.{w, w'} h D₂).symm).symm

/-- **`CupCap.capEDerivedIsoPaste'` is conjugate to the derived `CupCap.capECompIsoOfEq'`**, with
the composites of the derived functors identified with the derived functors of the composites
by `Functor.mapDerivedCategoryCompIso`. -/
theorem capEDerivedIsoPaste'_isComparisonSquare (D₁ : CapAppendData k Q Λ Λc j hj ν₀ L ν a)
    (D₂ : CapAppendData k Q Λ Λc j hj ν₀ L (({a} : Multiset I) + ν) b)
    (hp : ({b} : Multiset I) + ((({a} : Multiset I) + ν) + ν₀) = δ + ν₀)
    [Module.Projective (TA ν) (CB ν)]
    [Module.Projective (TA (({a} : Multiset I) + ν)) (CB (({a} : Multiset I) + ν))]
    [Module.Projective (TA δ) (CB δ)] :
    IsComparisonSquare
      (squarePaste (derivedBlackEComparisonIso.{w, w'} Q Λ a ν)
        (derivedBlackEOfEqComparisonIso.{w, w'} Q Λ h) ≪≫
        Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso _ _))
      (coevaluationComparisonOrdIso.{w, w'} k Q Λ Λc j hj ν₀ L ν)
      (coevaluationComparisonOrdIso.{w, w'} k Q Λ Λc j hj ν₀ L δ)
      (squarePaste (derivedPlusEComparisonIsoOfEq.{w, w'} k Q Λ Λc j hj ν₀ ν a)
        (derivedPlusEOfEqComparisonIso.{w, w'} k Q Λ Λc j hj ν₀ h hp) ≪≫
        Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso _ _))
      (derivedSquareIso (capECompIsoOfEq' D₁ D₂ h hp)) (capEDerivedIsoPaste'.{w, w'} h D₁ D₂) :=
  (((capEDerivedIsoOfData_isComparisonSquareOfEq D₁).paste
      (capEDerivedIsoOfData'_isComparisonSquare h D₂ hp)).changeX
      (Functor.mapDerivedCategoryCompIso _ _) (eh' := Functor.isoWhiskerRight
        (Functor.mapDerivedCategoryCompIso _ _).symm _ ≪≫ squarePaste _ _) rfl).changeY
    (Functor.mapDerivedCategoryCompIso _ _) (by
      rw [Iso.trans_hom, Category.assoc, ← derivedSquareIso_squarePaste, ← Category.assoc,
        Functor.isoWhiskerRight_hom, ← Functor.whiskerRight_comp, Iso.symm_hom, Iso.inv_hom_id,
        Functor.whiskerRight_id', Category.id_comp]
      rfl)

end Paste

/-! ### The mixed crossing -/

section MixedCross

variable (ν : Multiset I) (a b : I)

set_option hygiene false in
local notation "νa" => ((Singleton.singleton a : Multiset I) + ν)
set_option hygiene false in
local notation "νb" => ((Singleton.singleton b : Multiset I) + ν)
set_option hygiene false in
local notation "νab" =>
  ((Singleton.singleton a : Multiset I) + ((Singleton.singleton b : Multiset I) + ν))

variable [DG.HasDerivedCategory.{w, 0} (TA ν)ᵐᵒᵖ] [DG.HasDerivedCategory.{w, 0} (TA νa)ᵐᵒᵖ]
  [DG.HasDerivedCategory.{w, 0} (TA νb)ᵐᵒᵖ] [DG.HasDerivedCategory.{w, 0} (TA νab)ᵐᵒᵖ]
  [DG.HasDerivedCategory.{w, 0} (TPp ν)ᵐᵒᵖ] [DG.HasDerivedCategory.{w, 0} (TPp νa)ᵐᵒᵖ]
  [DG.HasDerivedCategory.{w, 0} (TPp νb)ᵐᵒᵖ] [DG.HasDerivedCategory.{w, 0} (TPp νab)ᵐᵒᵖ]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TA ν)ᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TA νa)ᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TA νb)ᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TA νab)ᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TPp ν)ᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TPp νa)ᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TPp νb)ᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TPp νab)ᵐᵒᵖ)]

/-- **The crossing of different colours on the dg derived `𝔈_a 𝔈_b`** of right
`T^λ`-modules: the conjugate of the derived crossing `resCrossOfEq` (through
`Functor.mapDerivedCategoryCompIso`) along the pasted comparison isomorphisms. -/
def dgMixedCross (hQ : KLRSymm Q) :
    derivedBlackEOfEq.{w} Q Λ (mixedSwap ν a b) ⋙ derivedBlackE.{w} Q Λ a ν ⟶
      derivedBlackEOfEq.{w} Q Λ (rfl : ({a} : Multiset I) + νb = νab) ⋙
        derivedBlackE.{w} Q Λ b ν :=
  comparisonConj (Functor.FullyFaithful.ofFullyFaithful (derivedComparison.{w, w'} (TA ν)ᵐᵒᵖ))
    (squarePaste (derivedBlackEComparisonIso.{w, w'} Q Λ a ν)
      (derivedBlackEOfEqComparisonIso.{w, w'} Q Λ (mixedSwap ν a b)))
    (squarePaste (derivedBlackEComparisonIso.{w, w'} Q Λ b ν)
      (derivedBlackEOfEqComparisonIso.{w, w'} Q Λ (rfl : ({a} : Multiset I) + νb = νab)))
    ((Functor.mapDerivedCategoryCompIso _ _).hom ≫
      (resCrossOfEq Λ hQ a b rfl rfl rfl (mixedSwap ν a b)).mapDerivedCategory ≫
      (Functor.mapDerivedCategoryCompIso
        (blackEOfEq Q Λ a (rfl : ({a} : Multiset I) + νb = νab)) (blackE Q Λ b ν)).inv)

variable (k Q Λ Λc j hj ν₀) in
/-- **The crossing of different colours on the dg derived `𝔈⁺_a 𝔈⁺_b`** of right
`T^{λ⁺}`-modules: the conjugate of the derived crossing `resCrossOfEq` of `T^{λ⁺}` along the
pasted comparison isomorphisms. -/
def dgPlusMixedCross (hQ : KLRSymm Q) :
    derivedPlusEOfEq.{w} k Q Λ Λc j hj ν₀ (mixedSwap ν a b) ⋙
        derivedPlusE.{w} k Q Λ Λc j hj ν₀ ν a ⟶
      derivedPlusEOfEq.{w} k Q Λ Λc j hj ν₀ (rfl : ({a} : Multiset I) + νb = νab) ⋙
        derivedPlusE.{w} k Q Λ Λc j hj ν₀ ν b :=
  comparisonConj (Functor.FullyFaithful.ofFullyFaithful (derivedComparison.{w, w'} (TPp ν)ᵐᵒᵖ))
    (squarePaste (derivedPlusEComparisonIsoOfEq.{w, w'} k Q Λ Λc j hj ν₀ ν a)
      (derivedPlusEOfEqComparisonIso.{w, w'} k Q Λ Λc j hj ν₀ (mixedSwap ν a b)
        (plusWeight_assoc_mixed_swap ν a b)))
    (squarePaste (derivedPlusEComparisonIsoOfEq.{w, w'} k Q Λ Λc j hj ν₀ ν b)
      (derivedPlusEOfEqComparisonIso.{w, w'} k Q Λ Λc j hj ν₀
        (rfl : ({a} : Multiset I) + νb = νab) (plusWeight_assoc νb ν₀ a)))
    ((Functor.mapDerivedCategoryCompIso _ _).hom ≫
      (resCrossOfEq (plusLabels Λ Λc j hj) hQ a b (plusWeight_assoc ν ν₀ b)
        (plusWeight_assoc νb ν₀ a) (plusWeight_assoc ν ν₀ a)
        (plusWeight_assoc_mixed_swap ν a b)).mapDerivedCategory ≫
      (Functor.mapDerivedCategoryCompIso _ _).inv)

variable {ν a b}

/-- **`𝕂 ⋙ 𝔈_a 𝔈_b ≅ 𝔈_a 𝔈_b ⋙ 𝕂` carries the crossing of different colours to the crossing on
derived categories of dg modules** (Webster, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21), from the module-level compatibility `hmix` for `CupCap.capECompIsoOfEq'`. -/
theorem capEDerivedIsoPaste'_mixedCross (hQ : KLRSymm Q)
    (Dₐ : CapAppendData k Q Λ Λc j hj ν₀ L ν a) (Dₐ_b : CapAppendData k Q Λ Λc j hj ν₀ L νa b)
    (D_b : CapAppendData k Q Λ Λc j hj ν₀ L ν b) (D_bₐ : CapAppendData k Q Λ Λc j hj ν₀ L νb a)
    [Module.Projective (TA ν) (CB ν)] [Module.Projective (TA νa) (CB νa)]
    [Module.Projective (TA νb) (CB νb)] [Module.Projective (TA νab) (CB νab)]
    (hmix : Functor.whiskerRight (resCrossOfEq Λ hQ a b rfl rfl rfl (mixedSwap ν a b))
          (OrdK ν) ≫ (capECompIsoOfEq' D_b D_bₐ rfl (plusWeight_assoc νb ν₀ a)).hom =
        (capECompIsoOfEq' Dₐ Dₐ_b (mixedSwap ν a b) (plusWeight_assoc_mixed_swap ν a b)).hom ≫
          Functor.whiskerLeft (OrdK νab)
            (resCrossOfEq (plusLabels Λ Λc j hj) hQ a b (plusWeight_assoc ν ν₀ b)
              (plusWeight_assoc νb ν₀ a) (plusWeight_assoc ν ν₀ a)
              (plusWeight_assoc_mixed_swap ν a b))) :
    Functor.whiskerLeft (coevaluationFunctor.{0, w} k Q Λ Λc j hj νab ν₀ L)
        (dgPlusMixedCross.{w, w'} k Q Λ Λc j hj ν₀ ν a b hQ) ≫
        (capEDerivedIsoPaste'.{w, w'} (rfl : ({a} : Multiset I) + νb = νab) D_b D_bₐ).hom =
      (capEDerivedIsoPaste'.{w, w'} (mixedSwap ν a b) Dₐ Dₐ_b).hom ≫
        Functor.whiskerRight (dgMixedCross.{w, w'} ν a b hQ)
          (coevaluationFunctor.{0, w} k Q Λ Λc j hj ν ν₀ L) :=
  (capEDerivedIsoPaste'_isComparisonSquare (mixedSwap ν a b) Dₐ Dₐ_b
      (plusWeight_assoc_mixed_swap ν a b)).whisker
    (capEDerivedIsoPaste'_isComparisonSquare rfl D_b D_bₐ (plusWeight_assoc νb ν₀ a))
    ((isComparisonConj_comparisonConj _ _ _ _).trans_whiskerLeft _ _ (by
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]))
    ((isComparisonConj_comparisonConj _ _ _ _).trans_whiskerLeft _ _ (by
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]))
    (derivedSquareIso_whisker _ _ hmix)

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

variable (ν a b)

/-- **`𝕂 ⋙ 𝔈_a 𝔈_b ≅ 𝔈_a 𝔈_b ⋙ 𝕂` carries the crossing of different colours to the crossing on
derived categories of dg modules, for `j < ℓ`** (Webster, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21), for the pastings of the isomorphisms of `CupCap.capAppendDataMid` for the two
orders of appending. Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`,
`hproj`. -/
theorem capEDerivedIsoPaste'Mid_mixedCross (h : j < ℓ) (hab : a ≠ b) :
    letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := ν) hL hQ hκ hP hPL
      hfin hproj
    letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := νa) hL hQ hκ hP hPL
      hfin hproj
    letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := νb) hL hQ hκ hP hPL
      hfin hproj
    letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := νab) hL hQ hκ hP hPL
      hfin hproj
    Functor.whiskerLeft (coevaluationFunctor.{0, w} k Q Λ Λc j hj νab ν₀ L)
        (dgPlusMixedCross.{w, w'} k Q Λ Λc j hj ν₀ ν a b hQ) ≫
        (capEDerivedIsoPaste'.{w, w'} (rfl : ({a} : Multiset I) + νb = νab)
          (capAppendDataMid (hL := hL) ν b (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP hPL
            hκ hQ hfin h)
          (capAppendDataMid (hL := hL) νb a (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP hPL
            hκ hQ hfin h)).hom =
      (capEDerivedIsoPaste'.{w, w'} (mixedSwap ν a b)
          (capAppendDataMid (hL := hL) ν a (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP hPL
            hκ hQ hfin h)
          (capAppendDataMid (hL := hL) νa b (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP hPL
            hκ hQ hfin h)).hom ≫
        Functor.whiskerRight (dgMixedCross.{w, w'} ν a b hQ)
          (coevaluationFunctor.{0, w} k Q Λ Λc j hj ν ν₀ L) :=
  have := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := ν) hL hQ hκ hP hPL
    hfin hproj
  have := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := νa) hL hQ hκ hP hPL
    hfin hproj
  have := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := νb) hL hQ hκ hP hPL
    hfin hproj
  have := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := νab) hL hQ hκ hP hPL
    hfin hproj
  capEDerivedIsoPaste'_mixedCross hQ _ _ _ _
    (capECompIsoOfEq'Mid_mixedCross ν a b (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL)
      (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP hPL hκ hQ hfin h hab)

/-- **`𝕂 ⋙ 𝔈_a 𝔈_b ≅ 𝔈_a 𝔈_b ⋙ 𝕂` carries the crossing of different colours to the crossing on
derived categories of dg modules, for `j = ℓ`** (Webster, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21), for the pastings of the isomorphisms of `CupCap.capAppendDataTop` for the two
orders of appending. Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`,
`hproj`. -/
theorem capEDerivedIsoPaste'Top_mixedCross (h : ¬ j < ℓ) (hab : a ≠ b) :
    letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := ν) hL hQ hκ hP hPL
      hfin hproj
    letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := νa) hL hQ hκ hP hPL
      hfin hproj
    letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := νb) hL hQ hκ hP hPL
      hfin hproj
    letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := νab) hL hQ hκ hP hPL
      hfin hproj
    Functor.whiskerLeft (coevaluationFunctor.{0, w} k Q Λ Λc j hj νab ν₀ L)
        (dgPlusMixedCross.{w, w'} k Q Λ Λc j hj ν₀ ν a b hQ) ≫
        (capEDerivedIsoPaste'.{w, w'} (rfl : ({a} : Multiset I) + νb = νab)
          (capAppendDataTop (hL := hL) ν b (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP hPL
            hκ hQ hfin h)
          (capAppendDataTop (hL := hL) νb a (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP hPL
            hκ hQ hfin h)).hom =
      (capEDerivedIsoPaste'.{w, w'} (mixedSwap ν a b)
          (capAppendDataTop (hL := hL) ν a (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP hPL
            hκ hQ hfin h)
          (capAppendDataTop (hL := hL) νa b (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP hPL
            hκ hQ hfin h)).hom ≫
        Functor.whiskerRight (dgMixedCross.{w, w'} ν a b hQ)
          (coevaluationFunctor.{0, w} k Q Λ Λc j hj ν ν₀ L) :=
  have := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := ν) hL hQ hκ hP hPL
    hfin hproj
  have := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := νa) hL hQ hκ hP hPL
    hfin hproj
  have := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := νb) hL hQ hκ hP hPL
    hfin hproj
  have := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := νab) hL hQ hκ hP hPL
    hfin hproj
  capEDerivedIsoPaste'_mixedCross hQ _ _ _ _
    (capECompIsoOfEq'Top_mixedCross ν a b (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL)
      (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP hPL hκ hQ hfin h hab)

end Cases

end MixedCross

end Categorification.Stendhal.CupCap
