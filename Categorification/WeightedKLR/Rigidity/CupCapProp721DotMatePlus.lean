/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721DotMateDirect

/-!
# The conjugate dot on `𝔈⁺_i` is the dot

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21 (the dots of the categorical action on derived categories, §4.6), on the `λ⁺`
side. On derived categories of dg modules over `T^{λ⁺}`, the dot on `𝔈⁺_i` was defined in two
ways: as the conjugate along the comparison isomorphism of the derived dot on restriction along
`appendBlackOpOfEq` (`CupCap.dgPlusDot`), and as the conjugate along `𝔉⁺_i ⊣ 𝔈⁺_i` of the dot on
`𝔉⁺_i` (`CupCap.dgPlusEDotMate`). The adjunction `𝔉⁺_i ⊣ 𝔈⁺_i` is the one along
`appendBlackTPAOp`, while the dots use `appendBlackOpOfEq`; the two ring maps agree pointwise
(`CupCap.appendBlackTPAOp_eq_ofEq`), and the identifications of induction and restriction along
them are conjugate (`CupCap.conjugateEquiv_indFunctorIsoOfEq_inv`).

## Main results

* `CupCap.conjugateEquiv_indFunctorIsoOfEq_inv`, `CupCap.conjugateEquiv_indFunctorIsoOfEq_hom`:
  for pointwise equal ring maps, the identification of inductions is conjugate to that of
  restrictions.
* `CupCap.dgPlusEDotMate_eq_dgPlusDot`.

Route hypotheses: none beyond `C`, `hRq : IsRouquierQ C Q` (Webster's setting for
Theorem 4.31) for the exactness of `𝔉⁺_i`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open CategoryTheory Limits KLR KLRAlgebra MulOpposite InductionAlong DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Module

variable {A B : Type} [Ring A] [Ring B] {φ φ' : A →ₙ+* B} (h : ∀ a, φ a = φ' a)

/-- **The identifications along pointwise equal maps are conjugate**: along induction ⊣
restriction for `φ` and `φ'`, the conjugate of the inverse of `indFunctorIsoOfEq` is
`resFunctorIsoOfEq`. -/
theorem conjugateEquiv_indFunctorIsoOfEq_inv :
    conjugateEquiv (InductionAlong.adjunction.{0, 0} φ) (InductionAlong.adjunction.{0, 0} φ')
      (indFunctorIsoOfEq h).inv = (resFunctorIsoOfEq.{0, 0} h).hom := by
  refine conjugateEquiv_eq_of_counit _ _ _ _ fun d => ModuleCat.hom_ext (Ind.ext fun z m => ?_)
  change z.1 • m.val = (z.1 * φ' 1) • m.val
  rw [z.2]

/-- The conjugate of `indFunctorIsoOfEq` along induction ⊣ restriction for `φ'` and `φ` is the
inverse of `resFunctorIsoOfEq`. -/
theorem conjugateEquiv_indFunctorIsoOfEq_hom :
    conjugateEquiv (InductionAlong.adjunction.{0, 0} φ') (InductionAlong.adjunction.{0, 0} φ)
      (indFunctorIsoOfEq h).hom = (resFunctorIsoOfEq.{0, 0} h).inv := by
  refine conjugateEquiv_eq_of_counit _ _ _ _ fun d => ModuleCat.hom_ext (Ind.ext fun z m => ?_)
  change z.1 • m.val = (z.1 * φ 1) • m.val
  rw [z.2]

end Module

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} {ν₀ : Multiset I}
  (ν : Multiset I) (i : I)

set_option hygiene false in
local notation "TPp" => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
set_option hygiene false in
local notation "TPpᵢ" =>
  TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (((Singleton.singleton i : Multiset I) + ν) + ν₀)
set_option hygiene false in
local notation "aT" => appendBlackTPAOp k Q Λ Λc j hj ν ν₀ i
set_option hygiene false in
local notation "Fᵖ" => blackFOfEq Q (plusLabels Λ Λc j hj) i (plusWeight_assoc ν ν₀ i)
set_option hygiene false in
local notation "Eᵖ" => blackEOfEq Q (plusLabels Λ Λc j hj) i (plusWeight_assoc ν ν₀ i)

private theorem blackFOfEq_additive_dotMatePlus : Fᵖ.Additive :=
  inferInstanceAs (InductionAlong.functor.{0, 0} _).Additive

private theorem blackEOfEq_additive_dotMatePlus : Eᵖ.Additive :=
  inferInstanceAs (resFunctor.{0, 0} _).Additive

private theorem blackEOfEq_limits_dotMatePlus : PreservesFiniteLimits Eᵖ :=
  inferInstanceAs (PreservesFiniteLimits (resFunctor.{0, 0} _))

private theorem blackEOfEq_colimits_dotMatePlus : PreservesFiniteColimits Eᵖ :=
  inferInstanceAs (PreservesFiniteColimits (resFunctor.{0, 0} _))

attribute [local instance] blackFOfEq_additive_dotMatePlus blackEOfEq_additive_dotMatePlus
  blackEOfEq_limits_dotMatePlus blackEOfEq_colimits_dotMatePlus

variable [DG.HasDerivedCategory.{0, 0} (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ]
  [DG.HasDerivedCategory.{0, 0} (TensorProductAlgebra k Q Λ ({i} + ν))ᵐᵒᵖ]
  [DG.HasDerivedCategory.{0, 0} TPpᵐᵒᵖ] [DG.HasDerivedCategory.{0, 0} TPpᵢᵐᵒᵖ]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TensorProductAlgebra k Q Λ ({i} + ν))ᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} TPpᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} TPpᵢᵐᵒᵖ)]

variable (C : QuantumGroup.CartanDatum I) (hRq : IsRouquierQ C Q)

set_option linter.unusedSectionVars false in
/-- **The conjugate dot on `𝔈⁺_i` is the dot** (Webster, arXiv:1309.3796v3, §4.6 and §7.3,
proof of Proposition 7.21): on derived categories of dg modules over `T^{λ⁺}`, the conjugate
along `𝔉⁺_i ⊣ 𝔈⁺_i` of the dot on `𝔉⁺_i` is the dot on `𝔈⁺_i`. -/
theorem dgPlusEDotMate_eq_dgPlusDot :
    dgPlusEDotMate k Q Λ Λc j hj ν₀ ν i C hRq =
      dgPlusDot.{0, 0} k Q Λ Λc j hj ν₀ ν i := by
  let := projective_plusCorner k Q Λ Λc j hj ν₀ ν i C hRq
  let := functor_preservesFiniteLimits aT
  let := functor_preservesFiniteColimits aT
  let := blackFOfEqPlus_preservesFiniteLimits k Q Λ Λc j hj ν₀ ν i
  let := blackFOfEqPlus_preservesFiniteColimits k Q Λ Λc j hj ν₀ ν i
  let : PreservesFiniteLimits (InductionAlong.functor.{0, 0}
      (appendBlackOpOfEq Q (plusLabels Λ Λc j hj) i (plusWeight_assoc ν ν₀ i))) :=
    blackFOfEqPlus_preservesFiniteLimits k Q Λ Λc j hj ν₀ ν i
  let : PreservesFiniteColimits (InductionAlong.functor.{0, 0}
      (appendBlackOpOfEq Q (plusLabels Λ Λc j hj) i (plusWeight_assoc ν ν₀ i))) :=
    blackFOfEqPlus_preservesFiniteColimits k Q Λ Λc j hj ν₀ ν i
  have he := appendBlackTPAOp_eq_ofEq k Q Λ Λc j hj ν₀ ν i
  have hmod : conjugateEquiv
      (blackAdjOfEq Q (plusLabels Λ Λc j hj) i (plusWeight_assoc ν ν₀ i))
      (blackAdjOfEq Q (plusLabels Λ Λc j hj) i (plusWeight_assoc ν ν₀ i))
      (indDotOfEq Q (plusLabels Λ Λc j hj) i (plusWeight_assoc ν ν₀ i)) =
      resDotOfEq Q (plusLabels Λ Λc j hj) i (plusWeight_assoc ν ν₀ i) :=
    (conjugateEquiv _ _).apply_symm_apply _
  have hder := conjugateEquiv_mapDerivedCategory
    (blackAdjOfEq Q (plusLabels Λ Λc j hj) i (plusWeight_assoc ν ν₀ i))
    (blackAdjOfEq Q (plusLabels Λ Λc j hj) i (plusWeight_assoc ν ν₀ i))
    (indDotOfEq Q (plusLabels Λ Λc j hj) i (plusWeight_assoc ν ν₀ i))
  rw [hmod] at hder
  -- the derived counits of the two adjunctions, through the identifications
  have hcon := conjugateEquiv_mapDerivedCategory (InductionAlong.adjunction.{0, 0} aT)
    (blackAdjOfEq Q (plusLabels Λ Λc j hj) i (plusWeight_assoc ν ν₀ i))
    (indFunctorIsoOfEq he).inv
  rw [show conjugateEquiv (InductionAlong.adjunction.{0, 0} aT)
      (blackAdjOfEq Q (plusLabels Λ Λc j hj) i (plusWeight_assoc ν ν₀ i))
      (indFunctorIsoOfEq he).inv = (resFunctorIsoOfEq.{0, 0} he).hom from
    conjugateEquiv_indFunctorIsoOfEq_inv he] at hcon
  have hcounit : ∀ y, ((mapDerivedCategoryIsoOfIso (indFunctorIsoOfEq he)).hom.app
        ((resFunctor.{0, 0} aT).mapDerivedCategory.obj y) ≫
      Fᵖ.mapDerivedCategory.map ((mapDerivedCategoryIsoOfIso
        (resFunctorIsoOfEq.{0, 0} he)).hom.app y) ≫
      (blackAdjOfEq Q (plusLabels Λ Λc j hj) i
        (plusWeight_assoc ν ν₀ i)).mapDerivedCategory.counit.app y) =
      (InductionAlong.adjunction.{0, 0} aT).mapDerivedCategory.counit.app y := fun y => by
    have c := conjugateEquiv_counit (InductionAlong.adjunction.{0, 0} aT).mapDerivedCategory
      (blackAdjOfEq Q (plusLabels Λ Λc j hj) i (plusWeight_assoc ν ν₀ i)).mapDerivedCategory
      (indFunctorIsoOfEq he).inv.mapDerivedCategory y
    rw [hcon] at c
    rw [mapDerivedCategoryIsoOfIso_hom_eq, mapDerivedCategoryIsoOfIso_hom_eq, c,
      ← NatTrans.comp_app_assoc, ← NatTrans.mapDerivedCategory_comp, Iso.hom_inv_id,
      NatTrans.mapDerivedCategory_id, NatTrans.id_app, Category.id_comp]
  refine conjugateEquiv_eq_of_comparison
    (derivedPlusFComparisonIsoOfEq.{0, 0} k Q Λ Λc j hj ν₀ ν i C hRq)
    (derivedPlusEComparisonIsoOfEq.{0, 0} k Q Λ Λc j hj ν₀ ν i)
    (adj' := (blackAdjOfEq Q (plusLabels Λ Λc j hj) i (plusWeight_assoc ν ν₀ i)).mapDerivedCategory)
    (fun d => ?_) _ _ hder _ _
    (isComparisonConj_comparisonConj _ _ _ _)
    (isComparisonConj_comparisonConj _ _ _ _)
  refine (adjunctionOfComparison_counit_map (derivedComparisonEquivalence.{0, 0} TPpᵐᵒᵖ)
    (derivedComparisonEquivalence.{0, 0} TPpᵢᵐᵒᵖ)
    (InductionAlong.adjunction.{0, 0} aT).mapDerivedCategory
    (derivedPlusFComparisonIso.{0, 0} k Q Λ Λc j hj ν₀ ν i C hRq)
    (derivedPlusEComparisonIso.{0, 0} k Q Λ Λc j hj ν₀ ν i) d).trans ?_
  rw [← hcounit]
  simp only [derivedPlusFComparisonIsoOfEq, derivedPlusEComparisonIsoOfEq, Iso.trans_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.map_comp,
    Category.assoc]
  congr 1
  rw [← NatTrans.naturality_assoc]
  rfl

end Categorification.Stendhal.CupCap
