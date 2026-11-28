/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721DotMatePlus

/-!
# The conjugate crossings on `𝔈_i²` and `𝔈⁺_i²` are the crossings

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21 (the crossings of the categorical action on derived categories, §4.6). On
derived categories of dg modules over `T^λ`, the crossing on `𝔈_i²` was defined in two ways:
directly, as the conjugate along the pasted comparison isomorphisms of the derived crossing on
restrictions (`CupCap.dgBlackCross`), and as the conjugate along the composite adjunction
`𝔉_i² ⊣ 𝔈_i²` of the crossing on `𝔉_i²` (`CupCap.dgBlackECrossMate`), which is the form used by
the quantum trace statements. They agree (`CupCap.dgBlackECrossMate_eq_dgBlackCross`): on
modules the crossing on inductions is by definition the conjugate of the crossing on
restrictions (`indCrossOfEq`), conjugates along composite adjunctions pass to derived categories
(`CupCap.conjugateEquiv_comp_mapDerivedCategory`, an iterated mate,
`iterated_mateEquiv_conjugateEquiv`, of `CupCap.mateEquiv_mapDerivedCategory`), and along
comparison functors (`CupCap.conjugateEquiv_eq_of_comparison`, with the counit of a composite
adjunction read off under the comparisons by `CupCap.comp_counit_map_of_comparison`). The same
holds on the `λ⁺` side (`CupCap.dgPlusECrossMate_eq_dgPlusCross`), where the comparisons are
taken along `plusWeight_assoc` (`CupCap.derivedPlusFEAdjunction_counit_comparisonOfEq`).

## Main results

* `CupCap.comp_counit_map_of_comparison`: the counit condition of
  `CupCap.conjugateEquiv_eq_of_comparison` for composite adjunctions and pasted comparisons.
* `CupCap.conjugateEquiv_comp_mapDerivedCategory`: conjugates along composite adjunctions pass
  to Mathlib's derived categories.
* `CupCap.derivedPlusFEAdjunction_counit_comparisonOfEq`: the counit of `𝔉⁺_i ⊣ 𝔈⁺_i` under
  the comparisons along `plusWeight_assoc`.
* `CupCap.dgBlackECrossMate_eq_dgBlackCross`, `CupCap.dgPlusECrossMate_eq_dgPlusCross`.

Route hypotheses: none beyond `C`, `hRq : IsRouquierQ C Q` (Webster's setting for
Theorem 4.31) for the adjunction, and `hQ : KLRSymm Q` for the crossing.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open CategoryTheory Limits KLR KLRAlgebra MulOpposite InductionAlong DG.DegreeZero

section CompCounit

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

variable {A : Type u₁} {A₂ : Type u₂} {A₃ : Type u₃} {A' : Type u₄} {A₂' : Type u₅}
  {A₃' : Type u₆} [Category.{v₁} A] [Category.{v₂} A₂] [Category.{v₃} A₃] [Category.{v₄} A']
  [Category.{v₅} A₂'] [Category.{v₆} A₃'] {c₁ : A ⥤ A'} {c₂ : A₂ ⥤ A₂'} {c₃ : A₃ ⥤ A₃'}
  {F₁ : A ⥤ A₂} {E₁ : A₂ ⥤ A} {F₂ : A₂ ⥤ A₃} {E₂ : A₃ ⥤ A₂}
  {F₁' : A' ⥤ A₂'} {E₁' : A₂' ⥤ A'} {F₂' : A₂' ⥤ A₃'} {E₂' : A₃' ⥤ A₂'}
  {adj₁ : F₁ ⊣ E₁} {adj₂ : F₂ ⊣ E₂} {adj₁' : F₁' ⊣ E₁'} {adj₂' : F₂' ⊣ E₂'}
  {iF₁ : F₁ ⋙ c₂ ≅ c₁ ⋙ F₁'} {iE₁ : E₁ ⋙ c₁ ≅ c₂ ⋙ E₁'}
  {iF₂ : F₂ ⋙ c₃ ≅ c₂ ⋙ F₂'} {iE₂ : E₂ ⋙ c₂ ≅ c₃ ⋙ E₂'}

/-- **The counit of a composite adjunction under comparisons**: if the comparisons carry the
counits of `F₁ ⊣ E₁` and `F₂ ⊣ E₂` to those of `F₁' ⊣ E₁'` and `F₂' ⊣ E₂'` through the
isomorphisms `iF`, `iE`, then they carry the counit of `F₁ F₂ ⊣ E₂ E₁` to that of
`F₁' F₂' ⊣ E₂' E₁'` through the pasted isomorphisms. -/
theorem comp_counit_map_of_comparison
    (hε₁ : ∀ d, c₂.map (adj₁.counit.app d) =
      iF₁.hom.app (E₁.obj d) ≫ F₁'.map (iE₁.hom.app d) ≫ adj₁'.counit.app (c₂.obj d))
    (hε₂ : ∀ d, c₃.map (adj₂.counit.app d) =
      iF₂.hom.app (E₂.obj d) ≫ F₂'.map (iE₂.hom.app d) ≫ adj₂'.counit.app (c₃.obj d))
    (d : A₃) :
    c₃.map ((adj₁.comp adj₂).counit.app d) =
      (squarePaste iF₂ iF₁).hom.app ((E₂ ⋙ E₁).obj d) ≫
        (F₁' ⋙ F₂').map ((squarePaste iE₁ iE₂).hom.app d) ≫
          (adj₁'.comp adj₂').counit.app (c₃.obj d) := by
  have nF := NatIso.naturality_2 iF₂ (adj₁.counit.app (E₂.obj d))
  simp only [Functor.comp_map] at nF
  have nε := adj₁'.counit.naturality (iE₂.hom.app d)
  simp only [Functor.comp_map, Functor.id_map] at nε
  rw [Adjunction.comp_counit_app, Functor.map_comp, ← nF, hε₁, hε₂, squarePaste_hom_app,
    squarePaste_hom_app, Adjunction.comp_counit_app]
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc]
  erw [Iso.inv_hom_id_app_assoc]
  erw [← F₂'.map_comp_assoc (F₁'.map (E₁'.map _)), nε, F₂'.map_comp_assoc]
  rfl

end CompCounit

section DerivedComp

variable {C₁ C₂ C₃ : Type*} [Category* C₁] [Abelian C₁] [HasDerivedCategory C₁]
  [Category* C₂] [Abelian C₂] [HasDerivedCategory C₂]
  [Category* C₃] [Abelian C₃] [HasDerivedCategory C₃]
  {L₁ : C₁ ⥤ C₂} [L₁.Additive] [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
  {R₁ : C₂ ⥤ C₁} [R₁.Additive] [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
  {L₂ : C₂ ⥤ C₃} [L₂.Additive] [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
  {R₂ : C₃ ⥤ C₂} [R₂.Additive] [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

/-- **Conjugates along composite adjunctions pass to derived categories**: for adjunctions
`L₁ ⊣ R₁`, `L₂ ⊣ R₂` of exact functors and `α : L₁ L₂ ⟶ L₁ L₂`, the conjugate along
`L₁^D L₂^D ⊣ R₂^D R₁^D` of the derived `α` (through `mapDerivedCategoryCompIso`) is the derived
conjugate of `α` along `L₁ L₂ ⊣ R₂ R₁`. Both conjugates are iterated mates
(`iterated_mateEquiv_conjugateEquiv`), and mates pass to derived categories
(`CupCap.mateEquiv_mapDerivedCategory`). -/
theorem conjugateEquiv_comp_mapDerivedCategory (α : L₁ ⋙ L₂ ⟶ L₁ ⋙ L₂) :
    conjugateEquiv (adj₁.mapDerivedCategory.comp adj₂.mapDerivedCategory)
        (adj₁.mapDerivedCategory.comp adj₂.mapDerivedCategory)
        ((Functor.mapDerivedCategoryCompIso L₁ L₂).hom ≫ α.mapDerivedCategory ≫
          (Functor.mapDerivedCategoryCompIso L₁ L₂).inv) =
      (Functor.mapDerivedCategoryCompIso R₂ R₁).hom ≫
        (conjugateEquiv (adj₁.comp adj₂) (adj₁.comp adj₂) α).mapDerivedCategory ≫
          (Functor.mapDerivedCategoryCompIso R₂ R₁).inv := by
  have h₁ := mateEquiv_mapDerivedCategory adj₁ adj₂ α
    (mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ α)).natTrans rfl
  have h₂ := mateEquiv_mapDerivedCategory adj₂ adj₁
    (mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ α)).natTrans
    (conjugateEquiv (adj₁.comp adj₂) (adj₁.comp adj₂) α)
    (iterated_mateEquiv_conjugateEquiv adj₁ adj₂ adj₁ adj₂ (TwoSquare.mk _ _ _ _ α))
  rw [← iterated_mateEquiv_conjugateEquiv]
  refine Eq.trans ?_ h₂
  congr 2

end DerivedComp

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Black

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}
  (ν : Multiset I) (i : I)

set_option hygiene false in
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
set_option hygiene false in
local notation "νᵢᵢ" =>
  ((Singleton.singleton i : Multiset I) + ((Singleton.singleton i : Multiset I) + ν))
set_option hygiene false in
local notation "TA" μ:max => TensorProductAlgebra k Q Λ μ

private theorem blackE_additive_crossMateDirect (μ : Multiset I) : (blackE Q Λ i μ).Additive :=
  inferInstanceAs (resFunctor.{0, 0} (appendBlackOp Q Λ i μ)).Additive

private theorem blackF_additive_crossMateDirect (μ : Multiset I) : (blackF Q Λ i μ).Additive :=
  inferInstanceAs (InductionAlong.functor.{0, 0} (appendBlackOp Q Λ i μ)).Additive

attribute [local instance] blackE_additive_crossMateDirect blackF_additive_crossMateDirect

variable [DG.HasDerivedCategory.{0, 0} (TA ν)ᵐᵒᵖ] [DG.HasDerivedCategory.{0, 0} (TA νᵢ)ᵐᵒᵖ]
  [DG.HasDerivedCategory.{0, 0} (TA νᵢᵢ)ᵐᵒᵖ]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TA ν)ᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TA νᵢ)ᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TA νᵢᵢ)ᵐᵒᵖ)]
  (C : QuantumGroup.CartanDatum I) (hRq : IsRouquierQ C Q)

/-- **The conjugate crossing on `𝔈_i²` is the crossing** (Webster, arXiv:1309.3796v3, §4.6 and
§7.3, proof of Proposition 7.21): on derived categories of dg modules over `T^λ`, the conjugate
along `𝔉_i² ⊣ 𝔈_i²` of the crossing on `𝔉_i²` is the crossing on `𝔈_i²`. -/
theorem dgBlackECrossMate_eq_dgBlackCross (hQ : KLRSymm Q) :
    dgBlackECrossMate (Λ := Λ) ν i C hRq hQ = dgBlackCross.{0, 0} (Q := Q) (Λ := Λ) ν i := by
  let := blackF_preservesFiniteLimits Q Λ i ν C hRq
  let := blackF_preservesFiniteColimits Q Λ i ν C hRq
  let := blackF_preservesFiniteLimits Q Λ i νᵢ C hRq
  let := blackF_preservesFiniteColimits Q Λ i νᵢ C hRq
  have hmod : conjugateEquiv ((blackAdjunction.{0} Q Λ i ν).comp (blackAdjunction.{0} Q Λ i νᵢ))
      ((blackAdjunction.{0} Q Λ i ν).comp (blackAdjunction.{0} Q Λ i νᵢ))
      (indCrossOfEq Λ hQ i i rfl rfl rfl rfl :
        blackF Q Λ i ν ⋙ blackF Q Λ i νᵢ ⟶ blackF Q Λ i ν ⋙ blackF Q Λ i νᵢ) =
      blackCross Q Λ i ν :=
    ((conjugateEquiv _ _).apply_symm_apply _).trans (resCrossOfEq_self Λ hQ i ν)
  have hder := conjugateEquiv_comp_mapDerivedCategory (blackAdjunction.{0} Q Λ i ν)
    (blackAdjunction.{0} Q Λ i νᵢ)
    (indCrossOfEq Λ hQ i i rfl rfl rfl rfl :
      blackF Q Λ i ν ⋙ blackF Q Λ i νᵢ ⟶ blackF Q Λ i ν ⋙ blackF Q Λ i νᵢ)
  rw [hmod] at hder
  exact conjugateEquiv_eq_of_comparison
    (squarePaste (derivedBlackFComparisonIso.{0, 0} Q Λ i νᵢ C hRq)
      (derivedBlackFComparisonIso.{0, 0} Q Λ i ν C hRq))
    (squarePaste (derivedBlackEComparisonIso.{0, 0} Q Λ i ν)
      (derivedBlackEComparisonIso.{0, 0} Q Λ i νᵢ))
    (adj' := (derivedBlackAdjunction.{0} Q Λ i ν C hRq).comp
      (derivedBlackAdjunction.{0} Q Λ i νᵢ C hRq))
    (comp_counit_map_of_comparison
      (fun d => adjunctionOfComparison_counit_map (derivedComparisonEquivalence.{0, 0} (TA ν)ᵐᵒᵖ)
        (derivedComparisonEquivalence.{0, 0} (TA νᵢ)ᵐᵒᵖ) (derivedBlackAdjunction.{0} Q Λ i ν C hRq)
        (derivedBlackFComparisonIso.{0, 0} Q Λ i ν C hRq)
        (derivedBlackEComparisonIso.{0, 0} Q Λ i ν) d)
      (fun d => adjunctionOfComparison_counit_map
        (derivedComparisonEquivalence.{0, 0} (TA νᵢ)ᵐᵒᵖ)
        (derivedComparisonEquivalence.{0, 0} (TA νᵢᵢ)ᵐᵒᵖ)
        (derivedBlackAdjunction.{0} Q Λ i νᵢ C hRq)
        (derivedBlackFComparisonIso.{0, 0} Q Λ i νᵢ C hRq)
        (derivedBlackEComparisonIso.{0, 0} Q Λ i νᵢ) d))
    _ _ hder _ _
    (isComparisonConj_comparisonConj _ _ _ _)
    (isComparisonConj_comparisonConj _ _ _ _)

end Black

section PlusStep

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

private theorem blackFOfEq_additive_crossMateDirect : Fᵖ.Additive :=
  inferInstanceAs (InductionAlong.functor.{0, 0} _).Additive

private theorem blackEOfEq_additive_crossMateDirect : Eᵖ.Additive :=
  inferInstanceAs (resFunctor.{0, 0} _).Additive

private theorem blackEOfEq_limits_crossMateDirect : PreservesFiniteLimits Eᵖ :=
  inferInstanceAs (PreservesFiniteLimits (resFunctor.{0, 0} _))

private theorem blackEOfEq_colimits_crossMateDirect : PreservesFiniteColimits Eᵖ :=
  inferInstanceAs (PreservesFiniteColimits (resFunctor.{0, 0} _))

attribute [local instance] blackFOfEq_additive_crossMateDirect
  blackEOfEq_additive_crossMateDirect blackEOfEq_limits_crossMateDirect
  blackEOfEq_colimits_crossMateDirect

variable [DG.HasDerivedCategory.{0, 0} (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ]
  [DG.HasDerivedCategory.{0, 0} (TensorProductAlgebra k Q Λ ({i} + ν))ᵐᵒᵖ]
  [DG.HasDerivedCategory.{0, 0} TPpᵐᵒᵖ] [DG.HasDerivedCategory.{0, 0} TPpᵢᵐᵒᵖ]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TensorProductAlgebra k Q Λ ({i} + ν))ᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} TPpᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} TPpᵢᵐᵒᵖ)]
  (C : QuantumGroup.CartanDatum I) (hRq : IsRouquierQ C Q)

set_option linter.unusedSectionVars false in
/-- **The counit of `𝔉⁺_i ⊣ 𝔈⁺_i` under the comparisons along `plusWeight_assoc`** (Webster,
arXiv:1309.3796v3, §4.6 and §7.3): the comparison carries the counit of
`CupCap.derivedPlusFEAdjunction` to the derived counit of `blackAdjOfEq` along
`plusWeight_assoc`, through `CupCap.derivedPlusFComparisonIsoOfEq` and
`CupCap.derivedPlusEComparisonIsoOfEq`. -/
theorem derivedPlusFEAdjunction_counit_comparisonOfEq
    (d : DG.DerivedCategory.{0, 0} TPpᵢᵐᵒᵖ) :
    letI := projective_plusCorner k Q Λ Λc j hj ν₀ ν i C hRq
    letI := functor_preservesFiniteLimits aT
    letI := functor_preservesFiniteColimits aT
    letI := blackF_preservesFiniteLimits Q Λ i ν C hRq
    letI := blackF_preservesFiniteColimits Q Λ i ν C hRq
    letI := blackFOfEqPlus_preservesFiniteLimits k Q Λ Λc j hj ν₀ ν i
    letI := blackFOfEqPlus_preservesFiniteColimits k Q Λ Λc j hj ν₀ ν i
    (derivedComparison.{0, 0} TPpᵢᵐᵒᵖ).map ((derivedPlusFEAdjunction ν i C hRq).counit.app d) =
      (derivedPlusFComparisonIsoOfEq.{0, 0} k Q Λ Λc j hj ν₀ ν i C hRq).hom.app
          ((derivedPlusE.{0} k Q Λ Λc j hj ν₀ ν i).obj d) ≫
        Fᵖ.mapDerivedCategory.map
          ((derivedPlusEComparisonIsoOfEq.{0, 0} k Q Λ Λc j hj ν₀ ν i).hom.app d) ≫
        (blackAdjOfEq Q (plusLabels Λ Λc j hj) i
          (plusWeight_assoc ν ν₀ i)).mapDerivedCategory.counit.app
            ((derivedComparison.{0, 0} TPpᵢᵐᵒᵖ).obj d) := by
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

end PlusStep

section Plus

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} {ν₀ : Multiset I}
  (ν : Multiset I) (i : I)

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
local notation "aT" μ:max => appendBlackTPAOp k Q Λ Λc j hj μ ν₀ i
set_option hygiene false in
local notation "pl" => plusLabels Λ Λc j hj

private theorem blackEOfEq_additive_crossMatePlus (μ β : Multiset I)
    (h : ({i} : Multiset I) + μ = β) : (blackEOfEq Q pl i h).Additive :=
  inferInstanceAs (resFunctor.{0, 0} _).Additive

private theorem blackFOfEq_additive_crossMatePlus (μ β : Multiset I)
    (h : ({i} : Multiset I) + μ = β) : (blackFOfEq Q pl i h).Additive :=
  inferInstanceAs (InductionAlong.functor.{0, 0} _).Additive

private theorem blackEOfEq_limits_crossMatePlus (μ β : Multiset I)
    (h : ({i} : Multiset I) + μ = β) : PreservesFiniteLimits (blackEOfEq Q pl i h) :=
  inferInstanceAs (PreservesFiniteLimits (resFunctor.{0, 0} _))

private theorem blackEOfEq_colimits_crossMatePlus (μ β : Multiset I)
    (h : ({i} : Multiset I) + μ = β) : PreservesFiniteColimits (blackEOfEq Q pl i h) :=
  inferInstanceAs (PreservesFiniteColimits (resFunctor.{0, 0} _))

attribute [local instance] blackEOfEq_additive_crossMatePlus blackFOfEq_additive_crossMatePlus
  blackEOfEq_limits_crossMatePlus blackEOfEq_colimits_crossMatePlus

variable [DG.HasDerivedCategory.{0, 0} (TA ν)ᵐᵒᵖ] [DG.HasDerivedCategory.{0, 0} (TA νᵢ)ᵐᵒᵖ]
  [DG.HasDerivedCategory.{0, 0} (TA νᵢᵢ)ᵐᵒᵖ]
  [DG.HasDerivedCategory.{0, 0} (TPp ν)ᵐᵒᵖ] [DG.HasDerivedCategory.{0, 0} (TPp νᵢ)ᵐᵒᵖ]
  [DG.HasDerivedCategory.{0, 0} (TPp νᵢᵢ)ᵐᵒᵖ]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TA ν)ᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TA νᵢ)ᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TA νᵢᵢ)ᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TPp ν)ᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TPp νᵢ)ᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TPp νᵢᵢ)ᵐᵒᵖ)]
  (C : QuantumGroup.CartanDatum I) (hRq : IsRouquierQ C Q)

set_option linter.unusedSectionVars false in
/-- **The conjugate crossing on `𝔈⁺_i²` is the crossing** (Webster, arXiv:1309.3796v3, §4.6 and
§7.3, proof of Proposition 7.21): on derived categories of dg modules over `T^{λ⁺}`, the
conjugate along `𝔉⁺_i² ⊣ 𝔈⁺_i²` of the crossing on `𝔉⁺_i²` is the crossing on `𝔈⁺_i²`. -/
theorem dgPlusECrossMate_eq_dgPlusCross (hQ : KLRSymm Q) :
    dgPlusECrossMate k Q Λ Λc j hj ν₀ ν i C hRq hQ =
      dgPlusCross.{0, 0} k Q Λ Λc j hj ν₀ ν i hQ := by
  let := blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q pl i (plusWeight_assoc ν ν₀ i) C hRq
  let := blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q pl i (plusWeight_assoc ν ν₀ i) C hRq
  let := blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q pl i (plusWeight_assoc νᵢ ν₀ i) C hRq
  let := blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q pl i (plusWeight_assoc νᵢ ν₀ i) C
    hRq
  have hmod : conjugateEquiv ((blackAdjOfEq Q pl i (plusWeight_assoc ν ν₀ i)).comp
        (blackAdjOfEq Q pl i (plusWeight_assoc νᵢ ν₀ i)))
      ((blackAdjOfEq Q pl i (plusWeight_assoc ν ν₀ i)).comp
        (blackAdjOfEq Q pl i (plusWeight_assoc νᵢ ν₀ i)))
      (indCrossOfEq pl hQ i i (plusWeight_assoc ν ν₀ i) (plusWeight_assoc νᵢ ν₀ i)
        (plusWeight_assoc ν ν₀ i) (plusWeight_assoc νᵢ ν₀ i)) =
      resCrossOfEq pl hQ i i (plusWeight_assoc ν ν₀ i) (plusWeight_assoc νᵢ ν₀ i)
        (plusWeight_assoc ν ν₀ i) (plusWeight_assoc νᵢ ν₀ i) :=
    (conjugateEquiv _ _).apply_symm_apply _
  have hder := conjugateEquiv_comp_mapDerivedCategory
    (blackAdjOfEq Q pl i (plusWeight_assoc ν ν₀ i))
    (blackAdjOfEq Q pl i (plusWeight_assoc νᵢ ν₀ i))
    (indCrossOfEq pl hQ i i (plusWeight_assoc ν ν₀ i) (plusWeight_assoc νᵢ ν₀ i)
      (plusWeight_assoc ν ν₀ i) (plusWeight_assoc νᵢ ν₀ i))
  rw [hmod] at hder
  exact conjugateEquiv_eq_of_comparison
    (squarePaste (derivedPlusFComparisonIsoOfEq.{0, 0} k Q Λ Λc j hj ν₀ νᵢ i C hRq)
      (derivedPlusFComparisonIsoOfEq.{0, 0} k Q Λ Λc j hj ν₀ ν i C hRq))
    (squarePaste (derivedPlusEComparisonIsoOfEq.{0, 0} k Q Λ Λc j hj ν₀ ν i)
      (derivedPlusEComparisonIsoOfEq.{0, 0} k Q Λ Λc j hj ν₀ νᵢ i))
    (adj' := (blackAdjOfEq Q pl i (plusWeight_assoc ν ν₀ i)).mapDerivedCategory.comp
      (blackAdjOfEq Q pl i (plusWeight_assoc νᵢ ν₀ i)).mapDerivedCategory)
    (comp_counit_map_of_comparison
      (derivedPlusFEAdjunction_counit_comparisonOfEq (Λ := Λ) ν i C hRq)
      (derivedPlusFEAdjunction_counit_comparisonOfEq (Λ := Λ) νᵢ i C hRq))
    _ _ hder _ _
    (isComparisonConj_comparisonConj _ _ _ _)
    (isComparisonConj_comparisonConj _ _ _ _)

end Plus

end Categorification.Stendhal.CupCap
