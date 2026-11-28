/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721CrossMateDirect
import Categorification.WeightedKLR.Rigidity.CupCapProp721TraceShiftEMixed

/-!
# The conjugate crossings of different colours on `𝔈_a 𝔈_b` are the crossings

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21 (the crossings of the categorical action on derived categories, §4.6). On
derived categories of dg modules over `T^λ`, the crossing of different colours `a`, `b` on
`𝔈_a 𝔈_b` was defined in two ways: directly, as the conjugate along the pasted comparison
isomorphisms of the derived crossing `resCrossOfEq` (`CupCap.dgMixedCross`), and as the
conjugate along the composite adjunctions `𝔉_a 𝔉_b ⊣ 𝔈_b 𝔈_a`, `𝔉_b 𝔉_a ⊣ 𝔈_a 𝔈_b` of the
crossing on `𝔉` (`CupCap.dgBlackEMixedCrossMate`), the form used by the quantum trace
statements. They agree (`CupCap.dgBlackEMixedCrossMate_eq_dgMixedCross`), and likewise on the
`λ⁺` side (`CupCap.dgPlusEMixedCrossMate_eq_dgPlusMixedCross`). This is the analogue for two
different adjunctions of `CupCap.dgBlackECrossMate_eq_dgBlackCross`: on modules `indCrossOfEq`
is by definition the conjugate of `resCrossOfEq`; conjugates between two composite adjunctions
pass to derived categories (`CupCap.conjugateEquiv_comp_mapDerivedCategory_between`, an
iterated mate of `CupCap.mateEquiv_mapDerivedCategory`), and along comparison functors
(`CupCap.conjugateEquiv_eq_of_comparison_between`). The quantum trace statements for the
crossing of different colours on `𝔈` then hold for the directly defined crossings
(`CupCap.capEQuantumTraceShiftIsoMid_dgMixedCross`,
`CupCap.capEQuantumTraceShiftIsoTop_dgMixedCross`).

## Main results

* `CupCap.conjugateEquiv_eq_of_comparison_between`.
* `CupCap.conjugateEquiv_comp_mapDerivedCategory_between`.
* `CupCap.derivedBlackFEAdjunctionOfEq_counit_comparison`,
  `CupCap.derivedPlusFEAdjunctionOfEq_counit_comparison`.
* `CupCap.dgBlackEMixedCrossMate_eq_dgMixedCross`,
  `CupCap.dgPlusEMixedCrossMate_eq_dgPlusMixedCross`.
* `CupCap.capEQuantumTraceShiftIsoMid_dgMixedCross`,
  `CupCap.capEQuantumTraceShiftIsoTop_dgMixedCross`.

Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj` for the quantum trace
statements, as for `CupCap.capFDerivedIso`; `C`, `hRq : IsRouquierQ C Q` is Webster's setting
for Theorem 4.31, and `hQ : KLRSymm Q` is needed for the crossing.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open CategoryTheory Limits KLR KLRAlgebra MulOpposite InductionAlong DG.DegreeZero

section TransportBetween

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {A : Type u₁} {Aᵢ : Type u₂} {A' : Type u₃} {Aᵢ' : Type u₄}
  [Category.{v₁} A] [Category.{v₂} Aᵢ] [Category.{v₃} A'] [Category.{v₄} Aᵢ']
  {cA : A ⥤ A'} {cAᵢ : Aᵢ ⥤ Aᵢ'} {F₁ F₂ : A ⥤ Aᵢ} {E₁ E₂ : Aᵢ ⥤ A}
  {F₁' F₂' : A' ⥤ Aᵢ'} {E₁' E₂' : Aᵢ' ⥤ A'}
  {adj₁ : F₁ ⊣ E₁} {adj₂ : F₂ ⊣ E₂} {adj₁' : F₁' ⊣ E₁'} {adj₂' : F₂' ⊣ E₂'}
  (iF₁ : F₁ ⋙ cAᵢ ≅ cA ⋙ F₁') (iE₁ : E₁ ⋙ cA ≅ cAᵢ ⋙ E₁')
  (iF₂ : F₂ ⋙ cAᵢ ≅ cA ⋙ F₂') (iE₂ : E₂ ⋙ cA ≅ cAᵢ ⋙ E₂')

/-- **Conjugates between two adjunctions transport along comparison functors**: if the
comparisons intertwine `F₁ ⊣ E₁` with `F₁' ⊣ E₁'` and `F₂ ⊣ E₂` with `F₂' ⊣ E₂'` on the counits,
the comparison of `Aᵢ` is faithful, and `α`, `β` correspond under the comparisons to `α'`, `β'`
with `β'` the conjugate of `α'`, then `β` is the conjugate of `α`. -/
theorem conjugateEquiv_eq_of_comparison_between [cAᵢ.Faithful]
    (hε₁ : ∀ d, cAᵢ.map (adj₁.counit.app d) =
      iF₁.hom.app (E₁.obj d) ≫ F₁'.map (iE₁.hom.app d) ≫ adj₁'.counit.app (cAᵢ.obj d))
    (hε₂ : ∀ d, cAᵢ.map (adj₂.counit.app d) =
      iF₂.hom.app (E₂.obj d) ≫ F₂'.map (iE₂.hom.app d) ≫ adj₂'.counit.app (cAᵢ.obj d))
    (α' : F₂' ⟶ F₁') (β' : E₁' ⟶ E₂') (hmate : conjugateEquiv adj₁' adj₂' α' = β')
    (α : F₂ ⟶ F₁) (β : E₁ ⟶ E₂)
    (hα : ∀ a, cAᵢ.map (α.app a) = iF₂.hom.app a ≫ α'.app (cA.obj a) ≫ iF₁.inv.app a)
    (hβ : ∀ d, cA.map (β.app d) = iE₁.hom.app d ≫ β'.app (cAᵢ.obj d) ≫ iE₂.inv.app d) :
    conjugateEquiv adj₁ adj₂ α = β := by
  have hmod : ∀ x, F₂'.map (β'.app x) ≫ adj₂'.counit.app x =
      α'.app (E₁'.obj x) ≫ adj₁'.counit.app x := fun x => by
    rw [← hmate]
    exact conjugateEquiv_counit adj₁' adj₂' α' x
  refine conjugateEquiv_eq_of_counit adj₁ adj₂ α β fun d => cAᵢ.map_injective ?_
  have nF := NatIso.naturality_2 iF₂ (β.app d)
  simp only [Functor.comp_map] at nF
  simp only [Functor.map_comp, hε₁, hε₂, hα]
  rw [← nF, hβ]
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← F₂'.map_comp_assoc (iE₂.inv.app d), Iso.inv_hom_id_app, F₂'.map_id, Category.id_comp,
    hmod]
  have nα := α'.naturality (iE₁.hom.app d)
  rw [reassoc_of% nα]

end TransportBetween

section DerivedCompBetween

variable {C₁ C₂ C₂' C₃ : Type*} [Category* C₁] [Abelian C₁] [HasDerivedCategory C₁]
  [Category* C₂] [Abelian C₂] [HasDerivedCategory C₂]
  [Category* C₂'] [Abelian C₂'] [HasDerivedCategory C₂']
  [Category* C₃] [Abelian C₃] [HasDerivedCategory C₃]
  {L₁ : C₁ ⥤ C₂} [L₁.Additive] [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
  {R₁ : C₂ ⥤ C₁} [R₁.Additive] [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
  {F₂ : C₂ ⥤ C₃} [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  {U₂ : C₃ ⥤ C₂} [U₂.Additive] [PreservesFiniteLimits U₂] [PreservesFiniteColimits U₂]
  {F₁ : C₁ ⥤ C₂'} [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  {U₁ : C₂' ⥤ C₁} [U₁.Additive] [PreservesFiniteLimits U₁] [PreservesFiniteColimits U₁]
  {L₂ : C₂' ⥤ C₃} [L₂.Additive] [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
  {R₂ : C₃ ⥤ C₂'} [R₂.Additive] [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
  (adj₁ : L₁ ⊣ R₁) (adj₄ : F₂ ⊣ U₂) (adj₃ : F₁ ⊣ U₁) (adj₂ : L₂ ⊣ R₂)

/-- **Conjugates between two composite adjunctions pass to derived categories**: for
adjunctions `L₁ ⊣ R₁`, `F₂ ⊣ U₂`, `F₁ ⊣ U₁`, `L₂ ⊣ R₂` of exact functors and
`α : F₁ L₂ ⟶ L₁ F₂`, the conjugate along `L₁^D F₂^D ⊣ U₂^D R₁^D` and `F₁^D L₂^D ⊣ R₂^D U₁^D` of
the derived `α` (through `mapDerivedCategoryCompIso`) is the derived conjugate of `α`. Both are
iterated mates (`iterated_mateEquiv_conjugateEquiv`), and mates pass to derived categories
(`CupCap.mateEquiv_mapDerivedCategory`). -/
theorem conjugateEquiv_comp_mapDerivedCategory_between (α : F₁ ⋙ L₂ ⟶ L₁ ⋙ F₂) :
    conjugateEquiv (adj₁.mapDerivedCategory.comp adj₄.mapDerivedCategory)
        (adj₃.mapDerivedCategory.comp adj₂.mapDerivedCategory)
        ((Functor.mapDerivedCategoryCompIso F₁ L₂).hom ≫ α.mapDerivedCategory ≫
          (Functor.mapDerivedCategoryCompIso L₁ F₂).inv) =
      (Functor.mapDerivedCategoryCompIso U₂ R₁).hom ≫
        (conjugateEquiv (adj₁.comp adj₄) (adj₃.comp adj₂) α).mapDerivedCategory ≫
          (Functor.mapDerivedCategoryCompIso R₂ U₁).inv := by
  have h₁ := mateEquiv_mapDerivedCategory adj₁ adj₂ α
    (mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ α)).natTrans rfl
  have h₂ := mateEquiv_mapDerivedCategory adj₄ adj₃
    (mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ α)).natTrans
    (conjugateEquiv (adj₁.comp adj₄) (adj₃.comp adj₂) α)
    (iterated_mateEquiv_conjugateEquiv adj₁ adj₂ adj₃ adj₄ (TwoSquare.mk _ _ _ _ α))
  rw [← iterated_mateEquiv_conjugateEquiv]
  refine Eq.trans ?_ h₂
  congr 2

end DerivedCompBetween

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} {ν₀ : Multiset I}

set_option hygiene false in
local notation "TA" μ:max => TensorProductAlgebra k Q Λ μ
set_option hygiene false in
local notation "TPp" μ:max => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (μ + ν₀)
set_option hygiene false in
local notation "pl" => plusLabels Λ Λc j hj
set_option hygiene false in
local notation "aT" μ:max i':max => appendBlackTPAOp k Q Λ Λc j hj μ ν₀ i'

section Exact

variable {n : ℕ} (Λ' : Fin n → I →₀ ℕ) (i : I) {μ β : Multiset I}
  (h : ({i} : Multiset I) + μ = β)

private theorem blackE_additive_mixedMateDirect (ν : Multiset I) : (blackE Q Λ' i ν).Additive :=
  inferInstanceAs (resFunctor.{0, 0} (appendBlackOp Q Λ' i ν)).Additive

private theorem blackF_additive_mixedMateDirect (ν : Multiset I) : (blackF Q Λ' i ν).Additive :=
  inferInstanceAs (InductionAlong.functor.{0, 0} (appendBlackOp Q Λ' i ν)).Additive

private theorem blackEOfEq_limits_mixedMateDirect : PreservesFiniteLimits (blackEOfEq Q Λ' i h) :=
  inferInstanceAs (PreservesFiniteLimits (resFunctor.{0, 0} (appendBlackOpOfEq Q Λ' i h)))

private theorem blackEOfEq_colimits_mixedMateDirect :
    PreservesFiniteColimits (blackEOfEq Q Λ' i h) :=
  inferInstanceAs (PreservesFiniteColimits (resFunctor.{0, 0} (appendBlackOpOfEq Q Λ' i h)))

end Exact

attribute [local instance] blackE_additive_mixedMateDirect blackF_additive_mixedMateDirect
  blackEOfEq_limits_mixedMateDirect blackEOfEq_colimits_mixedMateDirect

/-! ### The counits of `𝔉_i ⊣ 𝔈_i` along a content equality under the comparisons -/

section OfEqCounit

variable {ν : Multiset I} {i : I} {β : Multiset I} (h : ({i} : Multiset I) + ν = β)
  (C : QuantumGroup.CartanDatum I) (hRq : IsRouquierQ C Q)

section Black

variable [DG.HasDerivedCategory.{0, 0} (TA ν)ᵐᵒᵖ] [DG.HasDerivedCategory.{0, 0} (TA β)ᵐᵒᵖ]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TA ν)ᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TA β)ᵐᵒᵖ)]

/-- **The counit of `𝔉_i ⊣ 𝔈_i` along a content equality under the comparisons** (Webster,
arXiv:1309.3796v3, Theorem 4.31): the comparison carries the counit of
`CupCap.derivedBlackFEAdjunctionOfEq` to the derived counit of `blackAdjOfEq`, through
`CupCap.derivedBlackFOfEqComparisonIso` and `CupCap.derivedBlackEOfEqComparisonIso`. -/
theorem derivedBlackFEAdjunctionOfEq_counit_comparison (d : DG.DerivedCategory.{0, 0} (TA β)ᵐᵒᵖ) :
    letI := blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q Λ i h C hRq
    letI := blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q Λ i h C hRq
    (derivedComparison.{0, 0} (TA β)ᵐᵒᵖ).map
        ((derivedBlackFEAdjunctionOfEq (Λ := Λ) h C hRq).counit.app d) =
      (derivedBlackFOfEqComparisonIso.{0, 0} Q Λ h C hRq).hom.app
          ((derivedBlackEOfEq.{0} Q Λ h).obj d) ≫
        (blackFOfEq Q Λ i h).mapDerivedCategory.map
          ((derivedBlackEOfEqComparisonIso.{0, 0} Q Λ h).hom.app d) ≫
        (blackAdjOfEq Q Λ i h).mapDerivedCategory.counit.app
          ((derivedComparison.{0, 0} (TA β)ᵐᵒᵖ).obj d) := by
  subst h
  let := blackF_preservesFiniteLimits Q Λ i ν C hRq
  let := blackF_preservesFiniteColimits Q Λ i ν C hRq
  exact adjunctionOfComparison_counit_map (derivedComparisonEquivalence.{0, 0} (TA ν)ᵐᵒᵖ)
    (derivedComparisonEquivalence.{0, 0} (TA ((Singleton.singleton i : Multiset I) + ν))ᵐᵒᵖ)
    (derivedBlackAdjunction.{0} Q Λ i ν C hRq) (derivedBlackFComparisonIso.{0, 0} Q Λ i ν C hRq)
    (derivedBlackEComparisonIso.{0, 0} Q Λ i ν) d

end Black

section Plus

variable [DG.HasDerivedCategory.{0, 0} (TA ν)ᵐᵒᵖ] [DG.HasDerivedCategory.{0, 0} (TA β)ᵐᵒᵖ]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TA ν)ᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TA β)ᵐᵒᵖ)]
  [DG.HasDerivedCategory.{0, 0} (TPp ν)ᵐᵒᵖ] [DG.HasDerivedCategory.{0, 0} (TPp β)ᵐᵒᵖ]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TPp ν)ᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TPp β)ᵐᵒᵖ)]

set_option linter.unusedSectionVars false in
/-- **The counit of `𝔉⁺_i ⊣ 𝔈⁺_i` along a content equality under the comparisons** (Webster,
arXiv:1309.3796v3, Theorem 4.31 on the `λ⁺` side): for any `hp : {i} + (ν + ν₀) = β + ν₀`, the
comparison carries the counit of `CupCap.derivedPlusFEAdjunctionOfEq` to the derived counit of
`blackAdjOfEq` along `hp`, through `CupCap.derivedPlusFOfEqComparisonIso` and
`CupCap.derivedPlusEOfEqComparisonIso`. -/
theorem derivedPlusFEAdjunctionOfEq_counit_comparison
    (hp : ({i} : Multiset I) + (ν + ν₀) = β + ν₀) (d : DG.DerivedCategory.{0, 0} (TPp β)ᵐᵒᵖ) :
    letI := blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q pl i hp C hRq
    letI := blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q pl i hp C hRq
    (derivedComparison.{0, 0} (TPp β)ᵐᵒᵖ).map
        ((derivedPlusFEAdjunctionOfEq k Q Λ Λc j hj ν₀ h C hRq).counit.app d) =
      (derivedPlusFOfEqComparisonIso.{0, 0} k Q Λ Λc j hj ν₀ h C hRq hp).hom.app
          ((derivedPlusEOfEq.{0} k Q Λ Λc j hj ν₀ h).obj d) ≫
        (blackFOfEq Q pl i hp).mapDerivedCategory.map
          ((derivedPlusEOfEqComparisonIso.{0, 0} k Q Λ Λc j hj ν₀ h hp).hom.app d) ≫
        (blackAdjOfEq Q pl i hp).mapDerivedCategory.counit.app
          ((derivedComparison.{0, 0} (TPp β)ᵐᵒᵖ).obj d) := by
  subst h
  exact derivedPlusFEAdjunction_counit_comparisonOfEq (Λ := Λ) ν i C hRq d

end Plus

end OfEqCounit

/-! ### The crossings of different colours -/

section MixedCross

variable (ν : Multiset I) (a b : I)

set_option hygiene false in
local notation "νa" => ((Singleton.singleton a : Multiset I) + ν)
set_option hygiene false in
local notation "νb" => ((Singleton.singleton b : Multiset I) + ν)
set_option hygiene false in
local notation "νab" =>
  ((Singleton.singleton a : Multiset I) + ((Singleton.singleton b : Multiset I) + ν))

variable [DG.HasDerivedCategory.{0, 0} (TA ν)ᵐᵒᵖ] [DG.HasDerivedCategory.{0, 0} (TA νa)ᵐᵒᵖ]
  [DG.HasDerivedCategory.{0, 0} (TA νb)ᵐᵒᵖ] [DG.HasDerivedCategory.{0, 0} (TA νab)ᵐᵒᵖ]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TA ν)ᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TA νa)ᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TA νb)ᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TA νab)ᵐᵒᵖ)]
  (C : QuantumGroup.CartanDatum I) (hRq : IsRouquierQ C Q)

/-- **The conjugate crossing of different colours on `𝔈_a 𝔈_b` is the crossing** (Webster,
arXiv:1309.3796v3, §4.6 and §7.3, proof of Proposition 7.21): on derived categories of dg
modules over `T^λ`, the conjugate along the composite adjunctions of the crossing
`CupCap.dgBlackFMixedCross` on `𝔉_a 𝔉_b` is the directly defined crossing
`CupCap.dgMixedCross` on `𝔈_a 𝔈_b`. -/
theorem dgBlackEMixedCrossMate_eq_dgMixedCross (hQ : KLRSymm Q) :
    dgBlackEMixedCrossMate (Λ := Λ) ν a b C hRq hQ = dgMixedCross.{0, 0} ν a b hQ := by
  let := blackF_preservesFiniteLimits Q Λ a ν C hRq
  let := blackF_preservesFiniteColimits Q Λ a ν C hRq
  let := blackF_preservesFiniteLimits Q Λ b ν C hRq
  let := blackF_preservesFiniteColimits Q Λ b ν C hRq
  let := blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q Λ a
    (rfl : ({a} : Multiset I) + νb = νab) C hRq
  let := blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q Λ a
    (rfl : ({a} : Multiset I) + νb = νab) C hRq
  let := blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q Λ b (mixedSwap ν a b) C hRq
  let := blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q Λ b (mixedSwap ν a b) C hRq
  have hmod : conjugateEquiv
      ((blackAdjunction.{0} Q Λ a ν).comp (blackAdjOfEq Q Λ b (mixedSwap ν a b)))
      ((blackAdjunction.{0} Q Λ b ν).comp
        (blackAdjOfEq Q Λ a (rfl : ({a} : Multiset I) + νb = νab)))
      (indCrossOfEq Λ hQ a b rfl rfl rfl (mixedSwap ν a b)) =
      resCrossOfEq Λ hQ a b rfl rfl rfl (mixedSwap ν a b) :=
    (conjugateEquiv _ _).apply_symm_apply _
  have hder := conjugateEquiv_comp_mapDerivedCategory_between (blackAdjunction.{0} Q Λ a ν)
    (blackAdjOfEq Q Λ b (mixedSwap ν a b)) (blackAdjunction.{0} Q Λ b ν)
    (blackAdjOfEq Q Λ a (rfl : ({a} : Multiset I) + νb = νab))
    (indCrossOfEq Λ hQ a b rfl rfl rfl (mixedSwap ν a b))
  rw [hmod] at hder
  exact conjugateEquiv_eq_of_comparison_between
    (squarePaste (derivedBlackFOfEqComparisonIso.{0, 0} Q Λ (mixedSwap ν a b) C hRq)
      (derivedBlackFComparisonIso.{0, 0} Q Λ a ν C hRq))
    (squarePaste (derivedBlackEComparisonIso.{0, 0} Q Λ a ν)
      (derivedBlackEOfEqComparisonIso.{0, 0} Q Λ (mixedSwap ν a b)))
    (squarePaste
      (derivedBlackFOfEqComparisonIso.{0, 0} Q Λ (rfl : ({a} : Multiset I) + νb = νab) C hRq)
      (derivedBlackFComparisonIso.{0, 0} Q Λ b ν C hRq))
    (squarePaste (derivedBlackEComparisonIso.{0, 0} Q Λ b ν)
      (derivedBlackEOfEqComparisonIso.{0, 0} Q Λ (rfl : ({a} : Multiset I) + νb = νab)))
    (adj₁' := (blackAdjunction.{0} Q Λ a ν).mapDerivedCategory.comp
      (blackAdjOfEq Q Λ b (mixedSwap ν a b)).mapDerivedCategory)
    (adj₂' := (blackAdjunction.{0} Q Λ b ν).mapDerivedCategory.comp
      (blackAdjOfEq Q Λ a (rfl : ({a} : Multiset I) + νb = νab)).mapDerivedCategory)
    (comp_counit_map_of_comparison
      (fun d => adjunctionOfComparison_counit_map (derivedComparisonEquivalence.{0, 0} (TA ν)ᵐᵒᵖ)
        (derivedComparisonEquivalence.{0, 0} (TA νa)ᵐᵒᵖ) (derivedBlackAdjunction.{0} Q Λ a ν C hRq)
        (derivedBlackFComparisonIso.{0, 0} Q Λ a ν C hRq)
        (derivedBlackEComparisonIso.{0, 0} Q Λ a ν) d)
      (derivedBlackFEAdjunctionOfEq_counit_comparison (mixedSwap ν a b) C hRq))
    (comp_counit_map_of_comparison
      (fun d => adjunctionOfComparison_counit_map (derivedComparisonEquivalence.{0, 0} (TA ν)ᵐᵒᵖ)
        (derivedComparisonEquivalence.{0, 0} (TA νb)ᵐᵒᵖ) (derivedBlackAdjunction.{0} Q Λ b ν C hRq)
        (derivedBlackFComparisonIso.{0, 0} Q Λ b ν C hRq)
        (derivedBlackEComparisonIso.{0, 0} Q Λ b ν) d)
      (derivedBlackFEAdjunctionOfEq_counit_comparison (rfl : ({a} : Multiset I) + νb = νab) C
        hRq))
    _ _ hder _ _
    (isComparisonConj_comparisonConj _ _ _ _)
    (isComparisonConj_comparisonConj _ _ _ _)

section Plus

variable [DG.HasDerivedCategory.{0, 0} (TPp ν)ᵐᵒᵖ] [DG.HasDerivedCategory.{0, 0} (TPp νa)ᵐᵒᵖ]
  [DG.HasDerivedCategory.{0, 0} (TPp νb)ᵐᵒᵖ] [DG.HasDerivedCategory.{0, 0} (TPp νab)ᵐᵒᵖ]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TPp ν)ᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TPp νa)ᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TPp νb)ᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TPp νab)ᵐᵒᵖ)]

set_option linter.unusedSectionVars false in
/-- **The conjugate crossing of different colours on `𝔈⁺_a 𝔈⁺_b` is the crossing** (Webster,
arXiv:1309.3796v3, §4.6 and §7.3, proof of Proposition 7.21): on derived categories of dg
modules over `T^{λ⁺}`, the conjugate along the composite adjunctions of the crossing
`CupCap.dgPlusFMixedCross` on `𝔉⁺_a 𝔉⁺_b` is the directly defined crossing
`CupCap.dgPlusMixedCross` on `𝔈⁺_a 𝔈⁺_b`. -/
theorem dgPlusEMixedCrossMate_eq_dgPlusMixedCross (hQ : KLRSymm Q) :
    dgPlusEMixedCrossMate k Q Λ Λc j hj ν₀ ν a b C hRq hQ =
      dgPlusMixedCross.{0, 0} k Q Λ Λc j hj ν₀ ν a b hQ := by
  let := blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q pl a (plusWeight_assoc ν ν₀ a) C hRq
  let := blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q pl a (plusWeight_assoc ν ν₀ a) C
    hRq
  let := blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q pl b (plusWeight_assoc ν ν₀ b) C hRq
  let := blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q pl b (plusWeight_assoc ν ν₀ b) C
    hRq
  let := blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q pl a (plusWeight_assoc νb ν₀ a) C hRq
  let := blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q pl a (plusWeight_assoc νb ν₀ a) C
    hRq
  let := blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q pl b
    (plusWeight_assoc_mixed_swap (ν₀ := ν₀) ν a b) C hRq
  let := blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q pl b
    (plusWeight_assoc_mixed_swap (ν₀ := ν₀) ν a b) C hRq
  have hmod : conjugateEquiv
      ((blackAdjOfEq Q pl a (plusWeight_assoc ν ν₀ a)).comp
        (blackAdjOfEq Q pl b (plusWeight_assoc_mixed_swap ν a b)))
      ((blackAdjOfEq Q pl b (plusWeight_assoc ν ν₀ b)).comp
        (blackAdjOfEq Q pl a (plusWeight_assoc νb ν₀ a)))
      (indCrossOfEq pl hQ a b (plusWeight_assoc ν ν₀ b) (plusWeight_assoc νb ν₀ a)
        (plusWeight_assoc ν ν₀ a) (plusWeight_assoc_mixed_swap ν a b)) =
      resCrossOfEq pl hQ a b (plusWeight_assoc ν ν₀ b) (plusWeight_assoc νb ν₀ a)
        (plusWeight_assoc ν ν₀ a) (plusWeight_assoc_mixed_swap ν a b) :=
    (conjugateEquiv _ _).apply_symm_apply _
  have hder := conjugateEquiv_comp_mapDerivedCategory_between
    (blackAdjOfEq Q pl a (plusWeight_assoc ν ν₀ a))
    (blackAdjOfEq Q pl b (plusWeight_assoc_mixed_swap ν a b))
    (blackAdjOfEq Q pl b (plusWeight_assoc ν ν₀ b))
    (blackAdjOfEq Q pl a (plusWeight_assoc νb ν₀ a))
    (indCrossOfEq pl hQ a b (plusWeight_assoc ν ν₀ b) (plusWeight_assoc νb ν₀ a)
      (plusWeight_assoc ν ν₀ a) (plusWeight_assoc_mixed_swap ν a b))
  rw [hmod] at hder
  exact conjugateEquiv_eq_of_comparison_between
    (squarePaste (derivedPlusFOfEqComparisonIso.{0, 0} k Q Λ Λc j hj ν₀ (mixedSwap ν a b) C hRq
        (plusWeight_assoc_mixed_swap ν a b))
      (derivedPlusFComparisonIsoOfEq.{0, 0} k Q Λ Λc j hj ν₀ ν a C hRq))
    (squarePaste (derivedPlusEComparisonIsoOfEq.{0, 0} k Q Λ Λc j hj ν₀ ν a)
      (derivedPlusEOfEqComparisonIso.{0, 0} k Q Λ Λc j hj ν₀ (mixedSwap ν a b)
        (plusWeight_assoc_mixed_swap ν a b)))
    (squarePaste (derivedPlusFOfEqComparisonIso.{0, 0} k Q Λ Λc j hj ν₀
        (rfl : ({a} : Multiset I) + νb = νab) C hRq (plusWeight_assoc νb ν₀ a))
      (derivedPlusFComparisonIsoOfEq.{0, 0} k Q Λ Λc j hj ν₀ ν b C hRq))
    (squarePaste (derivedPlusEComparisonIsoOfEq.{0, 0} k Q Λ Λc j hj ν₀ ν b)
      (derivedPlusEOfEqComparisonIso.{0, 0} k Q Λ Λc j hj ν₀
        (rfl : ({a} : Multiset I) + νb = νab) (plusWeight_assoc νb ν₀ a)))
    (adj₁' := (blackAdjOfEq Q pl a (plusWeight_assoc ν ν₀ a)).mapDerivedCategory.comp
      (blackAdjOfEq Q pl b (plusWeight_assoc_mixed_swap ν a b)).mapDerivedCategory)
    (adj₂' := (blackAdjOfEq Q pl b (plusWeight_assoc ν ν₀ b)).mapDerivedCategory.comp
      (blackAdjOfEq Q pl a (plusWeight_assoc νb ν₀ a)).mapDerivedCategory)
    (comp_counit_map_of_comparison
      (derivedPlusFEAdjunction_counit_comparisonOfEq (Λ := Λ) ν a C hRq)
      (derivedPlusFEAdjunctionOfEq_counit_comparison (mixedSwap ν a b) C hRq
        (plusWeight_assoc_mixed_swap ν a b)))
    (comp_counit_map_of_comparison
      (derivedPlusFEAdjunction_counit_comparisonOfEq (Λ := Λ) ν b C hRq)
      (derivedPlusFEAdjunctionOfEq_counit_comparison (rfl : ({a} : Multiset I) + νb = νab) C hRq
        (plusWeight_assoc νb ν₀ a)))
    _ _ hder _ _
    (isComparisonConj_comparisonConj _ _ _ _)
    (isComparisonConj_comparisonConj _ _ _ _)

section Cases

variable {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
variable [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
  (hQ : KLRSymm Q) (hκ : ∀ i', IsUnit (cupScalar Q ν₀ i')) (hP : PullOff k Q Λc ν₀ L)
  (hPL : PullOffLeft k Q Λc ν₀ L)
  (hfin : ∀ (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t), Module.Finite k
    (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht))))
  (hproj : ∀ (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t), Module.Projective k
    (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht))))
  (shift : ℤ)


/-- **`𝔈⁺_a 𝔈⁺_b ⋙ 𝕋 ≅ 𝕋 ⋙ 𝔈_a 𝔈_b` carries the crossing of different colours to the
crossing, for `j < ℓ`** (Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21), for the
quantum trace with homological shift `shift`, with the directly defined crossings: the
conjugates of the pasted isomorphisms of `CupCap.capFDataMid` for the two orders of appending,
followed by the shift, carry `CupCap.dgPlusMixedCross` to `CupCap.dgMixedCross`. This is
`CupCap.capEQuantumTraceShiftIsoMid_mixedCross` with
`CupCap.dgPlusEMixedCrossMate_eq_dgPlusMixedCross` and
`CupCap.dgBlackEMixedCrossMate_eq_dgMixedCross`.
Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`. -/
theorem capEQuantumTraceShiftIsoMid_dgMixedCross (h : j < ℓ) (hab : a ≠ b) :
    letI := blackF_preservesFiniteLimits Q Λ a ν C hRq
    letI := blackF_preservesFiniteColimits Q Λ a ν C hRq
    letI := blackF_preservesFiniteLimits Q Λ b ν C hRq
    letI := blackF_preservesFiniteColimits Q Λ b ν C hRq
    letI := blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q Λ a (rfl : ({a} : Multiset I) + νb
      = νab) C hRq
    letI := blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q Λ a (rfl : ({a} : Multiset I) + νb
      = νab) C hRq
    letI := blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q Λ b (mixedSwap ν a b) C hRq
    letI := blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q Λ b (mixedSwap ν a b) C hRq
    letI := projective_plusCorner k Q Λ Λc j hj ν₀ ν a C hRq
    letI := functor_preservesFiniteLimits (aT ν a)
    letI := functor_preservesFiniteColimits (aT ν a)
    letI := projective_plusCorner k Q Λ Λc j hj ν₀ ν b C hRq
    letI := functor_preservesFiniteLimits (aT ν b)
    letI := functor_preservesFiniteColimits (aT ν b)
    letI := blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) a
      (plusWeight_assoc ν ν₀ a) C hRq
    letI := blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) a
      (plusWeight_assoc ν ν₀ a) C hRq
    letI := blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) b
      (plusWeight_assoc ν ν₀ b) C hRq
    letI := blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) b
      (plusWeight_assoc ν ν₀ b) C hRq
    letI := blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) a
      (plusWeight_assoc νb ν₀ a) C hRq
    letI := blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) a
      (plusWeight_assoc νb ν₀ a) C hRq
    letI := blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) b
      (plusWeight_assoc_mixed_swap (ν₀ := ν₀) ν a b) C hRq
    letI := blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) b
      (plusWeight_assoc_mixed_swap (ν₀ := ν₀) ν a b) C hRq
    letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := ν) hL hQ hκ hP hPL
      hfin hproj
    letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := νa) hL hQ hκ hP hPL
      hfin hproj
    letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := νb) hL hQ hκ hP hPL
      hfin hproj
    letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := νab) hL hQ hκ hP hPL
      hfin hproj
    letI := derivedBlackEAdjointCommShift (Λ := Λ) ν a C hRq
    letI := derivedBlackEAdjointCommShift (Λ := Λ) ν b C hRq
    letI := derivedBlackEOfEqAdjointCommShift (Λ := Λ) (mixedSwap ν a b) C hRq
    letI := derivedBlackEOfEqAdjointCommShift (Λ := Λ) (rfl : ({a} : Multiset I) + νb = νab) C
      hRq
    Functor.whiskerRight (dgPlusMixedCross.{0, 0} k Q Λ Λc j hj ν₀ ν a b hQ)
        (quantumTraceFunctor k Q Λ Λc j hj ν ν₀ L shift) ≫
        (quantumTraceCommIso
          ((derivedBlackFEAdjunction (Λ := Λ) ν b C hRq).comp
            (derivedBlackFEAdjunctionOfEq (Λ := Λ) (rfl : ({a} : Multiset I) + νb = νab) C
              hRq))
          ((derivedPlusFEAdjunction ν b C hRq).comp
            (derivedPlusFEAdjunctionOfEq k Q Λ Λc j hj ν₀ (rfl : ({a} : Multiset I) + νb = νab) C
              hRq))
          (capFDerivedIsoPaste'.{0, 0} (rfl : ({a} : Multiset I) + νb = νab) C hRq
            (capFDataMid (hL := hL) (ν := ν) (i := b) (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP
              hPL hκ h)
            (capFDataMid (hL := hL) (ν := νb) (i := a) (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL)
              hP hPL hκ h)) shift).hom =
      (quantumTraceCommIso
          ((derivedBlackFEAdjunction (Λ := Λ) ν a C hRq).comp
            (derivedBlackFEAdjunctionOfEq (Λ := Λ) (mixedSwap ν a b) C hRq))
          ((derivedPlusFEAdjunction ν a C hRq).comp
            (derivedPlusFEAdjunctionOfEq k Q Λ Λc j hj ν₀ (mixedSwap ν a b) C hRq))
          (capFDerivedIsoPaste'.{0, 0} (mixedSwap ν a b) C hRq
            (capFDataMid (hL := hL) (ν := ν) (i := a) (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP
              hPL hκ h)
            (capFDataMid (hL := hL) (ν := νa) (i := b) (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL)
              hP hPL hκ h)) shift).hom ≫
        Functor.whiskerLeft (quantumTraceFunctor k Q Λ Λc j hj νab ν₀ L shift)
          (dgMixedCross.{0, 0} ν a b hQ) := by
  rw [← dgPlusEMixedCrossMate_eq_dgPlusMixedCross (Λ := Λ) ν a b C hRq hQ,
    ← dgBlackEMixedCrossMate_eq_dgMixedCross (Λ := Λ) ν a b C hRq hQ]
  exact capEQuantumTraceShiftIsoMid_mixedCross ν a b C hRq hL hQ hκ hP hPL hfin hproj shift h hab

/-- **`𝔈⁺_a 𝔈⁺_b ⋙ 𝕋 ≅ 𝕋 ⋙ 𝔈_a 𝔈_b` carries the crossing of different colours to the
crossing, for `j = ℓ`** (Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21), for the
quantum trace with homological shift `shift`, with the directly defined crossings: the
conjugates of the pasted isomorphisms of `CupCap.capFDataTop` for the two orders of appending,
followed by the shift, carry `CupCap.dgPlusMixedCross` to `CupCap.dgMixedCross`. This is
`CupCap.capEQuantumTraceShiftIsoTop_mixedCross` with
`CupCap.dgPlusEMixedCrossMate_eq_dgPlusMixedCross` and
`CupCap.dgBlackEMixedCrossMate_eq_dgMixedCross`.
Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`. -/
theorem capEQuantumTraceShiftIsoTop_dgMixedCross (h : ¬ j < ℓ) (hab : a ≠ b) :
    letI := blackF_preservesFiniteLimits Q Λ a ν C hRq
    letI := blackF_preservesFiniteColimits Q Λ a ν C hRq
    letI := blackF_preservesFiniteLimits Q Λ b ν C hRq
    letI := blackF_preservesFiniteColimits Q Λ b ν C hRq
    letI := blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q Λ a (rfl : ({a} : Multiset I) + νb
      = νab) C hRq
    letI := blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q Λ a (rfl : ({a} : Multiset I) + νb
      = νab) C hRq
    letI := blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q Λ b (mixedSwap ν a b) C hRq
    letI := blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q Λ b (mixedSwap ν a b) C hRq
    letI := projective_plusCorner k Q Λ Λc j hj ν₀ ν a C hRq
    letI := functor_preservesFiniteLimits (aT ν a)
    letI := functor_preservesFiniteColimits (aT ν a)
    letI := projective_plusCorner k Q Λ Λc j hj ν₀ ν b C hRq
    letI := functor_preservesFiniteLimits (aT ν b)
    letI := functor_preservesFiniteColimits (aT ν b)
    letI := blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) a
      (plusWeight_assoc ν ν₀ a) C hRq
    letI := blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) a
      (plusWeight_assoc ν ν₀ a) C hRq
    letI := blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) b
      (plusWeight_assoc ν ν₀ b) C hRq
    letI := blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) b
      (plusWeight_assoc ν ν₀ b) C hRq
    letI := blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) a
      (plusWeight_assoc νb ν₀ a) C hRq
    letI := blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) a
      (plusWeight_assoc νb ν₀ a) C hRq
    letI := blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) b
      (plusWeight_assoc_mixed_swap (ν₀ := ν₀) ν a b) C hRq
    letI := blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) b
      (plusWeight_assoc_mixed_swap (ν₀ := ν₀) ν a b) C hRq
    letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := ν) hL hQ hκ hP hPL
      hfin hproj
    letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := νa) hL hQ hκ hP hPL
      hfin hproj
    letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := νb) hL hQ hκ hP hPL
      hfin hproj
    letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := νab) hL hQ hκ hP hPL
      hfin hproj
    letI := derivedBlackEAdjointCommShift (Λ := Λ) ν a C hRq
    letI := derivedBlackEAdjointCommShift (Λ := Λ) ν b C hRq
    letI := derivedBlackEOfEqAdjointCommShift (Λ := Λ) (mixedSwap ν a b) C hRq
    letI := derivedBlackEOfEqAdjointCommShift (Λ := Λ) (rfl : ({a} : Multiset I) + νb = νab) C
      hRq
    Functor.whiskerRight (dgPlusMixedCross.{0, 0} k Q Λ Λc j hj ν₀ ν a b hQ)
        (quantumTraceFunctor k Q Λ Λc j hj ν ν₀ L shift) ≫
        (quantumTraceCommIso
          ((derivedBlackFEAdjunction (Λ := Λ) ν b C hRq).comp
            (derivedBlackFEAdjunctionOfEq (Λ := Λ) (rfl : ({a} : Multiset I) + νb = νab) C
              hRq))
          ((derivedPlusFEAdjunction ν b C hRq).comp
            (derivedPlusFEAdjunctionOfEq k Q Λ Λc j hj ν₀ (rfl : ({a} : Multiset I) + νb = νab) C
              hRq))
          (capFDerivedIsoPaste'.{0, 0} (rfl : ({a} : Multiset I) + νb = νab) C hRq
            (capFDataTop (hL := hL) (ν := ν) (i := b) (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP
              hPL hκ h)
            (capFDataTop (hL := hL) (ν := νb) (i := a) (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL)
              hP hPL hκ h)) shift).hom =
      (quantumTraceCommIso
          ((derivedBlackFEAdjunction (Λ := Λ) ν a C hRq).comp
            (derivedBlackFEAdjunctionOfEq (Λ := Λ) (mixedSwap ν a b) C hRq))
          ((derivedPlusFEAdjunction ν a C hRq).comp
            (derivedPlusFEAdjunctionOfEq k Q Λ Λc j hj ν₀ (mixedSwap ν a b) C hRq))
          (capFDerivedIsoPaste'.{0, 0} (mixedSwap ν a b) C hRq
            (capFDataTop (hL := hL) (ν := ν) (i := a) (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP
              hPL hκ h)
            (capFDataTop (hL := hL) (ν := νa) (i := b) (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL)
              hP hPL hκ h)) shift).hom ≫
        Functor.whiskerLeft (quantumTraceFunctor k Q Λ Λc j hj νab ν₀ L shift)
          (dgMixedCross.{0, 0} ν a b hQ) := by
  rw [← dgPlusEMixedCrossMate_eq_dgPlusMixedCross (Λ := Λ) ν a b C hRq hQ,
    ← dgBlackEMixedCrossMate_eq_dgMixedCross (Λ := Λ) ν a b C hRq hQ]
  exact capEQuantumTraceShiftIsoTop_mixedCross ν a b C hRq hL hQ hκ hP hPL hfin hproj shift h hab

end Cases

end Plus

end MixedCross

end Categorification.Stendhal.CupCap
