/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721CapMateEFDG
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapTraceE

/-!
# The conjugate dot on `𝔈_i` is the dot

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21 (the dots of the categorical action on derived categories, §4.6). On derived
categories of dg modules over `T^λ`, the dot on `𝔈_i` was defined in two ways: directly, as the
conjugate along the comparison isomorphism of the derived dot on restriction
(`CupCap.dgBlackDot`), and as the conjugate along `𝔉_i ⊣ 𝔈_i` of the dot on `𝔉_i`
(`CupCap.dgBlackEDotMate`), which is the form used by the quantum trace statements
(`CupCap.capEQuantumTraceShiftIso_dot`). They agree (`CupCap.dgBlackEDotMate_eq_dgBlackDot`):
on modules the dot on induction is by definition the conjugate of the dot on restriction
(`indDotOfEq`), and conjugates pass to derived categories
(`CupCap.conjugateEquiv_mapDerivedCategory`) and along comparison functors
(`CupCap.conjugateEquiv_eq_of_comparison`).

## Main results

* `CupCap.conjugateEquiv_eq_of_counit`: a conjugate is recognised by the counit equation.
* `CupCap.conjugateEquiv_mapDerivedCategory`: conjugates pass to Mathlib's derived categories.
* `CupCap.conjugateEquiv_eq_of_comparison`: conjugates transport along comparison functors.
* `CupCap.dgBlackEDotMate_eq_dgBlackDot`.

Route hypotheses: none beyond `C`, `hRq : IsRouquierQ C Q` (Webster's setting for
Theorem 4.31) for the adjunction.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open CategoryTheory Limits KLR KLRAlgebra MulOpposite InductionAlong DG.DegreeZero

section Conjugate

universe v₁ v₂ u₁ u₂

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
  {L₁ L₂ : A ⥤ B} {R₁ R₂ : B ⥤ A} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

/-- **A conjugate is recognised by its compatibility with the counits**: if
`L₂ β_d ≫ ε₂ = α_{R₁ d} ≫ ε₁` for every `d`, then `β` is the conjugate of `α`. -/
theorem conjugateEquiv_eq_of_counit (α : L₂ ⟶ L₁) (β : R₁ ⟶ R₂)
    (h : ∀ d : B, L₂.map (β.app d) ≫ adj₂.counit.app d = α.app (R₁.obj d) ≫ adj₁.counit.app d) :
    conjugateEquiv adj₁ adj₂ α = β := by
  ext d
  apply (adj₂.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, h d]
  exact conjugateEquiv_counit adj₁ adj₂ α d

end Conjugate

section Derived

variable {C₁ C₂ : Type*} [Category* C₁] [Abelian C₁] [HasDerivedCategory C₁]
  [Category* C₂] [Abelian C₂] [HasDerivedCategory C₂]
  {L₁ L₂ : C₁ ⥤ C₂} [L₁.Additive] [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
  [L₂.Additive] [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
  {R₁ R₂ : C₂ ⥤ C₁} [R₁.Additive] [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
  [R₂.Additive] [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

/-- **Conjugates pass to derived categories**: the conjugate of the derived natural
transformation of `α` along the derived adjunctions is the derived natural transformation of the
conjugate of `α`. -/
theorem conjugateEquiv_mapDerivedCategory (α : L₂ ⟶ L₁) :
    conjugateEquiv adj₁.mapDerivedCategory adj₂.mapDerivedCategory α.mapDerivedCategory =
      (conjugateEquiv adj₁ adj₂ α).mapDerivedCategory := by
  have hmod : Functor.whiskerRight (conjugateEquiv adj₁ adj₂ α) L₂ ≫ adj₂.counit =
      Functor.whiskerLeft R₁ α ≫ adj₁.counit := by
    ext d
    exact conjugateEquiv_counit adj₁ adj₂ α d
  have key : Functor.whiskerRight (conjugateEquiv adj₁ adj₂ α).mapDerivedCategory
        L₂.mapDerivedCategory ≫ adj₂.mapDerivedCategory.counit =
      Functor.whiskerLeft R₁.mapDerivedCategory α.mapDerivedCategory ≫
        adj₁.mapDerivedCategory.counit := by
    rw [Adjunction.mapDerivedCategory_counit_eq, Adjunction.mapDerivedCategory_counit_eq,
      NatTrans.whiskerRight_mapDerivedCategory, NatTrans.whiskerLeft_mapDerivedCategory]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← NatTrans.mapDerivedCategory_comp_assoc, ← NatTrans.mapDerivedCategory_comp_assoc, hmod]
  exact conjugateEquiv_eq_of_counit adj₁.mapDerivedCategory adj₂.mapDerivedCategory _ _
    fun d => NatTrans.congr_app key d

end Derived

section Transport

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {A : Type u₁} {Aᵢ : Type u₂} {A' : Type u₃} {Aᵢ' : Type u₄}
  [Category.{v₁} A] [Category.{v₂} Aᵢ] [Category.{v₃} A'] [Category.{v₄} Aᵢ']
  {cA : A ⥤ A'} {cAᵢ : Aᵢ ⥤ Aᵢ'} {F : A ⥤ Aᵢ} {E : Aᵢ ⥤ A} {F' : A' ⥤ Aᵢ'} {E' : Aᵢ' ⥤ A'}
  {adj : F ⊣ E} {adj' : F' ⊣ E'}
  (iF : F ⋙ cAᵢ ≅ cA ⋙ F') (iE : E ⋙ cA ≅ cAᵢ ⋙ E')

/-- **Conjugates transport along comparison functors**: if the comparisons intertwine the two
adjunctions on the counits (`hε`), the comparison of `Aᵢ` is faithful, and `α`, `β` correspond
under the comparisons to `α'`, `β'` with `β'` the conjugate of `α'`, then `β` is the conjugate
of `α`. -/
theorem conjugateEquiv_eq_of_comparison [cAᵢ.Faithful]
    (hε : ∀ d, cAᵢ.map (adj.counit.app d) =
      iF.hom.app (E.obj d) ≫ F'.map (iE.hom.app d) ≫ adj'.counit.app (cAᵢ.obj d))
    (α' : F' ⟶ F') (β' : E' ⟶ E') (hmate : conjugateEquiv adj' adj' α' = β')
    (α : F ⟶ F) (β : E ⟶ E)
    (hα : ∀ a, cAᵢ.map (α.app a) = iF.hom.app a ≫ α'.app (cA.obj a) ≫ iF.inv.app a)
    (hβ : ∀ d, cA.map (β.app d) = iE.hom.app d ≫ β'.app (cAᵢ.obj d) ≫ iE.inv.app d) :
    conjugateEquiv adj adj α = β := by
  have hmod : ∀ x, F'.map (β'.app x) ≫ adj'.counit.app x =
      α'.app (E'.obj x) ≫ adj'.counit.app x := fun x => by
    rw [← hmate]
    exact conjugateEquiv_counit adj' adj' α' x
  refine conjugateEquiv_eq_of_counit adj adj α β fun d => cAᵢ.map_injective ?_
  have nF := NatIso.naturality_2 iF (β.app d)
  simp only [Functor.comp_map] at nF
  simp only [Functor.map_comp, hε, hα]
  rw [← nF, hβ]
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← F'.map_comp_assoc (iE.inv.app d), Iso.inv_hom_id_app, F'.map_id, Category.id_comp,
    hmod]
  have nα := α'.naturality (iE.hom.app d)
  rw [reassoc_of% nα]

end Transport

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}
  (ν : Multiset I) (i : I)

set_option hygiene false in
local notation "TA" => TensorProductAlgebra k Q Λ ν
set_option hygiene false in
local notation "TAᵢ" => TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν)

private theorem blackE_additive_dotMateDirect : (blackE Q Λ i ν).Additive :=
  inferInstanceAs (resFunctor.{0, 0} (appendBlackOp Q Λ i ν)).Additive

private theorem blackF_additive_dotMateDirect : (blackF Q Λ i ν).Additive :=
  inferInstanceAs (InductionAlong.functor.{0, 0} (appendBlackOp Q Λ i ν)).Additive

attribute [local instance] blackE_additive_dotMateDirect blackF_additive_dotMateDirect

variable [DG.HasDerivedCategory.{0, 0} TAᵐᵒᵖ] [DG.HasDerivedCategory.{0, 0} TAᵢᵐᵒᵖ]
  [HasDerivedCategory.{0} (ModuleCat.{0} TAᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} TAᵢᵐᵒᵖ)]
  (C : QuantumGroup.CartanDatum I) (hRq : IsRouquierQ C Q)

/-- **The conjugate dot on `𝔈_i` is the dot** (Webster, arXiv:1309.3796v3, §4.6 and §7.3,
proof of Proposition 7.21): on derived categories of dg modules over `T^λ`, the conjugate along
`𝔉_i ⊣ 𝔈_i` of the dot on `𝔉_i` is the dot on `𝔈_i`. -/
theorem dgBlackEDotMate_eq_dgBlackDot :
    dgBlackEDotMate (Λ := Λ) ν i C hRq = dgBlackDot.{0, 0} (Q := Q) (Λ := Λ) ν i := by
  let := blackF_preservesFiniteLimits Q Λ i ν C hRq
  let := blackF_preservesFiniteColimits Q Λ i ν C hRq
  have hmod : conjugateEquiv (blackAdjunction.{0} Q Λ i ν) (blackAdjunction.{0} Q Λ i ν)
      (indDotOfEq Q Λ i (rfl : ({i} : Multiset I) + ν = _) : blackF Q Λ i ν ⟶ blackF Q Λ i ν) =
      blackDot Q Λ i ν :=
    (conjugateEquiv (blackAdjOfEq Q Λ i (rfl : ({i} : Multiset I) + ν = _))
      (blackAdjOfEq Q Λ i rfl)).apply_symm_apply _
  have hder := conjugateEquiv_mapDerivedCategory (blackAdjunction.{0} Q Λ i ν)
    (blackAdjunction.{0} Q Λ i ν)
    (indDotOfEq Q Λ i (rfl : ({i} : Multiset I) + ν = _) : blackF Q Λ i ν ⟶ blackF Q Λ i ν)
  rw [hmod] at hder
  exact conjugateEquiv_eq_of_comparison
    (derivedBlackFComparisonIso.{0, 0} Q Λ i ν C hRq) (derivedBlackEComparisonIso.{0, 0} Q Λ i ν)
    (adj' := derivedBlackAdjunction.{0} Q Λ i ν C hRq)
    (fun d => adjunctionOfComparison_counit_map (derivedComparisonEquivalence.{0, 0} TAᵐᵒᵖ)
      (derivedComparisonEquivalence.{0, 0} TAᵢᵐᵒᵖ) (derivedBlackAdjunction.{0} Q Λ i ν C hRq)
      (derivedBlackFComparisonIso.{0, 0} Q Λ i ν C hRq)
      (derivedBlackEComparisonIso.{0, 0} Q Λ i ν) d)
    _ _ hder _ _
    (isComparisonConj_comparisonConj _ _ _ _)
    (isComparisonConj_comparisonConj _ _ _ _)

end Categorification.Stendhal.CupCap
