/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackRouqData
import Categorification.KLR.CyclotomicAction.GlobalSlides

/-!
# The nil-Hecke dot slides for black induction

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §4.6, and
Brundan, arXiv:1501.00350v1, (1.2) for equal labels (the `slide_left` and `slide_right` fields
of `TwoRep.RouqLoc`).

On restrictions the dot and the same-colour crossing act by the dot on the newest black strand
and minus the crossing of the two newest black strands, which satisfy the nil-Hecke relations
(`blackCross_dot_sub`, `blackDot_cross_sub`). Their mates through `Fᵢ ⊣ Eᵢ` satisfy the two dot
slides on inductions (`indCrossOfEq_slide_left`, `indCrossOfEq_slide_right`); these pass to the
derived functors (`derivedIndCrossOfEq_slide_left`, `derivedIndCrossOfEq_slide_right`) and to
weight spaces (`blackRouqCross_slide_left_self`, `blackRouqCross_slide_right_self`).

The same-colour crossing acts as `-ψ` throughout, the KL III convention (`resCrossOfEq`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory MulOpposite InductionAlong KLR TwoRep QuantumGroup
  CyclotomicAction

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe w u u₁

/-! ### Mates of differences -/

section Mates

variable {𝒜 ℬ : Type*} [Category 𝒜] [Category ℬ] [Preadditive ℬ] [Preadditive 𝒜]
  {L₁ L₂ : 𝒜 ⥤ ℬ} {R₁ R₂ : ℬ ⥤ 𝒜} [L₂.Additive]


/-- The inverse mate of a difference, for an additive left adjoint. -/
theorem conjugateEquiv_symm_sub_of_additive (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α β : R₁ ⟶ R₂) :
    (conjugateEquiv adj₁ adj₂).symm (α - β) =
      (conjugateEquiv adj₁ adj₂).symm α - (conjugateEquiv adj₁ adj₂).symm β := by
  ext X
  simp [conjugateEquiv_symm_apply_app, Functor.map_sub]

end Mates

variable {I : Type u} [DecidableEq I] {k : Type u} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin ℓ → I →₀ ℕ)

/-! ### On modules -/

/-- The nil-Hecke relation `y' τ - τ y = 1` on restrictions between arbitrary contents. -/
theorem resCrossOfEq_dot_sub (hsym : KLRSymm Q) (i : I) {μ β δ : Multiset I}
    (h₁ : ({i} : Multiset I) + μ = β) (h₂ : ({i} : Multiset I) + β = δ) :
    resCrossOfEq Λ hsym i i h₁ h₂ h₁ h₂ ≫
        Functor.whiskerRight (resDotOfEq Q Λ i h₂) (blackEOfEq Q Λ i h₁) -
      Functor.whiskerLeft (blackEOfEq Q Λ i h₂) (resDotOfEq Q Λ i h₁) ≫
        resCrossOfEq Λ hsym i i h₁ h₂ h₁ h₂ = 𝟙 _ := by
  subst h₁ h₂
  rw [resCrossOfEq_self]
  exact blackCross_dot_sub Q Λ i μ

/-- The nil-Hecke relation `τ y' - y τ = 1` on restrictions between arbitrary contents. -/
theorem resDotOfEq_cross_sub (hsym : KLRSymm Q) (i : I) {μ β δ : Multiset I}
    (h₁ : ({i} : Multiset I) + μ = β) (h₂ : ({i} : Multiset I) + β = δ) :
    Functor.whiskerRight (resDotOfEq Q Λ i h₂) (blackEOfEq Q Λ i h₁) ≫
        resCrossOfEq Λ hsym i i h₁ h₂ h₁ h₂ -
      resCrossOfEq Λ hsym i i h₁ h₂ h₁ h₂ ≫
        Functor.whiskerLeft (blackEOfEq Q Λ i h₂) (resDotOfEq Q Λ i h₁) = 𝟙 _ := by
  subst h₁ h₂
  rw [resCrossOfEq_self]
  exact blackDot_cross_sub Q Λ i μ

theorem whiskerLeft_indDotOfEq (i : I) {μ β δ : Multiset I}
    (h₁ : ({i} : Multiset I) + μ = β) (h₂ : ({i} : Multiset I) + β = δ) :
    Functor.whiskerLeft (blackFOfEq Q Λ i h₁) (indDotOfEq Q Λ i h₂) =
      (conjugateEquiv ((blackAdjOfEq Q Λ i h₁).comp (blackAdjOfEq Q Λ i h₂))
        ((blackAdjOfEq Q Λ i h₁).comp (blackAdjOfEq Q Λ i h₂))).symm
        (Functor.whiskerRight (resDotOfEq Q Λ i h₂) (blackEOfEq Q Λ i h₁)) := by
  rw [Equiv.eq_symm_apply, indDotOfEq, CategoryTheory.conjugateEquiv_whiskerLeft,
    Equiv.apply_symm_apply]

theorem whiskerRight_indDotOfEq (i : I) {μ β δ : Multiset I}
    (h₁ : ({i} : Multiset I) + μ = β) (h₂ : ({i} : Multiset I) + β = δ) :
    Functor.whiskerRight (indDotOfEq Q Λ i h₁) (blackFOfEq Q Λ i h₂) =
      (conjugateEquiv ((blackAdjOfEq Q Λ i h₁).comp (blackAdjOfEq Q Λ i h₂))
        ((blackAdjOfEq Q Λ i h₁).comp (blackAdjOfEq Q Λ i h₂))).symm
        (Functor.whiskerLeft (blackEOfEq Q Λ i h₂) (resDotOfEq Q Λ i h₁)) := by
  rw [Equiv.eq_symm_apply, indDotOfEq, CategoryTheory.conjugateEquiv_whiskerRight,
    Equiv.apply_symm_apply]

/-- **The left dot slide on black inductions** (Brundan (1.2), `RouqLoc.slide_left`):
`Fᵢ ◁ x ≫ τ - τ ≫ x ▷ Fᵢ = 1`, the mate of `resCrossOfEq_dot_sub`. -/
theorem indCrossOfEq_slide_left (hsym : KLRSymm Q) (i : I) {μ β δ : Multiset I}
    (h₁ : ({i} : Multiset I) + μ = β) (h₂ : ({i} : Multiset I) + β = δ) :
    Functor.whiskerLeft (blackFOfEq Q Λ i h₁) (indDotOfEq Q Λ i h₂) ≫
        indCrossOfEq Λ hsym i i h₁ h₂ h₁ h₂ -
      indCrossOfEq Λ hsym i i h₁ h₂ h₁ h₂ ≫
        Functor.whiskerRight (indDotOfEq Q Λ i h₁) (blackFOfEq Q Λ i h₂) = 𝟙 _ := by
  set A := (blackAdjOfEq Q Λ i h₁).comp (blackAdjOfEq Q Λ i h₂)
  rw [whiskerLeft_indDotOfEq, whiskerRight_indDotOfEq, indCrossOfEq,
    conjugateEquiv_symm_comp, conjugateEquiv_symm_comp, ← conjugateEquiv_symm_sub_of_additive,
    resCrossOfEq_dot_sub, conjugateEquiv_symm_id]

/-- **The right dot slide on black inductions** (Brundan (1.2), `RouqLoc.slide_right`):
`τ ≫ Fᵢ ◁ x - x ▷ Fᵢ ≫ τ = 1`, the mate of `resDotOfEq_cross_sub`. -/
theorem indCrossOfEq_slide_right (hsym : KLRSymm Q) (i : I) {μ β δ : Multiset I}
    (h₁ : ({i} : Multiset I) + μ = β) (h₂ : ({i} : Multiset I) + β = δ) :
    indCrossOfEq Λ hsym i i h₁ h₂ h₁ h₂ ≫
        Functor.whiskerLeft (blackFOfEq Q Λ i h₁) (indDotOfEq Q Λ i h₂) -
      Functor.whiskerRight (indDotOfEq Q Λ i h₁) (blackFOfEq Q Λ i h₂) ≫
        indCrossOfEq Λ hsym i i h₁ h₂ h₁ h₂ = 𝟙 _ := by
  set A := (blackAdjOfEq Q Λ i h₁).comp (blackAdjOfEq Q Λ i h₂)
  rw [whiskerLeft_indDotOfEq, whiskerRight_indDotOfEq, indCrossOfEq,
    conjugateEquiv_symm_comp, conjugateEquiv_symm_comp, ← conjugateEquiv_symm_sub_of_additive,
    resDotOfEq_cross_sub, conjugateEquiv_symm_id]


end Categorification.Stendhal

namespace CategoryTheory.NatTrans

open Limits

variable {C₁ : Type*} [Category* C₁] [Abelian C₁] [HasDerivedCategory C₁]
  {C₂ : Type*} [Category* C₂] [Abelian C₂] [HasDerivedCategory C₂]
  {C₃ : Type*} [Category* C₃] [Abelian C₃] [HasDerivedCategory C₃]
  {C₂' : Type*} [Category* C₂'] [Abelian C₂'] [HasDerivedCategory C₂']
  {F₁ : C₁ ⥤ C₂} [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  {F₁' : C₁ ⥤ C₂'} [F₁'.Additive] [PreservesFiniteLimits F₁'] [PreservesFiniteColimits F₁']
  {F₂ : C₂ ⥤ C₃} [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  {F₂' : C₂' ⥤ C₃} [F₂'.Additive] [PreservesFiniteLimits F₂'] [PreservesFiniteColimits F₂']

theorem derivedComp_sub (X Y : F₁ ⋙ F₂ ⟶ F₁' ⋙ F₂') :
    derivedComp (X - Y) = derivedComp X - derivedComp Y := by
  simp only [derivedComp, mapDerivedCategory_sub, Preadditive.comp_sub, Preadditive.sub_comp]

theorem derivedComp_id : derivedComp (𝟙 (F₁ ⋙ F₂)) = 𝟙 _ := by
  simp only [derivedComp, mapDerivedCategory_id, Category.id_comp, Iso.hom_inv_id]

end CategoryTheory.NatTrans

namespace Categorification.Stendhal

open CategoryTheory MulOpposite InductionAlong KLR TwoRep QuantumGroup
  CyclotomicAction

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe w u u₁

variable {I : Type u} [DecidableEq I] {k : Type u} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin ℓ → I →₀ ℕ) {C : CartanDatum I}
  (hQ : IsRouquierQ C Q)
  [∀ β : Multiset I, HasDerivedCategory.{w} (ModuleCat.{u} (TensorProductAlgebra k Q Λ β)ᵐᵒᵖ)]

/-! ### On derived categories -/

/-- **The left dot slide on derived black inductions** (Brundan (1.2)). -/
theorem derivedIndCrossOfEq_slide_left (hsym : KLRSymm Q) (i : I) {μ β δ : Multiset I}
    (h₁ : ({i} : Multiset I) + μ = β) (h₂ : ({i} : Multiset I) + β = δ) :
    Functor.whiskerLeft (derivedFOfEq Λ hQ i h₁) (derivedIndDotOfEq Λ hQ i h₂) ≫
        derivedIndCrossOfEq Λ hQ hsym i i h₁ h₂ h₁ h₂ -
      derivedIndCrossOfEq Λ hQ hsym i i h₁ h₂ h₁ h₂ ≫
        Functor.whiskerRight (derivedIndDotOfEq Λ hQ i h₁) (derivedFOfEq Λ hQ i h₂) = 𝟙 _ := by
  have := blackFOfEq_preservesFiniteLimits Λ hQ i h₁
  have := blackFOfEq_preservesFiniteColimits Λ hQ i h₁
  have := blackFOfEq_preservesFiniteLimits Λ hQ i h₂
  have := blackFOfEq_preservesFiniteColimits Λ hQ i h₂
  unfold derivedIndCrossOfEq derivedIndDotOfEq derivedFOfEq
  rw [NatTrans.whiskerLeft_mapDerivedCategory, NatTrans.whiskerRight_mapDerivedCategory]
  change NatTrans.derivedComp _ ≫ NatTrans.derivedComp _ -
    NatTrans.derivedComp _ ≫ NatTrans.derivedComp _ = _
  rw [NatTrans.derivedComp_comp, NatTrans.derivedComp_comp, ← NatTrans.derivedComp_sub,
    indCrossOfEq_slide_left, NatTrans.derivedComp_id]

/-- **The right dot slide on derived black inductions** (Brundan (1.2)). -/
theorem derivedIndCrossOfEq_slide_right (hsym : KLRSymm Q) (i : I) {μ β δ : Multiset I}
    (h₁ : ({i} : Multiset I) + μ = β) (h₂ : ({i} : Multiset I) + β = δ) :
    derivedIndCrossOfEq Λ hQ hsym i i h₁ h₂ h₁ h₂ ≫
        Functor.whiskerLeft (derivedFOfEq Λ hQ i h₁) (derivedIndDotOfEq Λ hQ i h₂) -
      Functor.whiskerRight (derivedIndDotOfEq Λ hQ i h₁) (derivedFOfEq Λ hQ i h₂) ≫
        derivedIndCrossOfEq Λ hQ hsym i i h₁ h₂ h₁ h₂ = 𝟙 _ := by
  have := blackFOfEq_preservesFiniteLimits Λ hQ i h₁
  have := blackFOfEq_preservesFiniteColimits Λ hQ i h₁
  have := blackFOfEq_preservesFiniteLimits Λ hQ i h₂
  have := blackFOfEq_preservesFiniteColimits Λ hQ i h₂
  unfold derivedIndCrossOfEq derivedIndDotOfEq derivedFOfEq
  rw [NatTrans.whiskerLeft_mapDerivedCategory, NatTrans.whiskerRight_mapDerivedCategory]
  change NatTrans.derivedComp _ ≫ NatTrans.derivedComp _ -
    NatTrans.derivedComp _ ≫ NatTrans.derivedComp _ = _
  rw [NatTrans.derivedComp_comp, NatTrans.derivedComp_comp, ← NatTrans.derivedComp_sub,
    indCrossOfEq_slide_right, NatTrans.derivedComp_id]

/-! ### On weight spaces -/

section Weight

open CategoryTheory.Bicategory

variable {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y] (RD : UDot.WeightDatum C X Y)
  (Λ₀ : X)

/-- `blackRouqE j ◁ blackRouqDot i` on generators. -/
theorem gen₂_whiskerLeft_blackRouqDot (i j : I) {x y t : X} (h₁ : x + RD.iX j = y)
    (h₂ : y + RD.iX i = t)
    (M : ∀ γ : WeightBlocks RD Λ₀ x,
      DerivedCategory (ModuleCat.{u} (TensorProductAlgebra k Q Λ γ.1)ᵐᵒᵖ))
    (γ : WeightBlocks RD Λ₀ x) {β : WeightBlocks RD Λ₀ y} {δ : WeightBlocks RD Λ₀ t}
    (hb : blockSucc RD Λ₀ j h₁ γ = β) (hd : blockSucc RD Λ₀ i h₂ β = δ) :
    gen₂ (blockSucc RD Λ₀ j h₁) (blockSucc RD Λ₀ i h₂) (derivedFBlock Λ hQ RD Λ₀ j h₁)
        (derivedFBlock Λ hQ RD Λ₀ i h₂) M γ hb hd ≫
        (blackRouqE Λ hQ RD Λ₀ j h₁ ◁ blackRouqDot Λ hQ RD Λ₀ i h₂).hom.app M δ =
      (Functor.whiskerLeft (derivedFOfEq Λ hQ j (blockSucc_eq RD Λ₀ j hb))
          (derivedIndDotOfEq Λ hQ i (blockSucc_eq RD Λ₀ i hd))).app (M γ) ≫
        gen₂ (blockSucc RD Λ₀ j h₁) (blockSucc RD Λ₀ i h₂) (derivedFBlock Λ hQ RD Λ₀ j h₁)
          (derivedFBlock Λ hQ RD Λ₀ i h₂) M γ hb hd :=
  gen₂_whiskerLeft (blockSucc RD Λ₀ j h₁) (blockSucc RD Λ₀ i h₂) (derivedFBlock Λ hQ RD Λ₀ j h₁)
    (fun _ _ hβ => derivedIndDotOfEq Λ hQ i (blockSucc_eq RD Λ₀ i hβ)) M γ hb hd

/-- `blackRouqDot j ▷ blackRouqE i` on generators. -/
theorem gen₂_blackRouqDot_whiskerRight (i j : I) {x y t : X} (h₁ : x + RD.iX j = y)
    (h₂ : y + RD.iX i = t)
    (M : ∀ γ : WeightBlocks RD Λ₀ x,
      DerivedCategory (ModuleCat.{u} (TensorProductAlgebra k Q Λ γ.1)ᵐᵒᵖ))
    (γ : WeightBlocks RD Λ₀ x) {β : WeightBlocks RD Λ₀ y} {δ : WeightBlocks RD Λ₀ t}
    (hb : blockSucc RD Λ₀ j h₁ γ = β) (hd : blockSucc RD Λ₀ i h₂ β = δ) :
    gen₂ (blockSucc RD Λ₀ j h₁) (blockSucc RD Λ₀ i h₂) (derivedFBlock Λ hQ RD Λ₀ j h₁)
        (derivedFBlock Λ hQ RD Λ₀ i h₂) M γ hb hd ≫
        (blackRouqDot Λ hQ RD Λ₀ j h₁ ▷ blackRouqE Λ hQ RD Λ₀ i h₂).hom.app M δ =
      (Functor.whiskerRight (derivedIndDotOfEq Λ hQ j (blockSucc_eq RD Λ₀ j hb))
          (derivedFOfEq Λ hQ i (blockSucc_eq RD Λ₀ i hd))).app (M γ) ≫
        gen₂ (blockSucc RD Λ₀ j h₁) (blockSucc RD Λ₀ i h₂) (derivedFBlock Λ hQ RD Λ₀ j h₁)
          (derivedFBlock Λ hQ RD Λ₀ i h₂) M γ hb hd :=
  gen₂_whiskerRight (blockSucc RD Λ₀ j h₁) (blockSucc RD Λ₀ i h₂) (derivedFBlock Λ hQ RD Λ₀ i h₂)
    (fun _ _ hβ => derivedIndDotOfEq Λ hQ j (blockSucc_eq RD Λ₀ j hβ)) M γ hb hd

/-- **Endomorphisms of `Fⱼ Fᵢ` on weight spaces compatible with the generators at a block `γ`**:
pairs of an endomorphism of the composite on weight spaces and of the composite of derived
black inductions starting at `γ`, intertwined by the generators `gen₂`. -/
def blackPairCompat (i j : I) {w₀ w₁ w₂ : X} (h₁ : w₀ + RD.iX j = w₁)
    (h₂ : w₁ + RD.iX i = w₂) (γ : WeightBlocks RD Λ₀ w₀) :
    Subalgebra k (End (blackRouqE Λ hQ RD Λ₀ j h₁ ≫ blackRouqE Λ hQ RD Λ₀ i h₂) ×
      End (derivedFOfEq Λ hQ j (blockSucc_step RD Λ₀ j h₁ γ) ⋙
        derivedFOfEq Λ hQ i (blockSucc_step RD Λ₀ i h₂ (blockSucc RD Λ₀ j h₁ γ)))) :=
  compatSubalgebra _ _ (fun M => M γ)
    (Pi.eval _ (blockSucc RD Λ₀ i h₂ (blockSucc RD Λ₀ j h₁ γ)))
    (fun M => gen₂ (blockSucc RD Λ₀ j h₁) (blockSucc RD Λ₀ i h₂)
      (derivedFBlock Λ hQ RD Λ₀ j h₁) (derivedFBlock Λ hQ RD Λ₀ i h₂) M γ rfl rfl)

/-- **The left dot slide on weight spaces** (Brundan, arXiv:1501.00350v1, (1.2) for equal
labels, the shape of `TwoRep.RouqLoc.slide_left`). -/
theorem blackRouqCross_slide_left_self (hsym : KLRSymm Q) (i : I) {w₀ w₁ w₂ : X}
    (h₁ : w₀ + RD.iX i = w₁) (h₂ : w₁ + RD.iX i = w₂) :
    blackRouqE Λ hQ RD Λ₀ i h₁ ◁ blackRouqDot Λ hQ RD Λ₀ i h₂ ≫
        blackRouqCross Λ hQ RD Λ₀ hsym i i h₁ h₂ h₁ h₂ -
      blackRouqCross Λ hQ RD Λ₀ hsym i i h₁ h₂ h₁ h₂ ≫
        blackRouqDot Λ hQ RD Λ₀ i h₁ ▷ blackRouqE Λ hQ RD Λ₀ i h₂ = 𝟙 _ := by
  apply ObjectProperty.hom_ext
  refine NatTrans.ext (funext fun M => ?_)
  refine gen₂_ext (blockSucc RD Λ₀ i h₁) (blockSucc RD Λ₀ i h₂) (derivedFBlock Λ hQ RD Λ₀ i h₁)
    (derivedFBlock Λ hQ RD Λ₀ i h₂) fun γ β δ hb hd => ?_
  subst hb hd
  have m₁ : (blackRouqE Λ hQ RD Λ₀ i h₁ ◁ blackRouqDot Λ hQ RD Λ₀ i h₂ ≫
        blackRouqCross Λ hQ RD Λ₀ hsym i i h₁ h₂ h₁ h₂,
      Functor.whiskerLeft (derivedFOfEq Λ hQ i (blockSucc_step RD Λ₀ i h₁ γ))
          (derivedIndDotOfEq Λ hQ i (blockSucc_step RD Λ₀ i h₂ _)) ≫
        derivedIndCrossOfEq Λ hQ hsym i i (blockSucc_step RD Λ₀ i h₁ γ)
          (blockSucc_step RD Λ₀ i h₂ _) (blockSucc_step RD Λ₀ i h₁ γ)
          (blockSucc_step RD Λ₀ i h₂ _)) ∈ blackPairCompat Λ hQ RD Λ₀ i i h₁ h₂ γ := fun M =>
    gen_comp_comp (gen₂_whiskerLeft_blackRouqDot Λ hQ RD Λ₀ i i h₁ h₂ M γ rfl rfl)
      (gen₂_blackRouqCross Λ hQ RD Λ₀ hsym i i h₁ h₂ h₁ h₂ M γ rfl rfl rfl rfl)
  have m₂ : (blackRouqCross Λ hQ RD Λ₀ hsym i i h₁ h₂ h₁ h₂ ≫
        blackRouqDot Λ hQ RD Λ₀ i h₁ ▷ blackRouqE Λ hQ RD Λ₀ i h₂,
      derivedIndCrossOfEq Λ hQ hsym i i (blockSucc_step RD Λ₀ i h₁ γ)
          (blockSucc_step RD Λ₀ i h₂ _) (blockSucc_step RD Λ₀ i h₁ γ)
          (blockSucc_step RD Λ₀ i h₂ _) ≫
        Functor.whiskerRight (derivedIndDotOfEq Λ hQ i (blockSucc_step RD Λ₀ i h₁ γ))
          (derivedFOfEq Λ hQ i (blockSucc_step RD Λ₀ i h₂ _))) ∈
      blackPairCompat Λ hQ RD Λ₀ i i h₁ h₂ γ := fun M =>
    gen_comp_comp (gen₂_blackRouqCross Λ hQ RD Λ₀ hsym i i h₁ h₂ h₁ h₂ M γ rfl rfl rfl rfl)
      (gen₂_blackRouqDot_whiskerRight Λ hQ RD Λ₀ i i h₁ h₂ M γ rfl rfl)
  have hS := Subalgebra.sub_mem _ m₁ m₂
  rw [Prod.mk_sub_mk, derivedIndCrossOfEq_slide_left] at hS
  exact (hS M).trans ((blackPairCompat Λ hQ RD Λ₀ i i h₁ h₂ γ).one_mem M).symm

/-- **The right dot slide on weight spaces** (Brundan, arXiv:1501.00350v1, (1.2) for equal
labels, the shape of `TwoRep.RouqLoc.slide_right`). -/
theorem blackRouqCross_slide_right_self (hsym : KLRSymm Q) (i : I) {w₀ w₁ w₂ : X}
    (h₁ : w₀ + RD.iX i = w₁) (h₂ : w₁ + RD.iX i = w₂) :
    blackRouqCross Λ hQ RD Λ₀ hsym i i h₁ h₂ h₁ h₂ ≫
        blackRouqE Λ hQ RD Λ₀ i h₁ ◁ blackRouqDot Λ hQ RD Λ₀ i h₂ -
      blackRouqDot Λ hQ RD Λ₀ i h₁ ▷ blackRouqE Λ hQ RD Λ₀ i h₂ ≫
        blackRouqCross Λ hQ RD Λ₀ hsym i i h₁ h₂ h₁ h₂ = 𝟙 _ := by
  apply ObjectProperty.hom_ext
  refine NatTrans.ext (funext fun M => ?_)
  refine gen₂_ext (blockSucc RD Λ₀ i h₁) (blockSucc RD Λ₀ i h₂) (derivedFBlock Λ hQ RD Λ₀ i h₁)
    (derivedFBlock Λ hQ RD Λ₀ i h₂) fun γ β δ hb hd => ?_
  subst hb hd
  have m₁ : (blackRouqCross Λ hQ RD Λ₀ hsym i i h₁ h₂ h₁ h₂ ≫
        blackRouqE Λ hQ RD Λ₀ i h₁ ◁ blackRouqDot Λ hQ RD Λ₀ i h₂,
      derivedIndCrossOfEq Λ hQ hsym i i (blockSucc_step RD Λ₀ i h₁ γ)
          (blockSucc_step RD Λ₀ i h₂ _) (blockSucc_step RD Λ₀ i h₁ γ)
          (blockSucc_step RD Λ₀ i h₂ _) ≫
        Functor.whiskerLeft (derivedFOfEq Λ hQ i (blockSucc_step RD Λ₀ i h₁ γ))
          (derivedIndDotOfEq Λ hQ i (blockSucc_step RD Λ₀ i h₂ _))) ∈
      blackPairCompat Λ hQ RD Λ₀ i i h₁ h₂ γ := fun M =>
    gen_comp_comp (gen₂_blackRouqCross Λ hQ RD Λ₀ hsym i i h₁ h₂ h₁ h₂ M γ rfl rfl rfl rfl)
      (gen₂_whiskerLeft_blackRouqDot Λ hQ RD Λ₀ i i h₁ h₂ M γ rfl rfl)
  have m₂ : (blackRouqDot Λ hQ RD Λ₀ i h₁ ▷ blackRouqE Λ hQ RD Λ₀ i h₂ ≫
        blackRouqCross Λ hQ RD Λ₀ hsym i i h₁ h₂ h₁ h₂,
      Functor.whiskerRight (derivedIndDotOfEq Λ hQ i (blockSucc_step RD Λ₀ i h₁ γ))
          (derivedFOfEq Λ hQ i (blockSucc_step RD Λ₀ i h₂ _)) ≫
        derivedIndCrossOfEq Λ hQ hsym i i (blockSucc_step RD Λ₀ i h₁ γ)
          (blockSucc_step RD Λ₀ i h₂ _) (blockSucc_step RD Λ₀ i h₁ γ)
          (blockSucc_step RD Λ₀ i h₂ _)) ∈ blackPairCompat Λ hQ RD Λ₀ i i h₁ h₂ γ := fun M =>
    gen_comp_comp (gen₂_blackRouqDot_whiskerRight Λ hQ RD Λ₀ i i h₁ h₂ M γ rfl rfl)
      (gen₂_blackRouqCross Λ hQ RD Λ₀ hsym i i h₁ h₂ h₁ h₂ M γ rfl rfl rfl rfl)
  have hS := Subalgebra.sub_mem _ m₁ m₂
  rw [Prod.mk_sub_mk, derivedIndCrossOfEq_slide_right] at hS
  exact (hS M).trans ((blackPairCompat Λ hQ RD Λ₀ i i h₁ h₂ γ).one_mem M).symm

end Weight

end Categorification.Stendhal
