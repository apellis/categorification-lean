/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackRouqMixedBraid

/-!
# The braid relation with distinct outer colours on derived categories of `T^λ`-modules

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §4.6 and §5.1;
Brundan, arXiv:1501.00350v1, Definition 1.1, (1.4) for outer labels `i ≠ c` (the field
`braid` of `TwoRep.RouqUpKLR`).

The braid relation on black inductions between arbitrary contents
(`indCrossOfEq_braid_three`) passes to the derived inductions
(`derivedIndCrossOfEq_braid_three`), through the identification of a composite of three derived
functors with the derived functor of the composite (`NatTrans.whiskerLeft_derivedComp_tripleIso`,
`NatTrans.whiskerRight_derivedComp_tripleIso`), and then to the weight spaces of
`blackRouqData` (`blackRouqCross_braid`), in the shape of `TwoRep.RouqUpKLR.braid`, by the
block generators `gen₃` as for `CyclotomicAction.globalCross_braid`.

Induction is exact for Rouquier polynomials over a field (Theorem 4.31), the hypothesis
`(C, hQ)`; otherwise the hypotheses are `KLRSymm Q` and `i ≠ c`. No route hypothesis is added.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CategoryTheory.NatTrans

open Limits

universe v₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇

variable {C₀ : Type*} [Category* C₀] [Abelian C₀] [HasDerivedCategory.{v₀} C₀]
  {C₁ : Type*} [Category* C₁] [Abelian C₁] [HasDerivedCategory.{v₁} C₁]
  {C₁' : Type*} [Category* C₁'] [Abelian C₁'] [HasDerivedCategory.{v₂} C₁']
  {C₁'' : Type*} [Category* C₁''] [Abelian C₁''] [HasDerivedCategory.{v₃} C₁'']
  {C₂ : Type*} [Category* C₂] [Abelian C₂] [HasDerivedCategory.{v₄} C₂]
  {C₂' : Type*} [Category* C₂'] [Abelian C₂'] [HasDerivedCategory.{v₅} C₂']
  {C₂'' : Type*} [Category* C₂''] [Abelian C₂''] [HasDerivedCategory.{v₆} C₂'']
  {C₃ : Type*} [Category* C₃] [Abelian C₃] [HasDerivedCategory.{v₇} C₃]
  {A₁ : C₀ ⥤ C₁} [A₁.Additive] [PreservesFiniteLimits A₁] [PreservesFiniteColimits A₁]
  {A₂ : C₁ ⥤ C₂} [A₂.Additive] [PreservesFiniteLimits A₂] [PreservesFiniteColimits A₂]
  {A₃ : C₂ ⥤ C₃} [A₃.Additive] [PreservesFiniteLimits A₃] [PreservesFiniteColimits A₃]
  {B₂ : C₁ ⥤ C₂'} [B₂.Additive] [PreservesFiniteLimits B₂] [PreservesFiniteColimits B₂]
  {B₃ : C₂' ⥤ C₃} [B₃.Additive] [PreservesFiniteLimits B₃] [PreservesFiniteColimits B₃]
  {D₁ : C₀ ⥤ C₁'} [D₁.Additive] [PreservesFiniteLimits D₁] [PreservesFiniteColimits D₁]
  {D₂ : C₁' ⥤ C₂'} [D₂.Additive] [PreservesFiniteLimits D₂] [PreservesFiniteColimits D₂]
  {E₂ : C₁' ⥤ C₂''} [E₂.Additive] [PreservesFiniteLimits E₂] [PreservesFiniteColimits E₂]
  {E₃ : C₂'' ⥤ C₃} [E₃.Additive] [PreservesFiniteLimits E₃] [PreservesFiniteColimits E₃]
  {G₁ : C₀ ⥤ C₁''} [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  {G₂ : C₁'' ⥤ C₂} [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
  {H₂ : C₁'' ⥤ C₂''} [H₂.Additive] [PreservesFiniteLimits H₂] [PreservesFiniteColimits H₂]

omit [Abelian C₁''] [HasDerivedCategory C₁''] [Abelian C₂''] [HasDerivedCategory C₂''] in
/-- `whiskerLeft_derivedComp_tripleIso` with different intermediate categories. -/
@[reassoc]
theorem whiskerLeft_derivedComp_tripleIso' (X : A₂ ⋙ A₃ ⟶ B₂ ⋙ B₃) :
    Functor.whiskerLeft A₁.mapDerivedCategory (derivedComp X) ≫
        (Functor.mapDerivedCategoryTripleIso A₁ B₂ B₃).hom =
      (Functor.mapDerivedCategoryTripleIso A₁ A₂ A₃).hom ≫
        (Functor.whiskerLeft A₁ X).mapDerivedCategory := by
  simp only [Functor.mapDerivedCategoryTripleIso, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    derivedComp, Functor.whiskerLeft_comp, Category.assoc]
  rw [← Functor.whiskerLeft_comp_assoc _ (Functor.mapDerivedCategoryCompIso B₂ B₃).inv,
    Iso.inv_hom_id, Functor.whiskerLeft_id', Category.id_comp,
    ← mapDerivedCategory_whiskerLeft]

omit [Abelian C₁''] [HasDerivedCategory C₁''] [Abelian C₂''] [HasDerivedCategory C₂''] in
/-- `whiskerRight_derivedComp_tripleIso` with different intermediate categories. -/
@[reassoc]
theorem whiskerRight_derivedComp_tripleIso' (X : A₁ ⋙ B₂ ⟶ D₁ ⋙ D₂) :
    Functor.whiskerRight (derivedComp X) B₃.mapDerivedCategory ≫
        (Functor.mapDerivedCategoryTripleIso D₁ D₂ B₃).hom =
      (Functor.mapDerivedCategoryTripleIso A₁ B₂ B₃).hom ≫
        (Functor.whiskerRight X B₃).mapDerivedCategory := by
  simp only [Functor.mapDerivedCategoryTripleIso_hom_eq, derivedComp, Functor.whiskerRight_comp,
    Category.assoc]
  rw [← Functor.whiskerRight_comp_assoc (Functor.mapDerivedCategoryCompIso D₁ D₂).inv,
    Iso.inv_hom_id, Functor.whiskerRight_id', Category.id_comp,
    ← mapDerivedCategory_whiskerRight]

/-- **A braid relation between six whiskered transformations of composites of three exact
functors passes to derived categories.** -/
theorem derivedComp_braid_three {X₁ : A₂ ⋙ A₃ ⟶ B₂ ⋙ B₃} {X₂ : A₁ ⋙ B₂ ⟶ D₁ ⋙ D₂}
    {X₃ : D₂ ⋙ B₃ ⟶ E₂ ⋙ E₃} {Y₁ : A₁ ⋙ A₂ ⟶ G₁ ⋙ G₂} {Y₂ : G₂ ⋙ A₃ ⟶ H₂ ⋙ E₃}
    {Y₃ : G₁ ⋙ H₂ ⟶ D₁ ⋙ E₂}
    (h : Functor.whiskerLeft A₁ X₁ ≫ Functor.whiskerRight X₂ B₃ ≫ Functor.whiskerLeft D₁ X₃ =
      Functor.whiskerRight Y₁ A₃ ≫ Functor.whiskerLeft G₁ Y₂ ≫ Functor.whiskerRight Y₃ E₃) :
    Functor.whiskerLeft A₁.mapDerivedCategory (derivedComp X₁) ≫
        ((Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (derivedComp X₂) B₃.mapDerivedCategory ≫
          (Functor.associator _ _ _).hom) ≫
        Functor.whiskerLeft D₁.mapDerivedCategory (derivedComp X₃) =
      ((Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (derivedComp Y₁) A₃.mapDerivedCategory ≫
          (Functor.associator _ _ _).hom) ≫
        Functor.whiskerLeft G₁.mapDerivedCategory (derivedComp Y₂) ≫
        ((Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (derivedComp Y₃) E₃.mapDerivedCategory ≫
          (Functor.associator _ _ _).hom) := by
  have key : Functor.whiskerLeft A₁.mapDerivedCategory (derivedComp X₁) ≫
      Functor.whiskerRight (derivedComp X₂) B₃.mapDerivedCategory ≫
        Functor.whiskerLeft D₁.mapDerivedCategory (derivedComp X₃) =
      Functor.whiskerRight (derivedComp Y₁) A₃.mapDerivedCategory ≫
        Functor.whiskerLeft G₁.mapDerivedCategory (derivedComp Y₂) ≫
          Functor.whiskerRight (derivedComp Y₃) E₃.mapDerivedCategory := by
    rw [← cancel_mono (Functor.mapDerivedCategoryTripleIso D₁ E₂ E₃).hom]
    simp only [Category.assoc, whiskerLeft_derivedComp_tripleIso',
      whiskerLeft_derivedComp_tripleIso'_assoc, whiskerRight_derivedComp_tripleIso',
      whiskerRight_derivedComp_tripleIso'_assoc]
    simp only [← mapDerivedCategory_comp]
    rw [h]
  ext X
  have hX := congrArg (fun η => NatTrans.app η X) key
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.associator_hom_app, Category.id_comp,
    Category.comp_id] using hX

end CategoryTheory.NatTrans

namespace Categorification.Stendhal

open CategoryTheory MulOpposite InductionAlong KLR TwoRep QuantumGroup CyclotomicAction
  Bicategory
open scoped Classical

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe w u u₁

variable {I : Type u} {k : Type u} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin ℓ → I →₀ ℕ) {C : CartanDatum I}
  (hQ : IsRouquierQ C Q)
  [∀ β : Multiset I,
    _root_.HasDerivedCategory.{w} (ModuleCat.{u} (TensorProductAlgebra k Q Λ β)ᵐᵒᵖ)]

/-- **The braid relation with distinct outer colours on derived black inductions** between
arbitrary contents, in the shape of `CyclotomicAction.signedCross_braid`. -/
theorem derivedIndCrossOfEq_braid_three (hsym : KLRSymm Q) (i j c : I) (hb : i ≠ c)
    {l w₁ w₂ w₃ w₄ w₅ w₆ m : Multiset I} (e1 : ({c} : Multiset I) + l = w₁)
    (e2 : ({j} : Multiset I) + w₁ = w₂) (e3 : ({i} : Multiset I) + w₂ = m)
    (e4 : ({i} : Multiset I) + w₁ = w₃) (e5 : ({j} : Multiset I) + w₃ = m)
    (e6 : ({i} : Multiset I) + l = w₄) (e7 : ({c} : Multiset I) + w₄ = w₃)
    (e8 : ({j} : Multiset I) + w₄ = w₅) (e9 : ({c} : Multiset I) + w₅ = m)
    (e10 : ({j} : Multiset I) + l = w₆) (e11 : ({c} : Multiset I) + w₆ = w₂)
    (e12 : ({i} : Multiset I) + w₆ = w₅) :
    Functor.whiskerLeft (derivedFOfEq Λ hQ c e1) (derivedIndCrossOfEq Λ hQ hsym i j e2 e3 e4 e5) ≫
        ((Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (derivedIndCrossOfEq Λ hQ hsym i c e1 e4 e6 e7)
            (derivedFOfEq Λ hQ j e5) ≫
          (Functor.associator _ _ _).hom) ≫
        Functor.whiskerLeft (derivedFOfEq Λ hQ i e6)
          (derivedIndCrossOfEq Λ hQ hsym j c e7 e5 e8 e9) =
      ((Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (derivedIndCrossOfEq Λ hQ hsym j c e1 e2 e10 e11)
            (derivedFOfEq Λ hQ i e3) ≫
          (Functor.associator _ _ _).hom) ≫
        Functor.whiskerLeft (derivedFOfEq Λ hQ j e10)
          (derivedIndCrossOfEq Λ hQ hsym i c e11 e3 e12 e9) ≫
        ((Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (derivedIndCrossOfEq Λ hQ hsym i j e10 e12 e6 e8)
            (derivedFOfEq Λ hQ c e9) ≫
          (Functor.associator _ _ _).hom) := by
  have hL : ∀ (x : I) {μ β : Multiset I} (h : ({x} : Multiset I) + μ = β),
      Limits.PreservesFiniteLimits (blackFOfEq Q Λ x h) := fun x _ _ h =>
    blackFOfEq_preservesFiniteLimits Λ hQ x h
  have hC : ∀ (x : I) {μ β : Multiset I} (h : ({x} : Multiset I) + μ = β),
      Limits.PreservesFiniteColimits (blackFOfEq Q Λ x h) := fun x _ _ h =>
    blackFOfEq_preservesFiniteColimits Λ hQ x h
  unfold derivedIndCrossOfEq derivedFOfEq
  exact NatTrans.derivedComp_braid_three
    (indCrossOfEq_braid_three Λ hsym i j c hb e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12)

/-! ### Weight spaces -/

variable {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y] (RD : UDot.WeightDatum C X Y)
  (Λ₀ : X)

/-- **The braid relation with distinct outer colours on weight spaces** (Brundan,
arXiv:1501.00350v1, (1.4) with `i ≠ c`): the field `braid` of `TwoRep.RouqUpKLR` for the
Rouquier generators `blackRouqData` on derived categories of `T^λ`-modules. -/
theorem blackRouqCross_braid (hsym : KLRSymm Q) (i j c : I) (hb : i ≠ c)
    {l w₁ w₂ w₃ w₄ w₅ w₆ m : X} (e1 : l + RD.iX c = w₁) (e2 : w₁ + RD.iX j = w₂)
    (e3 : w₂ + RD.iX i = m) (e4 : w₁ + RD.iX i = w₃) (e5 : w₃ + RD.iX j = m)
    (e6 : l + RD.iX i = w₄) (e7 : w₄ + RD.iX c = w₃) (e8 : w₄ + RD.iX j = w₅)
    (e9 : w₅ + RD.iX c = m) (e10 : l + RD.iX j = w₆) (e11 : w₆ + RD.iX c = w₂)
    (e12 : w₆ + RD.iX i = w₅) :
    (blackRouqE Λ hQ RD Λ₀ c e1) ◁ blackRouqCross Λ hQ RD Λ₀ hsym i j e2 e3 e4 e5 ≫
        ((α_ (blackRouqE Λ hQ RD Λ₀ c e1) (blackRouqE Λ hQ RD Λ₀ i e4) (blackRouqE Λ hQ RD Λ₀ j
            e5)).inv ≫ blackRouqCross Λ hQ RD Λ₀ hsym i c e1 e4 e6 e7 ▷ (blackRouqE Λ hQ RD Λ₀ j
                e5) ≫ (α_ (blackRouqE Λ hQ RD Λ₀ i e6) (blackRouqE Λ hQ RD Λ₀ c e7) (blackRouqE Λ
                    hQ RD Λ₀ j e5)).hom) ≫
        (blackRouqE Λ hQ RD Λ₀ i e6) ◁ blackRouqCross Λ hQ RD Λ₀ hsym j c e7 e5 e8 e9 =
      ((α_ (blackRouqE Λ hQ RD Λ₀ c e1) (blackRouqE Λ hQ RD Λ₀ j e2) (blackRouqE Λ hQ RD Λ₀ i
          e3)).inv ≫ blackRouqCross Λ hQ RD Λ₀ hsym j c e1 e2 e10 e11 ▷ (blackRouqE Λ hQ RD Λ₀ i
              e3) ≫ (α_ (blackRouqE Λ hQ RD Λ₀ j e10) (blackRouqE Λ hQ RD Λ₀ c e11) (blackRouqE Λ
                  hQ RD Λ₀ i e3)).hom) ≫
        (blackRouqE Λ hQ RD Λ₀ j e10) ◁ blackRouqCross Λ hQ RD Λ₀ hsym i c e11 e3 e12 e9 ≫
        ((α_ (blackRouqE Λ hQ RD Λ₀ j e10) (blackRouqE Λ hQ RD Λ₀ i e12) (blackRouqE Λ hQ RD Λ₀ c
            e9)).inv ≫ blackRouqCross Λ hQ RD Λ₀ hsym i j e10 e12 e6 e8 ▷ (blackRouqE Λ hQ RD Λ₀ c
                e9) ≫ (α_ (blackRouqE Λ hQ RD Λ₀ i e6) (blackRouqE Λ hQ RD Λ₀ j e8) (blackRouqE Λ
                    hQ RD Λ₀ c e9)).hom) := by
  apply ObjectProperty.hom_ext
  refine NatTrans.ext (funext fun M => ?_)
  refine gen₃_ext (blockSucc RD Λ₀ c e1) (blockSucc RD Λ₀ j e2) (blockSucc RD Λ₀ i e3)
    (derivedFBlock Λ hQ RD Λ₀ c e1) (derivedFBlock Λ hQ RD Λ₀ j e2)
    (derivedFBlock Λ hQ RD Λ₀ i e3) fun γ β δ μ hβ hδ hμ => ?_
  subst hβ hδ hμ
  have k1 : blockSucc RD Λ₀ j e5 (blockSucc RD Λ₀ i e4 (blockSucc RD Λ₀ c e1 γ)) =
      blockSucc RD Λ₀ i e3 (blockSucc RD Λ₀ j e2 (blockSucc RD Λ₀ c e1 γ)) :=
    Subtype.ext (by simp only [blockSucc_val]; abel)
  have k2 : blockSucc RD Λ₀ c e7 (blockSucc RD Λ₀ i e6 γ) =
      blockSucc RD Λ₀ i e4 (blockSucc RD Λ₀ c e1 γ) :=
    Subtype.ext (by simp only [blockSucc_val]; abel)
  have k3 : blockSucc RD Λ₀ c e9 (blockSucc RD Λ₀ j e8 (blockSucc RD Λ₀ i e6 γ)) =
      blockSucc RD Λ₀ i e3 (blockSucc RD Λ₀ j e2 (blockSucc RD Λ₀ c e1 γ)) :=
    Subtype.ext (by simp only [blockSucc_val]; abel)
  have r1 : blockSucc RD Λ₀ c e11 (blockSucc RD Λ₀ j e10 γ) =
      blockSucc RD Λ₀ j e2 (blockSucc RD Λ₀ c e1 γ) :=
    Subtype.ext (by simp only [blockSucc_val]; abel)
  have r2 : blockSucc RD Λ₀ i e12 (blockSucc RD Λ₀ j e10 γ) =
      blockSucc RD Λ₀ j e8 (blockSucc RD Λ₀ i e6 γ) :=
    Subtype.ext (by simp only [blockSucc_val]; abel)
  have s1 := gen₃_whiskerLeft (blockSucc RD Λ₀ c e1) (blockSucc RD Λ₀ j e2)
      (blockSucc RD Λ₀ i e3) (derivedFBlock Λ hQ RD Λ₀ c e1) (derivedFBlock Λ hQ RD Λ₀ j e2)
      (derivedFBlock Λ hQ RD Λ₀ i e3)
      (s₂' := blockSucc RD Λ₀ i e4) (s₃' := blockSucc RD Λ₀ j e5)
      (L₂' := derivedFBlock Λ hQ RD Λ₀ i e4) (L₃' := derivedFBlock Λ hQ RD Λ₀ j e5)
      (blackRouqCross Λ hQ RD Λ₀ hsym i j e2 e3 e4 e5).hom M γ rfl rfl rfl rfl k1 _
      (gen₂_blackRouqCross Λ hQ RD Λ₀ hsym i j e2 e3 e4 e5 _ _ rfl rfl rfl k1)
  have s3 := gen₃_whiskerRight (blockSucc RD Λ₀ c e1) (blockSucc RD Λ₀ i e4)
      (blockSucc RD Λ₀ j e5) (derivedFBlock Λ hQ RD Λ₀ c e1) (derivedFBlock Λ hQ RD Λ₀ i e4)
      (derivedFBlock Λ hQ RD Λ₀ j e5)
      (s₁' := blockSucc RD Λ₀ i e6) (s₂' := blockSucc RD Λ₀ c e7)
      (L₁' := derivedFBlock Λ hQ RD Λ₀ i e6) (L₂' := derivedFBlock Λ hQ RD Λ₀ c e7)
      (blackRouqCross Λ hQ RD Λ₀ hsym i c e1 e4 e6 e7).hom M γ rfl rfl rfl k2 k1 _
      (gen₂_blackRouqCross Λ hQ RD Λ₀ hsym i c e1 e4 e6 e7 M γ rfl rfl rfl k2)
  have s5 := gen₃_whiskerLeft (blockSucc RD Λ₀ i e6) (blockSucc RD Λ₀ c e7)
      (blockSucc RD Λ₀ j e5) (derivedFBlock Λ hQ RD Λ₀ i e6) (derivedFBlock Λ hQ RD Λ₀ c e7)
      (derivedFBlock Λ hQ RD Λ₀ j e5)
      (s₂' := blockSucc RD Λ₀ j e8) (s₃' := blockSucc RD Λ₀ c e9)
      (L₂' := derivedFBlock Λ hQ RD Λ₀ j e8) (L₃' := derivedFBlock Λ hQ RD Λ₀ c e9)
      (blackRouqCross Λ hQ RD Λ₀ hsym j c e7 e5 e8 e9).hom M γ rfl k2 k1 rfl k3 _
      (gen₂_blackRouqCross Λ hQ RD Λ₀ hsym j c e7 e5 e8 e9 _ _ k2 k1 rfl k3)
  have t2 := gen₃_whiskerRight (blockSucc RD Λ₀ c e1) (blockSucc RD Λ₀ j e2)
      (blockSucc RD Λ₀ i e3) (derivedFBlock Λ hQ RD Λ₀ c e1) (derivedFBlock Λ hQ RD Λ₀ j e2)
      (derivedFBlock Λ hQ RD Λ₀ i e3)
      (s₁' := blockSucc RD Λ₀ j e10) (s₂' := blockSucc RD Λ₀ c e11)
      (L₁' := derivedFBlock Λ hQ RD Λ₀ j e10) (L₂' := derivedFBlock Λ hQ RD Λ₀ c e11)
      (blackRouqCross Λ hQ RD Λ₀ hsym j c e1 e2 e10 e11).hom M γ rfl rfl rfl r1 rfl _
      (gen₂_blackRouqCross Λ hQ RD Λ₀ hsym j c e1 e2 e10 e11 M γ rfl rfl rfl r1)
  have t4 := gen₃_whiskerLeft (blockSucc RD Λ₀ j e10) (blockSucc RD Λ₀ c e11)
      (blockSucc RD Λ₀ i e3) (derivedFBlock Λ hQ RD Λ₀ j e10) (derivedFBlock Λ hQ RD Λ₀ c e11)
      (derivedFBlock Λ hQ RD Λ₀ i e3)
      (s₂' := blockSucc RD Λ₀ i e12) (s₃' := blockSucc RD Λ₀ c e9)
      (L₂' := derivedFBlock Λ hQ RD Λ₀ i e12) (L₃' := derivedFBlock Λ hQ RD Λ₀ c e9)
      (blackRouqCross Λ hQ RD Λ₀ hsym i c e11 e3 e12 e9).hom M γ rfl r1 rfl r2 k3 _
      (gen₂_blackRouqCross Λ hQ RD Λ₀ hsym i c e11 e3 e12 e9 _ _ r1 rfl r2 k3)
  have t6 := gen₃_whiskerRight (blockSucc RD Λ₀ j e10) (blockSucc RD Λ₀ i e12)
      (blockSucc RD Λ₀ c e9) (derivedFBlock Λ hQ RD Λ₀ j e10) (derivedFBlock Λ hQ RD Λ₀ i e12)
      (derivedFBlock Λ hQ RD Λ₀ c e9)
      (s₁' := blockSucc RD Λ₀ i e6) (s₂' := blockSucc RD Λ₀ j e8)
      (L₁' := derivedFBlock Λ hQ RD Λ₀ i e6) (L₂' := derivedFBlock Λ hQ RD Λ₀ j e8)
      (blackRouqCross Λ hQ RD Λ₀ hsym i j e10 e12 e6 e8).hom M γ rfl r2 rfl rfl k3 _
      (gen₂_blackRouqCross Λ hQ RD Λ₀ hsym i j e10 e12 e6 e8 M γ rfl r2 rfl rfl)
  refine (gen_chain_left s1 (gen_assoc _) s3 (gen_assoc _) s5).trans
    (Eq.trans ?_ (gen_chain_right (gen_assoc _) t2 (gen_assoc _) t4 (gen_assoc _) t6
      (gen_assoc _)).symm)
  exact congrArg (· ≫ _) (congrArg (fun η => NatTrans.app η (M γ))
    (derivedIndCrossOfEq_braid_three Λ hQ hsym i j c hb _ _ _ _ _ _ _ _ _ _ _ _))

end Categorification.Stendhal
