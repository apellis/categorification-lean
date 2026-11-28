/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackRouqSlides

/-!
# The weight-indexed Rouquier generators on categories of `T^λ`-modules

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §4.6 and
Theorem 4.31 (the action on `T^λ`-modules); Rouquier's generators (Brundan,
arXiv:1501.00350v1, Definition 1.1; `TwoRep.RouqData`).

This is the abelian counterpart of `blackRouqData`, without passing to derived categories. For a
weight `Λ₀ ∈ X`, the weight space at `x` (`blackModWeightSpace`) is the product of the
categories of all right modules over the blocks `T^λ_β` of weight `x`
(`blockWeight RD Λ₀ β = x`).

* `blackModE i h`, for `h : x + i_X = y`, is induction `blackFOfEq` assembled over
  blocks (`blockSum`), with right adjoint restriction `blackEOfEq` (`blackModF`,
  `blackModAdj`).
* `blackModDot` and `blackModCross` are the dot `indDotOfEq` and the crossing
  `indCrossOfEq` on each block (the same-colour crossing acts as `-ψ`, the convention of
  Khovanov–Lauda III); `blackModuleRouqData` packages them as a `TwoRep.RouqData`.

The nil-Hecke relations (`blackModCross_sq`, `blackModCross_sameBraid`) and the dot
slides for equal colours (`blackModCross_slide_left_self`,
`blackModCross_slide_right_self`) hold on weight spaces, from the module relations
`indCrossOfEq_sq`, `indCrossOfEq_braid`, `indCrossOfEq_slide_left` and
`indCrossOfEq_slide_right`. No exactness hypothesis is needed here.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory MulOpposite InductionAlong KLR TwoRep QuantumGroup
  CyclotomicAction Bicategory

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe u u₁

variable {I : Type u} [DecidableEq I] {k : Type u} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) {C : CartanDatum I}

set_option hygiene false in
local notation "D" β => ModuleCat.{u} (TensorProductAlgebra k Q Λ β)ᵐᵒᵖ

/-- **The braid relation on `Fᵢ³`** between arbitrary contents (`indCrossOfEq_braid`), with the
associators of functor composition. -/
theorem indCrossOfEq_braid_assoc {Q : I → I → MvPolynomial (Fin 2) k} (hsym : KLRSymm Q) (i : I)
    {μ β γ δ : Multiset I}
    (h₁ : ({i} : Multiset I) + μ = β) (h₂ : ({i} : Multiset I) + β = γ)
    (h₃ : ({i} : Multiset I) + γ = δ) :
    Functor.whiskerLeft (blackFOfEq Q Λ i h₁) (indCrossOfEq Λ hsym i i h₂ h₃ h₂ h₃) ≫
        ((Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (indCrossOfEq Λ hsym i i h₁ h₂ h₁ h₂) (blackFOfEq Q Λ i h₃) ≫
          (Functor.associator _ _ _).hom) ≫
        Functor.whiskerLeft (blackFOfEq Q Λ i h₁) (indCrossOfEq Λ hsym i i h₂ h₃ h₂ h₃) =
      ((Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (indCrossOfEq Λ hsym i i h₁ h₂ h₁ h₂) (blackFOfEq Q Λ i h₃) ≫
          (Functor.associator _ _ _).hom) ≫
        Functor.whiskerLeft (blackFOfEq Q Λ i h₁) (indCrossOfEq Λ hsym i i h₂ h₃ h₂ h₃) ≫
        ((Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (indCrossOfEq Λ hsym i i h₁ h₂ h₁ h₂) (blackFOfEq Q Λ i h₃) ≫
          (Functor.associator _ _ _).hom) := by
  refine NatTrans.ext (funext fun X => ?_)
  have hX := congrArg (fun η => NatTrans.app η X) (indCrossOfEq_braid Λ hsym i h₁ h₂ h₃)
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.associator_hom_app, Category.id_comp,
    Category.comp_id] using hX

/-! ### Weight spaces -/

variable {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y] (RD : UDot.WeightDatum C X Y)
  (Λ₀ : X)

/-- **The weight space at `x`**: the product of the categories of right `T^λ_β`-modules over the
contents `β` of weight `x` (`blockWeight RD Λ₀ β = x`). -/
abbrev blackModWeightSpace (x : X) : LinearCat k :=
  LinearCat.of k (∀ β : WeightBlocks RD Λ₀ x, D β.1)

/-- The blocks of `blackModE`. -/
abbrev moduleFBlock (i : I) {x y : X} (h : x + RD.iX i = y) (β : WeightBlocks RD Λ₀ x)
    (δ : WeightBlocks RD Λ₀ y) (hβ : blockSucc RD Λ₀ i h β = δ) : (D β.1) ⥤ (D δ.1) :=
  blackFOfEq Q Λ i (blockSucc_eq RD Λ₀ i hβ)

/-- The blocks of `blackModF`. -/
abbrev moduleEBlock (i : I) {x y : X} (h : x + RD.iX i = y) (β : WeightBlocks RD Λ₀ x)
    (δ : WeightBlocks RD Λ₀ y) (hβ : blockSucc RD Λ₀ i h β = δ) : (D δ.1) ⥤ (D β.1) :=
  blackEOfEq Q Λ i (blockSucc_eq RD Λ₀ i hβ)

/-- **`Fᵢ` on weight spaces**, `x ⟶ x + i_X`: induction assembled over blocks. -/
def blackModE (i : I) {x y : X} (h : x + RD.iX i = y) :
    blackModWeightSpace Q Λ RD Λ₀ x ⟶ blackModWeightSpace Q Λ RD Λ₀ y :=
  LinearCat.LinFun.of (TwoRep.blockSum (blockSucc RD Λ₀ i h) (moduleFBlock Q Λ RD Λ₀ i h))

/-- **`Eᵢ` on weight spaces**, `x + i_X ⟶ x`: restriction blockwise. -/
def blackModF (i : I) {x y : X} (h : x + RD.iX i = y) :
    blackModWeightSpace Q Λ RD Λ₀ y ⟶ blackModWeightSpace Q Λ RD Λ₀ x :=
  LinearCat.LinFun.of (TwoRep.blockRes (blockSucc RD Λ₀ i h) (moduleEBlock Q Λ RD Λ₀ i h))

/-- **The induction–restriction adjunction on weight spaces.** -/
def blackModAdj (i : I) {x y : X} (h : x + RD.iX i = y) :
    Bicategory.Adjunction (blackModE Q Λ RD Λ₀ i h) (blackModF Q Λ RD Λ₀ i h) :=
  LinearCat.ofAdjunction k (TwoRep.blockAdjunction (blockSucc RD Λ₀ i h)
    fun _ _ hβ => blackAdjOfEq Q Λ i (blockSucc_eq RD Λ₀ i hβ))

/-- **The dot on weight spaces**: the dot of `Fᵢ` on each block. -/
def blackModDot (i : I) {x y : X} (h : x + RD.iX i = y) :
    blackModE Q Λ RD Λ₀ i h ⟶ blackModE Q Λ RD Λ₀ i h :=
  ObjectProperty.homMk (TwoRep.blockSumMap (blockSucc RD Λ₀ i h)
    fun _ _ hβ => indDotOfEq Q Λ i (blockSucc_eq RD Λ₀ i hβ))

/-- **The crossing on weight spaces** `Fⱼ Fᵢ ⟶ Fᵢ Fⱼ`: the crossing on each block. -/
def blackModCross (hsym : KLRSymm Q) (i j : I) {x y z t : X} (h₁ : x + RD.iX j = y)
    (h₂ : y + RD.iX i = t) (h₃ : x + RD.iX i = z) (h₄ : z + RD.iX j = t) :
    blackModE Q Λ RD Λ₀ j h₁ ≫ blackModE Q Λ RD Λ₀ i h₂ ⟶
      blackModE Q Λ RD Λ₀ i h₃ ≫ blackModE Q Λ RD Λ₀ j h₄ :=
  ObjectProperty.homMk (TwoRep.blockCross (blockSucc RD Λ₀ j h₁) (blockSucc RD Λ₀ i h₂)
    (moduleFBlock Q Λ RD Λ₀ j h₁) (moduleFBlock Q Λ RD Λ₀ i h₂) (blockSucc RD Λ₀ i h₃)
    (blockSucc RD Λ₀ j h₄) (moduleFBlock Q Λ RD Λ₀ i h₃) (moduleFBlock Q Λ RD Λ₀ j h₄)
    (blockSucc_comm RD Λ₀ i j h₁ h₂ h₃ h₄) fun _ _ _ _ hb hd hb' hd' =>
      indCrossOfEq Λ hsym i j (blockSucc_eq RD Λ₀ j hb) (blockSucc_eq RD Λ₀ i hd)
        (blockSucc_eq RD Λ₀ i hb') (blockSucc_eq RD Λ₀ j hd'))

/-- `blackModCross` on the generators of `Fⱼ ≫ Fᵢ`, for any intermediate blocks. -/
theorem gen₂_blackModCross (hsym : KLRSymm Q) (i j : I) {x y z t : X} (h₁ : x + RD.iX j = y)
    (h₂ : y + RD.iX i = t) (h₃ : x + RD.iX i = z) (h₄ : z + RD.iX j = t)
    (M : ∀ γ : WeightBlocks RD Λ₀ x, D γ.1) (γ : WeightBlocks RD Λ₀ x)
    {β : WeightBlocks RD Λ₀ y} {β' : WeightBlocks RD Λ₀ z} {δ : WeightBlocks RD Λ₀ t}
    (hb : blockSucc RD Λ₀ j h₁ γ = β) (hd : blockSucc RD Λ₀ i h₂ β = δ)
    (hb' : blockSucc RD Λ₀ i h₃ γ = β') (hd' : blockSucc RD Λ₀ j h₄ β' = δ) :
    gen₂ (blockSucc RD Λ₀ j h₁) (blockSucc RD Λ₀ i h₂) (moduleFBlock Q Λ RD Λ₀ j h₁)
        (moduleFBlock Q Λ RD Λ₀ i h₂) M γ hb hd ≫
        (blackModCross Q Λ RD Λ₀ hsym i j h₁ h₂ h₃ h₄).hom.app M δ =
      (indCrossOfEq Λ hsym i j (blockSucc_eq RD Λ₀ j hb) (blockSucc_eq RD Λ₀ i hd)
          (blockSucc_eq RD Λ₀ i hb') (blockSucc_eq RD Λ₀ j hd')).app (M γ) ≫
        gen₂ (blockSucc RD Λ₀ i h₃) (blockSucc RD Λ₀ j h₄) (moduleFBlock Q Λ RD Λ₀ i h₃)
          (moduleFBlock Q Λ RD Λ₀ j h₄) M γ hb' hd' :=
  gen₂_blockCross _ _ _ _ _ _ _ _ _ _ M γ hb hd hb' hd'

/-- **The nil-Hecke quadratic relation on weight spaces** (the shape of
`TwoRep.RouqFamily.square`). -/
theorem blackModCross_sq (hsym : KLRSymm Q) (i : I) {x y t : X} (h₁ : x + RD.iX i = y)
    (h₂ : y + RD.iX i = t) :
    blackModCross Q Λ RD Λ₀ hsym i i h₁ h₂ h₁ h₂ ≫
      blackModCross Q Λ RD Λ₀ hsym i i h₁ h₂ h₁ h₂ = 0 := by
  apply ObjectProperty.hom_ext
  refine NatTrans.ext (funext fun M => ?_)
  refine gen₂_ext (blockSucc RD Λ₀ i h₁) (blockSucc RD Λ₀ i h₂) (moduleFBlock Q Λ RD Λ₀ i h₁)
    (moduleFBlock Q Λ RD Λ₀ i h₂) fun γ β δ hb hd => ?_
  refine (gen_comp_comp (gen₂_blackModCross Q Λ RD Λ₀ hsym i i h₁ h₂ h₁ h₂ M γ hb hd hb hd)
    (gen₂_blackModCross Q Λ RD Λ₀ hsym i i h₁ h₂ h₁ h₂ M γ hb hd hb hd)).trans ?_
  rw [← NatTrans.comp_app, indCrossOfEq_sq, NatTrans.app_zero]
  exact Limits.zero_comp.trans Limits.comp_zero.symm

/-- **The braid relation for three strands of the same colour on weight spaces** (the shape of
`TwoRep.RouqFamily.braid`). -/
theorem blackModCross_sameBraid (hsym : KLRSymm Q) (i : I) {w₀ w₁ w₂ w₃ : X}
    (h₁ : w₀ + RD.iX i = w₁) (h₂ : w₁ + RD.iX i = w₂) (h₃ : w₂ + RD.iX i = w₃) :
    blackModE Q Λ RD Λ₀ i h₁ ◁ blackModCross Q Λ RD Λ₀ hsym i i h₂ h₃ h₂ h₃ ≫
      ((α_ (blackModE Q Λ RD Λ₀ i h₁) (blackModE Q Λ RD Λ₀ i h₂)
          (blackModE Q Λ RD Λ₀ i h₃)).inv ≫
        blackModCross Q Λ RD Λ₀ hsym i i h₁ h₂ h₁ h₂ ▷ blackModE Q Λ RD Λ₀ i h₃ ≫
        (α_ (blackModE Q Λ RD Λ₀ i h₁) (blackModE Q Λ RD Λ₀ i h₂)
          (blackModE Q Λ RD Λ₀ i h₃)).hom) ≫
      blackModE Q Λ RD Λ₀ i h₁ ◁ blackModCross Q Λ RD Λ₀ hsym i i h₂ h₃ h₂ h₃ =
    ((α_ (blackModE Q Λ RD Λ₀ i h₁) (blackModE Q Λ RD Λ₀ i h₂)
          (blackModE Q Λ RD Λ₀ i h₃)).inv ≫
      blackModCross Q Λ RD Λ₀ hsym i i h₁ h₂ h₁ h₂ ▷ blackModE Q Λ RD Λ₀ i h₃ ≫
      (α_ (blackModE Q Λ RD Λ₀ i h₁) (blackModE Q Λ RD Λ₀ i h₂)
          (blackModE Q Λ RD Λ₀ i h₃)).hom) ≫
      blackModE Q Λ RD Λ₀ i h₁ ◁ blackModCross Q Λ RD Λ₀ hsym i i h₂ h₃ h₂ h₃ ≫
    ((α_ (blackModE Q Λ RD Λ₀ i h₁) (blackModE Q Λ RD Λ₀ i h₂)
          (blackModE Q Λ RD Λ₀ i h₃)).inv ≫
      blackModCross Q Λ RD Λ₀ hsym i i h₁ h₂ h₁ h₂ ▷ blackModE Q Λ RD Λ₀ i h₃ ≫
      (α_ (blackModE Q Λ RD Λ₀ i h₁) (blackModE Q Λ RD Λ₀ i h₂)
          (blackModE Q Λ RD Λ₀ i h₃)).hom) := by
  apply ObjectProperty.hom_ext
  refine NatTrans.ext (funext fun M => ?_)
  refine gen₃_ext (blockSucc RD Λ₀ i h₁) (blockSucc RD Λ₀ i h₂) (blockSucc RD Λ₀ i h₃)
    (moduleFBlock Q Λ RD Λ₀ i h₁) (moduleFBlock Q Λ RD Λ₀ i h₂)
    (moduleFBlock Q Λ RD Λ₀ i h₃) fun γ β δ μ hβ hδ hμ => ?_
  subst hβ hδ hμ
  have s1 := gen₃_whiskerLeft (blockSucc RD Λ₀ i h₁) (blockSucc RD Λ₀ i h₂)
      (blockSucc RD Λ₀ i h₃) (moduleFBlock Q Λ RD Λ₀ i h₁) (moduleFBlock Q Λ RD Λ₀ i h₂)
      (moduleFBlock Q Λ RD Λ₀ i h₃)
      (s₂' := blockSucc RD Λ₀ i h₂) (s₃' := blockSucc RD Λ₀ i h₃)
      (L₂' := moduleFBlock Q Λ RD Λ₀ i h₂) (L₃' := moduleFBlock Q Λ RD Λ₀ i h₃)
      (blackModCross Q Λ RD Λ₀ hsym i i h₂ h₃ h₂ h₃).hom M γ rfl rfl rfl rfl rfl _
      (gen₂_blackModCross Q Λ RD Λ₀ hsym i i h₂ h₃ h₂ h₃ _ _ rfl rfl rfl rfl)
  have s2 := gen₃_whiskerRight (blockSucc RD Λ₀ i h₁) (blockSucc RD Λ₀ i h₂)
      (blockSucc RD Λ₀ i h₃) (moduleFBlock Q Λ RD Λ₀ i h₁) (moduleFBlock Q Λ RD Λ₀ i h₂)
      (moduleFBlock Q Λ RD Λ₀ i h₃)
      (s₁' := blockSucc RD Λ₀ i h₁) (s₂' := blockSucc RD Λ₀ i h₂)
      (L₁' := moduleFBlock Q Λ RD Λ₀ i h₁) (L₂' := moduleFBlock Q Λ RD Λ₀ i h₂)
      (blackModCross Q Λ RD Λ₀ hsym i i h₁ h₂ h₁ h₂).hom M γ rfl rfl rfl rfl rfl _
      (gen₂_blackModCross Q Λ RD Λ₀ hsym i i h₁ h₂ h₁ h₂ M γ rfl rfl rfl rfl)
  refine (gen_chain_left s1 (gen_assoc _) s2 (gen_assoc _) s1).trans
    (Eq.trans ?_ (gen_chain_right (gen_assoc _) s2 (gen_assoc _) s1 (gen_assoc _) s2
      (gen_assoc _)).symm)
  exact congrArg (· ≫ _) (congrArg (fun η => NatTrans.app η (M γ))
    (indCrossOfEq_braid_assoc Λ hsym i _ _ _))

/-- **The Rouquier generators on categories of `T^λ`-modules** (`TwoRep.RouqData`):
weight spaces, `Fᵢ`, dots and crossings. -/
def blackModuleRouqData (hsym : KLRSymm Q) : RouqData (B := LinearCat k) RD where
  obj := blackModWeightSpace Q Λ RD Λ₀
  E i _ _ h := blackModE Q Λ RD Λ₀ i h
  dot i _ _ h := blackModDot Q Λ RD Λ₀ i h
  cross i j _ _ _ _ h₁ h₂ h₃ h₄ := blackModCross Q Λ RD Λ₀ hsym i j h₁ h₂ h₃ h₄

/-! ### Dot slides for equal colours -/

/-- `blackModE j ◁ blackModDot i` on generators. -/
theorem gen₂_whiskerLeft_blackModDot (i j : I) {x y t : X} (h₁ : x + RD.iX j = y)
    (h₂ : y + RD.iX i = t)
    (M : ∀ γ : WeightBlocks RD Λ₀ x,
      ModuleCat.{u} (TensorProductAlgebra k Q Λ γ.1)ᵐᵒᵖ)
    (γ : WeightBlocks RD Λ₀ x) {β : WeightBlocks RD Λ₀ y} {δ : WeightBlocks RD Λ₀ t}
    (hb : blockSucc RD Λ₀ j h₁ γ = β) (hd : blockSucc RD Λ₀ i h₂ β = δ) :
    gen₂ (blockSucc RD Λ₀ j h₁) (blockSucc RD Λ₀ i h₂) (moduleFBlock Q Λ RD Λ₀ j h₁)
        (moduleFBlock Q Λ RD Λ₀ i h₂) M γ hb hd ≫
        (blackModE Q Λ RD Λ₀ j h₁ ◁ blackModDot Q Λ RD Λ₀ i h₂).hom.app M δ =
      (Functor.whiskerLeft (blackFOfEq Q Λ j (blockSucc_eq RD Λ₀ j hb))
          (indDotOfEq Q Λ i (blockSucc_eq RD Λ₀ i hd))).app (M γ) ≫
        gen₂ (blockSucc RD Λ₀ j h₁) (blockSucc RD Λ₀ i h₂) (moduleFBlock Q Λ RD Λ₀ j h₁)
          (moduleFBlock Q Λ RD Λ₀ i h₂) M γ hb hd :=
  gen₂_whiskerLeft (blockSucc RD Λ₀ j h₁) (blockSucc RD Λ₀ i h₂) (moduleFBlock Q Λ RD Λ₀ j h₁)
    (fun _ _ hβ => indDotOfEq Q Λ i (blockSucc_eq RD Λ₀ i hβ)) M γ hb hd

/-- `blackModDot j ▷ blackModE i` on generators. -/
theorem gen₂_blackModDot_whiskerRight (i j : I) {x y t : X} (h₁ : x + RD.iX j = y)
    (h₂ : y + RD.iX i = t)
    (M : ∀ γ : WeightBlocks RD Λ₀ x,
      ModuleCat.{u} (TensorProductAlgebra k Q Λ γ.1)ᵐᵒᵖ)
    (γ : WeightBlocks RD Λ₀ x) {β : WeightBlocks RD Λ₀ y} {δ : WeightBlocks RD Λ₀ t}
    (hb : blockSucc RD Λ₀ j h₁ γ = β) (hd : blockSucc RD Λ₀ i h₂ β = δ) :
    gen₂ (blockSucc RD Λ₀ j h₁) (blockSucc RD Λ₀ i h₂) (moduleFBlock Q Λ RD Λ₀ j h₁)
        (moduleFBlock Q Λ RD Λ₀ i h₂) M γ hb hd ≫
        (blackModDot Q Λ RD Λ₀ j h₁ ▷ blackModE Q Λ RD Λ₀ i h₂).hom.app M δ =
      (Functor.whiskerRight (indDotOfEq Q Λ j (blockSucc_eq RD Λ₀ j hb))
          (blackFOfEq Q Λ i (blockSucc_eq RD Λ₀ i hd))).app (M γ) ≫
        gen₂ (blockSucc RD Λ₀ j h₁) (blockSucc RD Λ₀ i h₂) (moduleFBlock Q Λ RD Λ₀ j h₁)
          (moduleFBlock Q Λ RD Λ₀ i h₂) M γ hb hd :=
  gen₂_whiskerRight (blockSucc RD Λ₀ j h₁) (blockSucc RD Λ₀ i h₂) (moduleFBlock Q Λ RD Λ₀ i h₂)
    (fun _ _ hβ => indDotOfEq Q Λ j (blockSucc_eq RD Λ₀ j hβ)) M γ hb hd

/-- **Endomorphisms of `Fⱼ Fᵢ` on weight spaces compatible with the generators at a block `γ`**:
pairs of an endomorphism of the composite on weight spaces and of the composite of
black inductions starting at `γ`, intertwined by the generators `gen₂`. -/
def blackModPairCompat (i j : I) {w₀ w₁ w₂ : X} (h₁ : w₀ + RD.iX j = w₁)
    (h₂ : w₁ + RD.iX i = w₂) (γ : WeightBlocks RD Λ₀ w₀) :
    Subalgebra k (End (blackModE Q Λ RD Λ₀ j h₁ ≫ blackModE Q Λ RD Λ₀ i h₂) ×
      End (blackFOfEq Q Λ j (blockSucc_step RD Λ₀ j h₁ γ) ⋙
        blackFOfEq Q Λ i (blockSucc_step RD Λ₀ i h₂ (blockSucc RD Λ₀ j h₁ γ)))) :=
  compatSubalgebra _ _ (fun M => M γ)
    (Pi.eval _ (blockSucc RD Λ₀ i h₂ (blockSucc RD Λ₀ j h₁ γ)))
    (fun M => gen₂ (blockSucc RD Λ₀ j h₁) (blockSucc RD Λ₀ i h₂)
      (moduleFBlock Q Λ RD Λ₀ j h₁) (moduleFBlock Q Λ RD Λ₀ i h₂) M γ rfl rfl)

/-- **The left dot slide on weight spaces** (Brundan, arXiv:1501.00350v1, (1.2) for equal
labels, the shape of `TwoRep.RouqLoc.slide_left`). -/
theorem blackModCross_slide_left_self (hsym : KLRSymm Q) (i : I) {w₀ w₁ w₂ : X}
    (h₁ : w₀ + RD.iX i = w₁) (h₂ : w₁ + RD.iX i = w₂) :
    blackModE Q Λ RD Λ₀ i h₁ ◁ blackModDot Q Λ RD Λ₀ i h₂ ≫
        blackModCross Q Λ RD Λ₀ hsym i i h₁ h₂ h₁ h₂ -
      blackModCross Q Λ RD Λ₀ hsym i i h₁ h₂ h₁ h₂ ≫
        blackModDot Q Λ RD Λ₀ i h₁ ▷ blackModE Q Λ RD Λ₀ i h₂ = 𝟙 _ := by
  apply ObjectProperty.hom_ext
  refine NatTrans.ext (funext fun M => ?_)
  refine gen₂_ext (blockSucc RD Λ₀ i h₁) (blockSucc RD Λ₀ i h₂) (moduleFBlock Q Λ RD Λ₀ i h₁)
    (moduleFBlock Q Λ RD Λ₀ i h₂) fun γ β δ hb hd => ?_
  subst hb hd
  have m₁ : (blackModE Q Λ RD Λ₀ i h₁ ◁ blackModDot Q Λ RD Λ₀ i h₂ ≫
        blackModCross Q Λ RD Λ₀ hsym i i h₁ h₂ h₁ h₂,
      Functor.whiskerLeft (blackFOfEq Q Λ i (blockSucc_step RD Λ₀ i h₁ γ))
          (indDotOfEq Q Λ i (blockSucc_step RD Λ₀ i h₂ _)) ≫
        indCrossOfEq Λ hsym i i (blockSucc_step RD Λ₀ i h₁ γ)
          (blockSucc_step RD Λ₀ i h₂ _) (blockSucc_step RD Λ₀ i h₁ γ)
          (blockSucc_step RD Λ₀ i h₂ _)) ∈ blackModPairCompat Q Λ RD Λ₀ i i h₁ h₂ γ := fun M =>
    gen_comp_comp (gen₂_whiskerLeft_blackModDot Q Λ RD Λ₀ i i h₁ h₂ M γ rfl rfl)
      (gen₂_blackModCross Q Λ RD Λ₀ hsym i i h₁ h₂ h₁ h₂ M γ rfl rfl rfl rfl)
  have m₂ : (blackModCross Q Λ RD Λ₀ hsym i i h₁ h₂ h₁ h₂ ≫
        blackModDot Q Λ RD Λ₀ i h₁ ▷ blackModE Q Λ RD Λ₀ i h₂,
      indCrossOfEq Λ hsym i i (blockSucc_step RD Λ₀ i h₁ γ)
          (blockSucc_step RD Λ₀ i h₂ _) (blockSucc_step RD Λ₀ i h₁ γ)
          (blockSucc_step RD Λ₀ i h₂ _) ≫
        Functor.whiskerRight (indDotOfEq Q Λ i (blockSucc_step RD Λ₀ i h₁ γ))
          (blackFOfEq Q Λ i (blockSucc_step RD Λ₀ i h₂ _))) ∈
      blackModPairCompat Q Λ RD Λ₀ i i h₁ h₂ γ := fun M =>
    gen_comp_comp (gen₂_blackModCross Q Λ RD Λ₀ hsym i i h₁ h₂ h₁ h₂ M γ rfl rfl rfl rfl)
      (gen₂_blackModDot_whiskerRight Q Λ RD Λ₀ i i h₁ h₂ M γ rfl rfl)
  have hS := Subalgebra.sub_mem _ m₁ m₂
  rw [Prod.mk_sub_mk, indCrossOfEq_slide_left] at hS
  exact (hS M).trans ((blackModPairCompat Q Λ RD Λ₀ i i h₁ h₂ γ).one_mem M).symm

/-- **The right dot slide on weight spaces** (Brundan, arXiv:1501.00350v1, (1.2) for equal
labels, the shape of `TwoRep.RouqLoc.slide_right`). -/
theorem blackModCross_slide_right_self (hsym : KLRSymm Q) (i : I) {w₀ w₁ w₂ : X}
    (h₁ : w₀ + RD.iX i = w₁) (h₂ : w₁ + RD.iX i = w₂) :
    blackModCross Q Λ RD Λ₀ hsym i i h₁ h₂ h₁ h₂ ≫
        blackModE Q Λ RD Λ₀ i h₁ ◁ blackModDot Q Λ RD Λ₀ i h₂ -
      blackModDot Q Λ RD Λ₀ i h₁ ▷ blackModE Q Λ RD Λ₀ i h₂ ≫
        blackModCross Q Λ RD Λ₀ hsym i i h₁ h₂ h₁ h₂ = 𝟙 _ := by
  apply ObjectProperty.hom_ext
  refine NatTrans.ext (funext fun M => ?_)
  refine gen₂_ext (blockSucc RD Λ₀ i h₁) (blockSucc RD Λ₀ i h₂) (moduleFBlock Q Λ RD Λ₀ i h₁)
    (moduleFBlock Q Λ RD Λ₀ i h₂) fun γ β δ hb hd => ?_
  subst hb hd
  have m₁ : (blackModCross Q Λ RD Λ₀ hsym i i h₁ h₂ h₁ h₂ ≫
        blackModE Q Λ RD Λ₀ i h₁ ◁ blackModDot Q Λ RD Λ₀ i h₂,
      indCrossOfEq Λ hsym i i (blockSucc_step RD Λ₀ i h₁ γ)
          (blockSucc_step RD Λ₀ i h₂ _) (blockSucc_step RD Λ₀ i h₁ γ)
          (blockSucc_step RD Λ₀ i h₂ _) ≫
        Functor.whiskerLeft (blackFOfEq Q Λ i (blockSucc_step RD Λ₀ i h₁ γ))
          (indDotOfEq Q Λ i (blockSucc_step RD Λ₀ i h₂ _))) ∈
      blackModPairCompat Q Λ RD Λ₀ i i h₁ h₂ γ := fun M =>
    gen_comp_comp (gen₂_blackModCross Q Λ RD Λ₀ hsym i i h₁ h₂ h₁ h₂ M γ rfl rfl rfl rfl)
      (gen₂_whiskerLeft_blackModDot Q Λ RD Λ₀ i i h₁ h₂ M γ rfl rfl)
  have m₂ : (blackModDot Q Λ RD Λ₀ i h₁ ▷ blackModE Q Λ RD Λ₀ i h₂ ≫
        blackModCross Q Λ RD Λ₀ hsym i i h₁ h₂ h₁ h₂,
      Functor.whiskerRight (indDotOfEq Q Λ i (blockSucc_step RD Λ₀ i h₁ γ))
          (blackFOfEq Q Λ i (blockSucc_step RD Λ₀ i h₂ _)) ≫
        indCrossOfEq Λ hsym i i (blockSucc_step RD Λ₀ i h₁ γ)
          (blockSucc_step RD Λ₀ i h₂ _) (blockSucc_step RD Λ₀ i h₁ γ)
          (blockSucc_step RD Λ₀ i h₂ _)) ∈ blackModPairCompat Q Λ RD Λ₀ i i h₁ h₂ γ := fun M =>
    gen_comp_comp (gen₂_blackModDot_whiskerRight Q Λ RD Λ₀ i i h₁ h₂ M γ rfl rfl)
      (gen₂_blackModCross Q Λ RD Λ₀ hsym i i h₁ h₂ h₁ h₂ M γ rfl rfl rfl rfl)
  have hS := Subalgebra.sub_mem _ m₁ m₂
  rw [Prod.mk_sub_mk, indCrossOfEq_slide_right] at hS
  exact (hS M).trans ((blackModPairCompat Q Λ RD Λ₀ i i h₁ h₂ γ).one_mem M).symm


end Categorification.Stendhal
