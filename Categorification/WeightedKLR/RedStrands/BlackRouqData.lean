/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackRouqBlocks
import Categorification.WeightedKLR.RedStrands.BlackDerivedFunctors
import Categorification.KLR.CyclotomicAction.GlobalCross
import Categorification.TwoRep.RouqModel
import Categorification.KLR.CyclotomicAction.GlobalBraid
import Categorification.Algebra.MapDerivedNatTransTriple

/-!
# The weight-indexed Rouquier generators on derived categories of `T^λ`-modules

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §4.6 and §5.1;
Rouquier's generators (Brundan, arXiv:1501.00350v1, Definition 1.1; `TwoRep.RouqData`).

The indexing is that of the cyclotomic family `KLR.CyclotomicAction.weightSpace`: for a weight
`Λ₀ ∈ X`, a content `β` has weight `blockWeight RD Λ₀ β = Σ_{i ∈ β} i_X - Λ₀`, and the weight
space at `x` (`blackWeightSpace`) is the product of the derived categories `D(T^λ_β)` of right
modules over the blocks `β` of weight `x`. Adding a black strand raises the weight.

* `blackRouqE i h`, for `h : x + i_X = y`, is the derived induction `Fᵢ` of `blackFOfEq`
  assembled over blocks (`blockSum`), with right adjoint the derived restriction
  (`blackRouqF`, `blackRouqAdj`).
* `blackRouqDot` and `blackRouqCross` are the derived mates of the dot and the crossings on
  restrictions (`indDotOfEq`, `indCrossOfEq`) on each block.

`blackRouqData` packages these as a `TwoRep.RouqData` in `LinearCat k`. Induction is exact for
Rouquier polynomials over a field (Theorem 4.31), the hypothesis `(C, hQ)`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory MulOpposite InductionAlong KLR TwoRep QuantumGroup
  CyclotomicAction Bicategory

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe w u u₁

variable {I : Type u} [DecidableEq I] {k : Type u} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin ℓ → I →₀ ℕ) {C : CartanDatum I}

/-! ### Exactness of induction between arbitrary contents -/

instance blackEOfEq_preservesFiniteLimits (i : I) {μ β : Multiset I}
    (h : ({i} : Multiset I) + μ = β) : Limits.PreservesFiniteLimits (blackEOfEq Q Λ i h) :=
  inferInstanceAs (Limits.PreservesFiniteLimits (resFunctor.{u, u} (appendBlackOpOfEq Q Λ i h)))

instance blackEOfEq_preservesFiniteColimits (i : I) {μ β : Multiset I}
    (h : ({i} : Multiset I) + μ = β) : Limits.PreservesFiniteColimits (blackEOfEq Q Λ i h) :=
  inferInstanceAs
    (Limits.PreservesFiniteColimits (resFunctor.{u, u} (appendBlackOpOfEq Q Λ i h)))

variable (hQ : IsRouquierQ C Q)

include hQ in
theorem blackFOfEq_preservesFiniteLimits (i : I) {μ β : Multiset I}
    (h : ({i} : Multiset I) + μ = β) : Limits.PreservesFiniteLimits (blackFOfEq Q Λ i h) := by
  subst h; exact blackF_preservesFiniteLimits Q Λ i μ C hQ

include hQ in
theorem blackFOfEq_preservesFiniteColimits (i : I) {μ β : Multiset I}
    (h : ({i} : Multiset I) + μ = β) : Limits.PreservesFiniteColimits (blackFOfEq Q Λ i h) := by
  subst h; exact blackF_preservesFiniteColimits Q Λ i μ C hQ

variable [∀ β : Multiset I,
  HasDerivedCategory.{w} (ModuleCat.{u} (TensorProductAlgebra k Q Λ β)ᵐᵒᵖ)]

set_option hygiene false in
local notation "D" β => DerivedCategory (ModuleCat.{u} (TensorProductAlgebra k Q Λ β)ᵐᵒᵖ)

/-! ### Derived blocks -/

variable (Q) in
/-- The derived restriction `Eᵢ : D(T^λ_β) ⥤ D(T^λ_μ)` for `{i} + μ = β`. -/
def derivedEOfEq (i : I) {μ β : Multiset I} (h : ({i} : Multiset I) + μ = β) :
    (D β) ⥤ (D μ) :=
  (blackEOfEq Q Λ i h).mapDerivedCategory

instance derivedEOfEq_additive (i : I) {μ β : Multiset I} (h : ({i} : Multiset I) + μ = β) :
    (derivedEOfEq Q Λ i h).Additive := by
  unfold derivedEOfEq; infer_instance

instance derivedEOfEq_linear (i : I) {μ β : Multiset I} (h : ({i} : Multiset I) + μ = β) :
    (derivedEOfEq Q Λ i h).Linear k := by
  unfold derivedEOfEq; infer_instance

include hQ

/-- The derived induction `Fᵢ : D(T^λ_μ) ⥤ D(T^λ_β)` for `{i} + μ = β`. -/
def derivedFOfEq (i : I) {μ β : Multiset I} (h : ({i} : Multiset I) + μ = β) :
    (D μ) ⥤ (D β) :=
  haveI := blackFOfEq_preservesFiniteLimits Λ hQ i h
  haveI := blackFOfEq_preservesFiniteColimits Λ hQ i h
  (blackFOfEq Q Λ i h).mapDerivedCategory

instance derivedFOfEq_additive (i : I) {μ β : Multiset I} (h : ({i} : Multiset I) + μ = β) :
    (derivedFOfEq Λ hQ i h).Additive := by
  unfold derivedFOfEq; infer_instance

instance derivedFOfEq_linear (i : I) {μ β : Multiset I} (h : ({i} : Multiset I) + μ = β) :
    (derivedFOfEq Λ hQ i h).Linear k := by
  unfold derivedFOfEq; infer_instance

/-- The derived `Fᵢ ⊣ Eᵢ`. -/
def derivedAdjOfEq (i : I) {μ β : Multiset I} (h : ({i} : Multiset I) + μ = β) :
    derivedFOfEq Λ hQ i h ⊣ derivedEOfEq Q Λ i h :=
  haveI := blackFOfEq_preservesFiniteLimits Λ hQ i h
  haveI := blackFOfEq_preservesFiniteColimits Λ hQ i h
  (blackAdjOfEq Q Λ i h).mapDerivedCategory

/-- The derived dot on `Fᵢ`. -/
def derivedIndDotOfEq (i : I) {μ β : Multiset I} (h : ({i} : Multiset I) + μ = β) :
    derivedFOfEq Λ hQ i h ⟶ derivedFOfEq Λ hQ i h :=
  haveI := blackFOfEq_preservesFiniteLimits Λ hQ i h
  haveI := blackFOfEq_preservesFiniteColimits Λ hQ i h
  (indDotOfEq Q Λ i h).mapDerivedCategory

/-- The derived crossing `Fⱼ Fᵢ ⟶ Fᵢ Fⱼ` on blocks. -/
def derivedIndCrossOfEq (hsym : KLRSymm Q) (i j : I) {μ β₁ β₂ δ : Multiset I}
    (h₁ : ({j} : Multiset I) + μ = β₁) (h₂ : ({i} : Multiset I) + β₁ = δ)
    (h₃ : ({i} : Multiset I) + μ = β₂) (h₄ : ({j} : Multiset I) + β₂ = δ) :
    derivedFOfEq Λ hQ j h₁ ⋙ derivedFOfEq Λ hQ i h₂ ⟶
      derivedFOfEq Λ hQ i h₃ ⋙ derivedFOfEq Λ hQ j h₄ :=
  haveI := blackFOfEq_preservesFiniteLimits Λ hQ i h₂
  haveI := blackFOfEq_preservesFiniteColimits Λ hQ i h₂
  haveI := blackFOfEq_preservesFiniteLimits Λ hQ j h₁
  haveI := blackFOfEq_preservesFiniteColimits Λ hQ j h₁
  haveI := blackFOfEq_preservesFiniteLimits Λ hQ i h₃
  haveI := blackFOfEq_preservesFiniteColimits Λ hQ i h₃
  haveI := blackFOfEq_preservesFiniteLimits Λ hQ j h₄
  haveI := blackFOfEq_preservesFiniteColimits Λ hQ j h₄
  NatTrans.derivedComp (F₁ := blackFOfEq Q Λ j h₁) (F₂ := blackFOfEq Q Λ i h₂)
    (F₁' := blackFOfEq Q Λ i h₃) (F₂' := blackFOfEq Q Λ j h₄)
    (indCrossOfEq Λ hsym i j h₁ h₂ h₃ h₄)

theorem derivedIndCrossOfEq_sq (hsym : KLRSymm Q) (i : I) {μ β δ : Multiset I}
    (h₁ : ({i} : Multiset I) + μ = β) (h₂ : ({i} : Multiset I) + β = δ) :
    derivedIndCrossOfEq Λ hQ hsym i i h₁ h₂ h₁ h₂ ≫ derivedIndCrossOfEq Λ hQ hsym i i h₁ h₂ h₁ h₂ =
      0 := by
  have := blackFOfEq_preservesFiniteLimits Λ hQ i h₁
  have := blackFOfEq_preservesFiniteColimits Λ hQ i h₁
  have := blackFOfEq_preservesFiniteLimits Λ hQ i h₂
  have := blackFOfEq_preservesFiniteColimits Λ hQ i h₂
  unfold derivedIndCrossOfEq
  exact NatTrans.derivedComp_comp_eq_zero (indCrossOfEq_sq Λ hsym i h₁ h₂)

/-- **The braid relation on the derived `Fᵢ³`** between arbitrary contents, in the shape of
`CyclotomicAction.signedCross_sameBraid`. -/
theorem derivedIndCrossOfEq_braid (hsym : KLRSymm Q) (i : I) {μ β γ δ : Multiset I}
    (h₁ : ({i} : Multiset I) + μ = β) (h₂ : ({i} : Multiset I) + β = γ)
    (h₃ : ({i} : Multiset I) + γ = δ) :
    Functor.whiskerLeft (derivedFOfEq Λ hQ i h₁) (derivedIndCrossOfEq Λ hQ hsym i i h₂ h₃ h₂ h₃) ≫
        ((Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (derivedIndCrossOfEq Λ hQ hsym i i h₁ h₂ h₁ h₂)
            (derivedFOfEq Λ hQ i h₃) ≫
          (Functor.associator _ _ _).hom) ≫
        Functor.whiskerLeft (derivedFOfEq Λ hQ i h₁)
          (derivedIndCrossOfEq Λ hQ hsym i i h₂ h₃ h₂ h₃) =
      ((Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (derivedIndCrossOfEq Λ hQ hsym i i h₁ h₂ h₁ h₂)
            (derivedFOfEq Λ hQ i h₃) ≫
          (Functor.associator _ _ _).hom) ≫
        Functor.whiskerLeft (derivedFOfEq Λ hQ i h₁)
          (derivedIndCrossOfEq Λ hQ hsym i i h₂ h₃ h₂ h₃) ≫
        ((Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (derivedIndCrossOfEq Λ hQ hsym i i h₁ h₂ h₁ h₂)
            (derivedFOfEq Λ hQ i h₃) ≫
          (Functor.associator _ _ _).hom) := by
  have := blackFOfEq_preservesFiniteLimits Λ hQ i h₁
  have := blackFOfEq_preservesFiniteColimits Λ hQ i h₁
  have := blackFOfEq_preservesFiniteLimits Λ hQ i h₂
  have := blackFOfEq_preservesFiniteColimits Λ hQ i h₂
  have := blackFOfEq_preservesFiniteLimits Λ hQ i h₃
  have := blackFOfEq_preservesFiniteColimits Λ hQ i h₃
  unfold derivedIndCrossOfEq derivedFOfEq
  have h := NatTrans.derivedComp_braid (indCrossOfEq_braid Λ hsym i h₁ h₂ h₃)
  ext X
  have hX := congrArg (fun η => NatTrans.app η X) h
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.associator_hom_app, Category.id_comp,
    Category.comp_id] using hX

/-! ### Weight spaces -/

variable {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y] (RD : UDot.WeightDatum C X Y)
  (Λ₀ : X)

omit hQ in
variable (Q) in
/-- **The weight space at `x`**: the product of the derived categories `D(T^λ_β)` over the
contents `β` of weight `x` (`blockWeight RD Λ₀ β = x`). -/
abbrev blackWeightSpace (x : X) : LinearCat k :=
  LinearCat.of k (∀ β : WeightBlocks RD Λ₀ x, D β.1)

/-- The blocks of `blackRouqE`. -/
abbrev derivedFBlock (i : I) {x y : X} (h : x + RD.iX i = y) (β : WeightBlocks RD Λ₀ x)
    (δ : WeightBlocks RD Λ₀ y) (hβ : blockSucc RD Λ₀ i h β = δ) : (D β.1) ⥤ (D δ.1) :=
  derivedFOfEq Λ hQ i (blockSucc_eq RD Λ₀ i hβ)

omit hQ in
variable (Q) in
/-- The blocks of `blackRouqF`. -/
abbrev derivedEBlock (i : I) {x y : X} (h : x + RD.iX i = y) (β : WeightBlocks RD Λ₀ x)
    (δ : WeightBlocks RD Λ₀ y) (hβ : blockSucc RD Λ₀ i h β = δ) : (D δ.1) ⥤ (D β.1) :=
  derivedEOfEq Q Λ i (blockSucc_eq RD Λ₀ i hβ)

/-- **`Fᵢ` on weight spaces**, `x ⟶ x + i_X`: derived induction assembled over blocks. -/
def blackRouqE (i : I) {x y : X} (h : x + RD.iX i = y) :
    blackWeightSpace Q Λ RD Λ₀ x ⟶ blackWeightSpace Q Λ RD Λ₀ y :=
  LinearCat.LinFun.of (TwoRep.blockSum (blockSucc RD Λ₀ i h) (derivedFBlock Λ hQ RD Λ₀ i h))

omit hQ in
variable (Q) in
/-- **`Eᵢ` on weight spaces**, `x + i_X ⟶ x`: derived restriction blockwise. -/
def blackRouqF (i : I) {x y : X} (h : x + RD.iX i = y) :
    blackWeightSpace Q Λ RD Λ₀ y ⟶ blackWeightSpace Q Λ RD Λ₀ x :=
  LinearCat.LinFun.of (TwoRep.blockRes (blockSucc RD Λ₀ i h) (derivedEBlock Q Λ RD Λ₀ i h))

/-- **The induction–restriction adjunction on weight spaces.** -/
def blackRouqAdj (i : I) {x y : X} (h : x + RD.iX i = y) :
    Bicategory.Adjunction (blackRouqE Λ hQ RD Λ₀ i h) (blackRouqF Q Λ RD Λ₀ i h) :=
  LinearCat.ofAdjunction k (TwoRep.blockAdjunction (blockSucc RD Λ₀ i h)
    fun _ _ hβ => derivedAdjOfEq Λ hQ i (blockSucc_eq RD Λ₀ i hβ))

/-- **The dot on weight spaces**: the derived dot of `Fᵢ` on each block. -/
def blackRouqDot (i : I) {x y : X} (h : x + RD.iX i = y) :
    blackRouqE Λ hQ RD Λ₀ i h ⟶ blackRouqE Λ hQ RD Λ₀ i h :=
  ObjectProperty.homMk (TwoRep.blockSumMap (blockSucc RD Λ₀ i h)
    fun _ _ hβ => derivedIndDotOfEq Λ hQ i (blockSucc_eq RD Λ₀ i hβ))

/-- **The crossing on weight spaces** `Fⱼ Fᵢ ⟶ Fᵢ Fⱼ`: the derived crossing on each block. -/
def blackRouqCross (hsym : KLRSymm Q) (i j : I) {x y z t : X} (h₁ : x + RD.iX j = y)
    (h₂ : y + RD.iX i = t) (h₃ : x + RD.iX i = z) (h₄ : z + RD.iX j = t) :
    blackRouqE Λ hQ RD Λ₀ j h₁ ≫ blackRouqE Λ hQ RD Λ₀ i h₂ ⟶
      blackRouqE Λ hQ RD Λ₀ i h₃ ≫ blackRouqE Λ hQ RD Λ₀ j h₄ :=
  ObjectProperty.homMk (TwoRep.blockCross (blockSucc RD Λ₀ j h₁) (blockSucc RD Λ₀ i h₂)
    (derivedFBlock Λ hQ RD Λ₀ j h₁) (derivedFBlock Λ hQ RD Λ₀ i h₂) (blockSucc RD Λ₀ i h₃)
    (blockSucc RD Λ₀ j h₄) (derivedFBlock Λ hQ RD Λ₀ i h₃) (derivedFBlock Λ hQ RD Λ₀ j h₄)
    (blockSucc_comm RD Λ₀ i j h₁ h₂ h₃ h₄) fun _ _ _ _ hb hd hb' hd' =>
      derivedIndCrossOfEq Λ hQ hsym i j (blockSucc_eq RD Λ₀ j hb) (blockSucc_eq RD Λ₀ i hd)
        (blockSucc_eq RD Λ₀ i hb') (blockSucc_eq RD Λ₀ j hd'))

/-- `blackRouqCross` on the generators of `Fⱼ ≫ Fᵢ`, for any intermediate blocks. -/
theorem gen₂_blackRouqCross (hsym : KLRSymm Q) (i j : I) {x y z t : X} (h₁ : x + RD.iX j = y)
    (h₂ : y + RD.iX i = t) (h₃ : x + RD.iX i = z) (h₄ : z + RD.iX j = t)
    (M : ∀ γ : WeightBlocks RD Λ₀ x, D γ.1) (γ : WeightBlocks RD Λ₀ x)
    {β : WeightBlocks RD Λ₀ y} {β' : WeightBlocks RD Λ₀ z} {δ : WeightBlocks RD Λ₀ t}
    (hb : blockSucc RD Λ₀ j h₁ γ = β) (hd : blockSucc RD Λ₀ i h₂ β = δ)
    (hb' : blockSucc RD Λ₀ i h₃ γ = β') (hd' : blockSucc RD Λ₀ j h₄ β' = δ) :
    gen₂ (blockSucc RD Λ₀ j h₁) (blockSucc RD Λ₀ i h₂) (derivedFBlock Λ hQ RD Λ₀ j h₁)
        (derivedFBlock Λ hQ RD Λ₀ i h₂) M γ hb hd ≫
        (blackRouqCross Λ hQ RD Λ₀ hsym i j h₁ h₂ h₃ h₄).hom.app M δ =
      (derivedIndCrossOfEq Λ hQ hsym i j (blockSucc_eq RD Λ₀ j hb) (blockSucc_eq RD Λ₀ i hd)
          (blockSucc_eq RD Λ₀ i hb') (blockSucc_eq RD Λ₀ j hd')).app (M γ) ≫
        gen₂ (blockSucc RD Λ₀ i h₃) (blockSucc RD Λ₀ j h₄) (derivedFBlock Λ hQ RD Λ₀ i h₃)
          (derivedFBlock Λ hQ RD Λ₀ j h₄) M γ hb' hd' :=
  gen₂_blockCross _ _ _ _ _ _ _ _ _ _ M γ hb hd hb' hd'

/-- **The nil-Hecke quadratic relation on weight spaces** (the shape of
`TwoRep.RouqFamily.square`). -/
theorem blackRouqCross_sq (hsym : KLRSymm Q) (i : I) {x y t : X} (h₁ : x + RD.iX i = y)
    (h₂ : y + RD.iX i = t) :
    blackRouqCross Λ hQ RD Λ₀ hsym i i h₁ h₂ h₁ h₂ ≫
      blackRouqCross Λ hQ RD Λ₀ hsym i i h₁ h₂ h₁ h₂ = 0 := by
  apply ObjectProperty.hom_ext
  refine NatTrans.ext (funext fun M => ?_)
  refine gen₂_ext (blockSucc RD Λ₀ i h₁) (blockSucc RD Λ₀ i h₂) (derivedFBlock Λ hQ RD Λ₀ i h₁)
    (derivedFBlock Λ hQ RD Λ₀ i h₂) fun γ β δ hb hd => ?_
  refine (gen_comp_comp (gen₂_blackRouqCross Λ hQ RD Λ₀ hsym i i h₁ h₂ h₁ h₂ M γ hb hd hb hd)
    (gen₂_blackRouqCross Λ hQ RD Λ₀ hsym i i h₁ h₂ h₁ h₂ M γ hb hd hb hd)).trans ?_
  rw [← NatTrans.comp_app, derivedIndCrossOfEq_sq, NatTrans.app_zero]
  exact Limits.zero_comp.trans Limits.comp_zero.symm

/-- **The braid relation for three strands of the same colour on weight spaces** (the shape of
`TwoRep.RouqFamily.braid`). -/
theorem blackRouqCross_sameBraid (hsym : KLRSymm Q) (i : I) {w₀ w₁ w₂ w₃ : X}
    (h₁ : w₀ + RD.iX i = w₁) (h₂ : w₁ + RD.iX i = w₂) (h₃ : w₂ + RD.iX i = w₃) :
    blackRouqE Λ hQ RD Λ₀ i h₁ ◁ blackRouqCross Λ hQ RD Λ₀ hsym i i h₂ h₃ h₂ h₃ ≫
      ((α_ (blackRouqE Λ hQ RD Λ₀ i h₁) (blackRouqE Λ hQ RD Λ₀ i h₂)
          (blackRouqE Λ hQ RD Λ₀ i h₃)).inv ≫
        blackRouqCross Λ hQ RD Λ₀ hsym i i h₁ h₂ h₁ h₂ ▷ blackRouqE Λ hQ RD Λ₀ i h₃ ≫
        (α_ (blackRouqE Λ hQ RD Λ₀ i h₁) (blackRouqE Λ hQ RD Λ₀ i h₂)
          (blackRouqE Λ hQ RD Λ₀ i h₃)).hom) ≫
      blackRouqE Λ hQ RD Λ₀ i h₁ ◁ blackRouqCross Λ hQ RD Λ₀ hsym i i h₂ h₃ h₂ h₃ =
    ((α_ (blackRouqE Λ hQ RD Λ₀ i h₁) (blackRouqE Λ hQ RD Λ₀ i h₂)
          (blackRouqE Λ hQ RD Λ₀ i h₃)).inv ≫
      blackRouqCross Λ hQ RD Λ₀ hsym i i h₁ h₂ h₁ h₂ ▷ blackRouqE Λ hQ RD Λ₀ i h₃ ≫
      (α_ (blackRouqE Λ hQ RD Λ₀ i h₁) (blackRouqE Λ hQ RD Λ₀ i h₂)
          (blackRouqE Λ hQ RD Λ₀ i h₃)).hom) ≫
      blackRouqE Λ hQ RD Λ₀ i h₁ ◁ blackRouqCross Λ hQ RD Λ₀ hsym i i h₂ h₃ h₂ h₃ ≫
    ((α_ (blackRouqE Λ hQ RD Λ₀ i h₁) (blackRouqE Λ hQ RD Λ₀ i h₂)
          (blackRouqE Λ hQ RD Λ₀ i h₃)).inv ≫
      blackRouqCross Λ hQ RD Λ₀ hsym i i h₁ h₂ h₁ h₂ ▷ blackRouqE Λ hQ RD Λ₀ i h₃ ≫
      (α_ (blackRouqE Λ hQ RD Λ₀ i h₁) (blackRouqE Λ hQ RD Λ₀ i h₂)
          (blackRouqE Λ hQ RD Λ₀ i h₃)).hom) := by
  apply ObjectProperty.hom_ext
  refine NatTrans.ext (funext fun M => ?_)
  refine gen₃_ext (blockSucc RD Λ₀ i h₁) (blockSucc RD Λ₀ i h₂) (blockSucc RD Λ₀ i h₃)
    (derivedFBlock Λ hQ RD Λ₀ i h₁) (derivedFBlock Λ hQ RD Λ₀ i h₂)
    (derivedFBlock Λ hQ RD Λ₀ i h₃) fun γ β δ μ hβ hδ hμ => ?_
  subst hβ hδ hμ
  have s1 := gen₃_whiskerLeft (blockSucc RD Λ₀ i h₁) (blockSucc RD Λ₀ i h₂)
      (blockSucc RD Λ₀ i h₃) (derivedFBlock Λ hQ RD Λ₀ i h₁) (derivedFBlock Λ hQ RD Λ₀ i h₂)
      (derivedFBlock Λ hQ RD Λ₀ i h₃)
      (s₂' := blockSucc RD Λ₀ i h₂) (s₃' := blockSucc RD Λ₀ i h₃)
      (L₂' := derivedFBlock Λ hQ RD Λ₀ i h₂) (L₃' := derivedFBlock Λ hQ RD Λ₀ i h₃)
      (blackRouqCross Λ hQ RD Λ₀ hsym i i h₂ h₃ h₂ h₃).hom M γ rfl rfl rfl rfl rfl _
      (gen₂_blackRouqCross Λ hQ RD Λ₀ hsym i i h₂ h₃ h₂ h₃ _ _ rfl rfl rfl rfl)
  have s2 := gen₃_whiskerRight (blockSucc RD Λ₀ i h₁) (blockSucc RD Λ₀ i h₂)
      (blockSucc RD Λ₀ i h₃) (derivedFBlock Λ hQ RD Λ₀ i h₁) (derivedFBlock Λ hQ RD Λ₀ i h₂)
      (derivedFBlock Λ hQ RD Λ₀ i h₃)
      (s₁' := blockSucc RD Λ₀ i h₁) (s₂' := blockSucc RD Λ₀ i h₂)
      (L₁' := derivedFBlock Λ hQ RD Λ₀ i h₁) (L₂' := derivedFBlock Λ hQ RD Λ₀ i h₂)
      (blackRouqCross Λ hQ RD Λ₀ hsym i i h₁ h₂ h₁ h₂).hom M γ rfl rfl rfl rfl rfl _
      (gen₂_blackRouqCross Λ hQ RD Λ₀ hsym i i h₁ h₂ h₁ h₂ M γ rfl rfl rfl rfl)
  refine (gen_chain_left s1 (gen_assoc _) s2 (gen_assoc _) s1).trans
    (Eq.trans ?_ (gen_chain_right (gen_assoc _) s2 (gen_assoc _) s1 (gen_assoc _) s2
      (gen_assoc _)).symm)
  exact congrArg (· ≫ _) (congrArg (fun η => NatTrans.app η (M γ))
    (derivedIndCrossOfEq_braid Λ hQ hsym i _ _ _))

/-- **The Rouquier generators on derived categories of `T^λ`-modules** (`TwoRep.RouqData`):
weight spaces, `Fᵢ`, dots and crossings. -/
def blackRouqData (hsym : KLRSymm Q) : RouqData (B := LinearCat k) RD where
  obj := blackWeightSpace Q Λ RD Λ₀
  E i _ _ h := blackRouqE Λ hQ RD Λ₀ i h
  dot i _ _ h := blackRouqDot Λ hQ RD Λ₀ i h
  cross i j _ _ _ _ h₁ h₂ h₃ h₄ := blackRouqCross Λ hQ RD Λ₀ hsym i j h₁ h₂ h₃ h₄

end Categorification.Stendhal
