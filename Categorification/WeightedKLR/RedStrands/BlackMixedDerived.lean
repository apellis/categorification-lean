/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.MapDerivedNatTransLinear
import Categorification.WeightedKLR.RedStrands.BlackMixedRelations

/-!
# The mixed crossings on derived categories

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §4.6 and §5.1;
Rouquier's crossing `τ_{ij}` for `i ≠ j` (Brundan, arXiv:1501.00350v1, Definition 1.1).

The mixed crossings `blackMixedCross : Eⱼ Eᵢ ⟶ Eᵢ Eⱼ'` and `blackMixedCrossRev` on right
`T^λ`-modules pass to the derived functors of the exact functors `Eᵢ`, `Eⱼ`, `Eⱼ'`
(`derivedBlackMixedCross`, `derivedBlackMixedCrossRev`), and so do their relations:

* the two quadratic relations `τ̄ τ = Q_{ij}(y, y')` and `τ τ̄ = Q_{ji}(y', y)`
  (`derivedBlackMixedCross_comp_derivedBlackMixedCrossRev`,
  `derivedBlackMixedCrossRev_comp_derivedBlackMixedCross`), through the map of algebras
  `NatTrans.derivedCompAlgHom`;
* the dot slides (`derivedBlackDot_whiskerRight_comp_derivedBlackMixedCross`,
  `derivedBlackDot_whiskerLeft_comp_derivedBlackMixedCross`).

The derived dots are `(blackDot …).mapDerivedCategory` and `(blackDotAt …).mapDerivedCategory`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory KLR MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe w u

variable {I : Type u} [DecidableEq I] {k : Type u} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I} {i j : I}

set_option hygiene false in
local notation "νj" => ((Singleton.singleton j : Multiset I) + ν)
set_option hygiene false in
local notation "νi" => ((Singleton.singleton i : Multiset I) + ν)
set_option hygiene false in
local notation "δ" => ((Singleton.singleton i : Multiset I) + νj)

private theorem blackE_additive₃ (i : I) (μ : Multiset I) : (blackE Q Λ i μ).Additive :=
  inferInstanceAs (resFunctor.{u, u} (appendBlackOp Q Λ i μ)).Additive

private theorem blackEAt_additive (ν : Multiset I) (i j : I) :
    (blackEAt (Q := Q) Λ ν i j).Additive :=
  inferInstanceAs (resFunctor.{u, u} (appendBlackAtOp (Q := Q) Λ ν i j)).Additive

attribute [local instance] blackE_additive₃ blackEAt_additive

instance blackEAt_preservesFiniteLimits (ν : Multiset I) (i j : I) :
    Limits.PreservesFiniteLimits (blackEAt (Q := Q) Λ ν i j) :=
  inferInstanceAs (Limits.PreservesFiniteLimits
    (resFunctor.{u, u} (appendBlackAtOp (Q := Q) Λ ν i j)))

instance blackEAt_preservesFiniteColimits (ν : Multiset I) (i j : I) :
    Limits.PreservesFiniteColimits (blackEAt (Q := Q) Λ ν i j) :=
  inferInstanceAs (Limits.PreservesFiniteColimits
    (resFunctor.{u, u} (appendBlackAtOp (Q := Q) Λ ν i j)))

variable [HasDerivedCategory.{w} (ModuleCat.{u} (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ)]
  [HasDerivedCategory.{w} (ModuleCat.{u} (TensorProductAlgebra k Q Λ νi)ᵐᵒᵖ)]
  [HasDerivedCategory.{w} (ModuleCat.{u} (TensorProductAlgebra k Q Λ νj)ᵐᵒᵖ)]
  [HasDerivedCategory.{w} (ModuleCat.{u} (TensorProductAlgebra k Q Λ δ)ᵐᵒᵖ)]

set_option hygiene false in
local notation "Ei" => blackE Q Λ i νj
set_option hygiene false in
local notation "Ej" => blackE Q Λ j ν
set_option hygiene false in
local notation "Ej'" => blackEAt (Q := Q) Λ ν i j
set_option hygiene false in
local notation "Ei'" => blackE Q Λ i ν

/-- **The mixed crossing on derived categories**: `Eⱼ Eᵢ ⟶ Eᵢ Eⱼ'` for the derived functors. -/
def derivedBlackMixedCross (hsym : KLRSymm Q) (hij : i ≠ j) :
    (Ei).mapDerivedCategory ⋙ (Ej).mapDerivedCategory ⟶
      (Ej').mapDerivedCategory ⋙ (Ei').mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (Ei) (Ej)).hom ≫
    (blackMixedCross hsym hij).mapDerivedCategory ≫
      (Functor.mapDerivedCategoryCompIso (Ej') (Ei')).inv

/-- **The reverse mixed crossing on derived categories**: `Eᵢ Eⱼ' ⟶ Eⱼ Eᵢ`. -/
def derivedBlackMixedCrossRev (hsym : KLRSymm Q) (hij : i ≠ j) :
    (Ej').mapDerivedCategory ⋙ (Ei').mapDerivedCategory ⟶
      (Ei).mapDerivedCategory ⋙ (Ej).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (Ej') (Ei')).hom ≫
    (blackMixedCrossRev hsym hij).mapDerivedCategory ≫
      (Functor.mapDerivedCategoryCompIso (Ei) (Ej)).inv

/-- **The quadratic relation on derived categories** (KL I, (2.6); Brundan, (1.3)):
`τ ≫ τ̄ = Q_{ij}(y, y')`, with `y` the derived dot on the `i` strand and `y'` the derived dot on
the `j` strand. -/
theorem derivedBlackMixedCross_comp_derivedBlackMixedCrossRev (hsym : KLRSymm Q) (hij : i ≠ j) :
    derivedBlackMixedCross hsym hij ≫ derivedBlackMixedCrossRev hsym hij =
      KLR.ncEval (A := End ((Ei).mapDerivedCategory ⋙ (Ej).mapDerivedCategory))
        ![Functor.whiskerRight (blackDot Q Λ i νj).mapDerivedCategory (Ej).mapDerivedCategory,
          Functor.whiskerLeft (Ei).mapDerivedCategory (blackDot Q Λ j ν).mapDerivedCategory]
        (Q i j) := by
  have h : derivedBlackMixedCross hsym hij ≫ derivedBlackMixedCrossRev hsym hij =
      NatTrans.derivedCompAlgHom k (Ei) (Ej)
        (blackMixedCross hsym hij ≫ blackMixedCrossRev hsym hij) := by
    rw [NatTrans.derivedCompAlgHom_apply, NatTrans.mapDerivedCategory_comp,
      derivedBlackMixedCross, derivedBlackMixedCrossRev]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [h, blackMixedCross_comp_blackMixedCrossRev, ncEval_map]
  congr 1
  funext a
  fin_cases a
  · exact (NatTrans.whiskerRight_mapDerivedCategory _).symm
  · exact (NatTrans.whiskerLeft_mapDerivedCategory _).symm

/-- **The second quadratic relation on derived categories**: `τ̄ ≫ τ = Q_{ji}(y', y)`, with
`y'` the derived dot on `Eⱼ'` and `y` the derived dot on the `i` strand. -/
theorem derivedBlackMixedCrossRev_comp_derivedBlackMixedCross (hsym : KLRSymm Q) (hij : i ≠ j) :
    derivedBlackMixedCrossRev hsym hij ≫ derivedBlackMixedCross hsym hij =
      KLR.ncEval (A := End ((Ej').mapDerivedCategory ⋙ (Ei').mapDerivedCategory))
        ![Functor.whiskerRight (blackDotAt Λ ν i j).mapDerivedCategory (Ei').mapDerivedCategory,
          Functor.whiskerLeft (Ej').mapDerivedCategory (blackDot Q Λ i ν).mapDerivedCategory]
        (Q j i) := by
  have h : derivedBlackMixedCrossRev hsym hij ≫ derivedBlackMixedCross hsym hij =
      NatTrans.derivedCompAlgHom k (Ej') (Ei')
        (blackMixedCrossRev hsym hij ≫ blackMixedCross hsym hij) := by
    rw [NatTrans.derivedCompAlgHom_apply, NatTrans.mapDerivedCategory_comp,
      derivedBlackMixedCross, derivedBlackMixedCrossRev]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [h, blackMixedCrossRev_comp_blackMixedCross, ncEval_map]
  congr 1
  funext a
  fin_cases a
  · exact (NatTrans.whiskerRight_mapDerivedCategory _).symm
  · exact (NatTrans.whiskerLeft_mapDerivedCategory _).symm

/-- **Dot slide on the `i` strand on derived categories**: `(yᵢ Eⱼ) ≫ τ = τ ≫ (Eⱼ' yᵢ)`. -/
theorem derivedBlackDot_whiskerRight_comp_derivedBlackMixedCross (hsym : KLRSymm Q)
    (hij : i ≠ j) :
    Functor.whiskerRight (blackDot Q Λ i νj).mapDerivedCategory (Ej).mapDerivedCategory ≫
        derivedBlackMixedCross hsym hij =
      derivedBlackMixedCross hsym hij ≫
        Functor.whiskerLeft (Ej').mapDerivedCategory (blackDot Q Λ i ν).mapDerivedCategory := by
  rw [NatTrans.whiskerRight_mapDerivedCategory, NatTrans.whiskerLeft_mapDerivedCategory,
    derivedBlackMixedCross]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← NatTrans.mapDerivedCategory_comp_assoc, ← NatTrans.mapDerivedCategory_comp_assoc,
    blackDot_whiskerRight_comp_blackMixedCross]

/-- **Dot slide on the `j` strand on derived categories**: `(Eᵢ yⱼ) ≫ τ = τ ≫ (yⱼ' Eᵢ)`. -/
theorem derivedBlackDot_whiskerLeft_comp_derivedBlackMixedCross (hsym : KLRSymm Q)
    (hij : i ≠ j) :
    Functor.whiskerLeft (Ei).mapDerivedCategory (blackDot Q Λ j ν).mapDerivedCategory ≫
        derivedBlackMixedCross hsym hij =
      derivedBlackMixedCross hsym hij ≫
        Functor.whiskerRight (blackDotAt Λ ν i j).mapDerivedCategory (Ei').mapDerivedCategory := by
  rw [NatTrans.whiskerRight_mapDerivedCategory, NatTrans.whiskerLeft_mapDerivedCategory,
    derivedBlackMixedCross]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← NatTrans.mapDerivedCategory_comp_assoc, ← NatTrans.mapDerivedCategory_comp_assoc,
    blackDot_whiskerLeft_comp_blackMixedCross]

end Categorification.Stendhal
