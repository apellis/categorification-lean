/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackRouqMixedBraidQ
import Categorification.WeightedKLR.RedStrands.BlackRouqMixedBraidWeight
import Categorification.Algebra.MapDerivedNatTransLinear
import Categorification.KLR.CyclotomicAction.GlobalBraidQ

/-!
# The braid relation with equal outer colours on derived categories of `T^λ`-modules

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §4.6 and §5.1;
Brundan, arXiv:1501.00350v1, Definition 1.1, (1.4) for outer labels `i, i` and middle label
`j ≠ i` (the field `braidQ` of `TwoRep.RouqUpKLR`).

Endomorphisms of a composite of three exact functors pass to the composite of the derived
functors by an algebra map (`NatTrans.derivedTripleAlgHom`), compatible with whiskering, so the
braid relation with a polynomial right-hand side passes to derived categories
(`NatTrans.derivedComp_braidQ_three`). Applied to `indCrossOfEq_braidQ` this gives the relation
on derived black inductions (`derivedIndCrossOfEq_braidQ`), and through the block generators
`gen₃` (as for `CyclotomicAction.globalCross_braidQ`) the relation on the weight spaces of
`blackRouqData` (`blackRouqCross_braidQ`), in the shape of `TwoRep.RouqUpKLR.braidQ`.

Induction is exact for Rouquier polynomials over a field (Theorem 4.31), the hypothesis
`(C, hQ)`; otherwise the hypotheses are `KLRSymm Q` and `i ≠ j`. No route hypothesis is added.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CategoryTheory.NatTrans

open Limits Category

universe v₀ v₁ v₁' v₁'' v₂ v₂' v₃

variable {C₀ : Type*} [Category* C₀] [Abelian C₀] [HasDerivedCategory.{v₀} C₀]
  {C₁ : Type*} [Category* C₁] [Abelian C₁] [HasDerivedCategory.{v₁} C₁]
  {C₁' : Type*} [Category* C₁'] [Abelian C₁'] [HasDerivedCategory.{v₁'} C₁']
  {C₁'' : Type*} [Category* C₁''] [Abelian C₁''] [HasDerivedCategory.{v₁''} C₁'']
  {C₂ : Type*} [Category* C₂] [Abelian C₂] [HasDerivedCategory.{v₂} C₂]
  {C₂' : Type*} [Category* C₂'] [Abelian C₂'] [HasDerivedCategory.{v₂'} C₂']
  {C₃ : Type*} [Category* C₃] [Abelian C₃] [HasDerivedCategory.{v₃} C₃]
  (R : Type*) [CommRing R] [Linear R C₃]
  (A₁ : C₀ ⥤ C₁) [A₁.Additive] [PreservesFiniteLimits A₁] [PreservesFiniteColimits A₁]
  (A₂ : C₁ ⥤ C₂) [A₂.Additive] [PreservesFiniteLimits A₂] [PreservesFiniteColimits A₂]
  (A₃ : C₂ ⥤ C₃) [A₃.Additive] [PreservesFiniteLimits A₃] [PreservesFiniteColimits A₃]

/-- **Endomorphisms of a triple composite on derived categories**: `α ↦ c ≫ α.mapDerivedCategory ≫
c⁻¹` for `c = mapDerivedCategoryTripleIso A₁ A₂ A₃`, a map of `R`-algebras. -/
def derivedTripleAlgHom :
    End (A₁ ⋙ A₂ ⋙ A₃) →ₐ[R]
      End (A₁.mapDerivedCategory ⋙ A₂.mapDerivedCategory ⋙ A₃.mapDerivedCategory) where
  toFun α := (Functor.mapDerivedCategoryTripleIso A₁ A₂ A₃).hom ≫ α.mapDerivedCategory ≫
    (Functor.mapDerivedCategoryTripleIso A₁ A₂ A₃).inv
  map_one' := by
    change _ ≫ (𝟙 (A₁ ⋙ A₂ ⋙ A₃) : A₁ ⋙ A₂ ⋙ A₃ ⟶ A₁ ⋙ A₂ ⋙ A₃).mapDerivedCategory ≫ _ = 𝟙 _
    rw [mapDerivedCategory_id, id_comp, Iso.hom_inv_id]
  map_mul' α β := by
    change _ ≫ (β ≫ α).mapDerivedCategory ≫ _ = (_ ≫ β.mapDerivedCategory ≫ _) ≫
      (_ ≫ α.mapDerivedCategory ≫ _)
    rw [mapDerivedCategory_comp]
    simp only [assoc, Iso.inv_hom_id_assoc]
  map_zero' := by
    change _ ≫ (0 : A₁ ⋙ A₂ ⋙ A₃ ⟶ A₁ ⋙ A₂ ⋙ A₃).mapDerivedCategory ≫ _ = 0
    rw [mapDerivedCategory_zero, zero_comp, comp_zero]
  map_add' α β := by
    change _ ≫ (α + β).mapDerivedCategory ≫ _ = (_ ≫ α.mapDerivedCategory ≫ _) +
      (_ ≫ β.mapDerivedCategory ≫ _)
    rw [mapDerivedCategory_add, Preadditive.add_comp, Preadditive.comp_add]
  commutes' r := by
    change _ ≫ (r • (𝟙 (A₁ ⋙ A₂ ⋙ A₃) : A₁ ⋙ A₂ ⋙ A₃ ⟶ A₁ ⋙ A₂ ⋙ A₃)).mapDerivedCategory ≫ _ =
      r • 𝟙 (A₁.mapDerivedCategory ⋙ A₂.mapDerivedCategory ⋙ A₃.mapDerivedCategory)
    rw [mapDerivedCategory_smul, mapDerivedCategory_id, Linear.smul_comp, Linear.comp_smul,
      id_comp, Iso.hom_inv_id]

variable {R A₁ A₂ A₃}

theorem derivedTripleAlgHom_eq_of {α : End (A₁ ⋙ A₂ ⋙ A₃)}
    {β : End (A₁.mapDerivedCategory ⋙ A₂.mapDerivedCategory ⋙ A₃.mapDerivedCategory)}
    (h : β ≫ (Functor.mapDerivedCategoryTripleIso A₁ A₂ A₃).hom =
      (Functor.mapDerivedCategoryTripleIso A₁ A₂ A₃).hom ≫ α.mapDerivedCategory) :
    derivedTripleAlgHom R A₁ A₂ A₃ α = β := by
  change (Functor.mapDerivedCategoryTripleIso A₁ A₂ A₃).hom ≫ α.mapDerivedCategory ≫
    (Functor.mapDerivedCategoryTripleIso A₁ A₂ A₃).inv = β
  rw [← reassoc_of% h, Iso.hom_inv_id, comp_id]

theorem derivedTripleAlgHom_whiskerLeft (X : A₂ ⋙ A₃ ⟶ A₂ ⋙ A₃) :
    derivedTripleAlgHom R A₁ A₂ A₃ (Functor.whiskerLeft A₁ X) =
      Functor.whiskerLeft A₁.mapDerivedCategory (derivedComp X) :=
  derivedTripleAlgHom_eq_of (whiskerLeft_derivedComp_tripleIso X)

theorem derivedTripleAlgHom_whiskerRight (X : A₁ ⋙ A₂ ⟶ A₁ ⋙ A₂) :
    derivedTripleAlgHom R A₁ A₂ A₃ (Functor.whiskerRight X A₃) =
      (Functor.whiskerRight (derivedComp X) A₃.mapDerivedCategory :
        End (A₁.mapDerivedCategory ⋙ A₂.mapDerivedCategory ⋙ A₃.mapDerivedCategory)) :=
  derivedTripleAlgHom_eq_of (whiskerRight_derivedComp_tripleIso X)

variable {B₂ : C₁ ⥤ C₂'} [B₂.Additive] [PreservesFiniteLimits B₂] [PreservesFiniteColimits B₂]
  {B₃ : C₂' ⥤ C₃} [B₃.Additive] [PreservesFiniteLimits B₃] [PreservesFiniteColimits B₃]
  {D₂ : C₁ ⥤ C₂'} [D₂.Additive] [PreservesFiniteLimits D₂] [PreservesFiniteColimits D₂]
  {G₁ : C₀ ⥤ C₁''} [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  {G₂ : C₁'' ⥤ C₂} [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
  {H₂ : C₁'' ⥤ C₂} [H₂.Additive] [PreservesFiniteLimits H₂] [PreservesFiniteColimits H₂]

/-- **A braid relation with a polynomial right-hand side passes to derived categories**: if the
difference of two composites of three whiskered transformations of `A₁ A₂ A₃` is a polynomial in
three whiskered endomorphisms, the same holds for the derived transformations. -/
theorem derivedComp_braidQ_three {X₁ : A₂ ⋙ A₃ ⟶ B₂ ⋙ B₃} {X₂ : A₁ ⋙ B₂ ⟶ A₁ ⋙ D₂}
    {X₃ : D₂ ⋙ B₃ ⟶ A₂ ⋙ A₃} {Y₁ : A₁ ⋙ A₂ ⟶ G₁ ⋙ G₂} {Y₂ : G₂ ⋙ A₃ ⟶ H₂ ⋙ A₃}
    {Y₃ : G₁ ⋙ H₂ ⟶ A₁ ⋙ A₂} {d₁ : A₁ ⟶ A₁} {d₂ : A₂ ⟶ A₂} {d₃ : A₃ ⟶ A₃}
    (P : MvPolynomial (Fin 3) R)
    (h : (Functor.whiskerLeft A₁ X₁ ≫ Functor.whiskerRight X₂ B₃ ≫ Functor.whiskerLeft A₁ X₃ :
        End (A₁ ⋙ A₂ ⋙ A₃)) -
      (Functor.whiskerRight Y₁ A₃ ≫ Functor.whiskerLeft G₁ Y₂ ≫ Functor.whiskerRight Y₃ A₃ :
        End (A₁ ⋙ A₂ ⋙ A₃)) =
      Categorification.KLR.ncEval (A := End (A₁ ⋙ A₂ ⋙ A₃))
        ![Functor.whiskerLeft A₁ (Functor.whiskerLeft A₂ d₃),
          Functor.whiskerLeft A₁ (Functor.whiskerRight d₂ A₃),
          Functor.whiskerRight d₁ (A₂ ⋙ A₃)] P) :
    (Functor.whiskerLeft A₁.mapDerivedCategory (derivedComp X₁) ≫
        ((Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (derivedComp X₂) B₃.mapDerivedCategory ≫
          (Functor.associator _ _ _).hom) ≫
        Functor.whiskerLeft A₁.mapDerivedCategory (derivedComp X₃)) -
      (((Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (derivedComp Y₁) A₃.mapDerivedCategory ≫
          (Functor.associator _ _ _).hom) ≫
        Functor.whiskerLeft G₁.mapDerivedCategory (derivedComp Y₂) ≫
        ((Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (derivedComp Y₃) A₃.mapDerivedCategory ≫
          (Functor.associator _ _ _).hom)) =
      Categorification.KLR.ncEval (A := End (A₁.mapDerivedCategory ⋙ A₂.mapDerivedCategory ⋙
          A₃.mapDerivedCategory))
        ![Functor.whiskerLeft A₁.mapDerivedCategory
            (Functor.whiskerLeft A₂.mapDerivedCategory d₃.mapDerivedCategory),
          Functor.whiskerLeft A₁.mapDerivedCategory
            (Functor.whiskerRight d₂.mapDerivedCategory A₃.mapDerivedCategory),
          Functor.whiskerRight d₁.mapDerivedCategory
            (A₂.mapDerivedCategory ⋙ A₃.mapDerivedCategory)] P := by
  have kL : derivedTripleAlgHom R A₁ A₂ A₃
      (Functor.whiskerLeft A₁ X₁ ≫ Functor.whiskerRight X₂ B₃ ≫ Functor.whiskerLeft A₁ X₃) =
      (Functor.whiskerLeft A₁.mapDerivedCategory (derivedComp X₁) ≫
        Functor.whiskerRight (derivedComp X₂) B₃.mapDerivedCategory ≫
          Functor.whiskerLeft A₁.mapDerivedCategory (derivedComp X₃) :
        End (A₁.mapDerivedCategory ⋙ A₂.mapDerivedCategory ⋙ A₃.mapDerivedCategory)) := by
    refine derivedTripleAlgHom_eq_of ?_
    simp only [Category.assoc, whiskerLeft_derivedComp_tripleIso',
      whiskerLeft_derivedComp_tripleIso'_assoc, whiskerRight_derivedComp_tripleIso_assoc]
    simp only [← mapDerivedCategory_comp]
  have kR : derivedTripleAlgHom R A₁ A₂ A₃
      (Functor.whiskerRight Y₁ A₃ ≫ Functor.whiskerLeft G₁ Y₂ ≫ Functor.whiskerRight Y₃ A₃) =
      (Functor.whiskerRight (derivedComp Y₁) A₃.mapDerivedCategory ≫
        Functor.whiskerLeft G₁.mapDerivedCategory (derivedComp Y₂) ≫
          Functor.whiskerRight (derivedComp Y₃) A₃.mapDerivedCategory :
        End (A₁.mapDerivedCategory ⋙ A₂.mapDerivedCategory ⋙ A₃.mapDerivedCategory)) := by
    refine derivedTripleAlgHom_eq_of ?_
    simp only [Category.assoc, whiskerLeft_derivedComp_tripleIso_assoc,
      whiskerRight_derivedComp_tripleIso', whiskerRight_derivedComp_tripleIso'_assoc]
    simp only [← mapDerivedCategory_comp]
  have e2 : derivedTripleAlgHom R A₁ A₂ A₃ (Functor.whiskerLeft A₁ (Functor.whiskerLeft A₂ d₃)) =
      Functor.whiskerLeft A₁.mapDerivedCategory
        (Functor.whiskerLeft A₂.mapDerivedCategory d₃.mapDerivedCategory) := by
    rw [derivedTripleAlgHom_whiskerLeft]
    exact congrArg (Functor.whiskerLeft A₁.mapDerivedCategory)
      (whiskerLeft_mapDerivedCategory (F := A₂) d₃).symm
  have e1 : derivedTripleAlgHom R A₁ A₂ A₃ (Functor.whiskerLeft A₁ (Functor.whiskerRight d₂ A₃)) =
      Functor.whiskerLeft A₁.mapDerivedCategory
        (Functor.whiskerRight d₂.mapDerivedCategory A₃.mapDerivedCategory) := by
    rw [derivedTripleAlgHom_whiskerLeft]
    exact congrArg (Functor.whiskerLeft A₁.mapDerivedCategory)
      (whiskerRight_mapDerivedCategory (G := A₃) d₂).symm
  have e0 : derivedTripleAlgHom R A₁ A₂ A₃ (Functor.whiskerRight d₁ (A₂ ⋙ A₃)) =
      Functor.whiskerRight d₁.mapDerivedCategory
        (A₂.mapDerivedCategory ⋙ A₃.mapDerivedCategory) := by
    refine (derivedTripleAlgHom_whiskerRight (A₃ := A₃) (Functor.whiskerRight d₁ A₂)).trans ?_
    exact congrArg (fun t => Functor.whiskerRight t A₃.mapDerivedCategory)
      (whiskerRight_mapDerivedCategory (G := A₂) d₁).symm
  have key := congrArg (derivedTripleAlgHom R A₁ A₂ A₃) h
  rw [map_sub, kL, kR, Categorification.KLR.ncEval_map] at key
  refine Eq.trans ?_ (key.trans ?_)
  · congr 1
    · ext X
      simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
        Functor.associator_inv_app, Functor.associator_hom_app, Category.id_comp,
        Category.comp_id]
    · ext X
      simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
        Functor.associator_inv_app, Functor.associator_hom_app, Category.id_comp,
        Category.comp_id]
  · congr 1
    funext a
    fin_cases a
    exacts [e2, e1, e0]

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

/-- **The braid relation with equal outer colours on derived black inductions** between
arbitrary contents, in the shape of `CyclotomicAction.braidLeft_sub_braidRight`. -/
theorem derivedIndCrossOfEq_braidQ (hsym : KLRSymm Q) (i j : I) (hij : i ≠ j)
    {l b c d e f : Multiset I} (h₁ : ({i} : Multiset I) + l = b)
    (h₂ : ({j} : Multiset I) + b = c) (h₃ : ({i} : Multiset I) + c = f)
    (h₄ : ({i} : Multiset I) + b = d) (h₅ : ({j} : Multiset I) + d = f)
    (h₆ : ({j} : Multiset I) + l = e) (h₇ : ({i} : Multiset I) + e = c) :
    (Functor.whiskerLeft (derivedFOfEq Λ hQ i h₁)
        (derivedIndCrossOfEq Λ hQ hsym i j h₂ h₃ h₄ h₅) ≫
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (derivedIndCrossOfEq Λ hQ hsym i i h₁ h₄ h₁ h₄)
          (derivedFOfEq Λ hQ j h₅) ≫
        (Functor.associator _ _ _).hom) ≫
      Functor.whiskerLeft (derivedFOfEq Λ hQ i h₁)
        (derivedIndCrossOfEq Λ hQ hsym j i h₄ h₅ h₂ h₃)) -
    (((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (derivedIndCrossOfEq Λ hQ hsym j i h₁ h₂ h₆ h₇)
          (derivedFOfEq Λ hQ i h₃) ≫
        (Functor.associator _ _ _).hom) ≫
      Functor.whiskerLeft (derivedFOfEq Λ hQ j h₆)
        (derivedIndCrossOfEq Λ hQ hsym i i h₇ h₃ h₇ h₃) ≫
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (derivedIndCrossOfEq Λ hQ hsym i j h₆ h₇ h₁ h₂)
          (derivedFOfEq Λ hQ i h₃) ≫
        (Functor.associator _ _ _).hom)) =
      KLR.ncEval (A := End (derivedFOfEq Λ hQ i h₁ ⋙ derivedFOfEq Λ hQ j h₂ ⋙
          derivedFOfEq Λ hQ i h₃))
        ![Functor.whiskerLeft (derivedFOfEq Λ hQ i h₁)
            (Functor.whiskerLeft (derivedFOfEq Λ hQ j h₂) (derivedIndDotOfEq Λ hQ i h₃)),
          Functor.whiskerLeft (derivedFOfEq Λ hQ i h₁)
            (Functor.whiskerRight (derivedIndDotOfEq Λ hQ j h₂) (derivedFOfEq Λ hQ i h₃)),
          Functor.whiskerRight (derivedIndDotOfEq Λ hQ i h₁)
            (derivedFOfEq Λ hQ j h₂ ⋙ derivedFOfEq Λ hQ i h₃)] (KLR.qbar (Q i j)) := by
  have hL : ∀ (x : I) {μ β : Multiset I} (h : ({x} : Multiset I) + μ = β),
      Limits.PreservesFiniteLimits (blackFOfEq Q Λ x h) := fun x _ _ h =>
    blackFOfEq_preservesFiniteLimits Λ hQ x h
  have hC : ∀ (x : I) {μ β : Multiset I} (h : ({x} : Multiset I) + μ = β),
      Limits.PreservesFiniteColimits (blackFOfEq Q Λ x h) := fun x _ _ h =>
    blackFOfEq_preservesFiniteColimits Λ hQ x h
  unfold derivedIndCrossOfEq derivedIndDotOfEq derivedFOfEq
  have key := NatTrans.derivedComp_braidQ_three (R := k) _
    (indCrossOfEq_braidQ Λ hsym i j hij h₁ h₂ h₃ h₄ h₅ h₆ h₇)
  exact key

end Categorification.Stendhal

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
  {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y] (RD : UDot.WeightDatum C X Y) (Λ₀ : X)
  (hsym : KLRSymm Q)

local notation "𝔼" => blackRouqE Λ hQ RD Λ₀
local notation "𝔻" => blackRouqDot Λ hQ RD Λ₀
local notation "𝕏" => blackRouqCross Λ hQ RD Λ₀ hsym
local notation "𝔽" => derivedFOfEq Λ hQ
local notation "𝕕" => derivedIndDotOfEq Λ hQ
local notation "𝕏'" => derivedIndCrossOfEq Λ hQ hsym
local notation "𝔾" => derivedFBlock Λ hQ RD Λ₀
local notation "𝕤" => blockSucc_step RD Λ₀
local notation "𝕓" => blockSucc RD Λ₀

/-! ### Weight spaces -/

/-- **Endomorphisms of `E_i E_j E_k` compatible with the generators at a block `γ`**: pairs of an
endomorphism of the composite on weight spaces and of the composite of derived black inductions
starting at `γ`, intertwined by the generators `gen₃`. -/
def blackTripleCompat (i j l : I) {w₀ w₁ w₂ w₃ : X} (h₁ : w₀ + RD.iX i = w₁)
    (h₂ : w₁ + RD.iX j = w₂) (h₃ : w₂ + RD.iX l = w₃) (γ : WeightBlocks RD Λ₀ w₀) :
    Subalgebra k (End (𝔼 i h₁ ≫
        (𝔼 j h₂ ≫ 𝔼 l h₃)) ×
      End (𝔽 i (𝕤 i h₁ γ) ⋙
        𝔽 j (𝕤 j h₂ _) ⋙ 𝔽 l (𝕤 l h₃ _))) :=
  compatSubalgebra _ _ (fun M => M γ)
    (Pi.eval _ (𝕓 l h₃ (𝕓 j h₂ (𝕓 i h₁ γ))))
    (fun M => gen₃ (𝕓 i h₁) (𝕓 j h₂) (𝕓 l h₃)
      (𝔾 i h₁) (𝔾 j h₂) (𝔾 l h₃) M γ rfl rfl rfl)

/-- The dots of `E_i E_j E_k` on weight spaces and on blocks are compatible, hence so are their
polynomial evaluations. -/
theorem blackRouqDots_ncEval_mem (i j l : I) {w₀ w₁ w₂ w₃ : X} (h₁ : w₀ + RD.iX i = w₁)
    (h₂ : w₁ + RD.iX j = w₂) (h₃ : w₂ + RD.iX l = w₃) (γ : WeightBlocks RD Λ₀ w₀)
    (p : MvPolynomial (Fin 3) k) :
    (KLR.ncEval (A := End (𝔼 i h₁ ≫
        (𝔼 j h₂ ≫ 𝔼 l h₃)))
      ![𝔼 i h₁ ◁ (𝔼 j h₂ ◁ 𝔻 l h₃),
        𝔼 i h₁ ◁ (𝔻 j h₂ ▷ 𝔼 l h₃),
        𝔻 i h₁ ▷ (𝔼 j h₂ ≫ 𝔼 l h₃)] p,
      KLR.ncEval (A := End (𝔽 i (𝕤 i h₁ γ) ⋙
          𝔽 j (𝕤 j h₂ _) ⋙ 𝔽 l (𝕤 l h₃ _)))
        ![Functor.whiskerLeft (𝔽 i (𝕤 i h₁ γ))
            (Functor.whiskerLeft (𝔽 j (𝕤 j h₂ _))
              (𝕕 l (𝕤 l h₃ _))),
          Functor.whiskerLeft (𝔽 i (𝕤 i h₁ γ))
            (Functor.whiskerRight (𝕕 j (𝕤 j h₂ _))
              (𝔽 l (𝕤 l h₃ _))),
          Functor.whiskerRight (𝕕 i (𝕤 i h₁ γ))
            (𝔽 j (𝕤 j h₂ _) ⋙ 𝔽 l (𝕤 l h₃ _))]
        p) ∈ blackTripleCompat Λ hQ RD Λ₀ i j l h₁ h₂ h₃ γ := by
  intro M
  refine ncEval_compat (𝔼 i h₁ ≫
      (𝔼 j h₂ ≫ 𝔼 l h₃))
    (𝔽 i (𝕤 i h₁ γ) ⋙
      𝔽 j (𝕤 j h₂ _) ⋙ 𝔽 l (𝕤 l h₃ _))
    (fun M => M γ)
    (Pi.eval _ (𝕓 l h₃ (𝕓 j h₂ (𝕓 i h₁ γ))))
    (fun M => gen₃ (𝕓 i h₁) (𝕓 j h₂) (𝕓 l h₃)
      (𝔾 i h₁) (𝔾 j h₂) (𝔾 l h₃) M γ rfl rfl rfl)
    _ _ ?_ p M
  intro c M'
  fin_cases c
  · have d := gen₃_whiskerLeft (𝕓 i h₁) (𝕓 j h₂)
      (𝕓 l h₃) (𝔾 i h₁) (𝔾 j h₂)
      (𝔾 l h₃) (s₂' := 𝕓 j h₂) (s₃' := 𝕓 l h₃)
      (L₂' := 𝔾 j h₂) (L₃' := 𝔾 l h₃)
      (𝔼 j h₂ ◁ 𝔻 l h₃).hom M' γ rfl rfl rfl rfl rfl _
      (gen₂_whiskerLeft_blackRouqDot Λ hQ RD Λ₀ l j h₂ h₃ _ _ rfl rfl)
    exact d
  · have d := gen₃_whiskerLeft (𝕓 i h₁) (𝕓 j h₂)
      (𝕓 l h₃) (𝔾 i h₁) (𝔾 j h₂)
      (𝔾 l h₃) (s₂' := 𝕓 j h₂) (s₃' := 𝕓 l h₃)
      (L₂' := 𝔾 j h₂) (L₃' := 𝔾 l h₃)
      (𝔻 j h₂ ▷ 𝔼 l h₃).hom M' γ rfl rfl rfl rfl rfl _
      (gen₂_blackRouqDot_whiskerRight Λ hQ RD Λ₀ l j h₂ h₃ _ _ rfl rfl)
    exact d
  · have d := gen₃_whiskerRight (𝕓 i h₁) (𝕓 j h₂)
      (𝕓 l h₃) (𝔾 i h₁) (𝔾 j h₂)
      (𝔾 l h₃) (s₁' := 𝕓 i h₁) (s₂' := 𝕓 j h₂)
      (L₁' := 𝔾 i h₁) (L₂' := 𝔾 j h₂)
      (𝔻 i h₁ ▷ 𝔼 j h₂).hom M' γ rfl rfl rfl rfl rfl _
      (gen₂_blackRouqDot_whiskerRight Λ hQ RD Λ₀ j i h₁ h₂ M' γ rfl rfl)
    exact d

/-- The first composite of the braid relation with outer labels `i, i` on weight spaces is
compatible with its blockwise counterpart. -/
theorem blackRouqBraidLeft_mem (i j : I) {w₀ w₁ w₂ w₃ w₅ : X} (h₁ : w₀ + RD.iX i = w₁)
    (h₂ : w₁ + RD.iX j = w₂) (h₃ : w₂ + RD.iX i = w₅) (h₄ : w₁ + RD.iX i = w₃)
    (h₅ : w₃ + RD.iX j = w₅) (γ : WeightBlocks RD Λ₀ w₀) :
    (𝔼 i h₁ ◁ 𝕏 i j h₂ h₃ h₄ h₅ ≫
        ((α_ (𝔼 i h₁) (𝔼 i h₄) (𝔼 j h₅)).inv ≫
          𝕏 i i h₁ h₄ h₁ h₄ ▷ 𝔼 j h₅ ≫
          (α_ (𝔼 i h₁) (𝔼 i h₄) (𝔼 j h₅)).hom) ≫
        𝔼 i h₁ ◁ 𝕏 j i h₄ h₅ h₂ h₃,
      Functor.whiskerLeft (𝔽 i (𝕤 i h₁ γ)) (𝕏' i j (𝕤 j h₂ _) (𝕤 i h₃ _) (𝕤 i h₄ _)
          (blockSucc_eq RD Λ₀ j (blockSucc_comm RD Λ₀ j i h₄ h₅ h₂ h₃ (𝕓 i h₁ γ)))) ≫
        ((Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (𝕏' i i (𝕤 i h₁ γ) (𝕤 i h₄ _) (𝕤 i h₁ γ) (𝕤 i h₄ _))
            (𝔽 j (blockSucc_eq RD Λ₀ j (blockSucc_comm RD Λ₀ j i h₄ h₅ h₂ h₃ (𝕓 i h₁ γ)))) ≫
          (Functor.associator _ _ _).hom) ≫
        Functor.whiskerLeft (𝔽 i (𝕤 i h₁ γ)) (𝕏' j i (𝕤 i h₄ _)
          (blockSucc_eq RD Λ₀ j (blockSucc_comm RD Λ₀ j i h₄ h₅ h₂ h₃ (𝕓 i h₁ γ)))
          (𝕤 j h₂ _) (𝕤 i h₃ _))) ∈
      blackTripleCompat Λ hQ RD Λ₀ i j i h₁ h₂ h₃ γ := by
  intro M
  have q1 := blockSucc_comm RD Λ₀ j i h₄ h₅ h₂ h₃ (𝕓 i h₁ γ)
  have u1 := gen₃_whiskerLeft (𝕓 i h₁) (𝕓 j h₂) (𝕓 i h₃)
      (𝔾 i h₁) (𝔾 j h₂) (𝔾 i h₃)
      (s₂' := 𝕓 i h₄) (s₃' := 𝕓 j h₅) (L₂' := 𝔾 i h₄)
      (L₃' := 𝔾 j h₅) (𝕏 i j h₂ h₃ h₄ h₅).hom M γ
      rfl rfl rfl rfl q1 _ (gen₂_blackRouqCross Λ hQ RD Λ₀ hsym i j h₂ h₃ h₄ h₅ _ _ rfl rfl rfl q1)
  have u3 := gen₃_whiskerRight (𝕓 i h₁) (𝕓 i h₄) (𝕓 j h₅)
      (𝔾 i h₁) (𝔾 i h₄) (𝔾 j h₅)
      (s₁' := 𝕓 i h₁) (s₂' := 𝕓 i h₄) (L₁' := 𝔾 i h₁)
      (L₂' := 𝔾 i h₄) (𝕏 i i h₁ h₄ h₁ h₄).hom M γ
      rfl rfl rfl rfl q1 _ (gen₂_blackRouqCross Λ hQ RD Λ₀ hsym i i h₁ h₄ h₁ h₄ M γ rfl rfl rfl rfl)
  have u5 := gen₃_whiskerLeft (𝕓 i h₁) (𝕓 i h₄) (𝕓 j h₅)
      (𝔾 i h₁) (𝔾 i h₄) (𝔾 j h₅)
      (s₂' := 𝕓 j h₂) (s₃' := 𝕓 i h₃) (L₂' := 𝔾 j h₂)
      (L₃' := 𝔾 i h₃) (𝕏 j i h₄ h₅ h₂ h₃).hom M γ
      rfl rfl q1 rfl rfl _ (gen₂_blackRouqCross Λ hQ RD Λ₀ hsym j i h₄ h₅ h₂ h₃ _ _ rfl q1 rfl rfl)
  exact gen_chain_left u1 (gen_assoc _) u3 (gen_assoc _) u5

/-- The second composite of the braid relation with outer labels `i, i` on weight spaces is
compatible with its blockwise counterpart. -/
theorem blackRouqBraidRight_mem (i j : I) {w₀ w₁ w₂ w₄ w₅ : X} (h₁ : w₀ + RD.iX i = w₁)
    (h₂ : w₁ + RD.iX j = w₂) (h₃ : w₂ + RD.iX i = w₅) (h₆ : w₀ + RD.iX j = w₄)
    (h₇ : w₄ + RD.iX i = w₂) (γ : WeightBlocks RD Λ₀ w₀) :
    (((α_ (𝔼 i h₁) (𝔼 j h₂)
          (𝔼 i h₃)).inv ≫
        𝕏 j i h₁ h₂ h₆ h₇ ▷ 𝔼 i h₃ ≫
        (α_ (𝔼 j h₆) (𝔼 i h₇) (𝔼 i h₃)).hom) ≫
        𝔼 j h₆ ◁ 𝕏 i i h₇ h₃ h₇ h₃ ≫
        ((α_ (𝔼 j h₆) (𝔼 i h₇) (𝔼 i h₃)).inv ≫
          𝕏 i j h₆ h₇ h₁ h₂ ▷ 𝔼 i h₃ ≫
          (α_ (𝔼 i h₁) (𝔼 j h₂) (𝔼 i h₃)).hom),
      ((Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (𝕏' j i (𝕤 i h₁ γ) (𝕤 j h₂ _) (𝕤 j h₆ γ)
            (blockSucc_eq RD Λ₀ i (blockSucc_comm RD Λ₀ i j h₆ h₇ h₁ h₂ γ))) (𝔽 i (𝕤 i h₃ _)) ≫
          (Functor.associator _ _ _).hom) ≫
        Functor.whiskerLeft (𝔽 j (𝕤 j h₆ γ))
          (𝕏' i i (blockSucc_eq RD Λ₀ i (blockSucc_comm RD Λ₀ i j h₆ h₇ h₁ h₂ γ)) (𝕤 i h₃ _)
            (blockSucc_eq RD Λ₀ i (blockSucc_comm RD Λ₀ i j h₆ h₇ h₁ h₂ γ)) (𝕤 i h₃ _)) ≫
        ((Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (𝕏' i j (𝕤 j h₆ γ)
            (blockSucc_eq RD Λ₀ i (blockSucc_comm RD Λ₀ i j h₆ h₇ h₁ h₂ γ)) (𝕤 i h₁ γ)
            (𝕤 j h₂ _)) (𝔽 i (𝕤 i h₃ _)) ≫
          (Functor.associator _ _ _).hom)) ∈
      blackTripleCompat Λ hQ RD Λ₀ i j i h₁ h₂ h₃ γ := by
  intro M
  have q2 := blockSucc_comm RD Λ₀ i j h₆ h₇ h₁ h₂ γ
  have v2 := gen₃_whiskerRight (𝕓 i h₁) (𝕓 j h₂) (𝕓 i h₃)
      (𝔾 i h₁) (𝔾 j h₂) (𝔾 i h₃)
      (s₁' := 𝕓 j h₆) (s₂' := 𝕓 i h₇) (L₁' := 𝔾 j h₆)
      (L₂' := 𝔾 i h₇) (𝕏 j i h₁ h₂ h₆ h₇).hom M γ
      rfl rfl rfl q2 rfl _ (gen₂_blackRouqCross Λ hQ RD Λ₀ hsym j i h₁ h₂ h₆ h₇ M γ rfl rfl rfl q2)
  have v4 := gen₃_whiskerLeft (𝕓 j h₆) (𝕓 i h₇) (𝕓 i h₃)
      (𝔾 j h₆) (𝔾 i h₇) (𝔾 i h₃)
      (s₂' := 𝕓 i h₇) (s₃' := 𝕓 i h₃) (L₂' := 𝔾 i h₇)
      (L₃' := 𝔾 i h₃) (𝕏 i i h₇ h₃ h₇ h₃).hom M γ
      rfl q2 rfl q2 rfl _ (gen₂_blackRouqCross Λ hQ RD Λ₀ hsym i i h₇ h₃ h₇ h₃ _ _ q2 rfl q2 rfl)
  have v6 := gen₃_whiskerRight (𝕓 j h₆) (𝕓 i h₇) (𝕓 i h₃)
      (𝔾 j h₆) (𝔾 i h₇) (𝔾 i h₃)
      (s₁' := 𝕓 i h₁) (s₂' := 𝕓 j h₂) (L₁' := 𝔾 i h₁)
      (L₂' := 𝔾 j h₂) (𝕏 i j h₆ h₇ h₁ h₂).hom M γ
      rfl q2 rfl rfl rfl _ (gen₂_blackRouqCross Λ hQ RD Λ₀ hsym i j h₆ h₇ h₁ h₂ M γ rfl q2 rfl rfl)
  exact gen_chain_right (gen_assoc _) v2 (gen_assoc _) v4 (gen_assoc _) v6 (gen_assoc _)

/-- **The braid relation with equal outer labels on weight spaces** (Brundan,
arXiv:1501.00350v1, (1.4) for outer labels `i, i` and middle label `j ≠ i`): the field `braidQ`
of `TwoRep.RouqUpKLR` for the Rouquier generators `blackRouqData` on derived categories of
`T^λ`-modules. The difference of the two composites of crossings on `E_i E_j E_i` is `Q̄_ij`
evaluated at the three dots. -/
theorem blackRouqCross_braidQ (i j : I) (hij : i ≠ j) {w₀ w₁ w₂ w₃ w₄ w₅ : X}
    (h₁ : w₀ + RD.iX i = w₁) (h₂ : w₁ + RD.iX j = w₂) (h₃ : w₂ + RD.iX i = w₅)
    (h₄ : w₁ + RD.iX i = w₃) (h₅ : w₃ + RD.iX j = w₅)
    (h₆ : w₀ + RD.iX j = w₄) (h₇ : w₄ + RD.iX i = w₂) :
    (𝔼 i h₁ ◁ 𝕏 i j h₂ h₃ h₄ h₅ ≫
      ((α_ (𝔼 i h₁) (𝔼 i h₄) (𝔼 j h₅)).inv ≫
        𝕏 i i h₁ h₄ h₁ h₄ ▷ 𝔼 j h₅ ≫
        (α_ (𝔼 i h₁) (𝔼 i h₄) (𝔼 j h₅)).hom) ≫
      𝔼 i h₁ ◁ 𝕏 j i h₄ h₅ h₂ h₃) -
    (((α_ (𝔼 i h₁) (𝔼 j h₂) (𝔼 i h₃)).inv ≫
      𝕏 j i h₁ h₂ h₆ h₇ ▷ 𝔼 i h₃ ≫
      (α_ (𝔼 j h₆) (𝔼 i h₇) (𝔼 i h₃)).hom) ≫
      𝔼 j h₆ ◁ 𝕏 i i h₇ h₃ h₇ h₃ ≫
      ((α_ (𝔼 j h₆) (𝔼 i h₇) (𝔼 i h₃)).inv ≫
        𝕏 i j h₆ h₇ h₁ h₂ ▷ 𝔼 i h₃ ≫
        (α_ (𝔼 i h₁) (𝔼 j h₂) (𝔼 i h₃)).hom)) =
      KLR.ncEval (A := End (𝔼 i h₁ ≫
          (𝔼 j h₂ ≫ 𝔼 i h₃)))
        ![𝔼 i h₁ ◁ (𝔼 j h₂ ◁ 𝔻 i h₃),
          𝔼 i h₁ ◁ (𝔻 j h₂ ▷ 𝔼 i h₃),
          𝔻 i h₁ ▷ (𝔼 j h₂ ≫ 𝔼 i h₃)]
        (KLR.qbar (Q i j)) := by
  apply ObjectProperty.hom_ext
  refine NatTrans.ext (funext fun M => ?_)
  refine gen₃_ext (𝕓 i h₁) (𝕓 j h₂) (𝕓 i h₃)
    (𝔾 i h₁) (𝔾 j h₂) (𝔾 i h₃)
    fun γ β δ μ hβ hδ hμ => ?_
  subst hβ hδ hμ
  have hS := Subalgebra.sub_mem _ (blackRouqBraidLeft_mem Λ hQ RD Λ₀ hsym i j h₁ h₂ h₃ h₄ h₅ γ)
    (blackRouqBraidRight_mem Λ hQ RD Λ₀ hsym i j h₁ h₂ h₃ h₆ h₇ γ)
  rw [Prod.mk_sub_mk, derivedIndCrossOfEq_braidQ Λ hQ hsym i j hij] at hS
  exact (hS M).trans
    (blackRouqDots_ncEval_mem Λ hQ RD Λ₀ i j i h₁ h₂ h₃ γ (KLR.qbar (Q i j)) M).symm


end Categorification.Stendhal
