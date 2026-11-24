/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.WeightModuleExactTriangle
import Categorification.WeightedKLR.Rigidity.FundamentalBraidGradedCoend
import Categorification.Algebra.DiagramWeightCorner
import DG.Category.SubQuotient

/-!
# The two-stage projective model of the graded fundamental middle head

For Webster, arXiv:1309.3796v2, §7.1, Lemma 7.3 and Proposition 7.11, the
two projective resolution maps give an iterated cone on the loading
projectives of the identity braid corner. Its augmentation to the middle
simple is a quasi-isomorphism. This gives a model for the derived braid.
-/

noncomputable section
namespace Categorification.Stendhal.FundamentalCorner
open CategoryTheory CategoryTheory.Pretriangulated DG DG.CatModule
universe u v w
variable {C : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [DGCategory C]
  {A B E S : CatModule.{w} C} (f : A ⟶ B) (g : B ⟶ E) (a : E ⟶ S)
  (fg : f ≫ g = 0) (ga : g ≫ a = 0)

omit [DGCategory C] in
private theorem evaluation_zero {U V : CatModule.{w} C} (φ : U ⟶ V) (h : φ = 0)
    (X : C) (x : U.obj X) : φ.app X x = 0 :=
  congrArg (fun z : U ⟶ V => z.app X x) h

include ga in
private theorem descent_aug_zero :
    coneDescent f g fg ≫ a = 0 := by
  apply CatModule.Hom.ext
  intro X x
  exact evaluation_zero _ ga X (cone.sndAddHom f X x)

/-- The quotient augmentation on the cone of the two projective-resolution maps. -/
def weightTwoStageAugmentation : cone (coneDescent f g fg) ⟶ S :=
  coneDescent _ a (descent_aug_zero f g a fg ga)

private theorem iso_cone_map_of_quasiIso {A₁ B₁ A₂ B₂ : CatModule.{w} C}
    (q : A₁ ⟶ B₁) (r : A₂ ⟶ B₂) (l : A₁ ⟶ A₂) (m : B₁ ⟶ B₂)
    (h : q ≫ m = l ≫ r) (hl : IsQuasiIso l) (hm : IsQuasiIso m) :
    IsQuasiIso (cone.map l m h) := by
  let _ := CatModule.HasDerivedCategory.standard.{w} C
  let Q := CatModule.DerivedCategory.Q (C := C)
  let d := Q.mapTriangle.map (cone.triangleMap q r l m h)
  have hd (U V : CatModule.{w} C) (t : U ⟶ V) :
      Q.mapTriangle.obj (cone.triangle t) ∈ distTriang _ :=
    (CatModule.DerivedCategory.mem_distTriang_iff _).mpr ⟨_, _, t, ⟨Iso.refl _⟩⟩
  exact (CatModule.DerivedCategory.isIso_Q_map_iff _).mp
    (isIso₃_of_isIso₁₂ d (hd _ _ q) (hd _ _ r)
      ((CatModule.DerivedCategory.isIso_Q_map_iff _).mpr hl)
      ((CatModule.DerivedCategory.isIso_Q_map_iff _).mpr hm))

/-- A pointwise exact augmented length-two sequence of diagram-weight modules
gives a quasi-isomorphism from its iterated cone to the quotient. -/
theorem weightTwoStageAugmentation_quasiIso
    (hinj : ∀ X, Function.Injective (f.app X)) (hex : ∀ X, Function.Exact (f.app X) (g.app X))
    (hex' : ∀ X, Function.Exact (g.app X) (a.app X)) (hsur : ∀ X, Function.Surjective (a.app X)) :
    IsQuasiIso (weightTwoStageAugmentation f g a fg ga) := by
  let J := g.range
  let g' := CatSubmodule.codRestrict (S := J) g (fun _ x => ⟨x,rfl⟩)
  have fg' : f ≫ g' = 0 := CatModule.Hom.ext fun X x => Subtype.ext (evaluation_zero _ fg X x)
  let k := coneDescent f g' fg'
  have hk : IsQuasiIso k := by
    apply coneDescent_quasiIso _ _ _ hinj
    · intro X y
      exact (Subtype.ext_iff.trans (hex X y))
    · intro X ⟨z,y,hy⟩
      exact ⟨y,Subtype.ext hy⟩
  have ja : J.subtype ≫ a = 0 := by
    apply CatModule.Hom.ext
    rintro X ⟨z,y,rfl⟩
    exact evaluation_zero _ ga X y
  let j := coneDescent J.subtype a ja
  have hj : IsQuasiIso j := by
    apply coneDescent_quasiIso _ _ _ J.subtype_injective _ hsur
    intro X y
    exact (hex' X y).trans ⟨fun hy => ⟨⟨y,hy⟩,rfl⟩,
      fun ⟨t,ht⟩ => ht ▸ t.property⟩
  have sq : coneDescent f g fg ≫ 𝟙 E = k ≫ J.subtype := CatModule.Hom.ext fun _ _ => rfl
  have hc := iso_cone_map_of_quasiIso _ _ k (𝟙 E) sq hk (isQuasiIso_id E)
  have hcomp : cone.map k (𝟙 E) sq ≫ j = weightTwoStageAugmentation f g a fg ga :=
    CatModule.Hom.ext fun _ _ => rfl
  rw [← hcomp]
  exact hc.comp hj
end Categorification.Stendhal.FundamentalCorner

namespace Categorification.Stendhal.FundamentalCorner
open CategoryTheory DG CatModule BraidedStendhalAlgebra
open scoped DG.DegreeZero
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance] fundamentalBraidSourceCornerGrades fundamentalBraidSourceCornerInternal
  fundamentalBraidSourceCornerBigraded fundamentalBraidSourceOrderedInternal fundamentalBraidSourceOrderedBigraded
local notation "ν" => ({()} : Multiset Unit)
local notation "R" => ViolOrderCorner (k := ℚ) (Q := Q) (Λ := wt) («ν» := ν) (List.finRange 2)
private theorem mOrdered : IsRedOrdered middle := by unfold IsRedOrdered; decide +kernel
local notation "L₂" => fundamentalBraidSourceLoadingIso middle mOrdered 2
local notation "L₁" => fundamentalBraidSourceLoadingIso terminal terminal_ordered 1
local notation "L₀" => fundamentalBraidSourceLoadingIso middle mOrdered 0
local notation "res" => CatModule.precomp fundamentalBraidSourceWeightFunctor
local notation "f₂" => fundamentalBraidGradedSourceD₂
local notation "f₁" => fundamentalBraidGradedSourceD₁

/-- The middle character on the generating-weight-zero source loading projective. -/
abbrev fundamentalBraidGradedSourceAugmentation := (L₀).hom ≫ (res).map gradedMiddleAugmentation
local notation "a₀" => fundamentalBraidGradedSourceAugmentation

private def appEquiv {C : Type*} [Category C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
    {M N : CatModule C} (e : M ≅ N) (X : C) : M.obj X ≃+ N.obj X where
  __ := e.hom.app X
  invFun := e.inv.app X
  left_inv x := congrArg (fun a : M ⟶ M => a.app X x) e.hom_inv_id
  right_inv x := congrArg (fun a : N ⟶ N => a.app X x) e.inv_hom_id

private theorem exact_conjugate {A B C A' B' C' : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
    (eA : A' ≃+ A) (eB : B' ≃+ B) (eC : C' ≃+ C)
    (f : A →+ B) (g : B →+ C) (h : Function.Exact f g) :
    Function.Exact (fun x => eB.symm (f (eA x))) (fun y => eC.symm (g (eB y))) := by
  intro y
  rw [map_eq_zero_iff _ eC.symm.injective, h]
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨eA.symm x, by change eB.symm (f (eA (eA.symm x))) = y; rw [eA.apply_symm_apply,hx,eB.symm_apply_apply]⟩
  · rintro ⟨x,hx⟩
    exact ⟨eA x, (eB.apply_symm_apply _).symm.trans (congrArg eB hx)⟩

private theorem sourceExact (X : WeightCategory Rᵐᵒᵖ) :
    Function.Injective ((f₂).app X) ∧ Function.Exact ((f₂).app X) ((f₁).app X) ∧
      Function.Exact ((f₁).app X) ((a₀).app X) ∧ Function.Surjective ((a₀).app X) := by
  obtain ⟨hi, hf, hg, hs⟩ := fundamentalBraidSourceGradedResolution X
  let l₂ := appEquiv L₂ X
  let l₁ := appEquiv L₁ X
  let l₀ := appEquiv L₀ X
  exact ⟨l₁.symm.injective.comp (hi.comp l₂.injective),
    exact_conjugate l₂ l₁ l₀ _ _ hf,
    exact_conjugate l₁ l₀ (AddEquiv.refl _) _ _ hg, hs.comp l₀.surjective⟩

/-- Consecutive mixed crossings in the source resolution compose to zero. -/
theorem fundamentalBraidGradedSource_comp_zero : f₂ ≫ f₁ = 0 := by
  apply CatModule.Hom.ext
  intro X x
  exact ((sourceExact X).2.1 _).mpr ⟨x,rfl⟩

private theorem gradedBraidAug_zero : f₁ ≫ a₀ = 0 := by
  apply CatModule.Hom.ext
  intro X x
  exact ((sourceExact X).2.2.1 _).mpr ⟨x,rfl⟩

/-- The iterated mapping cone of the two source mixed crossings in the
fundamental case of Webster v2, §7.1, Proposition 7.11. -/
def fundamentalBraidGradedResolutionModel : CatModule.{0} (WeightCategory Rᵐᵒᵖ) :=
  cone (coneDescent f₂ f₁ fundamentalBraidGradedSource_comp_zero)

/-- The two-stage resolution is K-projective over the source weight category. -/
theorem fundamentalBraidGradedResolutionModel_isKProjective :
    IsKProjective fundamentalBraidGradedResolutionModel :=
  IsKProjective.cone (IsKProjective.cone (isKProjective_corner _) (isKProjective_corner _))
    (isKProjective_corner _)

/-- The augmentation from the two-stage model to the fundamental middle simple. -/
def fundamentalBraidGradedResolutionAugmentation :
    fundamentalBraidGradedResolutionModel ⟶ fundamentalBraidSourceGradedHead :=
  weightTwoStageAugmentation f₂ f₁ a₀ fundamentalBraidGradedSource_comp_zero gradedBraidAug_zero

/-- The augmented loading resolution represents the graded middle simple
in the source derived category (Webster v2, Lemma 7.3 and Proposition 7.11). -/
theorem fundamentalBraidGradedResolutionAugmentation_quasiIso :
    IsQuasiIso fundamentalBraidGradedResolutionAugmentation :=
  weightTwoStageAugmentation_quasiIso f₂ f₁ a₀ fundamentalBraidGradedSource_comp_zero gradedBraidAug_zero
    (fun X => (sourceExact X).1) (fun X => (sourceExact X).2.1)
    (fun X => (sourceExact X).2.2.1) (fun X => (sourceExact X).2.2.2)

attribute [local instance] fundamentalBraidCoendTargetCornerGrades fundamentalBraidCoendTargetInternal
  fundamentalBraidCoendTargetBigraded
local notation "κ₁" => ([1,0] : List (Fin 2))
local notation "U" => ViolOrderCorner (k := ℚ) (Q := Q) (Λ := wt) («ν» := ν) κ₁
local notation "V" => violAuxiliaryGrade («ν» := ν) grading
local notation "he" => isIdempotentElem_violMk_redProj ℚ Q wt ν
local notation "h₀" => redProj_mem_violAuxiliaryGrade grading
local notation "DF" => diagramCornerWeightDerivedRightTensor V (he (List.finRange 2)) (he κ₁)
  (h₀ (List.finRange 2)) (h₀ κ₁)
local notation "D" => diagramCornerWeightRightBimodule V (he (List.finRange 2)) (he κ₁)
  (h₀ (List.finRange 2)) (h₀ κ₁)

universe z
variable [CatModule.HasDerivedCategory.{z,0} (WeightCategory Rᵐᵒᵖ)]
  [CatModule.HasDerivedCategory.{z,0} (WeightCategory Uᵐᵒᵖ)]

/-- The derived fundamental braid evaluated on the middle simple is represented
by tensoring its two-stage loading resolution (Webster v2, Proposition 7.11). -/
def fundamentalBraidGradedDerivedModelIso :
    (DF).obj (CatModule.DerivedCategory.Q.obj fundamentalBraidSourceGradedHead) ≅
      CatModule.DerivedCategory.Q.obj ((D).tensorFunctor.obj fundamentalBraidGradedResolutionModel) := by
  let Q₀ : CatModule.{0} (WeightCategory Rᵐᵒᵖ) ⥤ CatModule.DerivedCategory.{z,0} (WeightCategory Rᵐᵒᵖ) :=
    CatModule.DerivedCategory.Q
  let K := fundamentalBraidGradedResolutionModel
  let a := fundamentalBraidGradedResolutionAugmentation
  have hi : IsIso (Q₀.map a) := (CatModule.DerivedCategory.isIso_Q_map_iff _).mpr
    fundamentalBraidGradedResolutionAugmentation_quasiIso
  refine ((DF).mapIso (@asIso _ _ _ _ (Q₀.map a) hi)).symm ≪≫ ?_
  apply diagramCornerWeightDerivedRightTensorIsoOfResolution V (he (List.finRange 2)) (he κ₁)
    (h₀ (List.finRange 2)) (h₀ κ₁) (𝟙 K) fundamentalBraidGradedResolutionModel_isKProjective
    (isQuasiIso_id K)
  change IsQuasiIso ((D).tensorFunctor.map (𝟙 K))
  rw [CategoryTheory.Functor.map_id]
  exact isQuasiIso_id _
end Categorification.Stendhal.FundamentalCorner
