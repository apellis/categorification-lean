/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KLR.MatEndModuleCross
import Categorification.Diagrams.KLR.MatEndModuleNaturality

/-!
# Naturality of restriction and induction along different matrix maps

The identifications `resIndCrossModuleEquiv` and `indResCrossModuleEquiv` of
`Res_{φ₁'} (Ind M φ₁)` and `Ind (Res_{φ₂} M) φ₂'` with module functors are natural in the
module, and hence so is the isomorphism `Res_{φ₁'} (Ind M φ₁) ≅ Ind (Res_{φ₂} M) φ₂'`
(`MatEnd.resIndEquivIndResCross_map`). This is the module-map compatibility of the relation
`Eⱼ Fᵢ ≅ Fᵢ Eⱼ` (`i ≠ j`) of Webster, arXiv:1309.3796v3, Theorem 4.31, used for the tensor
factors in the proof of Proposition 5.5 there.
-/

noncomputable section

namespace Categorification

/-- `LinearEquiv.ofSemilinearTrans` is natural: maps compatible with the three given
equivalences are carried to each other. -/
theorem LinearEquiv.ofSemilinearTrans_naturality {R S : Type*} [Ring R] [Ring S] (σ : R ≃+* S)
    {U V T T' U₂ V₂ T₂ T₂' : Type*} [AddCommGroup U] [AddCommGroup V] [AddCommGroup T]
    [AddCommGroup T'] [Module R U] [Module R V] [Module S T] [Module S T']
    [AddCommGroup U₂] [AddCommGroup V₂] [AddCommGroup T₂] [AddCommGroup T₂'] [Module R U₂]
    [Module R V₂] [Module S T₂] [Module S T₂']
    (eU : U ≃ₗ[ℤ] T) (heU : ∀ (a : R) (x : U), eU (a • x) = σ a • eU x) (f : T ≃ₗ[S] T')
    (eV : V ≃ₗ[ℤ] T') (heV : ∀ (a : R) (x : V), eV (a • x) = σ a • eV x)
    (eU₂ : U₂ ≃ₗ[ℤ] T₂) (heU₂ : ∀ (a : R) (x : U₂), eU₂ (a • x) = σ a • eU₂ x)
    (f₂ : T₂ ≃ₗ[S] T₂') (eV₂ : V₂ ≃ₗ[ℤ] T₂')
    (heV₂ : ∀ (a : R) (x : V₂), eV₂ (a • x) = σ a • eV₂ x)
    (gU : U → U₂) (gT : T → T₂) (gT' : T' → T₂') (gV : V → V₂)
    (hU : ∀ x, eU₂ (gU x) = gT (eU x)) (hf : ∀ y, f₂ (gT y) = gT' (f y))
    (hV : ∀ z, eV₂ (gV z) = gT' (eV z)) (x : U) :
    LinearEquiv.ofSemilinearTrans σ eU₂ heU₂ f₂ eV₂ heV₂ (gU x) =
      gV (LinearEquiv.ofSemilinearTrans σ eU heU f eV heV x) := by
  apply eV₂.injective
  change eV₂ (eV₂.symm (f₂ (eU₂ (gU x)))) = eV₂ (gV (eV.symm (f (eU x))))
  rw [LinearEquiv.apply_symm_apply, hU, hf, hV, LinearEquiv.apply_symm_apply]

end Categorification

namespace Categorification.KLR.Diagram

open CategoryTheory CategoryTheory.Idempotents Preadditive MulOpposite InductionAlong

namespace MatEnd

universe v w

attribute [local instance] HomTensor.bimodule

variable {C : Type*} [Category.{v} C] [Preadditive C] {C' : Type*} [Category.{v} C']
  [Preadditive C'] {D : Type*} [Category.{v} D] [Preadditive D] {C₂ : Type*}
  [Category.{v} C₂] [Preadditive C₂]
  {ι ι' κ κ₂ : Type w} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
  [Fintype κ] [DecidableEq κ] [Fintype κ₂] [DecidableEq κ₂]
  {X : ι → C} {X' : ι' → C'} {Y : κ → D} {Z : κ₂ → C₂}
  {M M₂ : Type (max w v)} [AddCommGroup M] [Module (MatEnd X)ᵐᵒᵖ M] [AddCommGroup M₂]
  [Module (MatEnd X)ᵐᵒᵖ M₂] (f : M →ₗ[(MatEnd X)ᵐᵒᵖ] M₂)

section ResInd

variable (F₁ : C ⥤ D) [F₁.Additive] {e₁ : ι → κ} (he₁ : Function.Injective e₁)
  (h₁ : ∀ i, F₁.obj (X i) = Y (e₁ i))
  (F₁' : C' ⥤ D) [F₁'.Additive] {e₁' : ι' → κ} (he₁' : Function.Injective e₁')
  (h₁' : ∀ i, F₁'.obj (X' i) = Y (e₁' i))
  {E₁' : Karoubi (Mat_ D) ⥤ Karoubi (Mat_ C')} (adj₁' : mapKaroubi F₁'.mapMat_ ⊣ E₁')
  [E₁'.Additive]

/-- `resIndCrossModuleEquiv` is natural in the module. -/
theorem resIndCrossModuleEquiv_map
    (m : Res (mapEmbOp F₁' he₁' h₁') (Ind M (mapEmbOp F₁ he₁ h₁))) :
    letI := HomTensor.transferModule (karoubiMatrixOp X) M
    letI := HomTensor.transferModule (karoubiMatrixOp X) M₂
    resIndCrossModuleEquiv M₂ F₁ he₁ h₁ F₁' he₁' h₁' adj₁' (Res.map (Ind.map f) m) =
      BalancedTensor.mapRight (HomTensor.transferLinearMap (karoubiMatrixOp X) f)
        (resIndCrossModuleEquiv M F₁ he₁ h₁ F₁' he₁' h₁' adj₁' m) := by
  let _ := HomTensor.transferModule (karoubiMatrixOp X) M
  let _ := HomTensor.transferModule (karoubiMatrixOp X) M₂
  let _ := HomTensor.transferModule (karoubiMatrixOpY Y) (Ind M (mapEmbOp F₁ he₁ h₁))
  let _ := HomTensor.transferModule (karoubiMatrixOpY Y) (Ind M₂ (mapEmbOp F₁ he₁ h₁))
  exact (congrArg (HomTensor.compModuleEquiv ℤ (mapKaroubi F₁.mapMat_) E₁' _ _ _
      (fun _ : Unit => karoubiSect F₁ h₁) (fun _ => karoubiGen F₁ he₁ h₁)
      (karoubiSect_gen_sum F₁ he₁ h₁) M₂)
    (BalancedTensor.congrRight_mapRight (indModuleLinearEquiv F₁ he₁ h₁ M)
      (indModuleLinearEquiv F₁ he₁ h₁ M₂)
      (HomTensor.transferLinearMap (karoubiMatrixOpY Y) (Ind.map f))
      (BalancedTensor.mapRight (HomTensor.transferLinearMap (karoubiMatrixOp X) f))
      (fun x => indModuleEquiv_map F₁ he₁ h₁ f x)
      (resModuleEquiv F₁' he₁' h₁' adj₁' (Ind M (mapEmbOp F₁ he₁ h₁)) m))).trans
    (HomTensor.compModuleEquiv_mapRight _ _ _ _ _ _ _ _ _ _)

end ResInd

section IndRes

variable (F₂ : C₂ ⥤ C) [F₂.Additive] {e₂ : κ₂ → ι} (he₂ : Function.Injective e₂)
  (h₂ : ∀ j, F₂.obj (Z j) = X (e₂ j))
  {E₂ : Karoubi (Mat_ C) ⥤ Karoubi (Mat_ C₂)} (adj₂ : mapKaroubi F₂.mapMat_ ⊣ E₂)
  [E₂.Additive]
  (F₂' : C₂ ⥤ C') [F₂'.Additive] {e₂' : κ₂ → ι'} (he₂' : Function.Injective e₂')
  (h₂' : ∀ j, F₂'.obj (Z j) = X' (e₂' j))
  {J : Type*} [Fintype J]
  (π : J → (E₂.obj ((toKaroubi _).obj (familySum X)) ⟶ (toKaroubi _).obj (familySum Z)))
  (ι₁ : J → ((toKaroubi _).obj (familySum Z) ⟶ E₂.obj ((toKaroubi _).obj (familySum X))))
  (hπ : ∑ j, π j ≫ ι₁ j = 𝟙 _)

/-- `indResCrossModuleEquiv` is natural in the module. -/
theorem indResCrossModuleEquiv_map
    (x : Ind (Res (mapEmbOp F₂ he₂ h₂) M) (mapEmbOp F₂' he₂' h₂')) :
    letI := HomTensor.transferModule (karoubiMatrixOpY X) M
    letI := HomTensor.transferModule (karoubiMatrixOpY X) M₂
    indResCrossModuleEquiv M₂ F₂ he₂ h₂ adj₂ F₂' he₂' h₂' π ι₁ hπ (Ind.map (Res.map f) x) =
      BalancedTensor.mapRight (HomTensor.transferLinearMap (karoubiMatrixOpY X) f)
        (indResCrossModuleEquiv M F₂ he₂ h₂ adj₂ F₂' he₂' h₂' π ι₁ hπ x) := by
  let _ := HomTensor.transferModule (karoubiMatrixOpY X) M
  let _ := HomTensor.transferModule (karoubiMatrixOpY X) M₂
  let _ := HomTensor.transferModule (karoubiMatrixOp Z) (Res (mapEmbOp F₂ he₂ h₂) M)
  let _ := HomTensor.transferModule (karoubiMatrixOp Z) (Res (mapEmbOp F₂ he₂ h₂) M₂)
  exact (congrArg (HomTensor.compModuleEquiv ℤ E₂ (mapKaroubi F₂'.mapMat_) _ _ _ π ι₁ hπ M₂)
    ((congrArg (BalancedTensor.congrRight (k := ℤ)
      (B := (End ((toKaroubi _).obj (familySum X')))ᵐᵒᵖ)
      (M := (toKaroubi _).obj (familySum X') ⟶
        (mapKaroubi F₂'.mapMat_).obj ((toKaroubi _).obj (familySum Z)))
      (resModuleLinearEquiv F₂ he₂ h₂ adj₂ M₂))
      (indModuleEquiv_map F₂' he₂' h₂' (Res.map f) x)).trans
    (BalancedTensor.congrRight_mapRight (resModuleLinearEquiv F₂ he₂ h₂ adj₂ M)
      (resModuleLinearEquiv F₂ he₂ h₂ adj₂ M₂)
      (HomTensor.transferLinearMap (karoubiMatrixOp Z) (Res.map f))
      (BalancedTensor.mapRight (HomTensor.transferLinearMap (karoubiMatrixOpY X) f))
      (fun m => resModuleEquiv_map F₂ he₂ h₂ adj₂ f m)
      (indModuleEquiv F₂' he₂' h₂' (Res (mapEmbOp F₂ he₂ h₂) M) x)))).trans
    (HomTensor.compModuleEquiv_mapRight _ _ _ _ _ _ _ _ _ _)

end IndRes

variable (F₁ : C ⥤ D) [F₁.Additive] {e₁ : ι → κ} (he₁ : Function.Injective e₁)
  (h₁ : ∀ i, F₁.obj (X i) = Y (e₁ i))
  (F₁' : C' ⥤ D) [F₁'.Additive] {e₁' : ι' → κ} (he₁' : Function.Injective e₁')
  (h₁' : ∀ i, F₁'.obj (X' i) = Y (e₁' i))
  {E₁' : Karoubi (Mat_ D) ⥤ Karoubi (Mat_ C')} (adj₁' : mapKaroubi F₁'.mapMat_ ⊣ E₁')
  [E₁'.Additive]
  (F₂ : C₂ ⥤ C) [F₂.Additive] {e₂ : κ₂ → ι} (he₂ : Function.Injective e₂)
  (h₂ : ∀ j, F₂.obj (Z j) = X (e₂ j))
  {E₂ : Karoubi (Mat_ C) ⥤ Karoubi (Mat_ C₂)} (adj₂ : mapKaroubi F₂.mapMat_ ⊣ E₂)
  [E₂.Additive]
  (F₂' : C₂ ⥤ C') [F₂'.Additive] {e₂' : κ₂ → ι'} (he₂' : Function.Injective e₂')
  (h₂' : ∀ j, F₂'.obj (Z j) = X' (e₂' j))
  {J : Type*} [Fintype J]
  (π : J → (E₂.obj ((toKaroubi _).obj (familySum X)) ⟶ (toKaroubi _).obj (familySum Z)))
  (ι₁ : J → ((toKaroubi _).obj (familySum Z) ⟶ E₂.obj ((toKaroubi _).obj (familySum X))))
  (hπ : ∑ j, π j ≫ ι₁ j = 𝟙 _)
  (eG : mapKaroubi F₁.mapMat_ ⋙ E₁' ≅ E₂ ⋙ mapKaroubi F₂'.mapMat_)

/-- **Naturality of `resIndEquivIndResCross`**: the isomorphism
`Res_{φ₁'} (Ind M φ₁) ≅ Ind (Res_{φ₂} M) φ₂'` carries `Res (Ind f)` to `Ind (Res f)`. -/
theorem resIndEquivIndResCross_map
    (x : Res (mapEmbOp F₁' he₁' h₁') (Ind M (mapEmbOp F₁ he₁ h₁))) :
    resIndEquivIndResCross M₂ F₁ he₁ h₁ F₁' he₁' h₁' adj₁' F₂ he₂ h₂ adj₂ F₂' he₂' h₂' π ι₁
        hπ eG (Res.map (Ind.map f) x) =
      Ind.map (Res.map f) (resIndEquivIndResCross M F₁ he₁ h₁ F₁' he₁' h₁' adj₁' F₂ he₂ h₂
        adj₂ F₂' he₂' h₂' π ι₁ hπ eG x) := by
  let _ := HomTensor.transferModule (karoubiMatrixOp X) M
  let _ := HomTensor.transferModule (karoubiMatrixOp X) M₂
  let tf := HomTensor.transferLinearMap (karoubiMatrixOp X) f
  exact LinearEquiv.ofSemilinearTrans_naturality _ _ _ _ _ _ _ _ _ _ _
    (Res.map (Ind.map f)) (BalancedTensor.mapRight tf) (BalancedTensor.mapRight tf)
    (Ind.map (Res.map f))
    (fun m => resIndCrossModuleEquiv_map f F₁ he₁ h₁ F₁' he₁' h₁' adj₁' m)
    (fun y => HomTensor.natModuleEquiv_mapRight _ _ eG tf y)
    (fun y => indResCrossModuleEquiv_map f F₂ he₂ h₂ adj₂ F₂' he₂' h₂' π ι₁ hπ y) x

end MatEnd

end Categorification.KLR.Diagram
