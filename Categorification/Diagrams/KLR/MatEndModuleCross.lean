/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KLR.MatEndModuleComp

/-!
# Restriction and induction along different matrix maps as module functors

`MatEndModuleComp` identifies restriction after induction along one matrix map `φ` with the
module functor of `F' ⋙ E`. This file allows the two maps to differ. For matrix maps
`φ₁ : X → Y` (of `F₁`) and `φ₁' : X' → Y` (of `F₁'`, whose completion has a right adjoint `E₁'`),
and every right `MatEnd X`-module `M`,

`Res_{φ₁'} (Ind M φ₁) ≅ (G_{X'} ⟶ E₁' (F₁' G_X)) ⊗_{End G_X} M`   (`resIndCrossModuleEquiv`);

for matrix maps `φ₂ : Z → X` (of `F₂`, with right adjoint `E₂`) and `φ₂' : Z → X'` (of `F₂'`),
when `E₂ G_X` is a summand of finitely many copies of `G_Z`,

`Ind (Res_{φ₂} M) φ₂' ≅ (G_{X'} ⟶ F₂' (E₂ G_X)) ⊗_{End G_X} M`   (`indResCrossModuleEquiv`).

An isomorphism of the two composite functors therefore gives an isomorphism of right
`MatEnd X'`-modules `Res_{φ₁'} (Ind M φ₁) ≅ Ind (Res_{φ₂} M) φ₂'` (`resIndEquivIndResCross`).
This is the form of the relation `Eⱼ Fᵢ ≅ Fᵢ Eⱼ` (`i ≠ j`) on all modules used in the proof of
Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
Proposition 5.5.
-/

noncomputable section

namespace Categorification

/-- An `R`-linear equivalence `U ≃ V` from additive equivalences `U ≃ T`, `V ≃ T'` that are
semilinear along `σ : R ≃+* S` and an `S`-linear equivalence `T ≃ T'`. -/
def LinearEquiv.ofSemilinearTrans {R S : Type*} [Ring R] [Ring S] (σ : R ≃+* S)
    {U V T T' : Type*} [AddCommGroup U] [AddCommGroup V] [AddCommGroup T] [AddCommGroup T']
    [Module R U] [Module R V] [Module S T] [Module S T']
    (eU : U ≃ₗ[ℤ] T) (heU : ∀ (a : R) (x : U), eU (a • x) = σ a • eU x) (f : T ≃ₗ[S] T')
    (eV : V ≃ₗ[ℤ] T') (heV : ∀ (a : R) (x : V), eV (a • x) = σ a • eV x) : U ≃ₗ[R] V where
  toFun x := eV.symm (f (eU x))
  invFun y := eU.symm (f.symm (eV y))
  map_add' x y := by simp
  map_smul' a x := by
    apply eV.injective
    rw [heV, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, heU, map_smul]
    rfl
  left_inv x := by simp
  right_inv y := by simp

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
  (M : Type (max w v)) [AddCommGroup M] [Module (MatEnd X)ᵐᵒᵖ M]

section ResInd

variable (F₁ : C ⥤ D) [F₁.Additive] {e₁ : ι → κ} (he₁ : Function.Injective e₁)
  (h₁ : ∀ i, F₁.obj (X i) = Y (e₁ i))
  (F₁' : C' ⥤ D) [F₁'.Additive] {e₁' : ι' → κ} (he₁' : Function.Injective e₁')
  (h₁' : ∀ i, F₁'.obj (X' i) = Y (e₁' i))
  {E₁' : Karoubi (Mat_ D) ⥤ Karoubi (Mat_ C')} (adj₁' : mapKaroubi F₁'.mapMat_ ⊣ E₁')
  [E₁'.Additive]

/-- **Restriction after induction along different matrix maps as a module functor**:
`Res_{φ₁'} (Ind M φ₁) ≅ (G_{X'} ⟶ E₁' (F₁' G_X)) ⊗_{End G_X} M`. -/
def resIndCrossModuleEquiv :
    letI := HomTensor.transferModule (karoubiMatrixOp X) M
    Res (mapEmbOp F₁' he₁' h₁') (Ind M (mapEmbOp F₁ he₁ h₁)) ≃ₗ[ℤ]
      BalancedTensor ℤ (End ((toKaroubi _).obj (familySum X')))ᵐᵒᵖ
      (End ((toKaroubi _).obj (familySum X)))ᵐᵒᵖ
      ((toKaroubi _).obj (familySum X') ⟶
        (mapKaroubi F₁.mapMat_ ⋙ E₁').obj ((toKaroubi _).obj (familySum X))) M :=
  letI := HomTensor.transferModule (karoubiMatrixOp X) M
  letI := HomTensor.transferModule (karoubiMatrixOpY Y) (Ind M (mapEmbOp F₁ he₁ h₁))
  (resModuleEquiv F₁' he₁' h₁' adj₁' (Ind M (mapEmbOp F₁ he₁ h₁))).trans
    (((BalancedTensor.congrRight (k := ℤ)
      (B := (End ((toKaroubi _).obj (familySum X')))ᵐᵒᵖ)
      (M := (toKaroubi _).obj (familySum X') ⟶ E₁'.obj ((toKaroubi _).obj (familySum Y)))
      (indModuleLinearEquiv F₁ he₁ h₁ M)).trans
      (HomTensor.compModuleEquiv ℤ (mapKaroubi F₁.mapMat_) E₁' _ _ _
        (fun _ : Unit => karoubiSect F₁ h₁) (fun _ => karoubiGen F₁ he₁ h₁)
        (karoubiSect_gen_sum F₁ he₁ h₁) M)).restrictScalars ℤ)

/-- `resIndCrossModuleEquiv` is semilinear along `karoubiMatrixOp`. -/
theorem resIndCrossModuleEquiv_smul (a : (MatEnd X')ᵐᵒᵖ)
    (m : Res (mapEmbOp F₁' he₁' h₁') (Ind M (mapEmbOp F₁ he₁ h₁))) :
    letI := HomTensor.transferModule (karoubiMatrixOp X) M
    resIndCrossModuleEquiv M F₁ he₁ h₁ F₁' he₁' h₁' adj₁' (a • m) =
      karoubiMatrixOp X' a • resIndCrossModuleEquiv M F₁ he₁ h₁ F₁' he₁' h₁' adj₁' m := by
  let _ := HomTensor.transferModule (karoubiMatrixOp X) M
  let _ := HomTensor.transferModule (karoubiMatrixOpY Y) (Ind M (mapEmbOp F₁ he₁ h₁))
  simp only [resIndCrossModuleEquiv, LinearEquiv.trans_apply, resModuleEquiv_smul,
    LinearEquiv.restrictScalars_apply, LinearEquiv.map_smul]

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

/-- **Induction after restriction along different matrix maps as a module functor**: when
`E₂ G_X` is a summand of finitely many copies of `G_Z`,
`Ind (Res_{φ₂} M) φ₂' ≅ (G_{X'} ⟶ F₂' (E₂ G_X)) ⊗_{End G_X} M`. -/
def indResCrossModuleEquiv :
    letI := HomTensor.transferModule (karoubiMatrixOpY X) M
    Ind (Res (mapEmbOp F₂ he₂ h₂) M) (mapEmbOp F₂' he₂' h₂') ≃ₗ[ℤ]
      BalancedTensor ℤ (End ((toKaroubi _).obj (familySum X')))ᵐᵒᵖ
      (End ((toKaroubi _).obj (familySum X)))ᵐᵒᵖ
      ((toKaroubi _).obj (familySum X') ⟶
        (E₂ ⋙ mapKaroubi F₂'.mapMat_).obj ((toKaroubi _).obj (familySum X))) M :=
  letI := HomTensor.transferModule (karoubiMatrixOpY X) M
  letI := HomTensor.transferModule (karoubiMatrixOp Z) (Res (mapEmbOp F₂ he₂ h₂) M)
  letI := HomTensor.transferModule (karoubiMatrixOpY X')
    (Ind (Res (mapEmbOp F₂ he₂ h₂) M) (mapEmbOp F₂' he₂' h₂'))
  ((indModuleLinearEquiv F₂' he₂' h₂' (Res (mapEmbOp F₂ he₂ h₂) M)).trans
    ((BalancedTensor.congrRight (k := ℤ)
      (B := (End ((toKaroubi _).obj (familySum X')))ᵐᵒᵖ)
      (M := (toKaroubi _).obj (familySum X') ⟶
        (mapKaroubi F₂'.mapMat_).obj ((toKaroubi _).obj (familySum Z)))
      (resModuleLinearEquiv F₂ he₂ h₂ adj₂ M)).trans
      (HomTensor.compModuleEquiv ℤ E₂ (mapKaroubi F₂'.mapMat_) _ _ _ π ι₁ hπ
        M))).restrictScalars ℤ

/-- `indResCrossModuleEquiv` is semilinear along `karoubiMatrixOpY`. -/
theorem indResCrossModuleEquiv_smul (b : (MatEnd X')ᵐᵒᵖ)
    (x : Ind (Res (mapEmbOp F₂ he₂ h₂) M) (mapEmbOp F₂' he₂' h₂')) :
    letI := HomTensor.transferModule (karoubiMatrixOpY X) M
    indResCrossModuleEquiv M F₂ he₂ h₂ adj₂ F₂' he₂' h₂' π ι₁ hπ (b • x) =
      karoubiMatrixOpY X' b •
        indResCrossModuleEquiv M F₂ he₂ h₂ adj₂ F₂' he₂' h₂' π ι₁ hπ x := by
  let _ := HomTensor.transferModule (karoubiMatrixOpY X) M
  let _ := HomTensor.transferModule (karoubiMatrixOp Z) (Res (mapEmbOp F₂ he₂ h₂) M)
  let _ := HomTensor.transferModule (karoubiMatrixOpY X')
    (Ind (Res (mapEmbOp F₂ he₂ h₂) M) (mapEmbOp F₂' he₂' h₂'))
  have : b • x = (karoubiMatrixOpY X' b) • x := by
    change _ = (karoubiMatrixOpY X').symm (karoubiMatrixOpY X' b) • x
    rw [RingEquiv.symm_apply_apply]
  rw [this]
  exact LinearEquiv.map_smul ((indModuleLinearEquiv F₂' he₂' h₂'
    (Res (mapEmbOp F₂ he₂ h₂) M)).trans
    ((BalancedTensor.congrRight (k := ℤ)
      (B := (End ((toKaroubi _).obj (familySum X')))ᵐᵒᵖ)
      (M := (toKaroubi _).obj (familySum X') ⟶
        (mapKaroubi F₂'.mapMat_).obj ((toKaroubi _).obj (familySum Z)))
      (resModuleLinearEquiv F₂ he₂ h₂ adj₂ M)).trans
      (HomTensor.compModuleEquiv ℤ E₂ (mapKaroubi F₂'.mapMat_) _ _ _ π ι₁ hπ M))) _ _

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

/-- **Restriction after induction against induction after restriction, along different
matrix maps**: an isomorphism `F₁' ⋙ E₁' ≅ E₂ ⋙ F₂'` of functors on completions gives
`Res_{φ₁'} (Ind M φ₁) ≅ Ind (Res_{φ₂} M) φ₂'` as modules over the matrix ring of `X'`. -/
def resIndEquivIndResCross :
    Res (mapEmbOp F₁' he₁' h₁') (Ind M (mapEmbOp F₁ he₁ h₁)) ≃ₗ[(MatEnd X')ᵐᵒᵖ]
      Ind (Res (mapEmbOp F₂ he₂ h₂) M) (mapEmbOp F₂' he₂' h₂') :=
  letI := HomTensor.transferModule (karoubiMatrixOp X) M
  LinearEquiv.ofSemilinearTrans (karoubiMatrixOp X')
    (resIndCrossModuleEquiv M F₁ he₁ h₁ F₁' he₁' h₁' adj₁')
    (resIndCrossModuleEquiv_smul M F₁ he₁ h₁ F₁' he₁' h₁' adj₁')
    (HomTensor.natModuleEquiv _ _ M eG)
    (indResCrossModuleEquiv M F₂ he₂ h₂ adj₂ F₂' he₂' h₂' π ι₁ hπ)
    (indResCrossModuleEquiv_smul M F₂ he₂ h₂ adj₂ F₂' he₂' h₂' π ι₁ hπ)

end MatEnd

end Categorification.KLR.Diagram
