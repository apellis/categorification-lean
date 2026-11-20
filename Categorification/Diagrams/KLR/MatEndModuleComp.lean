/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KLR.MatEndModuleFunctor
import Categorification.Algebra.HomTensorComp

/-!
# Restriction after induction along a matrix map as a module functor

In the setting of `MatEndModuleFunctor`, with `F'` the functor induced by `F` on completed
additive envelopes and `E` a right adjoint of `F'`, restriction after induction along the
matrix map `φ` of `F` is the module functor of the composite `F' ⋙ E`: for every right
`MatEnd X`-module `N`,

`Res_φ (Ind N φ) ≅ (G_X ⟶ E (F' G_X)) ⊗_{End G_X} N`   (`resIndModuleEquiv`),
and, when `E G_Y` is a summand of finitely many copies of `G_X`, for every right
`MatEnd Y`-module `M`, `Ind (Res_φ M) φ ≅ (G_Y ⟶ F' (E G_Y)) ⊗_{End G_Y} M`
(`indResModuleEquiv`).

The composition step uses that `F' G_X` is a summand of `G_Y` (`karoubiSect_gen`). This is how
the commutation relations of the categorical action pass to Webster's functors `Eᵢ Fⱼ` on all
modules, as used in the proof of Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v3, Proposition 5.5.
-/

noncomputable section

namespace Categorification.KLR.Diagram

open CategoryTheory CategoryTheory.Idempotents Preadditive MulOpposite InductionAlong

namespace MatEnd

universe v w

variable {C : Type*} [Category.{v} C] [Preadditive C] {D : Type*} [Category.{v} D]
  [Preadditive D] {ι κ : Type w} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {X : ι → C} {Y : κ → D} (F : C ⥤ D) [F.Additive] {e : ι → κ}
  (he : Function.Injective e) (h : ∀ i, F.obj (X i) = Y (e i))

attribute [local instance] HomTensor.bimodule

variable (N : Type (max w v)) [AddCommGroup N] [Module (MatEnd X)ᵐᵒᵖ N]

/-- `indModuleEquiv` as a map of right `End G_Y`-modules, for the module structure on the
induced module transferred along `karoubiMatrixOpY`. -/
def indModuleLinearEquiv :
    letI := HomTensor.transferModule (karoubiMatrixOp X) N
    letI := HomTensor.transferModule (karoubiMatrixOpY Y) (Ind N (mapEmbOp F he h))
    Ind N (mapEmbOp F he h) ≃ₗ[(End ((toKaroubi _).obj (familySum Y)))ᵐᵒᵖ]
      BalancedTensor ℤ (End ((toKaroubi _).obj (familySum Y)))ᵐᵒᵖ
      (End ((toKaroubi _).obj (familySum X)))ᵐᵒᵖ
      ((toKaroubi _).obj (familySum Y) ⟶
        (mapKaroubi F.mapMat_).obj ((toKaroubi _).obj (familySum X))) N :=
  letI := HomTensor.transferModule (karoubiMatrixOp X) N
  letI := HomTensor.transferModule (karoubiMatrixOpY Y) (Ind N (mapEmbOp F he h))
  { indModuleEquiv F he h N with
    map_smul' := fun a x => by
      change indModuleEquiv F he h N ((karoubiMatrixOpY Y).symm a • x) = a • _
      rw [indModuleEquiv_smul, RingEquiv.apply_symm_apply]
      rfl }

theorem indModuleLinearEquiv_apply (x : Ind N (mapEmbOp F he h)) :
    letI := HomTensor.transferModule (karoubiMatrixOp X) N
    letI := HomTensor.transferModule (karoubiMatrixOpY Y) (Ind N (mapEmbOp F he h))
    indModuleLinearEquiv F he h N x = indModuleEquiv F he h N x :=
  rfl

theorem karoubiSect_gen_sum :
    ∑ _j : Unit, karoubiSect F h ≫ karoubiGen F he h = 𝟙 _ := by
  rw [Finset.univ_unique, Finset.sum_singleton, karoubiSect_gen]

variable {E : Karoubi (Mat_ D) ⥤ Karoubi (Mat_ C)} (adj : mapKaroubi F.mapMat_ ⊣ E) [E.Additive]

/-- **Restriction after induction as a module functor**:
`Res_φ (Ind N φ) ≅ (G_X ⟶ E (F' G_X)) ⊗_{End G_X} N`. -/
def resIndModuleEquiv :
    letI := HomTensor.transferModule (karoubiMatrixOp X) N
    Res (mapEmbOp F he h) (Ind N (mapEmbOp F he h)) ≃ₗ[ℤ]
      BalancedTensor ℤ (End ((toKaroubi _).obj (familySum X)))ᵐᵒᵖ
      (End ((toKaroubi _).obj (familySum X)))ᵐᵒᵖ
      ((toKaroubi _).obj (familySum X) ⟶
        (mapKaroubi F.mapMat_ ⋙ E).obj ((toKaroubi _).obj (familySum X))) N :=
  letI := HomTensor.transferModule (karoubiMatrixOp X) N
  letI := HomTensor.transferModule (karoubiMatrixOpY Y) (Ind N (mapEmbOp F he h))
  (resModuleEquiv F he h adj (Ind N (mapEmbOp F he h))).trans
    (((BalancedTensor.congrRight (k := ℤ)
      (B := (End ((toKaroubi _).obj (familySum X)))ᵐᵒᵖ)
      (M := (toKaroubi _).obj (familySum X) ⟶ E.obj ((toKaroubi _).obj (familySum Y)))
      (indModuleLinearEquiv F he h N)).trans
      (HomTensor.compModuleEquiv ℤ (mapKaroubi F.mapMat_) E _ _ _
        (fun _ : Unit => karoubiSect F h) (fun _ => karoubiGen F he h)
        (karoubiSect_gen_sum F he h) N)).restrictScalars ℤ)

/-- `resIndModuleEquiv` is semilinear along `karoubiMatrixOp`. -/
theorem resIndModuleEquiv_smul (a : (MatEnd X)ᵐᵒᵖ)
    (m : Res (mapEmbOp F he h) (Ind N (mapEmbOp F he h))) :
    letI := HomTensor.transferModule (karoubiMatrixOp X) N
    resIndModuleEquiv F he h N adj (a • m) =
      karoubiMatrixOp X a • resIndModuleEquiv F he h N adj m := by
  let _ := HomTensor.transferModule (karoubiMatrixOp X) N
  let _ := HomTensor.transferModule (karoubiMatrixOpY Y) (Ind N (mapEmbOp F he h))
  simp only [resIndModuleEquiv, LinearEquiv.trans_apply, resModuleEquiv_smul,
    LinearEquiv.restrictScalars_apply, LinearEquiv.map_smul]

section IndRes

variable (M : Type (max w v)) [AddCommGroup M] [Module (MatEnd Y)ᵐᵒᵖ M]

/-- `resModuleEquiv` as a map of right `End G_X`-modules, for the module structure on the
restricted module transferred along `karoubiMatrixOp`. -/
def resModuleLinearEquiv :
    letI := HomTensor.transferModule (karoubiMatrixOpY Y) M
    letI := HomTensor.transferModule (karoubiMatrixOp X) (Res (mapEmbOp F he h) M)
    Res (mapEmbOp F he h) M ≃ₗ[(End ((toKaroubi _).obj (familySum X)))ᵐᵒᵖ]
      BalancedTensor ℤ (End ((toKaroubi _).obj (familySum X)))ᵐᵒᵖ
      (End ((toKaroubi _).obj (familySum Y)))ᵐᵒᵖ
      ((toKaroubi _).obj (familySum X) ⟶ E.obj ((toKaroubi _).obj (familySum Y))) M :=
  letI := HomTensor.transferModule (karoubiMatrixOpY Y) M
  letI := HomTensor.transferModule (karoubiMatrixOp X) (Res (mapEmbOp F he h) M)
  { resModuleEquiv F he h adj M with
    map_smul' := fun a x => by
      change resModuleEquiv F he h adj M ((karoubiMatrixOp X).symm a • x) = a • _
      rw [resModuleEquiv_smul, RingEquiv.apply_symm_apply]
      rfl }

variable {J : Type*} [Fintype J]
  (π : J → (E.obj ((toKaroubi _).obj (familySum Y)) ⟶ (toKaroubi _).obj (familySum X)))
  (ι' : J → ((toKaroubi _).obj (familySum X) ⟶ E.obj ((toKaroubi _).obj (familySum Y))))
  (hπ : ∑ j, π j ≫ ι' j = 𝟙 _)

/-- **Induction after restriction as a module functor**: when `E G_Y` is a summand of finitely
many copies of `G_X`, `Ind (Res_φ M) φ ≅ (G_Y ⟶ F' (E G_Y)) ⊗_{End G_Y} M`. -/
def indResModuleEquiv :
    letI := HomTensor.transferModule (karoubiMatrixOpY Y) M
    Ind (Res (mapEmbOp F he h) M) (mapEmbOp F he h) ≃ₗ[ℤ]
      BalancedTensor ℤ (End ((toKaroubi _).obj (familySum Y)))ᵐᵒᵖ
      (End ((toKaroubi _).obj (familySum Y)))ᵐᵒᵖ
      ((toKaroubi _).obj (familySum Y) ⟶
        (E ⋙ mapKaroubi F.mapMat_).obj ((toKaroubi _).obj (familySum Y))) M :=
  letI := HomTensor.transferModule (karoubiMatrixOpY Y) M
  letI := HomTensor.transferModule (karoubiMatrixOp X) (Res (mapEmbOp F he h) M)
  letI := HomTensor.transferModule (karoubiMatrixOpY Y)
    (Ind (Res (mapEmbOp F he h) M) (mapEmbOp F he h))
  ((indModuleLinearEquiv F he h (Res (mapEmbOp F he h) M)).trans
    ((BalancedTensor.congrRight (k := ℤ)
      (B := (End ((toKaroubi _).obj (familySum Y)))ᵐᵒᵖ)
      (M := (toKaroubi _).obj (familySum Y) ⟶
        (mapKaroubi F.mapMat_).obj ((toKaroubi _).obj (familySum X)))
      (resModuleLinearEquiv F he h adj M)).trans
      (HomTensor.compModuleEquiv ℤ E (mapKaroubi F.mapMat_) _ _ _ π ι' hπ M))).restrictScalars
    ℤ

/-- `indResModuleEquiv` is semilinear along `karoubiMatrixOpY`. -/
theorem indResModuleEquiv_smul (b : (MatEnd Y)ᵐᵒᵖ)
    (x : Ind (Res (mapEmbOp F he h) M) (mapEmbOp F he h)) :
    letI := HomTensor.transferModule (karoubiMatrixOpY Y) M
    indResModuleEquiv F he h adj M π ι' hπ (b • x) =
      karoubiMatrixOpY Y b • indResModuleEquiv F he h adj M π ι' hπ x := by
  let _ := HomTensor.transferModule (karoubiMatrixOpY Y) M
  let _ := HomTensor.transferModule (karoubiMatrixOp X) (Res (mapEmbOp F he h) M)
  let _ := HomTensor.transferModule (karoubiMatrixOpY Y)
    (Ind (Res (mapEmbOp F he h) M) (mapEmbOp F he h))
  have : b • x = (karoubiMatrixOpY Y b) • x := by
    change _ = (karoubiMatrixOpY Y).symm (karoubiMatrixOpY Y b) • x
    rw [RingEquiv.symm_apply_apply]
  rw [this]
  exact LinearEquiv.map_smul (((indModuleLinearEquiv F he h (Res (mapEmbOp F he h) M)).trans
    ((BalancedTensor.congrRight (k := ℤ)
      (B := (End ((toKaroubi _).obj (familySum Y)))ᵐᵒᵖ)
      (M := (toKaroubi _).obj (familySum Y) ⟶
        (mapKaroubi F.mapMat_).obj ((toKaroubi _).obj (familySum X)))
      (resModuleLinearEquiv F he h adj M)).trans
      (HomTensor.compModuleEquiv ℤ E (mapKaroubi F.mapMat_) _ _ _ π ι' hπ M)))) _ _

end IndRes

end MatEnd

end Categorification.KLR.Diagram
