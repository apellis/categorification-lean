/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KLR.MatEndModuleAdjunction
import Categorification.Diagrams.KLR.MatEndModuleNaturality
import Categorification.Algebra.InductionAlongRes

/-!
# Naturality of the adjunction between restriction and induction along a matrix map

The bijection `MatEnd.resIndHomEquiv : Hom(Res_φ M, N) ≃ Hom(M, Ind N φ)` is natural in `M`
(`resIndHomEquiv_naturality_left`) and in `N` (`resIndHomEquiv_naturality_right`), so it is an
adjunction `Res_φ ⊣ Ind_φ` between module categories (`resIndAdjunction`). For Webster's
functors on modules over tensor product algebras this is the adjunction `Eᵢ ⊣ Fᵢ` of
arXiv:1309.3796v3, Theorem 4.31, which with `Fᵢ ⊣ Eᵢ` makes `Eᵢ` and `Fᵢ` biadjoint, as
Chuang–Rouquier's `sl₂`-categorifications require (arXiv:math/0407205v2, §5.1.1).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KLR.Diagram

open CategoryTheory CategoryTheory.Idempotents Preadditive MulOpposite InductionAlong

namespace MatEnd

universe v w

variable {C : Type*} [Category.{v} C] [Preadditive C] {D : Type*} [Category.{v} D]
  [Preadditive D] {ι κ : Type w} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {X : ι → C} {Y : κ → D} (F : C ⥤ D) [F.Additive] {e : ι → κ}
  (he : Function.Injective e) (h : ∀ i, F.obj (X i) = Y (e i))
  {E : Karoubi (Mat_ D) ⥤ Karoubi (Mat_ C)} [E.Additive] (adj : mapKaroubi F.mapMat_ ⊣ E)
  (adj' : E ⊣ mapKaroubi F.mapMat_)
  {J : Type*} [Fintype J]
  (π : J → (E.obj ((toKaroubi _).obj (familySum Y)) ⟶ (toKaroubi _).obj (familySum X)))
  (ι' : J → ((toKaroubi _).obj (familySum X) ⟶ E.obj ((toKaroubi _).obj (familySum Y))))
  (hπ : ∑ j, π j ≫ ι' j = 𝟙 _)

attribute [local instance] HomTensor.bimodule

/-- `resIndHomEquiv` is natural in the restricted module. -/
theorem resIndHomEquiv_naturality_left
    {M M' : Type (max w v)} [AddCommGroup M] [Module (MatEnd Y)ᵐᵒᵖ M] [AddCommGroup M']
    [Module (MatEnd Y)ᵐᵒᵖ M'] {N : Type (max w v)} [AddCommGroup N] [Module (MatEnd X)ᵐᵒᵖ N]
    (g : M' →ₗ[(MatEnd Y)ᵐᵒᵖ] M)
    (f : Res (mapEmbOp F he h) M →ₗ[(MatEnd X)ᵐᵒᵖ] N) :
    resIndHomEquiv F he h adj adj' π ι' hπ M' N (f.comp (Res.map g)) =
      (resIndHomEquiv F he h adj adj' π ι' hπ M N f).comp g := by
  let _ := HomTensor.transferModule (karoubiMatrixOpY Y) M
  let _ := HomTensor.transferModule (karoubiMatrixOpY Y) M'
  let _ := HomTensor.transferModule (karoubiMatrixOp X) N
  have key : ∀ x, (Res.map g) ((resModuleEquiv F he h adj M').symm x) =
      (resModuleEquiv F he h adj M).symm
        (BalancedTensor.mapRight (HomTensor.transferLinearMap (karoubiMatrixOpY Y) g) x) := by
    intro x
    apply (resModuleEquiv F he h adj M).injective
    rw [LinearEquiv.apply_symm_apply, resModuleEquiv_map, LinearEquiv.apply_symm_apply]
  have hinner :
      (LinearMap.ringEquivCongr (karoubiMatrixOp X) (resModuleEquiv F he h adj M').toAddEquiv
          (AddEquiv.refl N) (resModuleEquiv_smul F he h adj M')
          (fun a n => (HomTensor.transferModule_smul a n).symm)) (f.comp (Res.map g)) =
        ((LinearMap.ringEquivCongr (karoubiMatrixOp X) (resModuleEquiv F he h adj M).toAddEquiv
          (AddEquiv.refl N) (resModuleEquiv_smul F he h adj M)
          (fun a n => (HomTensor.transferModule_smul a n).symm)) f).comp
          (BalancedTensor.mapRight (HomTensor.transferLinearMap (karoubiMatrixOpY Y) g)) := by
    ext x
    exact congrArg f (key x)
  ext m
  change (indModuleEquiv F he h N).symm (HomTensor.homEquiv adj' π ι' hπ _ m) =
    (indModuleEquiv F he h N).symm (HomTensor.homEquiv adj' π ι' hπ _ (g m))
  rw [hinner, HomTensor.homEquiv_naturality_left]
  rfl

/-- `resIndHomEquiv` is natural in the induced module. -/
theorem resIndHomEquiv_naturality_right
    {M : Type (max w v)} [AddCommGroup M] [Module (MatEnd Y)ᵐᵒᵖ M]
    {N N' : Type (max w v)} [AddCommGroup N] [Module (MatEnd X)ᵐᵒᵖ N] [AddCommGroup N']
    [Module (MatEnd X)ᵐᵒᵖ N'] (q : N →ₗ[(MatEnd X)ᵐᵒᵖ] N')
    (f : Res (mapEmbOp F he h) M →ₗ[(MatEnd X)ᵐᵒᵖ] N) :
    resIndHomEquiv F he h adj adj' π ι' hπ M N' (q.comp f) =
      (Ind.map q).comp (resIndHomEquiv F he h adj adj' π ι' hπ M N f) := by
  let _ := HomTensor.transferModule (karoubiMatrixOpY Y) M
  let _ := HomTensor.transferModule (karoubiMatrixOp X) N
  let _ := HomTensor.transferModule (karoubiMatrixOp X) N'
  have key : ∀ y, (indModuleEquiv F he h N').symm
      (BalancedTensor.mapRight (HomTensor.transferLinearMap (karoubiMatrixOp X) q) y) =
        Ind.map q ((indModuleEquiv F he h N).symm y) := by
    intro y
    apply (indModuleEquiv F he h N').injective
    rw [LinearEquiv.apply_symm_apply, indModuleEquiv_map, LinearEquiv.apply_symm_apply]
  have hinner :
      (LinearMap.ringEquivCongr (karoubiMatrixOp X) (resModuleEquiv F he h adj M).toAddEquiv
          (AddEquiv.refl N') (resModuleEquiv_smul F he h adj M)
          (fun a n => (HomTensor.transferModule_smul a n).symm)) (q.comp f) =
        (HomTensor.transferLinearMap (karoubiMatrixOp X) q).comp
          ((LinearMap.ringEquivCongr (karoubiMatrixOp X)
            (resModuleEquiv F he h adj M).toAddEquiv
            (AddEquiv.refl N) (resModuleEquiv_smul F he h adj M)
            (fun a n => (HomTensor.transferModule_smul a n).symm)) f) := by
    ext x
    rfl
  ext m
  change (indModuleEquiv F he h N').symm (HomTensor.homEquiv adj' π ι' hπ _ m) =
    Ind.map q ((indModuleEquiv F he h N).symm (HomTensor.homEquiv adj' π ι' hπ _ m))
  rw [hinner, HomTensor.homEquiv_naturality_right]
  exact key _

/-- **Restriction is left adjoint to induction** along the matrix map, as functors on module
categories, when `F'` is also right adjoint to its right adjoint `E` and `E G_Y` is a summand of
finitely many copies of `G_X` (`resIndHomEquiv` with its naturality). -/
def resIndAdjunction :
    resFunctor.{max w v, max w v} (mapEmbOp F he h) ⊣
      InductionAlong.functor.{max w v, max w v} (mapEmbOp F he h) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M N =>
        { toFun := fun f => ModuleCat.ofHom (resIndHomEquiv F he h adj adj' π ι' hπ M N f.hom)
          invFun := fun g =>
            ModuleCat.ofHom ((resIndHomEquiv F he h adj adj' π ι' hπ M N).symm g.hom)
          left_inv := fun f => ModuleCat.hom_ext (by simp)
          right_inv := fun g => ModuleCat.hom_ext (by simp) }
      homEquiv_naturality_left_symm := fun {M' M N} f g => by
        refine ModuleCat.hom_ext ?_
        change (resIndHomEquiv F he h adj adj' π ι' hπ M' N).symm (g.hom.comp f.hom) =
          ((resIndHomEquiv F he h adj adj' π ι' hπ M N).symm g.hom).comp (Res.map f.hom)
        rw [Equiv.symm_apply_eq, resIndHomEquiv_naturality_left, Equiv.apply_symm_apply]
      homEquiv_naturality_right := fun {M N N'} f g => by
        refine ModuleCat.hom_ext ?_
        exact resIndHomEquiv_naturality_right F he h adj adj' π ι' hπ g.hom f.hom }

end MatEnd

end Categorification.KLR.Diagram
