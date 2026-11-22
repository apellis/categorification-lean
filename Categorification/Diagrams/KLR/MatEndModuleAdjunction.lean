/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KLR.MatEndModuleFunctor
import Categorification.Algebra.HomTensorAdjunction
import Categorification.Algebra.LinearMapRingEquiv

/-!
# Restriction is left adjoint to induction along a matrix map

In the setting of `MatEndModuleFunctor` (an additive functor `F : C ⥤ D`, finite families `X`,
`Y` with `F (X i) = Y (e i)`, completed sums `G_X`, `G_Y`, the functor `F'` induced by `F` on
completed additive envelopes and the matrix map `φ` of `F`), suppose that `F'` has a right
adjoint `E` which is also a left adjoint of `F'`, and that `E G_Y` is a summand of finitely
many copies of `G_X`. Then restriction along `φ` is left adjoint to induction along `φ`: for a
right `MatEnd Y`-module `M` and a right `MatEnd X`-module `N`,

`Hom_{MatEnd X}(Res_φ M, N) ≃ Hom_{MatEnd Y}(M, Ind N φ)`   (`resIndHomEquiv`),

naturally in `M` and `N`. Induction is always left adjoint to restriction; the point is the
other direction, which comes from the biadjunction of the categorical action through the
module functors of `MatEndModuleFunctor` and `HomTensor.homEquiv`. For Webster's functors
`Fᵢ` (induction) and `Eᵢ` (restriction) on right `T^λ`-modules this is the adjunction
`Eᵢ ⊣ Fᵢ` of arXiv:1309.3796v3, Theorem 4.31, needed for Chuang–Rouquier's theory of
`sl₂`-categorifications (arXiv:math/0407205, §5) as used in §5 there.
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
  {E : Karoubi (Mat_ D) ⥤ Karoubi (Mat_ C)} [E.Additive] (adj : mapKaroubi F.mapMat_ ⊣ E)
  (adj' : E ⊣ mapKaroubi F.mapMat_)
  {J : Type*} [Fintype J]
  (π : J → (E.obj ((toKaroubi _).obj (familySum Y)) ⟶ (toKaroubi _).obj (familySum X)))
  (ι' : J → ((toKaroubi _).obj (familySum X) ⟶ E.obj ((toKaroubi _).obj (familySum Y))))
  (hπ : ∑ j, π j ≫ ι' j = 𝟙 _)
  (M : Type (max w v)) [AddCommGroup M] [Module (MatEnd Y)ᵐᵒᵖ M]
  (N : Type (max w v)) [AddCommGroup N] [Module (MatEnd X)ᵐᵒᵖ N]

attribute [local instance] HomTensor.bimodule

/-- **Restriction is left adjoint to induction** along the matrix map, when `F'` is also
right adjoint to its right adjoint `E` and `E G_Y` is a summand of finitely many copies of
`G_X`: `Hom(Res_φ M, N) ≃ Hom(M, Ind N φ)`. -/
def resIndHomEquiv :
    (Res (mapEmbOp F he h) M →ₗ[(MatEnd X)ᵐᵒᵖ] N) ≃
      (M →ₗ[(MatEnd Y)ᵐᵒᵖ] Ind N (mapEmbOp F he h)) :=
  letI := HomTensor.transferModule (karoubiMatrixOpY Y) M
  letI := HomTensor.transferModule (karoubiMatrixOp X) N
  (LinearMap.ringEquivCongr (karoubiMatrixOp X) (resModuleEquiv F he h adj M).toAddEquiv
      (AddEquiv.refl N) (resModuleEquiv_smul F he h adj M)
      (fun a n => (HomTensor.transferModule_smul a n).symm)).trans
    ((HomTensor.homEquiv adj' π ι' hπ).trans
      (LinearMap.ringEquivCongr (karoubiMatrixOpY Y) (AddEquiv.refl M)
        (indModuleEquiv F he h N).toAddEquiv
        (fun a m => (HomTensor.transferModule_smul a m).symm)
        (indModuleEquiv_smul F he h N)).symm)

end MatEnd

end Categorification.KLR.Diagram
