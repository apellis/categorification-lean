/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KLR.MatEndModuleComp
import Categorification.Algebra.HomTensorNaturality

/-!
# Naturality of induction and restriction as module functors

The identifications of induction and restriction along a matrix map with module functors
(`MatEnd.indModuleEquiv`, `MatEnd.resModuleEquiv`, `MatEnd.resIndModuleEquiv`,
`MatEnd.indResModuleEquiv` and their variants along isomorphisms of functors) are natural in the
module: they carry `Ind.map f` and `Res.map f` to `id ⊗ f`.

This is what makes the commutation relations of Webster's functors `Eᵢ` and `Fᵢ` on all
modules (arXiv:1309.3796v3, Theorem 4.31) compatible with module maps, as needed for the tensor
factors in the proof of Proposition 5.5 there.
-/

noncomputable section

namespace Categorification.HomTensor

open CategoryTheory MulOpposite

attribute [local instance] bimodule

variable {C : Type*} [Category C] [Preadditive C] {D : Type*} [Category D] [Preadditive D]
  (O : C) (O' : D) {M M' : Type*} [AddCommGroup M] [Module (End O)ᵐᵒᵖ M] [AddCommGroup M']
  [Module (End O)ᵐᵒᵖ M'] {F G : C ⥤ D} [F.Additive] [G.Additive]

/-- `natModuleEquiv` is natural in the module. -/
theorem natModuleEquiv_mapRight (e : F ≅ G) (g : M →ₗ[(End O)ᵐᵒᵖ] M')
    (x : BalancedTensor ℤ (End O')ᵐᵒᵖ (End O)ᵐᵒᵖ (O' ⟶ F.obj O) M) :
    natModuleEquiv O O' M' e (BalancedTensor.mapRight g x) =
      BalancedTensor.mapRight g (natModuleEquiv O O' M e x) :=
  natModuleMap_mapRight O O' e.hom g x

end Categorification.HomTensor

namespace Categorification.KLR.Diagram

open CategoryTheory CategoryTheory.Idempotents Preadditive MulOpposite InductionAlong

namespace MatEnd

universe v w

variable {C : Type*} [Category.{v} C] [Preadditive C] {D : Type*} [Category.{v} D]
  [Preadditive D] {ι κ : Type w} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {X : ι → C} {Y : κ → D} (F : C ⥤ D) [F.Additive] {e : ι → κ}
  (he : Function.Injective e) (h : ∀ i, F.obj (X i) = Y (e i))

attribute [local instance] HomTensor.bimodule

section Ind

variable {N N₂ : Type (max w v)} [AddCommGroup N] [Module (MatEnd X)ᵐᵒᵖ N] [AddCommGroup N₂]
  [Module (MatEnd X)ᵐᵒᵖ N₂] (f : N →ₗ[(MatEnd X)ᵐᵒᵖ] N₂)

/-- `indModuleEquiv` is natural in the module. -/
theorem indModuleEquiv_map (x : Ind N (mapEmbOp F he h)) :
    letI := HomTensor.transferModule (karoubiMatrixOp X) N
    letI := HomTensor.transferModule (karoubiMatrixOp X) N₂
    indModuleEquiv F he h N₂ (Ind.map f x) =
      BalancedTensor.mapRight (HomTensor.transferLinearMap (karoubiMatrixOp X) f)
        (indModuleEquiv F he h N x) :=
  letI := HomTensor.transferModule (karoubiMatrixOp X) N
  letI := HomTensor.transferModule (karoubiMatrixOp X) N₂
  HomTensor.indTensorEquiv_map (karoubiCorner F he h) (karoubiCorner_op_smul F he h)
    (AddEquiv.refl N) _ (AddEquiv.refl N₂) _ f _ (fun _ => rfl) x

variable {E : Karoubi (Mat_ D) ⥤ Karoubi (Mat_ C)} (adj : mapKaroubi F.mapMat_ ⊣ E) [E.Additive]

/-- `resIndModuleEquiv` is natural in the module. -/
theorem resIndModuleEquiv_map (m : Res (mapEmbOp F he h) (Ind N (mapEmbOp F he h))) :
    letI := HomTensor.transferModule (karoubiMatrixOp X) N
    letI := HomTensor.transferModule (karoubiMatrixOp X) N₂
    resIndModuleEquiv F he h N₂ adj (Res.map (Ind.map f) m) =
      BalancedTensor.mapRight (HomTensor.transferLinearMap (karoubiMatrixOp X) f)
        (resIndModuleEquiv F he h N adj m) := by
  let _ := HomTensor.transferModule (karoubiMatrixOp X) N
  let _ := HomTensor.transferModule (karoubiMatrixOp X) N₂
  let _ := HomTensor.transferModule (karoubiMatrixOpY Y) (Ind N (mapEmbOp F he h))
  let _ := HomTensor.transferModule (karoubiMatrixOpY Y) (Ind N₂ (mapEmbOp F he h))
  exact (congrArg (HomTensor.compModuleEquiv ℤ (mapKaroubi F.mapMat_) E _ _ _
      (fun _ : Unit => karoubiSect F h) (fun _ => karoubiGen F he h)
      (karoubiSect_gen_sum F he h) N₂)
    (BalancedTensor.congrRight_mapRight (indModuleLinearEquiv F he h N)
      (indModuleLinearEquiv F he h N₂)
      (HomTensor.transferLinearMap (karoubiMatrixOpY Y) (Ind.map f))
      (BalancedTensor.mapRight (HomTensor.transferLinearMap (karoubiMatrixOp X) f))
      (fun x => indModuleEquiv_map F he h f x)
      (resModuleEquiv F he h adj (Ind N (mapEmbOp F he h)) m))).trans
    (HomTensor.compModuleEquiv_mapRight _ _ _ _ _ _ _ _ _ _)

variable {G : Karoubi (Mat_ C) ⥤ Karoubi (Mat_ C)} [G.Additive]
  (eG : G ≅ mapKaroubi F.mapMat_ ⋙ E)

/-- `resIndModuleEquivOfIso` is natural in the module. -/
theorem resIndModuleEquivOfIso_map (m : Res (mapEmbOp F he h) (Ind N (mapEmbOp F he h))) :
    letI := HomTensor.transferModule (karoubiMatrixOp X) N
    letI := HomTensor.transferModule (karoubiMatrixOp X) N₂
    resIndModuleEquivOfIso F he h N₂ adj eG (Res.map (Ind.map f) m) =
      BalancedTensor.mapRight (HomTensor.transferLinearMap (karoubiMatrixOp X) f)
        (resIndModuleEquivOfIso F he h N adj eG m) := by
  let _ := HomTensor.transferModule (karoubiMatrixOp X) N
  let _ := HomTensor.transferModule (karoubiMatrixOp X) N₂
  simp only [resIndModuleEquivOfIso, LinearEquiv.trans_apply,
    LinearEquiv.restrictScalars_apply, resIndModuleEquiv_map]
  exact HomTensor.natModuleEquiv_mapRight _ _ _ _ _

end Ind

section IndRes

variable {E : Karoubi (Mat_ D) ⥤ Karoubi (Mat_ C)} (adj : mapKaroubi F.mapMat_ ⊣ E) [E.Additive]
  {M M₂ : Type (max w v)} [AddCommGroup M] [Module (MatEnd Y)ᵐᵒᵖ M] [AddCommGroup M₂]
  [Module (MatEnd Y)ᵐᵒᵖ M₂] (f : M →ₗ[(MatEnd Y)ᵐᵒᵖ] M₂)

/-- `resModuleEquiv` is natural in the module. -/
theorem resModuleEquiv_map (m : Res (mapEmbOp F he h) M) :
    letI := HomTensor.transferModule (karoubiMatrixOpY Y) M
    letI := HomTensor.transferModule (karoubiMatrixOpY Y) M₂
    resModuleEquiv F he h adj M₂ (Res.map f m) =
      BalancedTensor.mapRight (HomTensor.transferLinearMap (karoubiMatrixOpY Y) f)
        (resModuleEquiv F he h adj M m) :=
  rfl

variable {J : Type*} [Fintype J]
  (π : J → (E.obj ((toKaroubi _).obj (familySum Y)) ⟶ (toKaroubi _).obj (familySum X)))
  (ι' : J → ((toKaroubi _).obj (familySum X) ⟶ E.obj ((toKaroubi _).obj (familySum Y))))
  (hπ : ∑ j, π j ≫ ι' j = 𝟙 _)

/-- `indResModuleEquiv` is natural in the module. -/
theorem indResModuleEquiv_map (x : Ind (Res (mapEmbOp F he h) M) (mapEmbOp F he h)) :
    letI := HomTensor.transferModule (karoubiMatrixOpY Y) M
    letI := HomTensor.transferModule (karoubiMatrixOpY Y) M₂
    indResModuleEquiv F he h adj M₂ π ι' hπ (Ind.map (Res.map f) x) =
      BalancedTensor.mapRight (HomTensor.transferLinearMap (karoubiMatrixOpY Y) f)
        (indResModuleEquiv F he h adj M π ι' hπ x) := by
  let _ := HomTensor.transferModule (karoubiMatrixOpY Y) M
  let _ := HomTensor.transferModule (karoubiMatrixOpY Y) M₂
  let _ := HomTensor.transferModule (karoubiMatrixOp X) (Res (mapEmbOp F he h) M)
  let _ := HomTensor.transferModule (karoubiMatrixOp X) (Res (mapEmbOp F he h) M₂)
  exact (congrArg (HomTensor.compModuleEquiv ℤ E (mapKaroubi F.mapMat_) _ _ _ π ι' hπ M₂)
    ((congrArg (BalancedTensor.congrRight (k := ℤ)
      (B := (End ((toKaroubi _).obj (familySum Y)))ᵐᵒᵖ)
      (M := (toKaroubi _).obj (familySum Y) ⟶
        (mapKaroubi F.mapMat_).obj ((toKaroubi _).obj (familySum X)))
      (resModuleLinearEquiv F he h adj M₂))
      (indModuleEquiv_map F he h (Res.map f) x)).trans
    (BalancedTensor.congrRight_mapRight (resModuleLinearEquiv F he h adj M)
      (resModuleLinearEquiv F he h adj M₂)
      (HomTensor.transferLinearMap (karoubiMatrixOp X) (Res.map f))
      (BalancedTensor.mapRight (HomTensor.transferLinearMap (karoubiMatrixOpY Y) f))
      (fun m => resModuleEquiv_map F he h adj f m)
      (indModuleEquiv F he h (Res (mapEmbOp F he h) M) x)))).trans
    (HomTensor.compModuleEquiv_mapRight _ _ _ _ _ _ _ _ _ _)

variable {G' : Karoubi (Mat_ D) ⥤ Karoubi (Mat_ D)} [G'.Additive]
  (eG' : G' ≅ E ⋙ mapKaroubi F.mapMat_)

/-- `indResModuleEquivOfIso` is natural in the module. -/
theorem indResModuleEquivOfIso_map (x : Ind (Res (mapEmbOp F he h) M) (mapEmbOp F he h)) :
    letI := HomTensor.transferModule (karoubiMatrixOpY Y) M
    letI := HomTensor.transferModule (karoubiMatrixOpY Y) M₂
    indResModuleEquivOfIso F he h adj M₂ π ι' hπ eG' (Ind.map (Res.map f) x) =
      BalancedTensor.mapRight (HomTensor.transferLinearMap (karoubiMatrixOpY Y) f)
        (indResModuleEquivOfIso F he h adj M π ι' hπ eG' x) := by
  let _ := HomTensor.transferModule (karoubiMatrixOpY Y) M
  let _ := HomTensor.transferModule (karoubiMatrixOpY Y) M₂
  simp only [indResModuleEquivOfIso, LinearEquiv.trans_apply,
    LinearEquiv.restrictScalars_apply, indResModuleEquiv_map]
  exact HomTensor.natModuleEquiv_mapRight _ _ _ _ _

end IndRes

end MatEnd

end Categorification.KLR.Diagram
