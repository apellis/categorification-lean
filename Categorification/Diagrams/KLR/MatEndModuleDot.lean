/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KLR.MatEndModuleUnit
import Categorification.Algebra.HomTensorCompNat

/-!
# Endomorphisms of induction along a matrix map as module maps

In the setting of `MatEndModuleUnit`, let `d` be an element of the matrix ring of `Y` that
intertwines the matrix map `φ` with itself, so that right multiplication by `d` is an
endomorphism `z ⊗ n ↦ z d ⊗ n` of induction along `φ` (`InductionAlong.natMap`). Suppose that
on the corner generator it is a natural endomorphism `α` of the induced functor `F'`:
`karoubiCorner (φ(1) d) = karoubiGen ≫ α_{G_X}`. Then under the identifications of
`MatEndModuleComp` it is the module map of `α`:

* `MatEnd.indModuleEquiv_natMap`: on `Ind N`, the module map of `α`;
* `MatEnd.indResModuleEquiv_natMap`: on `Ind (Res M)`, the module map of `E ◁ α`;
* `MatEnd.resIndModuleEquiv_resMap_natMap`: on `Res (Ind N)`, the module map of `α ▷ E`.

These identify the dots of Webster's induction functors on modules over `T^λ`
(arXiv:1309.3796v3, §4.6) with the dots of the categorical action (Theorem 4.31 there).
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

variable {d : (MatEnd Y)ᵐᵒᵖ} (hd : Intertwines (mapEmbOp F he h) (mapEmbOp F he h) d)

theorem cornerMul_smul (b : (MatEnd Y)ᵐᵒᵖ) (z : Corner (mapEmbOp F he h)) :
    cornerMul hd (b • z) = b • cornerMul hd z :=
  Subtype.ext (mul_assoc b z.1 d)

variable {α : mapKaroubi F.mapMat_ ⟶ mapKaroubi F.mapMat_}
  (hα : karoubiCorner F he h (cornerMul hd (unitGen (mapEmbOp F he h))) =
    karoubiGen F he h ≫ α.app ((toKaroubi _).obj (familySum X)))

include hα in
theorem karoubiCorner_cornerMul (z : Corner (mapEmbOp F he h)) :
    karoubiCorner F he h (cornerMul hd z) =
      karoubiCorner F he h z ≫ α.app ((toKaroubi _).obj (familySum X)) := by
  have hz : z = z.1 • unitGen (mapEmbOp F he h) := Subtype.ext z.2.symm
  rw [hz, cornerMul_smul, karoubiCorner_smul, karoubiCorner_smul, hα, Category.assoc]

include hα in
/-- **Right multiplication by `d` on `Ind N` is the module map of `α`.** -/
theorem indModuleEquiv_natMap (N : Type (max w v)) [AddCommGroup N] [Module (MatEnd X)ᵐᵒᵖ N]
    (x : Ind N (mapEmbOp F he h)) :
    letI := HomTensor.transferModule (karoubiMatrixOp X) N
    indModuleEquiv F he h N (natMap hd x) =
      HomTensor.natModuleMap ℤ ((toKaroubi _).obj (familySum X))
        ((toKaroubi _).obj (familySum Y)) N α (indModuleEquiv F he h N x) := by
  let _ := HomTensor.transferModule (karoubiMatrixOp X) N
  induction x using Ind.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | add s t hs ht => rw [map_add, map_add, hs, ht, map_add, map_add]
  | tmul z n =>
    rw [natMap_tmul, indModuleEquiv_tmul, indModuleEquiv_tmul, HomTensor.natModuleMap_tmul,
      karoubiCorner_cornerMul F he h hd hα]

variable {E : Karoubi (Mat_ D) ⥤ Karoubi (Mat_ C)} (adj : mapKaroubi F.mapMat_ ⊣ E) [E.Additive]

section IndRes

variable (M : Type (max w v)) [AddCommGroup M] [Module (MatEnd Y)ᵐᵒᵖ M]
  {J : Type*} [Fintype J]
  (π : J → (E.obj ((toKaroubi _).obj (familySum Y)) ⟶ (toKaroubi _).obj (familySum X)))
  (ι' : J → ((toKaroubi _).obj (familySum X) ⟶ E.obj ((toKaroubi _).obj (familySum Y))))
  (hπ : ∑ j, π j ≫ ι' j = 𝟙 _)

include hα in
/-- **Right multiplication by `d` on `Ind (Res M)` is the module map of `E ◁ α`.** -/
theorem indResModuleEquiv_natMap (x : Ind (Res (mapEmbOp F he h) M) (mapEmbOp F he h)) :
    letI := HomTensor.transferModule (karoubiMatrixOpY Y) M
    indResModuleEquiv F he h adj M π ι' hπ (natMap hd x) =
      HomTensor.natModuleMap ℤ ((toKaroubi _).obj (familySum Y))
        ((toKaroubi _).obj (familySum Y)) M (Functor.whiskerLeft E α)
        (indResModuleEquiv F he h adj M π ι' hπ x) := by
  let _ := HomTensor.transferModule (karoubiMatrixOpY Y) M
  induction x using Ind.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | add s t hs ht => rw [map_add, map_add, hs, ht, map_add, map_add]
  | tmul z m =>
    rw [natMap_tmul]
    change BalancedTensor.tmul (show (toKaroubi _).obj (familySum Y) ⟶
        (E ⋙ mapKaroubi F.mapMat_).obj ((toKaroubi _).obj (familySum Y)) from
        karoubiCorner F he h (cornerMul hd z) ≫ (mapKaroubi F.mapMat_).map (adj.homEquiv _ _
          (karoubiSect F h ≫ (karoubiMatrixOpY Y (mapEmbOp F he h 1)).unop))) m.val =
      BalancedTensor.tmul (show (toKaroubi _).obj (familySum Y) ⟶
        (E ⋙ mapKaroubi F.mapMat_).obj ((toKaroubi _).obj (familySum Y)) from
        (karoubiCorner F he h z ≫ (mapKaroubi F.mapMat_).map (adj.homEquiv _ _
          (karoubiSect F h ≫ (karoubiMatrixOpY Y (mapEmbOp F he h 1)).unop))) ≫
          α.app (E.obj ((toKaroubi _).obj (familySum Y)))) m.val
    rw [karoubiCorner_cornerMul F he h hd hα, Category.assoc, Category.assoc, α.naturality]

end IndRes

include hα in
/-- **Right multiplication by `d` on `Res (Ind N)` is the module map of `α ▷ E`.** -/
theorem resIndModuleEquiv_resMap_natMap (N : Type (max w v)) [AddCommGroup N]
    [Module (MatEnd X)ᵐᵒᵖ N] (m : Res (mapEmbOp F he h) (Ind N (mapEmbOp F he h))) :
    letI := HomTensor.transferModule (karoubiMatrixOp X) N
    resIndModuleEquiv F he h N adj (Res.map (natMap hd) m) =
      HomTensor.natModuleMap ℤ ((toKaroubi _).obj (familySum X))
        ((toKaroubi _).obj (familySum X)) N (Functor.whiskerRight α E)
        (resIndModuleEquiv F he h N adj m) := by
  let _ := HomTensor.transferModule (karoubiMatrixOp X) N
  let _ := HomTensor.transferModule (karoubiMatrixOpY Y) (Ind N (mapEmbOp F he h))
  change HomTensor.compModuleEquiv ℤ (mapKaroubi F.mapMat_) E _ _ _
      (fun _ : Unit => karoubiSect F h) (fun _ => karoubiGen F he h)
      (karoubiSect_gen_sum F he h) N
      (BalancedTensor.tmul (resRegularHom F he h adj (resUnit _))
        (indModuleEquiv F he h N (natMap hd m.val))) =
    HomTensor.natModuleMap ℤ _ _ N (Functor.whiskerRight α E)
      (HomTensor.compModuleEquiv ℤ (mapKaroubi F.mapMat_) E _ _ _
        (fun _ : Unit => karoubiSect F h) (fun _ => karoubiGen F he h)
        (karoubiSect_gen_sum F he h) N
        (BalancedTensor.tmul (resRegularHom F he h adj (resUnit _))
          (indModuleEquiv F he h N m.val)))
  have key := HomTensor.compModuleEquiv_mapRight_natModuleMap ℤ (mapKaroubi F.mapMat_) E _ _ _
    (fun _ : Unit => karoubiSect F h) (fun _ => karoubiGen F he h) (karoubiSect_gen_sum F he h)
    N α (fun _ : Unit => karoubiSect F h) (fun _ => karoubiGen F he h)
    (karoubiSect_gen_sum F he h)
    (BalancedTensor.tmul (resRegularHom F he h adj (resUnit _))
      (indModuleEquiv F he h N m.val))
  rw [BalancedTensor.mapRight_tmul] at key
  rw [indModuleEquiv_natMap F he h hd hα]
  exact key

end MatEnd

end Categorification.KLR.Diagram
