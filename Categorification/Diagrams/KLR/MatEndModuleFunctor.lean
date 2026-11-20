/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KLR.MatEndCornerRes
import Categorification.Algebra.HomTensorIndModule

/-!
# Induction and restriction along a matrix map as module functors

In the setting of `MatEndCorner` (an additive functor `F : C ⥤ D`, finite families `X`, `Y` and
an injective `e` with `F (X i) = Y (e i)`), write `G_X`, `G_Y` for the completed sums of `X` and
`Y`, `F'` for the functor induced by `F` on completed additive envelopes and `φ` for the matrix
map of `F`. For every right `MatEnd X`-module `N`,

* induction along `φ` is the module functor of `F'`:
  `Ind N φ ≅ (G_Y ⟶ F' G_X) ⊗_{End G_X} N` (`indModuleEquiv`);

and for a right adjoint `E` of `F'` and every right `MatEnd Y`-module `M`,

* restriction along `φ` is the module functor of `E`:
  `Res_φ M ≅ (G_X ⟶ E G_Y) ⊗_{End G_Y} M` (`resModuleEquiv`).

Both are semilinear for the actions of the target matrix rings. This identifies Webster's
induction and restriction functors on all modules, not only on projective ones, with the
module functors of the categorical action, as used in the proof of Webster, *Knot invariants
and higher representation theory*, arXiv:1309.3796v3, Proposition 5.5.
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

section Ind

variable (N : Type (max w v)) [AddCommGroup N] [Module (MatEnd X)ᵐᵒᵖ N]

/-- **Induction along the matrix map as a module functor**:
`Ind N φ ≅ (G_Y ⟶ F' G_X) ⊗_{End G_X} N`. -/
def indModuleEquiv :
    letI := HomTensor.transferModule (karoubiMatrixOp X) N
    Ind N (mapEmbOp F he h) ≃ₗ[ℤ] BalancedTensor ℤ (End ((toKaroubi _).obj (familySum Y)))ᵐᵒᵖ
      (End ((toKaroubi _).obj (familySum X)))ᵐᵒᵖ
      ((toKaroubi _).obj (familySum Y) ⟶
        (mapKaroubi F.mapMat_).obj ((toKaroubi _).obj (familySum X))) N :=
  letI := HomTensor.transferModule (karoubiMatrixOp X) N
  HomTensor.indTensorEquiv (F := mapKaroubi F.mapMat_) (karoubiCorner F he h)
    (karoubiCorner_op_smul F he h) (AddEquiv.refl N)
    (fun a n => (HomTensor.transferModule_smul a n).symm)

theorem indModuleEquiv_tmul (z : Corner (mapEmbOp F he h)) (n : N) :
    letI := HomTensor.transferModule (karoubiMatrixOp X) N
    indModuleEquiv F he h N (Ind.tmul z n) = BalancedTensor.tmul (karoubiCorner F he h z) n :=
  rfl

/-- `indModuleEquiv` is semilinear along `karoubiMatrixOpY`. -/
theorem indModuleEquiv_smul (b : (MatEnd Y)ᵐᵒᵖ) (x : Ind N (mapEmbOp F he h)) :
    letI := HomTensor.transferModule (karoubiMatrixOp X) N
    indModuleEquiv F he h N (b • x) = karoubiMatrixOpY Y b • indModuleEquiv F he h N x :=
  letI := HomTensor.transferModule (karoubiMatrixOp X) N
  HomTensor.indTensorEquiv_smul (F := mapKaroubi F.mapMat_) (karoubiCorner F he h)
    (karoubiCorner_op_smul F he h) (AddEquiv.refl N) _ (karoubiMatrixOpY Y)
    (karoubiCorner_smul F he h) b x

end Ind

section Res

variable {E : Karoubi (Mat_ D) ⥤ Karoubi (Mat_ C)} (adj : mapKaroubi F.mapMat_ ⊣ E)

/-- The regular right module of `MatEnd Y` as endomorphisms of the completed sum. -/
def regularHom :
    letI := HomTensor.homModule _ (karoubiMatrixOpY Y) ((toKaroubi _).obj (familySum Y))
    (MatEnd Y)ᵐᵒᵖ ≃ₗ[(MatEnd Y)ᵐᵒᵖ]
      ((toKaroubi _).obj (familySum Y) ⟶ (toKaroubi _).obj (familySum Y)) :=
  letI := HomTensor.homModule _ (karoubiMatrixOpY Y) ((toKaroubi _).obj (familySum Y))
  { toFun := fun b => (karoubiMatrixOpY Y b).unop
    invFun := fun f => (karoubiMatrixOpY Y).symm (op f)
    left_inv := fun b => by simp
    right_inv := fun f => by simp
    map_add' := fun b b' => by rw [map_add]; rfl
    map_smul' := fun b b' => by
      change (karoubiMatrixOpY Y (b * b')).unop = (karoubiMatrixOpY Y b).unop ≫
        (karoubiMatrixOpY Y b').unop
      rw [map_mul, unop_mul, End.mul_def] }

theorem regularHom_apply (b : (MatEnd Y)ᵐᵒᵖ) :
    letI := HomTensor.homModule _ (karoubiMatrixOpY Y) ((toKaroubi _).obj (familySum Y))
    regularHom (Y := Y) b = (karoubiMatrixOpY Y b).unop :=
  rfl

/-- Restriction of the regular module along `regularHom`. -/
def resRegular :
    letI := HomTensor.homModule _ (karoubiMatrixOpY Y) ((toKaroubi _).obj (familySum Y))
    Res (mapEmbOp F he h) (MatEnd Y)ᵐᵒᵖ ≃+
      Res (mapEmbOp F he h) ((toKaroubi _).obj (familySum Y) ⟶ (toKaroubi _).obj (familySum Y)) :=
  letI := HomTensor.homModule _ (karoubiMatrixOpY Y) ((toKaroubi _).obj (familySum Y))
  { toFun := fun x => Res.mk (regularHom (Y := Y) x.val) (by rw [← map_smul, x.prop])
    invFun := fun x => Res.mk ((regularHom (Y := Y)).symm x.val) (by rw [← map_smul, x.prop])
    left_inv := fun x => Res.ext ((regularHom (Y := Y)).symm_apply_apply x.val)
    right_inv := fun x => Res.ext ((regularHom (Y := Y)).apply_symm_apply x.val)
    map_add' := fun x y => Res.ext (map_add (regularHom (Y := Y)) x.val y.val) }

/-- Restriction of the regular module along the matrix map, as morphisms into the right
adjoint: `Res_φ (MatEnd Y) ≅ (G_X ⟶ E G_Y)`. -/
def resRegularHom :
    Res (mapEmbOp F he h) (MatEnd Y)ᵐᵒᵖ ≃+
      ((toKaroubi _).obj (familySum X) ⟶ E.obj ((toKaroubi _).obj (familySum Y))) :=
  letI := HomTensor.homModule _ (karoubiMatrixOpY Y) ((toKaroubi _).obj (familySum Y))
  ((resRegular F he h).trans (resEquivKaroubi F he h _)).trans (adj.homAddEquiv _ _)

theorem resRegularHom_apply (x : Res (mapEmbOp F he h) (MatEnd Y)ᵐᵒᵖ) :
    letI := HomTensor.homModule _ (karoubiMatrixOpY Y) ((toKaroubi _).obj (familySum Y))
    resRegularHom F he h adj x =
      adj.homEquiv _ _ (karoubiSect F h ≫ (karoubiMatrixOpY Y x.val).unop) :=
  rfl

theorem resRegularHom_op_smul (b : (MatEnd Y)ᵐᵒᵖ) (x : Res (mapEmbOp F he h) (MatEnd Y)ᵐᵒᵖ) :
    resRegularHom F he h adj (op b • x) =
      resRegularHom F he h adj x ≫ E.map (karoubiMatrixOpY Y b).unop := by
  rw [resRegularHom_apply, resRegularHom_apply, ← adj.homEquiv_naturality_right,
    Category.assoc]
  congr 2
  change (karoubiMatrixOpY Y (x.val * b)).unop = _
  rw [map_mul, unop_mul, End.mul_def]

theorem resRegular_smul (a : (MatEnd X)ᵐᵒᵖ) (x : Res (mapEmbOp F he h) (MatEnd Y)ᵐᵒᵖ) :
    letI := HomTensor.homModule _ (karoubiMatrixOpY Y) ((toKaroubi _).obj (familySum Y))
    resRegular F he h (a • x) = a • resRegular F he h x :=
  letI := HomTensor.homModule _ (karoubiMatrixOpY Y) ((toKaroubi _).obj (familySum Y))
  Res.ext (map_smul (regularHom (Y := Y)) _ x.val)

theorem resRegularHom_eq (x : Res (mapEmbOp F he h) (MatEnd Y)ᵐᵒᵖ) :
    letI := HomTensor.homModule _ (karoubiMatrixOpY Y) ((toKaroubi _).obj (familySum Y))
    resRegularHom F he h adj x =
      adj.homEquiv _ _ (resEquivKaroubi F he h _ (resRegular F he h x)) :=
  rfl

theorem resRegularHom_smul (a : (MatEnd X)ᵐᵒᵖ) (x : Res (mapEmbOp F he h) (MatEnd Y)ᵐᵒᵖ) :
    resRegularHom F he h adj (a • x) =
      (karoubiMatrixOp X a).unop ≫ resRegularHom F he h adj x := by
  let _ := HomTensor.homModule _ (karoubiMatrixOpY Y) ((toKaroubi _).obj (familySum Y))
  rw [resRegularHom_eq, resRegularHom_eq, resRegular_smul, resEquivKaroubi_smul,
    adj.homEquiv_naturality_left]

variable [E.Additive] (M : Type (max w v)) [AddCommGroup M] [Module (MatEnd Y)ᵐᵒᵖ M]

/-- **Restriction along the matrix map as a module functor**: for a right adjoint `E` of
`F'`, `Res_φ M ≅ (G_X ⟶ E G_Y) ⊗_{End G_Y} M`. -/
def resModuleEquiv :
    letI := HomTensor.transferModule (karoubiMatrixOpY Y) M
    Res (mapEmbOp F he h) M ≃ₗ[ℤ] BalancedTensor ℤ (End ((toKaroubi _).obj (familySum X)))ᵐᵒᵖ
      (End ((toKaroubi _).obj (familySum Y)))ᵐᵒᵖ
      ((toKaroubi _).obj (familySum X) ⟶ E.obj ((toKaroubi _).obj (familySum Y))) M :=
  HomTensor.resTensorEquiv (F := E) (σ := karoubiMatrixOpY Y) (resRegularHom F he h adj)
    (resRegularHom_op_smul F he h adj) M

/-- `resModuleEquiv` is semilinear along `karoubiMatrixOp`. -/
theorem resModuleEquiv_smul (a : (MatEnd X)ᵐᵒᵖ) (m : Res (mapEmbOp F he h) M) :
    letI := HomTensor.transferModule (karoubiMatrixOpY Y) M
    resModuleEquiv F he h adj M (a • m) = karoubiMatrixOp X a • resModuleEquiv F he h adj M m :=
  HomTensor.resTensorEquiv_smul (F := E) (σ := karoubiMatrixOpY Y) (resRegularHom F he h adj)
    (resRegularHom_op_smul F he h adj) M (karoubiMatrixOp X) (resRegularHom_smul F he h adj) a m

end Res

end MatEnd

end Categorification.KLR.Diagram
