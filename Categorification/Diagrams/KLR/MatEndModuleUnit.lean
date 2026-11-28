/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KLR.MatEndModuleComp

/-!
# The unit and counit of induction along a matrix map as module functors

In the setting of `MatEndModuleComp` (an additive functor `F : C ⥤ D`, finite families `X`,
`Y` with `F (X i) = Y (e i)`, completed sums `G_X`, `G_Y`, the functor `F'` induced by `F` on
completed additive envelopes with a right adjoint `E`, `adj : F' ⊣ E`, and the matrix map `φ` of
`F`), restriction after induction and induction after restriction along `φ` are the module
functors of `F' ⋙ E` and `E ⋙ F'` (`MatEnd.resIndModuleEquiv`, `MatEnd.indResModuleEquiv`).
Under these identifications the unit and counit of the adjunction `Ind ⊣ Res` along `φ` are
the module maps of the unit and counit of `adj`:

* `MatEnd.resIndModuleEquiv_unitMap`: the unit `n ↦ φ(1) ⊗ n` is `n ↦ η_{G_X} ⊗ n`;
* `MatEnd.natModuleMap_counit_indResModuleEquiv`: the counit `z ⊗ m ↦ z m` followed by
  `m ↦ 𝟙 ⊗ m` is `ε` applied to the module functor of `E ⋙ F'`.

These identify Webster's induction–restriction adjunction on modules over `T^λ`
(arXiv:1309.3796v3, §4.6) with the adjunction of the categorical action.
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

variable {E : Karoubi (Mat_ D) ⥤ Karoubi (Mat_ C)} (adj : mapKaroubi F.mapMat_ ⊣ E) [E.Additive]

theorem karoubiSect_matrixOpY_one :
    karoubiSect F h ≫ (karoubiMatrixOpY Y (mapEmbOp F he h 1)).unop = karoubiSect F h := by
  rw [karoubiSect_matrixOpY F he h 1, map_one]
  change (mapKaroubi F.mapMat_).map (𝟙 _) ≫ _ = _
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

/-- **The unit of `Ind ⊣ Res` along the matrix map is the unit of `adj`**: under
`resIndModuleEquiv`, `n ↦ φ(1) ⊗ n` is `n ↦ η_{G_X} ⊗ n`. -/
theorem resIndModuleEquiv_unitMap (N : Type (max w v)) [AddCommGroup N]
    [Module (MatEnd X)ᵐᵒᵖ N] (n : N) :
    letI := HomTensor.transferModule (karoubiMatrixOp X) N
    resIndModuleEquiv F he h N adj (unitMap (φ := mapEmbOp F he h) N n) =
      BalancedTensor.tmul (show (toKaroubi _).obj (familySum X) ⟶
        (mapKaroubi F.mapMat_ ⋙ E).obj ((toKaroubi _).obj (familySum X)) from
          adj.unit.app ((toKaroubi _).obj (familySum X))) n := by
  let _ := HomTensor.transferModule (karoubiMatrixOp X) N
  let _ := HomTensor.transferModule (karoubiMatrixOpY Y) (Ind N (mapEmbOp F he h))
  change HomTensor.compModuleEquiv ℤ (mapKaroubi F.mapMat_) E _ _ _
      (fun _ : Unit => karoubiSect F h) (fun _ => karoubiGen F he h)
      (karoubiSect_gen_sum F he h) N
      (BalancedTensor.tmul (resRegularHom F he h adj (resUnit _))
        (indModuleEquiv F he h N (Ind.tmul (unitGen _) n))) = _
  rw [indModuleEquiv_tmul, HomTensor.compModuleEquiv_tmul]
  congr 1
  change adj.homEquiv _ _ (karoubiSect F h ≫ (karoubiMatrixOpY Y (mapEmbOp F he h 1)).unop) ≫
      E.map (karoubiGen F he h) = _
  rw [karoubiSect_matrixOpY_one, Adjunction.homEquiv_unit, Category.assoc, ← E.map_comp,
    karoubiSect_gen, CategoryTheory.Functor.map_id]
  exact Category.comp_id _

theorem karoubiCorner_sect (z : Corner (mapEmbOp F he h)) :
    karoubiCorner F he h z ≫ karoubiSect F h = (karoubiMatrixOpY Y z.1).unop := by
  have hz : z = z.1 • unitGen (mapEmbOp F he h) := Subtype.ext z.2.symm
  conv_lhs => rw [hz, karoubiCorner_smul, Category.assoc, karoubiGen_sect]
  have := congrArg (fun b => (karoubiMatrixOpY Y b).unop) z.2
  rwa [map_mul, unop_mul, End.mul_def] at this

section IndRes

variable (M : Type (max w v)) [AddCommGroup M] [Module (MatEnd Y)ᵐᵒᵖ M]
  {J : Type*} [Fintype J]
  (π : J → (E.obj ((toKaroubi _).obj (familySum Y)) ⟶ (toKaroubi _).obj (familySum X)))
  (ι' : J → ((toKaroubi _).obj (familySum X) ⟶ E.obj ((toKaroubi _).obj (familySum Y))))
  (hπ : ∑ j, π j ≫ ι' j = 𝟙 _)

/-- **The counit of `Ind ⊣ Res` along the matrix map is the counit of `adj`**: under
`indResModuleEquiv`, the module map of `ε : E ⋙ F' ⟶ 𝟭` is `z ⊗ m ↦ 𝟙 ⊗ z m`. -/
theorem natModuleMap_counit_indResModuleEquiv
    (x : Ind (Res (mapEmbOp F he h) M) (mapEmbOp F he h)) :
    letI := HomTensor.transferModule (karoubiMatrixOpY Y) M
    HomTensor.natModuleMap ℤ ((toKaroubi _).obj (familySum Y)) ((toKaroubi _).obj (familySum Y))
        M (show E ⋙ mapKaroubi F.mapMat_ ⟶ 𝟭 _ from adj.counit)
        (indResModuleEquiv F he h adj M π ι' hπ x) =
      BalancedTensor.tmul (show (toKaroubi _).obj (familySum Y) ⟶
        (𝟭 _).obj ((toKaroubi _).obj (familySum Y)) from 𝟙 _) (counitMap M x) := by
  let _ := HomTensor.transferModule (karoubiMatrixOpY Y) M
  induction x using Ind.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, BalancedTensor.tmul_zero]
  | add s t hs ht => rw [map_add, map_add, hs, ht, map_add, BalancedTensor.tmul_add]
  | tmul z m =>
    change BalancedTensor.tmul ((karoubiCorner F he h z ≫ (mapKaroubi F.mapMat_).map
        (adj.homEquiv _ _ (karoubiSect F h ≫
          (karoubiMatrixOpY Y (mapEmbOp F he h 1)).unop))) ≫ adj.counit.app _) m.val = _
    have key : (mapKaroubi F.mapMat_).map (adj.homEquiv _ _ (karoubiSect F h)) ≫
        adj.counit.app _ = karoubiSect F h := by
      have := (adj.homEquiv _ _).symm_apply_apply (karoubiSect F h)
      rw [Adjunction.homEquiv_counit] at this
      exact this
    rw [karoubiSect_matrixOpY_one, Category.assoc]
    erw [key]
    rw [karoubiCorner_sect, counitMap_tmul,
      ← HomTensor.transferModule_smul (σ := karoubiMatrixOpY Y), ← BalancedTensor.op_smul_tmul]
    congr 1
    exact (Category.id_comp _).symm

end IndRes

end MatEnd

end Categorification.KLR.Diagram
