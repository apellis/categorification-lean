/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.ProjectiveKProjective

/-!
# The regular input of derived tensor

The right tensor unitor computes derived tensor on the regular dg module.
This is used for Webster's fundamental cup in arXiv:1309.3796v2,
Definition 7.4.
-/

noncomputable section

namespace Categorification

open CategoryTheory DG MulOpposite
open scoped DG.DegreeZero

universe u v
variable (A B : Type u) [Ring A] [Ring B] (M : Type u) [AddCommGroup M]
  [Module A M] [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]

/-- The ordinary coefficient is recovered by tensoring with the regular dg module. -/
def tensorRegularCoefficientIso :
    (DGModuleCat.tensorFunctor A (InDegreeZero M)).obj (DGModuleCat.of B B) ≅
      DGModuleCat.of A (InDegreeZero M) := by
  let e := TensorProductOver.rid B (InDegreeZero M)
  have h (a : A) (z : TensorProductOver B (InDegreeZero M) B) : e (a • z) = a • e z := by
    induction z using TensorProductOver.induction_on with
    | zero => simp
    | tmul m b =>
      change e (TensorProductOver.tmul B (a • m) b) =
        a • e (TensorProductOver.tmul B m b)
      simpa only [e, TensorProductOver.rid_tmul] using
        (smul_comm a (op b) m).symm
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  exact DGModuleCat.isoOfDGModuleEquiv
    { toLinearEquiv := { e.toAddEquiv with map_smul' := h }
      map_mem' := fun hz => e.map_mem hz
      map_d' := e.map_d }

/-- The derived tensor of the regular module is the ordinary coefficient in degree zero. -/
def derivedTensorRegularCoefficientIso [HasDerivedCategory.{v,u} A] [HasDerivedCategory.{v,u} B] :
    (derivedTensor A B M).obj (DG.DerivedCategory.Q.obj (DGModuleCat.of B B)) ≅
      DG.DerivedCategory.Q.obj (DGModuleCat.of A (InDegreeZero M)) :=
  derivedTensorObjIso (A := A) (M := M) (isKProjective_self (A := B)) ≪≫
    DG.DerivedCategory.Q.mapIso (tensorRegularCoefficientIso A B M)

end Categorification
