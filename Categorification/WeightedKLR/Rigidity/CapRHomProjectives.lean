/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CapProjectives
import Categorification.WeightedKLR.Rigidity.DerivedCupHom
import DG.Category.Tensor.SingleObj

/-!
# The tensor–Hom adjoint on a projective input

For the evaluation in Webster, arXiv:1309.3796v2, Definition 7.4 and
Proposition 7.5, the left adjoint to the scalar derived Hom cup evaluates a
projective by ordinary tensor. This compares the one-object dg category
and dg ring tensor constructions at the level of the output modules.
-/

noncomputable section
namespace Categorification.Stendhal.Coevaluation
open CategoryTheory DG MulOpposite
open scoped DG.DegreeZero
universe u v
variable (k A L : Type u) [Field k] [Ring A] [Algebra k A] [AddCommGroup L]
    [Module k L] [Module A L] [IsScalarTower k A L]

private instance : SMulCommClass A k L where
  smul_comm a c x := smul_algebra_smul_comm c a x

local notation "M₀" => InDegreeZero (OpBimodule A L)
local notation "B₀" => DGBimodule.catBimodule k Aᵐᵒᵖ M₀

private def capTensorObjIso (P : DGModuleCat.{u} Aᵐᵒᵖ) :
    (B₀).tensorObj (DGModuleCat.toCatModuleObj P) ≅
      DGModuleCat.toCatModuleObj ((DGModuleCat.tensorFunctor k M₀).obj P) := by
  let e := CatTensorProduct.singleObjEquiv M₀ P
  refine CatModule.isoMk (fun _ => e.toAddEquiv) ?_ (fun {_} x => e.map_d x) ?_
  · intro X j x
    exact ⟨fun hx => (e.symm_apply_apply x) ▸ e.symm.map_mem hx, fun hx => e.map_mem hx⟩
  · intro X Y a z
    let Z := DGModuleCat.toCatModuleObj P
    let U := TensorProductOver Aᵐᵒᵖ M₀ P
    let F (j : SingleObj k) : CatTensorProduct ((B₀).right j) Z →+ U := e.toAddEquiv.toAddMonoidHom
    have elem (j : SingleObj k) (t : SingleObj Aᵐᵒᵖ) (m : M₀) (p : P) :
        F j (CatTensorProduct.tmul t m p) = TensorProductOver.tmul Aᵐᵒᵖ m p :=
      CatTensorProduct.singleObjEquiv_tmul M₀ P t m p
    have commute : (F Y).comp ((B₀).tensorAct Z a) =
        (DistribSMul.toAddMonoidHom U (show k from a)).comp (F X) := by
      apply CatTensorProduct.addHom_ext
      intro t m p
      change F Y ((B₀).tensorAct Z a (CatTensorProduct.tmul t m p)) =
        (show k from a) • F X (CatTensorProduct.tmul t m p)
      rw [CatBimodule.tensorAct_tmul]
      exact (elem Y t ((show k from a) • (show M₀ from m)) p).trans
        ((TensorProductOver.smul_tmul _ _ _).symm.trans
          (congrArg ((show k from a) • ·) (elem X t m p).symm))
    exact DFunLike.congr_fun commute z

variable [CatModule.HasDerivedCategory.{v,u} (SingleObj k)]
    [CatModule.HasDerivedCategory.{v,u} (SingleObj Aᵐᵒᵖ)]
    [HasDerivedCategory.{v,u} k] [HasDerivedCategory.{v,u} Aᵐᵒᵖ]

/-- The cap left adjoint to the scalar derived Hom cup and the projective-resolution
cap agree on each K-projective input. -/
def capBimoduleProjectiveIso (P : DGModuleCat.{u} Aᵐᵒᵖ) (hP : IsKProjective.{u} Aᵐᵒᵖ P) :
    (capBimoduleFunctor k A L).obj (DG.DerivedCategory.Q.obj P) ≅
      (capFunctor k A L).obj (DG.DerivedCategory.Q.obj P) := by
  let hM : IsKProjective.{u} k M₀ := InDegreeZero.isKProjective
  let hB := DGBimodule.catBimodule_left_isKProjective k Aᵐᵒᵖ M₀ hM
  let F := CatModule.DerivedCategory.singleObjEquivalence Aᵐᵒᵖ
  let G := CatModule.DerivedCategory.singleObjEquivalence k
  let t := CatModule.DerivedCategory.derivedTensor.{v,v} B₀ hB
  let Z := DGModuleCat.toCatModuleObj P
  have i : F.inverse.obj (DG.DerivedCategory.Q.obj P) ≅ CatModule.DerivedCategory.Q.obj Z :=
    F.inverse.mapIso (DG.DerivedCategory.singleObjEquivalenceObjIso P).symm ≪≫
      (F.unitIso.app _).symm
  exact G.functor.mapIso (t.mapIso i ≪≫
    (CatModule.DerivedCategory.derivedTensorObjIso B₀ hB hP.toCatModuleObj).symm ≪≫
    CatModule.DerivedCategory.Q.mapIso (capTensorObjIso k A L P)) ≪≫
    DG.DerivedCategory.singleObjEquivalenceObjIso _ ≪≫
    (derivedTensorObjIso (A := k) (M := OpBimodule A L) hP).symm

end Categorification.Stendhal.Coevaluation
