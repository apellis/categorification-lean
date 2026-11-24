/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DerivedTensor

/-!
# Maps on derived tensor in the ordinary coefficient

A bimodule map induces a natural transformation of derived tensor
functors. On a K-projective representative it is the ordinary DG
tensor map acting in the first factor.
-/

open CategoryTheory DG MulOpposite
open scoped DG.DegreeZero

set_option backward.isDefEq.respectTransparency false

namespace Categorification

noncomputable section

universe u w

section DG

open TensorProductOver

variable {A B : Type u} [Ring A] [DGAddCommGroup A] [Ring B] [DGAddCommGroup B]
  {M M' : Type u} [AddCommGroup M] [DGAddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M]
  [DGBimodule A B M] [AddCommGroup M'] [DGAddCommGroup M'] [Module A M'] [Module Bᵐᵒᵖ M']
  [DGBimodule A B M']

private def tensorCoeffRightLinear (f : M →ᵈᵍ[A] M') (hf : ∀ (b : B) (m : M), f (op b • m) = op b • f m) :
    M →ₗ[Bᵐᵒᵖ] M' where
  toFun := f
  map_add' := map_add f
  map_smul' b m := hf b.unop m

/-- A DG bimodule map acting on the coefficient of a balanced DG tensor. -/
def tensorCoeffHom (f : M →ᵈᵍ[A] M') (hf : ∀ (b : B) (m : M), f (op b • m) = op b • f m)
    (N : DGModuleCat.{u} B) : TensorProductOver B M N →ᵈᵍ[A] TensorProductOver B M' N where
  toFun := map (tensorCoeffRightLinear f hf) LinearMap.id
  map_add' := map_add _
  map_smul' a x := by
    induction x using TensorProductOver.induction_on with
    | zero => simp
    | tmul m n =>
      change tmul B (f (a • m)) n = a • tmul B (f m) n
      rw [map_smul, smul_tmul]
    | add x y hx hy => simp only [smul_add, map_add, hx, hy, RingHom.id_apply] at *
  map_mem' hx := map_mem _ _ (fun hm => f.map_mem hm) (fun hn => hn) hx
  map_d' x := by
    induction x using TensorProductOver.induction_on with
    | zero => simp
    | tmul m n =>
      induction m using DG.induction_on with
      | h_zero => simp
      | @h_homogeneous j m =>
        change map (tensorCoeffRightLinear f hf) LinearMap.id (d (tmul B (m : M) n)) =
          d (tmul B (f m) n)
        rw [TensorProductOver.d_tmul_of_mem m.2, TensorProductOver.d_tmul_of_mem (f.map_mem m.2),
          map_add, map_units_zsmul]
        change tmul B (f (d (m : M))) n + koszulSign j • tmul B (f m) (d n) = _
        rw [f.map_d]
      | h_add m m' hm hm' =>
        rw [add_tmul, d_add, map_add, map_add, d_add, hm, hm']
    | add x y hx hy => rw [d_add, map_add, map_add, hx, hy, d_add]

/-- The DG tensor map induced by a DG bimodule map in the coefficient. -/
def tensorCoeffNat (f : M →ᵈᵍ[A] M') (hf : ∀ (b : B) (m : M), f (op b • m) = op b • f m) :
    DGModuleCat.tensorFunctor (B := B) A M ⟶ DGModuleCat.tensorFunctor (B := B) A M' where
  app N := DGModuleCat.ofHom (tensorCoeffHom f hf N)
  naturality {_X _Y} _g := DGModuleCat.tensor_hom_ext (M := M) fun _ _ => rfl

/-- The coefficient map on balanced DG tensor descends to the homotopy category. -/
def homotopyTensorCoeffNat (f : M →ᵈᵍ[A] M')
    (hf : ∀ (b : B) (m : M), f (op b • m) = op b • f m) :
    DG.HomotopyCategory.tensorFunctor (B := B) A M ⟶
      DG.HomotopyCategory.tensorFunctor (B := B) A M' :=
  CategoryTheory.Quotient.natTransLift _
    ((DG.HomotopyCategory.tensorFunctorQuotientIso A M).hom ≫
      Functor.whiskerRight (tensorCoeffNat f hf) (DG.HomotopyCategory.quotient A) ≫
      (DG.HomotopyCategory.tensorFunctorQuotientIso A M').inv)

end DG

section Ordinary

variable {A B : Type u} [Ring A] [Ring B]
  {M M' : Type u} [AddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]
  [AddCommGroup M'] [Module A M'] [Module Bᵐᵒᵖ M'] [SMulCommClass A Bᵐᵒᵖ M']

private def coefficientHomDegreeZero (f : M →ₗ[A] M') :
    InDegreeZero M →ᵈᵍ[A] InDegreeZero M' where
  toFun := f
  map_add' := map_add f
  map_smul' := f.map_smul'
  map_mem' hx := by
    rw [InDegreeZero.mem_grading_iff] at hx ⊢
    exact hx.imp_right fun h => by rw [h]; exact map_zero f
  map_d' _ := map_zero f

/-- An ordinary bimodule map acting on the coefficient of the DG tensor functor. -/
def ordinaryTensorCoefficientMap (f : M →ₗ[A] M')
    (hf : ∀ (b : B) (m : M), f (op b • m) = op b • f m) :
    DGModuleCat.tensorFunctor (B := B) A (InDegreeZero M) ⟶
      DGModuleCat.tensorFunctor (B := B) A (InDegreeZero M') :=
  tensorCoeffNat (coefficientHomDegreeZero f) hf

/-- The ordinary coefficient map applies to the first component of a pure tensor. -/
theorem ordinaryTensorCoefficientMap_tmul (f : M →ₗ[A] M')
    (hf : ∀ (b : B) (m : M), f (op b • m) = op b • f m)
    (P : DGModuleCat.{u} B) (m : M) (p : P) :
    (ordinaryTensorCoefficientMap f hf).app P
        (TensorProductOver.tmul B (show InDegreeZero M from m) p) =
      TensorProductOver.tmul B (show InDegreeZero M' from f m) p := rfl

variable  [HasDerivedCategory.{w,u} A] [HasDerivedCategory.{w,u} B]

/-- The natural transformation of derived tensor functors induced by an ordinary bimodule map. -/
def derivedTensorCoefficientMap (f : M →ₗ[A] M')
    (hf : ∀ (b : B) (m : M), f (op b • m) = op b • f m) :
    derivedTensor.{w} A B M ⟶ derivedTensor.{w} A B M' :=
  Functor.whiskerLeft
    ((DG.DerivedCategory.kProjectiveEquivalence.{w} B).inverse ⋙
      (DG.HomotopyCategory.subcategoryKProjective B).ι)
    (Functor.whiskerRight (homotopyTensorCoeffNat (coefficientHomDegreeZero f) hf)
      (DG.DerivedCategory.Qh (A := A)))


open DG.DerivedCategory

/-- The derived coefficient map is computed by the ordinary tensor map
on a K-projective representative. -/
theorem derivedTensorObjIso_coefficient_naturality (f : M →ₗ[A] M')
    (hf : ∀ (b : B) (m : M), f (op b • m) = op b • f m)
    {P : DGModuleCat.{u} B} (hP : IsKProjective.{u} B P) :
    (derivedTensorCoefficientMap f hf).app (Q.obj P) ≫
        (derivedTensorObjIso (M := M') hP).hom =
      (derivedTensorObjIso (M := M) hP).hom ≫
        Q.map ((ordinaryTensorCoefficientMap f hf).app P) := by
  let E := kProjectiveEquivalence.{w} B
  let ι := (DG.HomotopyCategory.subcategoryKProjective B).ι
  let V : KProjective B := ⟨(DG.HomotopyCategory.quotient B).obj P,
    (DG.HomotopyCategory.quotient_obj_mem_subcategoryKProjective_iff P).mpr hP⟩
  let r : ι.obj (E.inverse.obj (Q.obj P)) ⟶
      (DG.HomotopyCategory.quotient B).obj P := ι.map (E.unitIso.inv.app V)
  let T := DG.HomotopyCategory.tensorFunctor (B := B) A (InDegreeZero M)
  let T' := DG.HomotopyCategory.tensorFunctor (B := B) A (InDegreeZero M')
  let η := tensorCoeffNat (coefficientHomDegreeZero f) hf
  let α := homotopyTensorCoeffNat (coefficientHomDegreeZero f) hf
  let e := DG.HomotopyCategory.tensorFunctorQuotientIso (B := B) A (InDegreeZero M)
  let e' := DG.HomotopyCategory.tensorFunctorQuotientIso (B := B) A (InDegreeZero M')
  have h := α.naturality r
  have hα : α.app ((DG.HomotopyCategory.quotient B).obj P) ≫ e'.hom.app P =
      e.hom.app P ≫ (DG.HomotopyCategory.quotient A).map (η.app P) := by
    change (e.hom.app P ≫ (DG.HomotopyCategory.quotient A).map (η.app P) ≫ e'.inv.app P) ≫
      e'.hom.app P = _
    simp
  simp only [derivedTensorObjIso, Functor.mapIso_hom, Iso.trans_hom, Functor.map_comp, Iso.symm_hom]
  change Qh.map (α.app (ι.obj (E.inverse.obj (Q.obj P)))) ≫
      (Qh.map (T'.map r) ≫ Qh.map (e'.hom.app P)) =
    (Qh.map (T.map r) ≫ Qh.map (e.hom.app P)) ≫
      Qh.map ((DG.HomotopyCategory.quotient A).map (η.app P))
  simp only [← Functor.map_comp, Category.assoc]
  rw [← Category.assoc (α.app _) (T'.map r), ← h, Category.assoc, hα]

end Ordinary
end
end Categorification
