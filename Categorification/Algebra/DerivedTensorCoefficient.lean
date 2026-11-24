/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DerivedTensorTriangulated

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

private theorem commShift_of_whiskerLeft_obj_surjective
    {C D E : Type*} [Category C] [Category D] [Category E]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
    (H : C ⥤ D) [H.CommShift ℤ] {F G : D ⥤ E}
    [F.CommShift ℤ] [G.CommShift ℤ] (τ : F ⟶ G)
    [NatTrans.CommShift (Functor.whiskerLeft H τ) ℤ]
    (hH : Function.Surjective H.obj) : NatTrans.CommShift τ ℤ where
  shift_comm n := by
    ext Y
    obtain ⟨X,rfl⟩ := hH Y
    have e := NatTrans.shift_app_comm (Functor.whiskerLeft H τ) n X
    simp only [Functor.commShiftIso_comp_hom_app, Functor.whiskerLeft_app,
      Functor.comp_obj, Category.assoc] at e
    let h : H.obj ((shiftFunctor C n).obj X) ⟶
        (shiftFunctor D n).obj (H.obj X) := (H.commShiftIso n).hom.app X
    have hnat := τ.naturality h
    change F.map h ≫ τ.app ((shiftFunctor D n).obj (H.obj X)) =
      τ.app (H.obj ((shiftFunctor C n).obj X)) ≫ G.map h at hnat
    rw [← Category.assoc (τ.app _) (G.map h), ← hnat, Category.assoc] at e
    exact (cancel_epi (F.map h)).mp e

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
  Functor.whiskerLeft (DG.DerivedCategory.kProjectiveEquivalence.{w} B).inverse
    (Functor.whiskerLeft (DG.HomotopyCategory.subcategoryKProjective B).ι
      (Functor.whiskerRight (homotopyTensorCoeffNat (coefficientHomDegreeZero f) hf)
        (DG.DerivedCategory.Qh (A := A))))


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

local instance : Fact (∀ m : InDegreeZero M, m ∈ grading 0) :=
  ⟨fun _ => (InDegreeZero.mem_grading_iff (M := M)).mpr (Or.inl rfl)⟩

local instance : Fact (∀ m : InDegreeZero M', m ∈ grading 0) :=
  ⟨fun _ => (InDegreeZero.mem_grading_iff (M := M')).mpr (Or.inl rfl)⟩

private instance tensorCoeffNat_commShift (f : M →ₗ[A] M')
    (hf : ∀ (b : B) (m : M), f (op b • m) = op b • f m) :
    NatTrans.CommShift (tensorCoeffNat (coefficientHomDegreeZero f) hf) ℤ where
  shift_comm n := by
    ext X : 2
    exact DGModuleCat.tensor_hom_ext (A := A) (M := InDegreeZero M)
      (N := DGModuleCat.of B (Shift n X)) fun _ _ => rfl


private instance homotopyOrdinaryTensorCoeffNat_commShift (f : M →ₗ[A] M')
    (hf : ∀ (b : B) (m : M), f (op b • m) = op b • f m) :
    NatTrans.CommShift (homotopyTensorCoeffNat (coefficientHomDegreeZero f) hf) ℤ := by
  let q := DG.HomotopyCategory.quotient B
  let q' := DG.HomotopyCategory.quotient A
  let e  := DG.HomotopyCategory.tensorFunctorQuotientIso (B := B) A (InDegreeZero M)
  let e' := DG.HomotopyCategory.tensorFunctorQuotientIso (B := B) A (InDegreeZero M')
  let η := tensorCoeffNat (coefficientHomDegreeZero f) hf
  let α := homotopyTensorCoeffNat (coefficientHomDegreeZero f) hf
  have he : Functor.whiskerLeft q α =
      e.hom ≫ Functor.whiskerRight η q' ≫ e'.inv := rfl
  have : NatTrans.CommShift (Functor.whiskerLeft q α) ℤ := by
    rw [he]
    infer_instance
  exact commShift_of_whiskerLeft_obj_surjective q α (fun ⟨X⟩ => ⟨X,rfl⟩)

set_option synthInstance.maxHeartbeats 300000 in
instance derivedTensorCoefficientMap_commShift (f : M →ₗ[A] M')
    (hf : ∀ (b : B) (m : M), f (op b • m) = op b • f m) :
    NatTrans.CommShift (derivedTensorCoefficientMap f hf) ℤ := by
  let : (kProjectiveEquivalence.{w} B).inverse.CommShift ℤ := by
    let : (kProjectiveEquivalence.{w} B).functor.CommShift ℤ :=
      inferInstanceAs ((kProjectiveFunctor.{w} B).CommShift ℤ)
    exact (kProjectiveEquivalence.{w} B).commShiftInverse ℤ
  let α := homotopyTensorCoeffNat (coefficientHomDegreeZero f) hf
  let β := Functor.whiskerRight α (Qh (A := A))
  let γ := Functor.whiskerLeft (DG.HomotopyCategory.subcategoryKProjective B).ι β
  have hα : NatTrans.CommShift α ℤ := homotopyOrdinaryTensorCoeffNat_commShift f hf
  have hβ : NatTrans.CommShift β ℤ := NatTrans.CommShift.whiskerRight α _ ℤ
  have hγ : NatTrans.CommShift γ ℤ := NatTrans.CommShift.whiskerLeft (F₁ := (DG.HomotopyCategory.subcategoryKProjective B).ι) _ _ β ℤ
  exact NatTrans.CommShift.whiskerLeft (F₁ := (kProjectiveEquivalence.{w} B).inverse) _ _ γ ℤ

open CategoryTheory.Pretriangulated

/-- A coefficient map yields a morphism of the two derived tensor triangles. -/
def derivedTensorCoefficientTriangleMap (f : M →ₗ[A] M')
    (hf : ∀ (b : B) (m : M), f (op b • m) = op b • f m)
    (D : Triangle (DerivedCategory.{w,u} B)) :
    (derivedTensor.{w} A B M).mapTriangle.obj D ⟶
      (derivedTensor.{w} A B M').mapTriangle.obj D where
  hom₁ := (derivedTensorCoefficientMap f hf).app D.obj₁
  hom₂ := (derivedTensorCoefficientMap f hf).app D.obj₂
  hom₃ := (derivedTensorCoefficientMap f hf).app D.obj₃
  comm₁ := (derivedTensorCoefficientMap f hf).naturality D.mor₁
  comm₂ := (derivedTensorCoefficientMap f hf).naturality D.mor₂
  comm₃ := by
    dsimp
    simp only [Category.assoc, NatTrans.shift_app_comm (derivedTensorCoefficientMap f hf) (1 : ℤ) D.obj₁,
      NatTrans.naturality_assoc]

end Ordinary
end
end Categorification
