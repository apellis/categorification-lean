/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DG.Category.Tensor.Basic
import DG.Category.Derived.FiniteCell
/-!
# Tensoring a representable summand by a right coefficient

For the loading projectives in Webster, arXiv:1309.3796v2, Proposition
7.11, the tensor with a diagram coefficient is its loading cut. A map
of projectives given by a crossing acts on this cut by the right action
of the same crossing.
-/

noncomputable section
namespace Categorification
open CategoryTheory DG DGCategory CatModule DGOpposite CatTensorProduct
open scoped DG.CatModule
universe u v w
variable {C : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  [DGCategory C] (N : CatModule.{w} (DGOpposite C)) {X : C} (e : Idempotent X)

/-- The subgroup of coefficient vectors fixed by the loading projector. -/
def coendLoadingCut : AddSubgroup (N.obj (op X)) where
  carrier := {x | x <• e.val = x}
  zero_mem' := zero_ract _
  add_mem' {x y} hx hy := (add_ract e.val x y).trans (congrArg₂ (· + ·) hx hy)
  neg_mem' {x} hx := (neg_ract e.val x).trans (congrArg Neg.neg hx)

/-- Evaluation on a tensor with a summand of the representable. -/
def coendLoadingEval : CatTensorProduct N (corner e) →+ N.obj (op X) :=
  (ridHom N X).comp (CatTensorProduct.map (𝟙 N) (cornerRetract e).i)

theorem coendLoadingEval_tmul (Y : C) (n : N.obj (op Y)) (h : (corner e).obj Y) :
    coendLoadingEval N e (tmul Y n h) = n <• h.val := by
  unfold coendLoadingEval
  rw [AddMonoidHom.comp_apply,map_tmul]
  exact ridHom_tmul X Y n h.val

private theorem eval_mem (z : CatTensorProduct N (corner e)) :
    coendLoadingEval N e z ∈ coendLoadingCut N e := by
  induction z using CatTensorProduct.induction_on with
  | zero => rw [map_zero]; exact (coendLoadingCut N e).zero_mem
  | add z z' h h' => rw [map_add]; exact (coendLoadingCut N e).add_mem h h'
  | tmul Y n h =>
    change coendLoadingEval N e _ <• e.val = _
    rw [coendLoadingEval_tmul]
    exact (ract_comp _ _ _).symm.trans (congrArg (fun f : X ⟶ Y => n <• f) h.property)

/-- Co-Yoneda for an idempotent summand, with inverse given by tensoring
with the corner generator. -/
def coendLoadingIso : CatTensorProduct N (corner e) ≃+ coendLoadingCut N e where
  toFun x := ⟨coendLoadingEval N e x,eval_mem N e x⟩
  invFun y := tmul X y.val (cornerGen e)
  left_inv x := by
    change tmul X (coendLoadingEval N e x) (cornerGen e) = x
    induction x using CatTensorProduct.induction_on with
    | zero => rw [map_zero,zero_tmul]
    | add a b ha hb => rw [map_add,add_tmul,ha,hb]
    | tmul Y n h =>
      rw [coendLoadingEval_tmul]
      exact (ract_tmul h.val n (cornerGen e)).trans
        (congrArg (tmul Y n) (Subtype.ext h.property))
  right_inv y := Subtype.ext ((coendLoadingEval_tmul _ _ _ _ _).trans y.property)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

/-- After evaluation, a map between loading projectives acts on the
right coefficient by the image of the corner generator. -/
theorem coendLoadingEval_map {Y : C} (f : Idempotent Y) (g : corner e ⟶ corner f)
    (z : CatTensorProduct N (corner e)) :
    coendLoadingEval N f (CatTensorProduct.map (𝟙 N) g z) =
      (coendLoadingEval N e z) <• (g.app X (cornerGen e)).val := by
  let b : Y ⟶ X := (g.app X (cornerGen e)).val
  change coendLoadingEval N f _ = (coendLoadingEval N e z) <• b
  induction z using CatTensorProduct.induction_on with
  | zero => rw [map_zero,map_zero,map_zero,zero_ract]
  | add a c ha hc => rw [map_add,map_add,map_add,add_ract,ha,hc]
  | tmul Z n m =>
    rw [map_tmul,coendLoadingEval_tmul,coendLoadingEval_tmul]
    have hh : (corner e).act (X := X) (Y := Z) (m.val : X ⟶ Z) (cornerGen e) = m := Subtype.ext m.property
    have hg : (g.app Z m).val = b ≫ (m.val : X ⟶ Z) :=
      congrArg Subtype.val ((congrArg (g.app Z) hh.symm).trans (g.map_smul (m.val : X ⟶ Z) (cornerGen e)))
    exact (congrArg (fun h : Y ⟶ Z => n <• h) hg).trans (ract_comp _ _ _)

/-- Evaluation on a loading both preserves and reflects cohomological degree. -/
theorem coendLoadingEval_mem_grading
    (z : CatTensorProduct N (corner e)) (i : ℤ) :
    coendLoadingEval N e z ∈ grading i ↔ z ∈ grading i := by
  constructor
  · intro h
    have he : cornerGen e ∈ grading 0 := e.mem_grading
    have hz : tmul X (coendLoadingEval N e z) (cornerGen e) = z := (coendLoadingIso N e).symm_apply_apply z
    have hh := CatTensorProduct.tmul_mem_grading (M := corner e) (N := N) h he
    simpa only [add_zero,hz] using hh
  · intro h
    exact (rid N X).map_mem (CatTensorProduct.map_mem (𝟙 N) (cornerRetract e).i h)

/-- Evaluation on a loading commutes with the differential of the right coefficient. -/
theorem coendLoadingEval_d
    (z : CatTensorProduct N (corner e)) : coendLoadingEval N e (d z) = d (coendLoadingEval N e z) := by
  change (rid N X) (CatTensorProduct.map (𝟙 N) (cornerRetract e).i (d z)) = _
  rw [CatTensorProduct.map_d,(rid N X).map_d]
  rfl

end Categorification
