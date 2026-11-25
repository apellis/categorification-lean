/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DG.Category.Tensor.Basic
import Mathlib.Logic.Equiv.Basic

/-!
# Reindexing a balanced dg tensor product

An equivalence on indices, arrows and module fibers transports each
pure tensor. Compatibility with the two actions identifies the balancing
relations in both directions. This reindexing applies to the internal
weight translation of the braid in Webster, arXiv:1309.3796v2, §7.2, Proposition 7.11.
-/

noncomputable section
namespace Categorification
open CategoryTheory DG DGOpposite
open scoped CatModule
universe u v w
variable {C D : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [DGCategory C]
  [Category.{v} D] [Preadditive D] [∀ X Y : D, DGAddCommGroup (X ⟶ Y)] [DGCategory D]
  (N : CatModule.{w} (DGOpposite C)) (M : CatModule.{w} C)
  (N' : CatModule.{w} (DGOpposite D)) (M' : CatModule.{w} D)
  (e : C ≃ D) (re : ∀ X : C, N.obj (op X) ≃+ N'.obj (op (e X)))
  (le : ∀ X : C, M.obj X ≃+ M'.obj (e X))
local notation "Src" => CatTensorProduct N M
local notation "Dst" => CatTensorProduct N' M'
private def forwardFamily (X : C) : N.obj (op X) →+ M.obj X →+ Dst :=
  ((CatTensorProduct.tmulAddHom N' M' (e X)).compl₂ (le X).toAddMonoidHom).comp (re X).toAddMonoidHom
private def backwardFamily : ∀ Y : D, N'.obj (op Y) →+ M'.obj Y →+ Src :=
  Equiv.piCongrLeft (fun Y => N'.obj (op Y) →+ M'.obj Y →+ Src) e (fun X =>
    ((CatTensorProduct.tmulAddHom N M X).compl₂ (le X).symm.toAddMonoidHom).comp (re X).symm.toAddMonoidHom)
local notation "F" => forwardFamily N M N' M' e re le
local notation "G" => backwardFamily N M N' M' e re le
private theorem back_apply (X : C) (b : N'.obj (op (e X))) (z : M'.obj (e X)) :
    (G) (e X) b z = CatTensorProduct.tmul X ((re X).symm b) ((le X).symm z) := by
  dsimp only [backwardFamily]
  rw [Equiv.piCongrLeft_apply_apply]
  rfl

variable (he : ∀ X Y : C, (X ⟶ Y) ≃ (e X ⟶ e Y))
  (hr : ∀ {X Y : C} (f : X ⟶ Y) (b : N.obj (op Y)), re X (N.ract f b) = N'.ract (he X Y f) (re Y b))
  (hl : ∀ {X Y : C} (f : X ⟶ Y) (z : M.obj X), le Y (f • z) = he X Y f • le X z)
include he hr hl
private theorem forwardBalanced : CatTensorProduct.Balanced F := by
  intro X Y f b z
  change CatTensorProduct.tmul (e X) (re X (N.ract f b)) _ = CatTensorProduct.tmul (e Y) _ (le Y (f • z))
  rw [hr, hl]
  exact CatTensorProduct.ract_tmul _ _ _

private theorem backwardBalanced : CatTensorProduct.Balanced G := by
  intro U V f b z
  obtain ⟨X, rfl⟩ := e.surjective U
  obtain ⟨Y, rfl⟩ := e.surjective V
  obtain ⟨a,rfl⟩ := (he X Y).surjective f
  obtain ⟨x,rfl⟩ := (re Y).surjective b
  obtain ⟨m,rfl⟩ := (le X).surjective z
  rw [back_apply,back_apply,← hr,← hl]
  simp only [AddEquiv.symm_apply_apply]
  exact CatTensorProduct.ract_tmul _ _ _

private abbrev fwd := CatTensorProduct.lift (F) (forwardBalanced N M N' M' e re le he hr hl)
private abbrev back := CatTensorProduct.lift (G) (backwardBalanced N M N' M' e re le he hr hl)
local notation "hf" => forwardBalanced N M N' M' e re le he hr hl
local notation "hback" => backwardBalanced N M N' M' e re le he hr hl
local notation "up" => fwd N M N' M' e re le he hr hl
local notation "down" => back N M N' M' e re le he hr hl
private theorem fwd_apply (X : C) (b : N.obj (op X)) (z : M.obj X) :
    (up) (CatTensorProduct.tmul X b z) = CatTensorProduct.tmul (e X) (re X b) (le X z) :=
  CatTensorProduct.lift_tmul F hf X b z
private theorem bwd_apply (X : C) (b : N'.obj (op (e X))) (z : M'.obj (e X)) :
    (down) (CatTensorProduct.tmul (e X) b z) = CatTensorProduct.tmul X ((re X).symm b) ((le X).symm z) :=
  (CatTensorProduct.lift_tmul G hback (e X) b z).trans (back_apply N M N' M' e re le X b z)

/-- Reindex a balanced tensor product along equivalences of the objects,
hom sets and module fibers which intertwine both actions. -/
def weightCoendReindexAddEquiv : Src ≃+ Dst := by
  have right : (up).comp down = AddMonoidHom.id _ := by
    apply CatTensorProduct.addHom_ext
    intro Y b z
    obtain ⟨X,rfl⟩ := e.surjective Y
    change up (down (CatTensorProduct.tmul (e X) b z)) = CatTensorProduct.tmul (e X) b z
    rw [bwd_apply,fwd_apply,AddEquiv.apply_symm_apply,AddEquiv.apply_symm_apply]
  have left : (down).comp up = AddMonoidHom.id _ := by
    apply CatTensorProduct.addHom_ext
    intro X b z
    change down (up (CatTensorProduct.tmul X b z)) = CatTensorProduct.tmul X b z
    rw [fwd_apply,bwd_apply,AddEquiv.symm_apply_apply,AddEquiv.symm_apply_apply]
  exact { toFun := up, invFun := down, map_add' := (up).map_add,
          left_inv := DFunLike.congr_fun left, right_inv := DFunLike.congr_fun right }

theorem weightCoendReindexAddEquiv_tmul (X : C) (b : N.obj (op X)) (z : M.obj X) :
    weightCoendReindexAddEquiv N M N' M' e re le he hr hl (CatTensorProduct.tmul X b z) =
      CatTensorProduct.tmul (e X) (re X b) (le X z) := fwd_apply N M N' M' e re le he hr hl X b z

/-- If the two fiber equivalences preserve dg degrees and differentials,
the reindexing equivalence is a dg equivalence. -/
def weightCoendReindexDGEquiv
    (rd : ∀ (X : C) {k : ℤ} {b : N.obj (op X)}, b ∈ grading k → re X b ∈ grading k)
    (ld : ∀ (X : C) {k : ℤ} {z : M.obj X}, z ∈ grading k → le X z ∈ grading k)
    (dr : ∀ (X : C) (b : N.obj (op X)), re X (d b) = d (re X b))
    (dl : ∀ (X : C) (z : M.obj X), le X (d z) = d (le X z)) : DGAddEquiv Src Dst where
  toAddEquiv := weightCoendReindexAddEquiv N M N' M' e re le he hr hl
  map_mem' := CatTensorProduct.lift_mem F hf (fun X _ _ _ _ hb hz => CatTensorProduct.tmul_mem_grading (rd X hb) (ld X hz))
  map_d' := CatTensorProduct.lift_d F hf (by
    intro X i b hb z
    change d (CatTensorProduct.tmul (e X) (re X b) (le X z)) =
      CatTensorProduct.tmul (e X) (re X (d b)) (le X z) +
        koszulSign i • CatTensorProduct.tmul (e X) (re X b) (le X (d z))
    rw [dr,dl,CatTensorProduct.d_tmul_of_mem _ (rd X hb)])
end Categorification
