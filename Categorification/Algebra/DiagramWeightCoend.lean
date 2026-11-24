/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DiagramWeightBimodule

/-!
# Multiplication over a weight category

A balanced homogeneous product of two diagram coefficients descends to
the tensor coend over the middle weight dg category. Its value on pure
tensors is the coefficient product.
-/

noncomputable section

namespace Categorification

open CategoryTheory DG MulOpposite
open scoped DG.DegreeZero

universe u

variable {A B C M N P : Type u} [Ring A] [Ring B] [Ring C]
  [InternalGrading A] [InternalGrading B] [InternalGrading C]
  [BigradedDGRing A] [BigradedDGRing B] [BigradedDGRing C]
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module A M] [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]
  [Module B N] [Module Cᵐᵒᵖ N] [SMulCommClass B Cᵐᵒᵖ N]
  (G : ℤ → AddSubgroup M) (H : ℤ → AddSubgroup N) (L : ℤ → AddSubgroup P)
  (hgL : ∀ {i j : ℤ} {a : A} {x : M}, a ∈ wgrading i → x ∈ G j → a • x ∈ G (i + j))
  (hgR : ∀ {i j : ℤ} {b : B} {x : M}, b ∈ wgrading i → x ∈ G j → op b • x ∈ G (j + i))
  (hhL : ∀ {i j : ℤ} {b : B} {y : N}, b ∈ wgrading i → y ∈ H j → b • y ∈ H (i + j))
  (hhR : ∀ {i j : ℤ} {c : C} {y : N}, c ∈ wgrading i → y ∈ H j → op c • y ∈ H (j + i))
  (β : M →+ N →+ P)
  (hw : ∀ {i j : ℤ} {x : M} {y : N}, x ∈ G i → y ∈ H j → β x y ∈ L (i + j))
  (hb : ∀ (b : B) (x : M) (y : N), β (op b • x) y = β x (b • y))
  (X : WeightCategory A) (Z : WeightCategory C)

local notation "D₁" => diagramWeightBimodule G hgL hgR
local notation "D₂" => diagramWeightBimodule H hhL hhR
local notation "Out" => InDegreeZero (L (WeightCategory.as X - WeightCategory.as Z))

private def weightProduct (Y : WeightCategory B) :
    ((D₁).right X).obj (DG.DGOpposite.op Y) →+ ((D₂).left Z).obj Y →+ Out where
  toFun x :=
    { toFun := fun y => ⟨β x.val y.val, by
        have h := hw x.property y.property
        rwa [show (X.as - Y.as) + (Y.as - Z.as) = X.as - Z.as by omega] at h⟩
      map_zero' := Subtype.ext (map_zero (β x.val))
      map_add' := fun y y' => Subtype.ext (map_add (β x.val) y.val y'.val) }
  map_zero' := AddMonoidHom.ext fun y => Subtype.ext
    (show β 0 y.val = 0 by rw [map_zero, AddMonoidHom.zero_apply])
  map_add' x x' := AddMonoidHom.ext fun y => Subtype.ext
    (DFunLike.congr_fun (map_add β x.val x'.val) y.val)

include hb in
private theorem weightProduct_balanced :
    CatTensorProduct.Balanced (N := (D₁).right X) (M := (D₂).left Z)
      (weightProduct G H L hgL hgR hhL hhR β hw X Z) := by
  intro Y Y' f x y
  rw [CatBimodule.right_ract]
  exact Subtype.ext (hb f.val x.val y.val)

/-- A homogeneous balanced multiplication gives a map from the actual
tensor coend over the middle weight category. -/
def diagramWeightCoendProduct :
    CatTensorProduct ((D₁).right X) ((D₂).left Z) →+ Out :=
  CatTensorProduct.lift (weightProduct G H L hgL hgR hhL hhR β hw X Z)
    (weightProduct_balanced G H L hgL hgR hhL hhR β hw hb X Z)

/-- On a pure coend tensor the map applies the coefficient product. -/
theorem diagramWeightCoendProduct_tmul (Y : WeightCategory B)
    (x : (D₁).obj X Y) (y : (D₂).obj Y Z) :
    (diagramWeightCoendProduct G H L hgL hgR hhL hhR β hw hb X Z
      (CatTensorProduct.tmul Y x y)).val = β x.val y.val := by
  exact congrArg (fun z : Out => (z.val : P))
    (CatTensorProduct.lift_tmul (N := (D₁).right X) (M := (D₂).left Z)
      (weightProduct G H L hgL hgR hhL hhR β hw X Z)
      (weightProduct_balanced G H L hgL hgR hhL hhR β hw hb X Z) Y x y)

/-- The product preserves cohomological degree. -/
theorem diagramWeightCoendProduct_mem {n : ℤ}
    {x : CatTensorProduct ((D₁).right X) ((D₂).left Z)} (hx : x ∈ grading n) :
    diagramWeightCoendProduct G H L hgL hgR hhL hhR β hw hb X Z x ∈ grading n := by
  apply CatTensorProduct.lift_mem (N := (D₁).right X) (M := (D₂).left Z)
    (weightProduct G H L hgL hgR hhL hhR β hw X Z)
    (weightProduct_balanced G H L hgL hgR hhL hhR β hw hb X Z) _ hx
  intro Y i j x y hx hy
  rcases (InDegreeZero.mem_grading_iff (G (X.as - Y.as))).mp hx with rfl | rfl
  · rcases (InDegreeZero.mem_grading_iff (H (Y.as - Z.as))).mp hy with rfl | rfl
    · exact InDegreeZero.mem_grading_zero _
    · exact (map_zero (weightProduct G H L hgL hgR hhL hhR β hw X Z Y x)).symm ▸ zero_mem _
  · have he := DFunLike.congr_fun (map_zero (weightProduct G H L hgL hgR hhL hhR β hw X Z Y)) y
    exact he.symm ▸ zero_mem _

/-- The product commutes with the cohomological differentials. -/
theorem diagramWeightCoendProduct_d
    (x : CatTensorProduct ((D₁).right X) ((D₂).left Z)) :
    diagramWeightCoendProduct G H L hgL hgR hhL hhR β hw hb X Z (d x) =
      d (diagramWeightCoendProduct G H L hgL hgR hhL hhR β hw hb X Z x) := by
  apply CatTensorProduct.lift_d (N := (D₁).right X) (M := (D₂).left Z)
    (weightProduct G H L hgL hgR hhL hhR β hw X Z)
    (weightProduct_balanced G H L hgL hgR hhL hhR β hw hb X Z) _ x
  intro Y i x hx y
  have hx₀ : d x = 0 := InDegreeZero.d_apply (G (X.as - Y.as)) x
  have hy₀ : d y = 0 := InDegreeZero.d_apply (H (Y.as - Z.as)) y
  rw [InDegreeZero.d_apply, hx₀, hy₀, map_zero, AddMonoidHom.zero_apply, map_zero,
    smul_zero, add_zero]

variable [Module A P] [Module Cᵐᵒᵖ P] [SMulCommClass A Cᵐᵒᵖ P]
  (hPL : ∀ {i j : ℤ} {a : A} {x : P}, a ∈ wgrading i → x ∈ L j → a • x ∈ L (i + j))
  (hPR : ∀ {i j : ℤ} {c : C} {x : P}, c ∈ wgrading i → x ∈ L j → op c • x ∈ L (j + i))
  (hβL : ∀ (a : A) (x : M) (y : N), β (a • x) y = a • β x y)

local notation "D₃" => diagramWeightBimodule L hPL hPR
local notation "F" => diagramWeightCoendProduct G H L hgL hgR hhL hhR β hw hb

/-- A homogeneous balanced product commuting with the outer left action gives
a dg map of the two tensor modules at the fixed right endpoint. -/
def diagramWeightCoendProductHom : (D₁).tensorObj ((D₂).left Z) ⟶ (D₃).left Z where
  app X := F X Z
  map_mem' {_ _ _} h := diagramWeightCoendProduct_mem G H L hgL hgR hhL hhR β hw hb _ Z h
  map_d' {X} x := diagramWeightCoendProduct_d G H L hgL hgR hhL hhR β hw hb X Z x
  map_smul' {X X'} f t := by
    let actIn : CatTensorProduct ((D₁).right X) ((D₂).left Z) →+
        CatTensorProduct ((D₁).right X') ((D₂).left Z) :=
      ((D₁).tensorObj ((D₂).left Z)).act f
    let actOut : InDegreeZero (L (X.as - Z.as)) →+ InDegreeZero (L (X'.as - Z.as)) :=
      ((D₃).left Z).act f
    have he : (F X' Z).comp actIn = actOut.comp (F X Z) := by
      apply CatTensorProduct.addHom_ext
      intro Y x y
      change (F X' Z) (((D₁).tensorObj ((D₂).left Z)).act f (CatTensorProduct.tmul Y x y)) =
        ((D₃).left Z).act f ((F X Z) (CatTensorProduct.tmul Y x y))
      rw [CatBimodule.tensorObj_act_tmul]
      apply Subtype.ext
      exact (diagramWeightCoendProduct_tmul G H L hgL hgR hhL hhR β hw hb X' Z Y
        ((D₁).lact f x) y).trans ((hβL f.val x.val y.val).trans
        (congrArg (fun z : P => f.val • z)
          (diagramWeightCoendProduct_tmul G H L hgL hgR hhL hhR β hw hb X Z Y x y)).symm)
    exact DFunLike.congr_fun he t

end Categorification
