/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DiagramWeightCoendNaturality
import Categorification.Algebra.DiagramWeightTensorShift

set_option backward.isDefEq.respectTransparency false

/-!
# Composing tensor products with diagram coefficients

A balanced homogeneous product `β : M × N → P` of three diagram coefficients gives a natural
map of dg modules `D_M ⊗ (D_N ⊗ L) ⟶ D_P ⊗ L` over the weight categories,
`x ⊗ (y ⊗ l) ↦ β x y ⊗ l`. This is the comparison map behind the composition of graded
braiding functors (Webster, arXiv:1309.3796v3, Lemma 6.12).
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
  [Module A P] [Module Cᵐᵒᵖ P] [SMulCommClass A Cᵐᵒᵖ P]
  (G : ℤ → AddSubgroup M) (H : ℤ → AddSubgroup N) (L : ℤ → AddSubgroup P)
  (hgL : ∀ {i j : ℤ} {a : A} {x : M}, a ∈ wgrading i → x ∈ G j → a • x ∈ G (i + j))
  (hgR : ∀ {i j : ℤ} {b : B} {x : M}, b ∈ wgrading i → x ∈ G j → op b • x ∈ G (j + i))
  (hhL : ∀ {i j : ℤ} {b : B} {y : N}, b ∈ wgrading i → y ∈ H j → b • y ∈ H (i + j))
  (hhR : ∀ {i j : ℤ} {c : C} {y : N}, c ∈ wgrading i → y ∈ H j → op c • y ∈ H (j + i))
  (hPL : ∀ {i j : ℤ} {a : A} {x : P}, a ∈ wgrading i → x ∈ L j → a • x ∈ L (i + j))
  (hPR : ∀ {i j : ℤ} {c : C} {x : P}, c ∈ wgrading i → x ∈ L j → op c • x ∈ L (j + i))
  (β : M →+ N →+ P)
  (hw : ∀ {i j : ℤ} {x : M} {y : N}, x ∈ G i → y ∈ H j → β x y ∈ L (i + j))

set_option hygiene false in
local notation "D₁" => diagramWeightBimodule G hgL hgR
set_option hygiene false in
local notation "D₂" => diagramWeightBimodule H hhL hhR
set_option hygiene false in
local notation "D₃" => diagramWeightBimodule L hPL hPR

/-- The product of two weight components. -/
def diagramWeightMul {X : WeightCategory A} {Y : WeightCategory B} {Z : WeightCategory C} :
    (D₁).obj X Y →+ (D₂).obj Y Z →+ (D₃).obj X Z where
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

@[simp]
theorem diagramWeightMul_val {X : WeightCategory A} {Y : WeightCategory B}
    {Z : WeightCategory C} (x : (D₁).obj X Y) (y : (D₂).obj Y Z) :
    (diagramWeightMul G H L hgL hgR hhL hhR hPL hPR β hw x y).val = β x.val y.val := rfl

set_option hygiene false in
local notation "μ" => diagramWeightMul G H L hgL hgR hhL hhR hPL hPR β hw

variable (hb : ∀ (b : B) (x : M) (y : N), β (op b • x) y = β x (b • y))
  (hβL : ∀ (a : A) (x : M) (y : N), β (a • x) y = a • β x y)
  (hβR : ∀ (c : C) (x : M) (y : N), β x (op c • y) = op c • β x y)
  (L₀ : CatModule.{u} (WeightCategory C)) (X : WeightCategory A)

/-- Every element of a diagram weight component has cohomological degree zero or vanishes. -/
private theorem weight_mem_grading {T : Type u} [AddCommGroup T] {x : InDegreeZero T} {i : ℤ}
    (hx : x ∈ DG.grading i) : i = 0 ∨ x = 0 :=
  ((InDegreeZero.mem_grading_iff (M := T)).mp hx).elim (fun h => Or.inl h) Or.inr

/-- The inner family `y ⊗ l ↦ β x y ⊗ l` for a fixed `x`. -/
private def innerFamily {Y : WeightCategory B} (x : (D₁).obj X Y) (Z : WeightCategory C) :
    ((D₂).right Y).obj (DGOpposite.op Z) →+ L₀.obj Z →+
      CatTensorProduct ((D₃).right X) L₀ :=
  (CatTensorProduct.tmulAddHom ((D₃).right X) L₀ Z).comp (μ x)

include hβR in
private theorem innerFamily_balanced {Y : WeightCategory B} (x : (D₁).obj X Y) :
    CatTensorProduct.Balanced (innerFamily G H L hgL hgR hhL hhR hPL hPR β hw L₀ X x) := by
  intro Z Z' f y l
  change CatTensorProduct.tmul (N := (D₃).right X) (M := L₀) Z (μ x (((D₂).right Y).ract f y)) l =
    CatTensorProduct.tmul (N := (D₃).right X) (M := L₀) Z' (μ x y) (f • l)
  rw [CatBimodule.right_ract, ← CatTensorProduct.ract_tmul, CatBimodule.right_ract]
  congr 1
  exact Subtype.ext (hβR f.val x.val y.val)

/-- The map `(D_N ⊗ L)(Y) → (D_P ⊗ L)(X)` of left multiplication by `x`. -/
private def leftMul {Y : WeightCategory B} (x : (D₁).obj X Y) :
    CatTensorProduct ((D₂).right Y) L₀ →+ CatTensorProduct ((D₃).right X) L₀ :=
  CatTensorProduct.lift (innerFamily G H L hgL hgR hhL hhR hPL hPR β hw L₀ X x)
    (innerFamily_balanced G H L hgL hgR hhL hhR hPL hPR β hw hβR L₀ X x)

private theorem leftMul_tmul {Y : WeightCategory B} (x : (D₁).obj X Y) (Z : WeightCategory C)
    (y : ((D₂).right Y).obj (DGOpposite.op Z)) (l : L₀.obj Z) :
    leftMul G H L hgL hgR hhL hhR hPL hPR β hw hβR L₀ X x
        (CatTensorProduct.tmul (N := (D₂).right Y) (M := L₀) Z y l) =
      innerFamily G H L hgL hgR hhL hhR hPL hPR β hw L₀ X x Z y l :=
  CatTensorProduct.lift_tmul (innerFamily G H L hgL hgR hhL hhR hPL hPR β hw L₀ X x)
    (innerFamily_balanced G H L hgL hgR hhL hhR hPL hPR β hw hβR L₀ X x) Z y l

/-- The outer family `x ⊗ t ↦ x · t`. -/
private def outerFamily (Y : WeightCategory B) :
    ((D₁).right X).obj (DGOpposite.op Y) →+ CatTensorProduct ((D₂).right Y) L₀ →+
      CatTensorProduct ((D₃).right X) L₀ where
  toFun x := leftMul G H L hgL hgR hhL hhR hPL hPR β hw hβR L₀ X x
  map_zero' := CatTensorProduct.addHom_ext fun Z y l =>
    (leftMul_tmul G H L hgL hgR hhL hhR hPL hPR β hw hβR L₀ X 0 Z y l).trans
      (show CatTensorProduct.tmul (N := (D₃).right X) (M := L₀) Z (μ 0 y) l = 0 by
        rw [map_zero, AddMonoidHom.zero_apply, CatTensorProduct.zero_tmul])
  map_add' x x' := CatTensorProduct.addHom_ext fun Z y l =>
    (leftMul_tmul G H L hgL hgR hhL hhR hPL hPR β hw hβR L₀ X (x + x') Z y l).trans
      ((show CatTensorProduct.tmul (N := (D₃).right X) (M := L₀) Z (μ (x + x') y) l =
          CatTensorProduct.tmul (N := (D₃).right X) (M := L₀) Z (μ x y) l +
            CatTensorProduct.tmul (N := (D₃).right X) (M := L₀) Z (μ x' y) l by
        rw [map_add, AddMonoidHom.add_apply, CatTensorProduct.add_tmul]).trans
      (congrArg₂ (· + ·)
        (leftMul_tmul G H L hgL hgR hhL hhR hPL hPR β hw hβR L₀ X x Z y l)
        (leftMul_tmul G H L hgL hgR hhL hhR hPL hPR β hw hβR L₀ X x' Z y l)).symm)

include hb in
private theorem outerFamily_balanced :
    CatTensorProduct.Balanced (N := (D₁).right X) (M := (D₂).tensorObj L₀)
      (outerFamily G H L hgL hgR hhL hhR hPL hPR β hw hβR L₀ X) := by
  intro Y Y' g x t
  change leftMul G H L hgL hgR hhL hhR hPL hPR β hw hβR L₀ X (((D₁).right X).ract g x) t =
    leftMul G H L hgL hgR hhL hhR hPL hPR β hw hβR L₀ X x (((D₂).tensorObj L₀).act g t)
  have he : leftMul G H L hgL hgR hhL hhR hPL hPR β hw hβR L₀ X (((D₁).right X).ract g x) =
      (leftMul G H L hgL hgR hhL hhR hPL hPR β hw hβR L₀ X x).comp ((D₂).tensorAct L₀ g) := by
    apply CatTensorProduct.addHom_ext
    intro Z y l
    rw [AddMonoidHom.comp_apply, CatBimodule.tensorAct_tmul]
    refine (leftMul_tmul G H L hgL hgR hhL hhR hPL hPR β hw hβR L₀ X _ Z y l).trans
      (Eq.trans ?_ (leftMul_tmul G H L hgL hgR hhL hhR hPL hPR β hw hβR L₀ X x Z _ l).symm)
    change CatTensorProduct.tmul (N := (D₃).right X) (M := L₀) Z
        (μ (((D₁).right X).ract g x) y) l =
      CatTensorProduct.tmul (N := (D₃).right X) (M := L₀) Z (μ x ((D₂).lact g y)) l
    rw [CatBimodule.right_ract]
    congr 1
    exact Subtype.ext (hb g.val x.val y.val)
  exact DFunLike.congr_fun he t

/-- The component `D_M ⊗ (D_N ⊗ L) → D_P ⊗ L` at an output weight. -/
def diagramWeightTensorCompApp :
    CatTensorProduct ((D₁).right X) ((D₂).tensorObj L₀) →+
      CatTensorProduct ((D₃).right X) L₀ :=
  CatTensorProduct.lift (N := (D₁).right X) (M := (D₂).tensorObj L₀)
    (outerFamily G H L hgL hgR hhL hhR hPL hPR β hw hβR L₀ X)
    (outerFamily_balanced G H L hgL hgR hhL hhR hPL hPR β hw hb hβR L₀ X)

/-- The comparison on pure tensors: `x ⊗ (y ⊗ l) ↦ β x y ⊗ l`. -/
theorem diagramWeightTensorCompApp_tmul (Y : WeightCategory B)
    (x : ((D₁).right X).obj (DGOpposite.op Y)) (Z : WeightCategory C)
    (y : ((D₂).right Y).obj (DGOpposite.op Z)) (l : L₀.obj Z) :
    diagramWeightTensorCompApp G H L hgL hgR hhL hhR hPL hPR β hw hb hβR L₀ X
        (CatTensorProduct.tmul (N := (D₁).right X) (M := (D₂).tensorObj L₀) Y x
          (CatTensorProduct.tmul (N := (D₂).right Y) (M := L₀) Z y l)) =
      CatTensorProduct.tmul (N := (D₃).right X) (M := L₀) Z (μ x y) l :=
  (CatTensorProduct.lift_tmul (N := (D₁).right X) (M := (D₂).tensorObj L₀)
    (outerFamily G H L hgL hgR hhL hhR hPL hPR β hw hβR L₀ X)
    (outerFamily_balanced G H L hgL hgR hhL hhR hPL hPR β hw hb hβR L₀ X) Y x _).trans
    (leftMul_tmul G H L hgL hgR hhL hhR hPL hPR β hw hβR L₀ X x Z y l)

private theorem innerFamily_mem {Y : WeightCategory B} (x : (D₁).obj X Y) (Z : WeightCategory C)
    {i j : ℤ} {y : ((D₂).right Y).obj (DGOpposite.op Z)} {l : L₀.obj Z}
    (hy : y ∈ DG.grading i) (hl : l ∈ DG.grading j) :
    innerFamily G H L hgL hgR hhL hhR hPL hPR β hw L₀ X x Z y l ∈ DG.grading (i + j) := by
  rcases weight_mem_grading hy with rfl | rfl
  · change CatTensorProduct.tmul (N := (D₃).right X) (M := L₀) Z (μ x y) l ∈ _
    have h := CatTensorProduct.tmul_mem_grading (N := (D₃).right X) (M := L₀)
      (InDegreeZero.mem_grading_zero (μ x y)) hl
    rwa [zero_add] at h ⊢
  · change CatTensorProduct.tmul (N := (D₃).right X) (M := L₀) Z (μ x 0) l ∈ _
    rw [map_zero, CatTensorProduct.zero_tmul]
    exact zero_mem _

private theorem leftMul_mem {Y : WeightCategory B} (x : (D₁).obj X Y) {j : ℤ}
    {t : CatTensorProduct ((D₂).right Y) L₀} (ht : t ∈ DG.grading j) :
    leftMul G H L hgL hgR hhL hhR hPL hPR β hw hβR L₀ X x t ∈ DG.grading j :=
  CatTensorProduct.lift_mem _
    (innerFamily_balanced G H L hgL hgR hhL hhR hPL hPR β hw hβR L₀ X x)
    (fun Z _ _ _ _ hy hl => innerFamily_mem G H L hgL hgR hhL hhR hPL hPR β hw L₀ X x Z hy hl) ht

private theorem leftMul_d {Y : WeightCategory B} (x : (D₁).obj X Y)
    (t : CatTensorProduct ((D₂).right Y) L₀) :
    leftMul G H L hgL hgR hhL hhR hPL hPR β hw hβR L₀ X x (d t) =
      d (leftMul G H L hgL hgR hhL hhR hPL hPR β hw hβR L₀ X x t) := by
  refine CatTensorProduct.lift_d _
    (innerFamily_balanced G H L hgL hgR hhL hhR hPL hPR β hw hβR L₀ X x) ?_ t
  intro Z i y hy l
  change d (CatTensorProduct.tmul (N := (D₃).right X) (M := L₀) Z (μ x y) l) =
    CatTensorProduct.tmul (N := (D₃).right X) (M := L₀) Z (μ x (d y)) l +
      koszulSign i • CatTensorProduct.tmul (N := (D₃).right X) (M := L₀) Z (μ x y) (d l)
  have h₁ : d (μ x y) = 0 := InDegreeZero.d_apply (M := L (X.as - Z.as)) (μ x y)
  have h₂ : d y = 0 := InDegreeZero.d_apply (M := H (Y.as - Z.as)) y
  rw [CatTensorProduct.d_tmul_of_mem Z (InDegreeZero.mem_grading_zero (μ x y)), h₁, h₂,
    map_zero, CatTensorProduct.zero_tmul, zero_add,
    koszulSign_zero, one_smul]
  have hy' : i = 0 ∨ y = 0 := (InDegreeZero.mem_grading_iff (M := H (Y.as - Z.as))).mp hy
  rcases hy' with rfl | rfl
  · rw [koszulSign_zero, one_smul, zero_add]
  · have hz : μ x (0 : ((D₂).right Y).obj (DGOpposite.op Z)) = 0 := map_zero _
    rw [hz, CatTensorProduct.zero_tmul, smul_zero, zero_add]

/-- The comparison `D_M ⊗ (D_N ⊗ L) ⟶ D_P ⊗ L`, `x ⊗ (y ⊗ l) ↦ β x y ⊗ l`, as a map of dg
modules over the outer weight category. -/
def diagramWeightTensorCompHom :
    (D₁).tensorObj ((D₂).tensorObj L₀) ⟶ (D₃).tensorObj L₀ where
  app X := diagramWeightTensorCompApp G H L hgL hgR hhL hhR hPL hPR β hw hb hβR L₀ X
  map_mem' {X _ _} h := by
    refine CatTensorProduct.lift_mem _
      (outerFamily_balanced G H L hgL hgR hhL hhR hPL hPR β hw hb hβR L₀ X) ?_ h
    intro Y i j x t hx ht
    rcases weight_mem_grading hx with rfl | rfl
    · rw [zero_add]
      exact leftMul_mem G H L hgL hgR hhL hhR hPL hPR β hw hβR L₀ X x ht
    · change outerFamily G H L hgL hgR hhL hhR hPL hPR β hw hβR L₀ X Y 0 t ∈ _
      rw [map_zero]
      exact zero_mem _
  map_d' {X} t := by
    refine CatTensorProduct.lift_d _
      (outerFamily_balanced G H L hgL hgR hhL hhR hPL hPR β hw hb hβR L₀ X) ?_ t
    intro Y i x hx t
    change d (leftMul G H L hgL hgR hhL hhR hPL hPR β hw hβR L₀ X x t) =
      outerFamily G H L hgL hgR hhL hhR hPL hPR β hw hβR L₀ X Y (d x) t +
        koszulSign i • leftMul G H L hgL hgR hhL hhR hPL hPR β hw hβR L₀ X x (d t)
    have h₁ : d x = 0 := InDegreeZero.d_apply (M := G (X.as - Y.as)) x
    have h₀ : outerFamily G H L hgL hgR hhL hhR hPL hPR β hw hβR L₀ X Y (d x) t = 0 := by
      rw [h₁, map_zero]
      rfl
    rw [h₀, zero_add]
    have hx' : i = 0 ∨ x = 0 := (InDegreeZero.mem_grading_iff (M := G (X.as - Y.as))).mp hx
    rcases hx' with rfl | rfl
    · rw [koszulSign_zero, one_smul]
      exact (leftMul_d G H L hgL hgR hhL hhR hPL hPR β hw hβR L₀ X x t).symm
    · have hz : leftMul G H L hgL hgR hhL hhR hPL hPR β hw hβR L₀ X
          (0 : ((D₁).right X).obj (DGOpposite.op Y)) = 0 :=
        map_zero (outerFamily G H L hgL hgR hhL hhR hPL hPR β hw hβR L₀ X Y)
      rw [hz]
      change d (0 : CatTensorProduct ((D₃).right X) L₀) =
        koszulSign i • (0 : CatTensorProduct ((D₃).right X) L₀)
      rw [d_zero, smul_zero]
  map_smul' {X X'} f t := by
    let F := diagramWeightTensorCompApp G H L hgL hgR hhL hhR hPL hPR β hw hb hβR L₀
    have he : (F X').comp ((D₁).tensorAct ((D₂).tensorObj L₀) f) =
        ((D₃).tensorAct L₀ f).comp (F X) := by
      apply CatTensorProduct.addHom_ext
      intro Y x t
      rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, CatBimodule.tensorAct_tmul]
      have h2 : (F X').comp ((CatTensorProduct.tmulAddHom ((D₁).right X') ((D₂).tensorObj L₀) Y)
            ((D₁).lact f x)) =
          ((D₃).tensorAct L₀ f).comp ((F X).comp
            ((CatTensorProduct.tmulAddHom ((D₁).right X) ((D₂).tensorObj L₀) Y) x)) := by
        apply CatTensorProduct.addHom_ext
        intro Z y l
        change F X' (CatTensorProduct.tmul (N := (D₁).right X') (M := (D₂).tensorObj L₀) Y
            ((D₁).lact f x) (CatTensorProduct.tmul (N := (D₂).right Y) (M := L₀) Z y l)) =
          (D₃).tensorAct L₀ f (F X (CatTensorProduct.tmul (N := (D₁).right X)
            (M := (D₂).tensorObj L₀) Y x
              (CatTensorProduct.tmul (N := (D₂).right Y) (M := L₀) Z y l)))
        rw [diagramWeightTensorCompApp_tmul, diagramWeightTensorCompApp_tmul,
          CatBimodule.tensorAct_tmul]
        congr 1
        exact Subtype.ext (hβL f.val x.val y.val)
      exact DFunLike.congr_fun h2 t
    exact DFunLike.congr_fun he t

@[simp]
theorem diagramWeightTensorCompHom_app :
    (diagramWeightTensorCompHom G H L hgL hgR hhL hhR hPL hPR β hw hb hβL hβR L₀).app X =
      diagramWeightTensorCompApp G H L hgL hgR hhL hhR hPL hPR β hw hb hβR L₀ X := rfl

/-- The comparison on pure tensors of a dg module map. -/
theorem diagramWeightTensorCompHom_app_tmul (Y : WeightCategory B)
    (x : ((D₁).right X).obj (DGOpposite.op Y)) (Z : WeightCategory C)
    (y : ((D₂).right Y).obj (DGOpposite.op Z)) (l : L₀.obj Z) :
    (diagramWeightTensorCompHom G H L hgL hgR hhL hhR hPL hPR β hw hb hβL hβR L₀).app X
        (CatTensorProduct.tmul (N := (D₁).right X) (M := (D₂).tensorObj L₀) Y x
          (CatTensorProduct.tmul (N := (D₂).right Y) (M := L₀) Z y l)) =
      CatTensorProduct.tmul (N := (D₃).right X) (M := L₀) Z (μ x y) l :=
  diagramWeightTensorCompApp_tmul G H L hgL hgR hhL hhR hPL hPR β hw hb hβR L₀ X Y x Z y l

omit L₀ X

/-- Two maps out of `D_M ⊗ (D_N ⊗ L)` agree when they agree on the pure tensors
`x ⊗ (y ⊗ l)`. -/
theorem diagramWeightTensorComp_hom_ext {L₀ : CatModule.{u} (WeightCategory C)}
    {T : CatModule.{u} (WeightCategory A)}
    {f g : (D₁).tensorObj ((D₂).tensorObj L₀) ⟶ T}
    (h : ∀ X Y (x : ((D₁).right X).obj (DGOpposite.op Y)) Z
      (y : ((D₂).right Y).obj (DGOpposite.op Z)) (l : L₀.obj Z),
      f.app X (CatTensorProduct.tmul (N := (D₁).right X) (M := (D₂).tensorObj L₀) Y x
          (CatTensorProduct.tmul (N := (D₂).right Y) (M := L₀) Z y l)) =
        g.app X (CatTensorProduct.tmul (N := (D₁).right X) (M := (D₂).tensorObj L₀) Y x
          (CatTensorProduct.tmul (N := (D₂).right Y) (M := L₀) Z y l))) :
    f = g := by
  apply CatModule.Hom.ext
  intro X t
  have he : (f.app X : _ →+ _) = g.app X := by
    apply CatTensorProduct.addHom_ext
    intro Y x t'
    have h2 : (f.app X).comp
          ((CatTensorProduct.tmulAddHom ((D₁).right X) ((D₂).tensorObj L₀) Y) x) =
        (g.app X).comp
          ((CatTensorProduct.tmulAddHom ((D₁).right X) ((D₂).tensorObj L₀) Y) x) := by
      apply CatTensorProduct.addHom_ext
      intro Z y l
      exact h X Y x Z y l
    exact DFunLike.congr_fun h2 t'
  exact DFunLike.congr_fun he t

/-- The comparison is natural in the dg module. -/
theorem diagramWeightTensorCompHom_naturality {L₀ L₁ : CatModule.{u} (WeightCategory C)}
    (ψ : L₀ ⟶ L₁) :
    (D₁).tensorMap ((D₂).tensorMap ψ) ≫
        diagramWeightTensorCompHom G H L hgL hgR hhL hhR hPL hPR β hw hb hβL hβR L₁ =
      diagramWeightTensorCompHom G H L hgL hgR hhL hhR hPL hPR β hw hb hβL hβR L₀ ≫
        (D₃).tensorMap ψ := by
  apply diagramWeightTensorComp_hom_ext
  intro X Y x Z y l
  rw [CatModule.comp_app, CatModule.comp_app, CatBimodule.tensorMap_tmul,
    CatBimodule.tensorMap_tmul, diagramWeightTensorCompHom_app_tmul,
    diagramWeightTensorCompHom_app_tmul, CatBimodule.tensorMap_tmul]

/-- **The comparison `D_M ⊗ (D_N ⊗ -) ⟶ D_P ⊗ -`** of functors on dg modules over the weight
category, `x ⊗ (y ⊗ l) ↦ β x y ⊗ l`. -/
def diagramWeightTensorCompNatTrans :
    CatBimodule.tensorFunctor.{u, u} (D₂) ⋙ CatBimodule.tensorFunctor.{u, u} (D₁) ⟶
      CatBimodule.tensorFunctor.{u, u} (D₃) where
  app L₀ := diagramWeightTensorCompHom G H L hgL hgR hhL hhR hPL hPR β hw hb hβL hβR L₀
  naturality _ _ ψ :=
    diagramWeightTensorCompHom_naturality G H L hgL hgR hhL hhR hPL hPR β hw hb hβL hβR ψ

@[simp]
theorem diagramWeightTensorCompNatTrans_app (L₀ : CatModule.{u} (WeightCategory C)) :
    (diagramWeightTensorCompNatTrans G H L hgL hgR hhL hhR hPL hPR β hw hb hβL hβR).app L₀ =
      diagramWeightTensorCompHom G H L hgL hgR hhL hhR hPL hPR β hw hb hβL hβR L₀ := rfl

/-- The comparison commutes with the cohomological shifts. -/
instance diagramWeightTensorCompNatTrans_commShift :
    NatTrans.CommShift (diagramWeightTensorCompNatTrans G H L hgL hgR hhL hhR hPL hPR β hw hb hβL
      hβR) ℤ where
  shift_comm a := by
    ext L₀ : 2
    apply diagramWeightTensorComp_hom_ext
    intro X Y x Z y l
    let τ := diagramWeightTensorCompNatTrans G H L hgL hgR hhL hhR hPL hPR β hw hb hβL hβR
    let e₁ := diagramWeightTensorShiftNatIso G hgL hgR a
    let e₂ := diagramWeightTensorShiftNatIso H hhL hhR a
    let e₃ := diagramWeightTensorShiftNatIso L hPL hPR a
    let l₀ : L₀.obj Z := Shift.unmk a (M := L₀.obj Z) l
    change (CatModule.shiftMap a (τ.app L₀)).app X ((e₁.hom.app ((D₂).tensorObj L₀)).app X
        (((D₁).tensorMap (e₂.hom.app L₀)).app X
          (CatTensorProduct.tmul (N := (D₁).right X) (M := (D₂).tensorObj (CatModule.shift a L₀))
            Y x (CatTensorProduct.tmul (N := (D₂).right Y) (M := CatModule.shift a L₀) Z y l)))) =
      (e₃.hom.app L₀).app X ((τ.app (CatModule.shift a L₀)).app X
        (CatTensorProduct.tmul (N := (D₁).right X) (M := (D₂).tensorObj (CatModule.shift a L₀))
          Y x (CatTensorProduct.tmul (N := (D₂).right Y) (M := CatModule.shift a L₀) Z y l)))
    have h₁ : ((D₁).tensorMap (e₂.hom.app L₀)).app X
        (CatTensorProduct.tmul (N := (D₁).right X) (M := (D₂).tensorObj (CatModule.shift a L₀))
          Y x (CatTensorProduct.tmul (N := (D₂).right Y) (M := CatModule.shift a L₀) Z y l)) =
        CatTensorProduct.tmul (N := (D₁).right X) (M := CatModule.shift a ((D₂).tensorObj L₀)) Y x
          (Shift.mk a (CatTensorProduct.tmul (N := (D₂).right Y) (M := L₀) Z y l₀)) := by
      rw [CatBimodule.tensorMap_tmul]
      exact congrArg _ (diagramWeightTensorShiftNatIso_hom_tmul H hhL hhR a L₀ Y Z y l)
    have h₂ : (e₁.hom.app ((D₂).tensorObj L₀)).app X
        (CatTensorProduct.tmul (N := (D₁).right X) (M := CatModule.shift a ((D₂).tensorObj L₀)) Y x
          (Shift.mk a (CatTensorProduct.tmul (N := (D₂).right Y) (M := L₀) Z y l₀))) =
        Shift.mk a (CatTensorProduct.tmul (N := (D₁).right X) (M := (D₂).tensorObj L₀) Y x
          (CatTensorProduct.tmul (N := (D₂).right Y) (M := L₀) Z y l₀)) :=
      diagramWeightTensorShiftNatIso_hom_tmul G hgL hgR a ((D₂).tensorObj L₀) X Y x
        (Shift.mk a (CatTensorProduct.tmul (N := (D₂).right Y) (M := L₀) Z y l₀))
    rw [h₁, h₂]
    change Shift.mk a ((diagramWeightTensorCompHom G H L hgL hgR hhL hhR hPL hPR β hw hb hβL hβR
          L₀).app X (CatTensorProduct.tmul (N := (D₁).right X) (M := (D₂).tensorObj L₀) Y x
            (CatTensorProduct.tmul (N := (D₂).right Y) (M := L₀) Z y l₀))) =
      (e₃.hom.app L₀).app X ((diagramWeightTensorCompHom G H L hgL hgR hhL hhR hPL hPR β hw hb hβL
          hβR (CatModule.shift a L₀)).app X
        (CatTensorProduct.tmul (N := (D₁).right X) (M := (D₂).tensorObj (CatModule.shift a L₀))
          Y x (CatTensorProduct.tmul (N := (D₂).right Y) (M := CatModule.shift a L₀) Z y l)))
    rw [diagramWeightTensorCompHom_app_tmul, diagramWeightTensorCompHom_app_tmul]
    exact (diagramWeightTensorShiftNatIso_hom_tmul L hPL hPR a L₀ X Z _ l).symm

end Categorification
