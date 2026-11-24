/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.BalancedTensor
import Categorification.Algebra.DiagramWeightCoend

/-!
# The ordinary balanced tensor and its weight coends

For two fixed endpoint weights, forgetting the intermediate weights maps
the tensor coend to the ordinary balanced tensor of the underlying
additive groups. Splitting the coefficients by weight gives a left
inverse, with a projection that selects the desired total weight.
-/

noncomputable section

namespace Categorification

open CategoryTheory DG MulOpposite
open scoped DG.DegreeZero

universe u

variable {A B C M N : Type u} [Ring A] [Ring B] [Ring C]
  [InternalGrading A] [InternalGrading B] [InternalGrading C]
  [BigradedDGRing A] [BigradedDGRing B] [BigradedDGRing C]
  [AddCommGroup M] [AddCommGroup N]
  [Module A M] [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]
  [Module B N] [Module Cᵐᵒᵖ N] [SMulCommClass B Cᵐᵒᵖ N]
  (G : ℤ → AddSubgroup M) (H : ℤ → AddSubgroup N) [DirectSum.Decomposition G] [DirectSum.Decomposition H]
  (hgL : ∀ {i j : ℤ} {a : A} {x : M}, a ∈ wgrading i → x ∈ G j → a • x ∈ G (i + j))
  (hgR : ∀ {i j : ℤ} {b : B} {x : M}, b ∈ wgrading i → x ∈ G j → op b • x ∈ G (j + i))
  (hhL : ∀ {i j : ℤ} {b : B} {y : N}, b ∈ wgrading i → y ∈ H j → b • y ∈ H (i + j))
  (hhR : ∀ {i j : ℤ} {c : C} {y : N}, c ∈ wgrading i → y ∈ H j → op c • y ∈ H (j + i))
  (X : WeightCategory A) (Z : WeightCategory C)

local notation "D₁" => diagramWeightBimodule G hgL hgR
local notation "D₂" => diagramWeightBimodule H hhL hhR
local notation "Out" => CatTensorProduct (CatBimodule.right D₁ X) (CatBimodule.left D₂ Z)

private abbrev sliceWeight (B : Type*) (a i : ℤ) : WeightCategory B := ⟨a - i⟩

private def sliceLeft (i : ℤ) :
    G i →+ ((D₁).right X).obj (DG.DGOpposite.op (sliceWeight B X.as i)) where
  toFun x := ⟨x.val, by
    change x.val ∈ G (X.as - (X.as - i))
    rw [show X.as - (X.as - i) = i by omega]
    exact x.property⟩
  map_zero' := rfl
  map_add' _ _ := rfl

private def sliceRight (Y : WeightCategory B) : N →+ ((D₂).left Z).obj Y where
  toFun y := DirectSum.decompose H y (Y.as - Z.as)
  map_zero' := by rw [DirectSum.decompose_zero]; rfl
  map_add' y y' := by rw [DirectSum.decompose_add]; rfl

private def tensorSliceAt (i : ℤ) : G i →+ N →+ Out :=
  let Y := sliceWeight B X.as i
  ((CatTensorProduct.tmulAddHom ((D₁).right X) ((D₂).left Z) Y).compl₂
    (sliceRight H hhL hhR Z Y)).comp (sliceLeft G hgL hgR X i)

/-- Split ordinary coefficients before taking their weight coend tensor. -/
def diagramWeightTensorSlice : M →+ N →+ Out :=
  (DirectSum.toAddMonoid (tensorSliceAt G H hgL hgR hhL hhR X Z)).comp
    (DirectSum.decomposeAddEquiv G).toAddMonoidHom

/-- Slicing homogeneous inputs of the required total degree gives one pure coend tensor. -/
theorem diagramWeightTensorSlice_of_homogeneous (i : ℤ) (x : G i) (y : N) :
    diagramWeightTensorSlice G H hgL hgR hhL hhR X Z x.val y =
      CatTensorProduct.tmul (sliceWeight B X.as i) (sliceLeft G hgL hgR X i x)
        (sliceRight H hhL hhR Z (sliceWeight B X.as i) y) := by
  change DirectSum.toAddMonoid (tensorSliceAt G H hgL hgR hhL hhR X Z)
    (DirectSum.decompose G x.val) y = _
  rw [DirectSum.decompose_coe G x, DirectSum.toAddMonoid_of]
  rfl


omit [BigradedDGRing B] in
include hhL in
private theorem slice_projection_smul (b : B) {l : ℤ} (hb : b ∈ wgrading l) (d : ℤ) (y : N) :
    (DirectSum.decompose H (b • y) (l + d)).val = b • (DirectSum.decompose H y d).val := by
  induction y using DirectSum.Decomposition.inductionOn H with
  | zero => simp [smul_zero, DirectSum.decompose_zero]
  | @homogeneous j y =>
    have hby : b • y.val ∈ H (l + j) := hhL hb y.property
    by_cases he : j = d
    · subst d
      rw [DirectSum.decompose_of_mem_same H hby, DirectSum.decompose_of_mem_same H y.property]
    · rw [DirectSum.decompose_of_mem_ne H hby (fun h => he (add_left_cancel h)),
        DirectSum.decompose_of_mem_ne H y.property he, smul_zero]
  | add y y' hy hy' =>
    simp only [smul_add, DirectSum.decompose_add, DirectSum.add_apply, AddSubgroup.coe_add, hy, hy']

private theorem tensorSlice_balanced_of_homogeneous {i l : ℤ} (x : G i)
    (b : B) (hb : b ∈ wgrading l) (y : N) :
    diagramWeightTensorSlice G H hgL hgR hhL hhR X Z (op b • x.val) y =
      diagramWeightTensorSlice G H hgL hgR hhL hhR X Z x.val (b • y) := by
  let Y := sliceWeight B X.as (i + l)
  let Y' := sliceWeight B X.as i
  let f : Y ⟶ Y' := WeightCategory.homMk b (by
    change b ∈ wgrading (X.as - i - (X.as - (i + l)))
    rw [show X.as - i - (X.as - (i + l)) = l by omega]
    exact hb)
  let xb : G (i + l) := ⟨op b • x.val, hgR hb x.property⟩
  rw [show op b • x.val = xb.val from rfl,
    diagramWeightTensorSlice_of_homogeneous G H hgL hgR hhL hhR X Z (i + l) xb,
    diagramWeightTensorSlice_of_homogeneous G H hgL hgR hhL hhR X Z i x]
  have hx : sliceLeft G hgL hgR X (i + l) xb =
      ((D₁).right X).ract f (sliceLeft G hgL hgR X i x) := by
    rw [CatBimodule.right_ract]
    rfl
  have hy : sliceRight H hhL hhR Z Y' (b • y) = f • sliceRight H hhL hhR Z Y y := by
    apply Subtype.ext
    change (DirectSum.decompose H (b • y) (X.as - i - Z.as)).val =
      b • (DirectSum.decompose H y (X.as - (i + l) - Z.as)).val
    rw [show X.as - i - Z.as = l + (X.as - (i + l) - Z.as) by omega]
    exact slice_projection_smul H hhL b hb _ y
  rw [hx, hy]
  exact CatTensorProduct.ract_tmul f _ _


/-- Splitting a product into weight components respects ordinary balancing. -/
theorem diagramWeightTensorSlice_balanced (b : B) (x : M) (y : N) :
    diagramWeightTensorSlice G H hgL hgR hhL hhR X Z (op b • x) y =
      diagramWeightTensorSlice G H hgL hgR hhL hhR X Z x (b • y) := by
  let F := diagramWeightTensorSlice G H hgL hgR hhL hhR X Z
  change F (op b • x) y = F x (b • y)
  induction b using DirectSum.Decomposition.inductionOn (wgrading (M := B)) with
  | zero => simp
  | @homogeneous l b =>
    induction x using DirectSum.Decomposition.inductionOn G with
    | zero => simp
    | @homogeneous i x =>
      exact tensorSlice_balanced_of_homogeneous G H hgL hgR hhL hhR X Z x b.val b.property y
    | add x x' hx hx' =>
      simp only [smul_add, map_add, AddMonoidHom.add_apply, hx, hx']
  | add b b' hb hb' =>
    have h : op (b + b') • x = (op b + op b') • x :=
      congrArg (fun c : Bᵐᵒᵖ => c • x) (op_add b b')
    rw [h]
    simp only [add_smul, map_add, AddMonoidHom.add_apply, hb, hb']


private def sliceLinear : M →ₗ[ℤ] N →ₗ[ℤ] Out :=
  let F := diagramWeightTensorSlice G H hgL hgR hhL hhR X Z
  LinearMap.mk₂ ℤ (fun x y => F x y)
    (fun x x' y => DFunLike.congr_fun (map_add F x x') y)
    (fun c x y => DFunLike.congr_fun (map_zsmul F c x) y)
    (fun x y y' => map_add (F x) y y')
    (fun c x y => map_zsmul (F x) c y)

/-- The slicing map on the ordinary additive balanced tensor product. -/
def diagramWeightTensorSliceOrdinary : BalancedTensor ℤ ℤ B M N →+ Out :=
  (BalancedTensor.lift (sliceLinear G H hgL hgR hhL hhR X Z)
    (fun x b y => diagramWeightTensorSlice_balanced G H hgL hgR hhL hhR X Z b x y)).toAddMonoidHom

/-- On an ordinary pure tensor, the descended map slices its two coefficients. -/
theorem diagramWeightTensorSliceOrdinary_tmul (x : M) (y : N) :
    diagramWeightTensorSliceOrdinary G H hgL hgR hhL hhR X Z
      (BalancedTensor.tmul (k := ℤ) (B := ℤ) (A := B) x y) =
    diagramWeightTensorSlice G H hgL hgR hhL hhR X Z x y := by
  exact BalancedTensor.lift_tmul (B := ℤ) (A := B) (sliceLinear G H hgL hgR hhL hhR X Z)
    (fun x b y => diagramWeightTensorSlice_balanced G H hgL hgR hhL hhR X Z b x y) x y

private theorem slice_tmul_at (i : ℤ) (Y : WeightCategory B) (hY : Y = sliceWeight B X.as i)
    (x : (D₁).obj X Y) (y : (D₂).obj Y Z) :
    diagramWeightTensorSlice G H hgL hgR hhL hhR X Z x.val y.val = CatTensorProduct.tmul Y x y := by
  subst Y
  let v : M := x.val
  let z : G i := ⟨v, by
    have hx : v ∈ G (X.as - (X.as - i)) := x.property
    rw [show X.as - (X.as - i) = i by omega] at hx
    exact hx⟩
  rw [show x.val = z.val from rfl, diagramWeightTensorSlice_of_homogeneous G H hgL hgR hhL hhR X Z i z]
  have hx : sliceLeft G hgL hgR X i z = x := Subtype.ext rfl
  have hy : sliceRight H hhL hhR Z (sliceWeight B X.as i) y.val = y :=
    Subtype.ext (DirectSum.decompose_of_mem_same H y.property)
  rw [hx, hy]

/-- Slicing the two entries of a pure weight tensor recovers that tensor. -/
theorem diagramWeightTensorSlice_tmul (Y : WeightCategory B)
    (x : (D₁).obj X Y) (y : (D₂).obj Y Z) :
    diagramWeightTensorSlice G H hgL hgR hhL hhR X Z x.val y.val = CatTensorProduct.tmul Y x y :=
  slice_tmul_at G H hgL hgR hhL hhR X Z (X.as - Y.as) Y
    (by
      cases Y with
      | mk a =>
        have he : X.as - (X.as - a) = a := by omega
        exact (congrArg (fun n : ℤ => (⟨n⟩ : WeightCategory B)) he).symm) x y

local notation "Ordinary" => BalancedTensor ℤ ℤ B M N

private def ordinaryTensorAt (Y : WeightCategory B) :
    ((D₁).right X).obj (DG.DGOpposite.op Y) →+ ((D₂).left Z).obj Y →+ Ordinary where
  toFun x :=
    { toFun := fun y => BalancedTensor.tmul x.val y.val
      map_zero' := BalancedTensor.tmul_zero x.val
      map_add' := fun y y' => BalancedTensor.tmul_add x.val y.val y'.val }
  map_zero' := AddMonoidHom.ext fun y => BalancedTensor.zero_tmul y.val
  map_add' x x' := AddMonoidHom.ext fun y => BalancedTensor.add_tmul x.val x'.val y.val

omit [DirectSum.Decomposition G] [DirectSum.Decomposition H] in
private theorem ordinaryTensorAt_balanced :
    CatTensorProduct.Balanced (N := (D₁).right X) (M := (D₂).left Z)
      (ordinaryTensorAt G H hgL hgR hhL hhR X Z) := by
  intro Y Y' f x y
  rw [CatBimodule.right_ract]
  exact BalancedTensor.op_smul_tmul x.val f.val y.val

/-- Forget the intermediate weight and send the tensor to the ordinary balanced tensor. -/
def diagramWeightTensorToOrdinary : Out →+ Ordinary :=
  CatTensorProduct.lift (ordinaryTensorAt G H hgL hgR hhL hhR X Z)
    (ordinaryTensorAt_balanced G H hgL hgR hhL hhR X Z)

omit [DirectSum.Decomposition G] [DirectSum.Decomposition H] in
/-- Forgetting the weight on a pure tensor gives the ordinary pure tensor. -/
theorem diagramWeightTensorToOrdinary_tmul (Y : WeightCategory B)
    (x : (D₁).obj X Y) (y : (D₂).obj Y Z) :
    diagramWeightTensorToOrdinary G H hgL hgR hhL hhR X Z (CatTensorProduct.tmul Y x y) =
      BalancedTensor.tmul x.val y.val :=
  CatTensorProduct.lift_tmul (ordinaryTensorAt G H hgL hgR hhL hhR X Z)
    (ordinaryTensorAt_balanced G H hgL hgR hhL hhR X Z) Y x y

/-- Slicing at the original endpoint weights is a left inverse to forgetting weights. -/
theorem diagramWeightTensorSlice_leftInverse :
    Function.LeftInverse (diagramWeightTensorSliceOrdinary G H hgL hgR hhL hhR X Z)
      (diagramWeightTensorToOrdinary G H hgL hgR hhL hhR X Z) := by
  let f := diagramWeightTensorToOrdinary G H hgL hgR hhL hhR X Z
  let g := diagramWeightTensorSliceOrdinary G H hgL hgR hhL hhR X Z
  intro t
  change g (f t) = t
  induction t using CatTensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul Y x y =>
    have hf : f (CatTensorProduct.tmul Y x y) = BalancedTensor.tmul x.val y.val :=
      diagramWeightTensorToOrdinary_tmul G H hgL hgR hhL hhR X Z Y x y
    rw [hf]
    exact (diagramWeightTensorSliceOrdinary_tmul G H hgL hgR hhL hhR X Z x.val y.val).trans
      (diagramWeightTensorSlice_tmul G H hgL hgR hhL hhR X Z Y x y)
  | add t t' ht ht' => rw [map_add, map_add, ht, ht']

/-- The endpoint weight coend embeds as a direct summand of the ordinary balanced tensor. -/
def diagramWeightTensorOrdinaryEquivRange :
    Out ≃+ (diagramWeightTensorToOrdinary G H hgL hgR hhL hhR X Z).range :=
  AddMonoidHom.ofInjective (diagramWeightTensorSlice_leftInverse G H hgL hgR hhL hhR X Z).injective

/-- Project the ordinary tensor to the summand of total weight `X - Z`. -/
def diagramWeightOrdinaryProjection : Ordinary →+ Ordinary :=
  (diagramWeightTensorToOrdinary G H hgL hgR hhL hhR X Z).comp
    (diagramWeightTensorSliceOrdinary G H hgL hgR hhL hhR X Z)

/-- The projection keeps homogeneous pure tensors in the endpoint degree and
kills homogeneous pure tensors in every other degree. -/
theorem diagramWeightOrdinaryProjection_tmul {i j : ℤ} (x : G i) (y : H j) :
    diagramWeightOrdinaryProjection G H hgL hgR hhL hhR X Z (BalancedTensor.tmul x.val y.val) =
      if i + j = X.as - Z.as then BalancedTensor.tmul x.val y.val else 0 := by
  let f := diagramWeightTensorToOrdinary G H hgL hgR hhL hhR X Z
  let Y := sliceWeight B X.as i
  change f (diagramWeightTensorSliceOrdinary G H hgL hgR hhL hhR X Z
    (BalancedTensor.tmul x.val y.val)) = _
  rw [diagramWeightTensorSliceOrdinary_tmul, diagramWeightTensorSlice_of_homogeneous]
  by_cases h : i + j = X.as - Z.as
  · rw [ite_eq_left h]
    have hf : f (CatTensorProduct.tmul Y (sliceLeft G hgL hgR X i x)
        (sliceRight H hhL hhR Z Y y.val)) =
        BalancedTensor.tmul (sliceLeft G hgL hgR X i x).val (sliceRight H hhL hhR Z Y y.val).val :=
      diagramWeightTensorToOrdinary_tmul G H hgL hgR hhL hhR X Z Y _ _
    rw [hf]
    have he : Y.as - Z.as = j := by
      change X.as - i - Z.as = j
      omega
    change BalancedTensor.tmul x.val (DirectSum.decompose H y.val (Y.as - Z.as)).val =
      BalancedTensor.tmul x.val y.val
    rw [he, DirectSum.decompose_of_mem_same H y.property]
  · rw [ite_eq_right h]
    have hz : sliceRight H hhL hhR Z Y y.val = 0 := by
      apply Subtype.ext
      change (DirectSum.decompose H y.val (Y.as - Z.as)).val = 0
      exact DirectSum.decompose_of_mem_ne H y.property fun he => h (by
        change j = X.as - i - Z.as at he
        omega)
    rw [hz, CatTensorProduct.tmul_zero, map_zero]

end Categorification
