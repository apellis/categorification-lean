/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DiagramWeightBimodule
import Categorification.Algebra.DiagramWeightLocalizedCohomology
import DG.Category.Derived.Induction
import DG.Category.Derived.RestrictionIso

/-!
# Internal translations of diagram weight tensors

Translating both indexing weights preserves the coefficient grade. The
resulting coend isomorphism also applies to the derived tensor because
restriction along the weight translation preserves K-projective modules.
This is the internal-grading comparison for the periodic companion
triangles in Webster, arXiv:1309.3796v2, §8.2, Proposition 8.4.
-/

noncomputable section

namespace Categorification

open CategoryTheory DG MulOpposite
open scoped DG.DegreeZero

universe u
variable {A B M : Type u} [Ring A] [Ring B] [InternalGrading A] [InternalGrading B]
  [BigradedDGRing A] [BigradedDGRing B]
  [AddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]

variable (G : ℤ → AddSubgroup M)
  (hl : ∀ {i j : ℤ} {a : A} {x : M}, a ∈ wgrading i → x ∈ G j → a • x ∈ G (i + j))
  (hr : ∀ {i j : ℤ} {b : B} {x : M}, b ∈ wgrading i → x ∈ G j → op b • x ∈ G (j + i))

local notation "D₀" => diagramWeightBimodule G hl hr
local notation "Ashift" j:arg => WeightCategory.shiftFunctor A j
local notation "Bshift" j:arg => WeightCategory.shiftFunctor B j

private theorem degreeZero_addEquiv_mem {U V : Type u} [AddCommGroup U] [AddCommGroup V]
    (e : InDegreeZero U ≃+ InDegreeZero V) (n : ℤ) (v : InDegreeZero U) :
    e v ∈ DG.grading (M := InDegreeZero V) n ↔ v ∈ DG.grading (M := InDegreeZero U) n := by
  rw [InDegreeZero.mem_grading_iff, InDegreeZero.mem_grading_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (e.injective (h.trans (map_zero e).symm))
  · rintro (h | rfl)
    · exact Or.inl h
    · exact Or.inr (map_zero _)

section ShiftLeft

variable (H : ℤ → AddSubgroup M)
  (hL : ∀ {i j : ℤ} {a : A} {x : M}, a ∈ wgrading i → x ∈ H j → a • x ∈ H (i + j))
  (hR : ∀ {i j : ℤ} {b : B} {x : M}, b ∈ wgrading i → x ∈ H j → op b • x ∈ H (j + i))
  (s : ℤ)

omit [Ring B] [InternalGrading B] [BigradedDGRing B]
  [Module A M] [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M] in
private theorem diagramWeight_shift_membership (hH : ∀ n, H n = G (n + s))
    (X : WeightCategory A) (Y : WeightCategory B)
    (v : M) :
    v ∈ H (X.as - Y.as) ↔ v ∈ G (((Ashift s).obj X).as - Y.as) := by
  change v ∈ H (X.as - Y.as) ↔ v ∈ G ((X.as + s) - Y.as)
  rw [hH, show (X.as - Y.as) + s = (X.as + s) - Y.as by omega]

private def diagramWeight_shift_piece (hH : ∀ n, H n = G (n + s))
    (X : WeightCategory A) (Y : WeightCategory B) :
    InDegreeZero (H (X.as - Y.as)) ≃+ InDegreeZero (G (((Ashift s).obj X).as - Y.as)) where
  toFun v := ⟨v.val, (diagramWeight_shift_membership G H s hH X Y v.val).mp v.property⟩
  invFun v := ⟨v.val, (diagramWeight_shift_membership G H s hH X Y v.val).mpr v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- Translating the grading of the coefficient reindexes its left
diagram weight module. -/
def diagramWeightLeftGradeShiftIso (hH : ∀ n, H n = G (n + s)) (Y : WeightCategory B) :
    (diagramWeightBimodule H hL hR).left Y ≅
      CatModule.precompObj (Ashift s) ((D₀).left Y) := by
  let e (X : WeightCategory A) := diagramWeight_shift_piece G H s hH X Y
  refine CatModule.isoMk e ?_ ?_ ?_
  · intro X n v
    exact degreeZero_addEquiv_mem (e X) n v
  · intro X v
    change e X 0 = 0
    exact map_zero _
  · intro X Z a v
    apply Subtype.ext
    rfl

end ShiftLeft

section KProjective

universe w

private def weightShiftCancellation (A : Type u) [Ring A] [InternalGrading A] [BigradedDGRing A]
    (s t : ℤ) (hst : s + t = 0) :
    WeightCategory.shiftFunctor A s ⋙ WeightCategory.shiftFunctor A t ≅ 𝟭 (WeightCategory A) :=
  NatIso.ofComponents (fun _ => WeightCategory.isoOfEq (by simp [add_assoc, hst]))
    (fun f => Subtype.ext (by simp))

private def weightPrecompShiftAdjunction (A : Type u) [Ring A] [InternalGrading A] [BigradedDGRing A]
    (j : ℤ) :
    CatModule.precomp.{w} (WeightCategory.shiftFunctor A j) ⊣
      CatModule.precomp.{w} (WeightCategory.shiftFunctor A (-j)) := by
  let F := WeightCategory.shiftFunctor A j
  let I := WeightCategory.shiftFunctor A (-j)
  let hu := CatModule.precompNatIso
    (weightShiftCancellation A (-j) j (neg_add_cancel j)).symm
    (fun _ => WeightCategory.mem_grading_zero_of_val_eq_one _ rfl)
    (fun _ => WeightCategory.d_eq_zero_of_val_eq_one _ rfl)
    (fun _ => WeightCategory.mem_grading_zero_of_val_eq_one _ rfl)
    (fun _ => WeightCategory.d_eq_zero_of_val_eq_one _ rfl)
  let hc := CatModule.precompNatIso
    (weightShiftCancellation A j (-j) (add_neg_cancel j))
    (fun _ => WeightCategory.mem_grading_zero_of_val_eq_one _ rfl)
    (fun _ => WeightCategory.d_eq_zero_of_val_eq_one _ rfl)
    (fun _ => WeightCategory.mem_grading_zero_of_val_eq_one _ rfl)
    (fun _ => WeightCategory.d_eq_zero_of_val_eq_one _ rfl)
  let E := CategoryTheory.Equivalence.mk (CatModule.precomp.{w} F) (CatModule.precomp.{w} I)
    ((CatModule.precompIdIso _).symm ≪≫ hu ≪≫ CatModule.precompCompIso I F)
    ((CatModule.precompCompIso F I).symm ≪≫ hc ≪≫ CatModule.precompIdIso _)
  change E.functor ⊣ E.inverse
  exact E.toAdjunction

/-- Reindexing the internal weights preserves K-projective weight modules. -/
theorem weightShift_precomp_isKProjective {A : Type u} [Ring A] [InternalGrading A] [BigradedDGRing A]
    (j : ℤ) {P : CatModule.{w} (WeightCategory A)} (hP : CatModule.IsKProjective P) :
    CatModule.IsKProjective (CatModule.precompObj (WeightCategory.shiftFunctor A j) P) :=
  CatModule.IsKProjective.of_adjunction (weightPrecompShiftAdjunction A j) hP

end KProjective

section Tensor

variable (t : ℤ) (L : CatModule.{u} (WeightCategory B))

local notation "L₀" => CatModule.precompObj (Bshift t) L

omit [Module A M] [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M] in
private theorem diagramWeight_diagonal_membership (X : WeightCategory A) (Y : WeightCategory B)
    (v : M) :
    v ∈ G (X.as - Y.as) ↔ v ∈ G (((Ashift t).obj X).as - ((Bshift t).obj Y).as) := by
  change v ∈ G (X.as - Y.as) ↔ v ∈ G ((X.as + t) - (Y.as + t))
  rw [add_sub_add_right_eq_sub]

private def diagramWeight_diagonal_piece (X : WeightCategory A) (Y : WeightCategory B) :
    (D₀).obj X Y ≃+ (D₀).obj ((Ashift t).obj X) ((Bshift t).obj Y) where
  toFun v := ⟨v.val, (diagramWeight_diagonal_membership G t X Y v.val).mp v.property⟩
  invFun v := ⟨v.val, (diagramWeight_diagonal_membership G t X Y v.val).mpr v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

set_option quotPrecheck false in
local notation "J" X:arg => (D₀).right X
local notation "S" X:arg => CatTensorProduct (J X) (L₀)
set_option quotPrecheck false in
local notation "T" X:arg => CatTensorProduct (J ((Ashift t).obj X)) L
local notation "E" => diagramWeight_diagonal_piece G hl hr t

private theorem diagramWeight_diagonal_ract (X : WeightCategory A) {Y Z : WeightCategory B}
    (a : Y ⟶ Z) (x : (D₀).obj X Z) :
    E X Y ((D₀).ract a x) = (D₀).ract ((Bshift t).map a) (E X Z x) :=
  Subtype.ext rfl

private theorem diagramWeight_diagonal_lact {X Z : WeightCategory A} (Y : WeightCategory B)
    (a : X ⟶ Z) (x : (D₀).obj X Y) :
    E Z Y ((D₀).lact a x) = (D₀).lact ((Ashift t).map a) (E X Y x) :=
  Subtype.ext rfl

private def diagramWeight_shift_tensor_family (X : WeightCategory A) (Y : WeightCategory B) :
    (J X).obj (DGOpposite.op Y) →+ (L₀).obj Y →+ T X :=
  (CatTensorProduct.tmulAddHom (J ((Ashift t).obj X)) L ((Bshift t).obj Y)).comp
    (E X Y).toAddMonoidHom

private theorem diagramWeight_shift_tensor_balanced (X : WeightCategory A) :
    CatTensorProduct.Balanced (diagramWeight_shift_tensor_family G hl hr t L X) := by
  intro Y Z a x y
  change CatTensorProduct.tmul (N := J ((Ashift t).obj X)) (M := L)
      ((Bshift t).obj Y) (E X Y ((J X).ract a x)) y =
    CatTensorProduct.tmul (N := J ((Ashift t).obj X)) (M := L)
      ((Bshift t).obj Z) (E X Z x) (L.act ((Bshift t).map a) y)
  rw [CatBimodule.right_ract, diagramWeight_diagonal_ract, ← CatBimodule.right_ract]
  exact CatTensorProduct.ract_tmul (N := J ((Ashift t).obj X)) (M := L)
    ((Bshift t).map a) (E X Z x) y


private def diagramWeight_shift_tensor_addHom (X : WeightCategory A) : S X →+ T X :=
  CatTensorProduct.lift (diagramWeight_shift_tensor_family G hl hr t L X)
    (diagramWeight_shift_tensor_balanced G hl hr t L X)

private theorem diagramWeight_shift_tensor_addHom_tmul
    (X : WeightCategory A) (Y : WeightCategory B) (x : (D₀).obj X Y) (y : (L₀).obj Y) :
    diagramWeight_shift_tensor_addHom G hl hr t L X
      (CatTensorProduct.tmul (N := J X) (M := L₀) Y x y) =
      CatTensorProduct.tmul (N := J ((Ashift t).obj X)) (M := L) ((Bshift t).obj Y) (E X Y x) y :=
  CatTensorProduct.lift_tmul (diagramWeight_shift_tensor_family G hl hr t L X)
    (diagramWeight_shift_tensor_balanced G hl hr t L X) Y x y


private theorem diagramWeight_diagonal_piece_mem (X : WeightCategory A) (Y : WeightCategory B)
    (i : ℤ) (x : (D₀).obj X Y) :
    E X Y x ∈ DG.grading i ↔ x ∈ DG.grading i :=
  degreeZero_addEquiv_mem (E X Y) i x

/-- Translate both weights on a pure tensor to move reindexing from the
input to the output of the diagram weight coend. -/
private def diagramWeightTensorInternalShiftHom :
    (D₀).tensorObj (L₀) ⟶ CatModule.precompObj (Ashift t) ((D₀).tensorObj L) where
  app X := diagramWeight_shift_tensor_addHom G hl hr t L X
  map_mem' {X i z} hz := by
    apply CatTensorProduct.lift_mem (diagramWeight_shift_tensor_family G hl hr t L X)
      (diagramWeight_shift_tensor_balanced G hl hr t L X) _ hz
    intro Y a b x y hx hy
    exact CatTensorProduct.tmul_mem_grading ((diagramWeight_diagonal_piece_mem G hl hr t X Y a x).mpr hx) hy
  map_d' {X} z := by
    apply CatTensorProduct.lift_d (diagramWeight_shift_tensor_family G hl hr t L X)
      (diagramWeight_shift_tensor_balanced G hl hr t L X) _ z
    intro Y a x hx y
    let Y' := (Bshift t).obj Y
    let y' : L.obj Y' := y
    have hx' : E X Y x ∈ DG.grading a :=
      (diagramWeight_diagonal_piece_mem G hl hr t X Y a x).mpr hx
    change d (CatTensorProduct.tmul (N := J ((Ashift t).obj X)) (M := L) Y' (E X Y x) y') =
      CatTensorProduct.tmul (N := J ((Ashift t).obj X)) (M := L) Y' (E X Y (d x)) y' +
      koszulSign a • CatTensorProduct.tmul (N := J ((Ashift t).obj X)) (M := L) Y' (E X Y x) (d y')
    have hₓ : d x = 0 := rfl
    have hₓ' : d (E X Y x) = 0 := rfl
    rw [CatTensorProduct.d_tmul_of_mem (N := J ((Ashift t).obj X)) (M := L) Y' hx' y']
    simp only [hₓ, hₓ', map_zero, CatTensorProduct.zero_tmul, zero_add]
  map_smul' {X Z} a v := by
    let l : S X →+ S Z := ((D₀).tensorObj L₀).act a
    let r : T X →+ T Z := ((D₀).tensorObj L).act ((Ashift t).map a)
    let f := diagramWeight_shift_tensor_addHom G hl hr t L X
    let g := diagramWeight_shift_tensor_addHom G hl hr t L Z
    change g (l v) = r (f v)
    have h : g.comp l = r.comp f := by
      apply CatTensorProduct.addHom_ext
      intro Y x y
      let y' : L.obj ((Bshift t).obj Y) := y
      change g (((D₀).tensorObj L₀).act a (CatTensorProduct.tmul Y x y')) =
        r (f (CatTensorProduct.tmul Y x y'))
      rw [CatBimodule.tensorObj_act_tmul]
      change diagramWeight_shift_tensor_addHom G hl hr t L Z
          (CatTensorProduct.tmul Y ((D₀).lact a x) y') =
        ((D₀).tensorObj L).act ((Ashift t).map a)
          (diagramWeight_shift_tensor_addHom G hl hr t L X (CatTensorProduct.tmul Y x y'))
      rw [diagramWeight_shift_tensor_addHom_tmul, diagramWeight_shift_tensor_addHom_tmul]
      change CatTensorProduct.tmul (N := J ((Ashift t).obj Z)) (M := L)
          ((Bshift t).obj Y) (E Z Y ((D₀).lact a x)) y' =
        ((D₀).tensorObj L).act ((Ashift t).map a)
          (CatTensorProduct.tmul (N := J ((Ashift t).obj X)) (M := L) ((Bshift t).obj Y) (E X Y x) y')
      rw [CatBimodule.tensorObj_act_tmul, diagramWeight_diagonal_lact]
    exact DFunLike.congr_fun h v


local notation "Bback" => Bshift (-t)

private def diagramWeight_unshift_obj (Y : WeightCategory B) :
    ((Bshift t).obj ((Bback).obj Y)) ≅ Y :=
  (weightShiftCancellation B (-t) t (neg_add_cancel t)).app Y

omit [Module A M] [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M] in
private theorem diagramWeight_unshift_membership (X : WeightCategory A) (Y : WeightCategory B)
    (v : M) :
    v ∈ G (((Ashift t).obj X).as - Y.as) ↔ v ∈ G (X.as - ((Bback).obj Y).as) := by
  change v ∈ G ((X.as + t) - Y.as) ↔ v ∈ G (X.as - (Y.as + -t))
  rw [show (X.as + t) - Y.as = X.as - (Y.as + -t) by omega]

private def diagramWeight_unshift_piece (X : WeightCategory A) (Y : WeightCategory B) :
    (D₀).obj ((Ashift t).obj X) Y ≃+ (D₀).obj X ((Bback).obj Y) where
  toFun v := ⟨v.val, (diagramWeight_unshift_membership G t X Y v.val).mp v.property⟩
  invFun v := ⟨v.val, (diagramWeight_unshift_membership G t X Y v.val).mpr v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

local notation "E'" => diagramWeight_unshift_piece G hl hr t
local notation "b" => diagramWeight_unshift_obj t

private theorem diagramWeight_unshift_ract (X : WeightCategory A) {Y Z : WeightCategory B}
    (a : Y ⟶ Z) (x : (D₀).obj ((Ashift t).obj X) Z) :
    E' X Y ((D₀).ract a x) = (D₀).ract ((Bback).map a) (E' X Z x) :=
  Subtype.ext rfl

private def diagramWeight_unshift_tensor_family (X : WeightCategory A) (Y : WeightCategory B) :
    (J ((Ashift t).obj X)).obj (DGOpposite.op Y) →+ L.obj Y →+ S X :=
  ((CatTensorProduct.tmulAddHom (J X) L₀ ((Bback).obj Y)).compl₂ (L.act (b Y).inv)).comp
    (E' X Y).toAddMonoidHom

private theorem diagramWeight_unshift_tensor_balanced (X : WeightCategory A) :
    CatTensorProduct.Balanced (diagramWeight_unshift_tensor_family G hl hr t L X) := by
  intro Y Z a x y
  let y₁ : (L₀).obj ((Bback).obj Y) := L.act (b Y).inv y
  let y₂ : (L₀).obj ((Bback).obj Z) := L.act (b Z).inv (L.act a y)
  change CatTensorProduct.tmul (N := J X) (M := L₀) ((Bback).obj Y)
      (E' X Y ((J ((Ashift t).obj X)).ract a x)) y₁ =
    CatTensorProduct.tmul (N := J X) (M := L₀) ((Bback).obj Z) (E' X Z x) y₂
  rw [CatBimodule.right_ract, diagramWeight_unshift_ract, ← CatBimodule.right_ract]
  refine (CatTensorProduct.ract_tmul (N := J X) (M := L₀) ((Bback).map a) (E' X Z x) y₁).trans ?_
  have h := (weightShiftCancellation B (-t) t (neg_add_cancel t)).inv.naturality a
  change a ≫ (b Z).inv = (b Y).inv ≫ (Bshift t).map ((Bback).map a) at h
  apply congrArg (CatTensorProduct.tmul (N := J X) (M := L₀) ((Bback).obj Z) (E' X Z x))
  change L.act ((Bshift t).map ((Bback).map a)) (L.act (b Y).inv y) =
    L.act (b Z).inv (L.act a y)
  simp only [CatModule.act_apply, ← CatModule.comp_smul, h]

private def diagramWeight_unshift_tensor_addHom (X : WeightCategory A) : T X →+ S X :=
  CatTensorProduct.lift (diagramWeight_unshift_tensor_family G hl hr t L X)
    (diagramWeight_unshift_tensor_balanced G hl hr t L X)

private theorem diagramWeight_unshift_tensor_addHom_tmul
    (X : WeightCategory A) (Y : WeightCategory B) (x : (D₀).obj ((Ashift t).obj X) Y)
    (y : L.obj Y) :
    diagramWeight_unshift_tensor_addHom G hl hr t L X
      (CatTensorProduct.tmul (N := J ((Ashift t).obj X)) (M := L) Y x y) =
      CatTensorProduct.tmul (N := J X) (M := L₀) ((Bback).obj Y)
        (E' X Y x) (L.act (b Y).inv y) :=
  CatTensorProduct.lift_tmul (diagramWeight_unshift_tensor_family G hl hr t L X)
    (diagramWeight_unshift_tensor_balanced G hl hr t L X) Y x y


private theorem diagramWeight_shift_unshift_tmul (X : WeightCategory A)
    (Y : WeightCategory B) (x : (D₀).obj ((Ashift t).obj X) Y) (y : L.obj Y) :
    diagramWeight_shift_tensor_addHom G hl hr t L X
      (diagramWeight_unshift_tensor_addHom G hl hr t L X
        (CatTensorProduct.tmul (N := J ((Ashift t).obj X)) (M := L) Y x y)) =
    CatTensorProduct.tmul (N := J ((Ashift t).obj X)) (M := L) Y x y := by
  let Y₀ := (Bback).obj Y
  let Y₁ := (Bshift t).obj Y₀
  let y₀ : (L₀).obj Y₀ := L.act (b Y).inv y
  let y₁ : L.obj Y₁ := y₀
  have hx : E X Y₀ (E' X Y x) = (J ((Ashift t).obj X)).ract (b Y).hom x := by
    rw [CatBimodule.right_ract]
    apply Subtype.ext
    change x.val = op (1 : B) • x.val
    rw [op_one, one_smul]
  have hy : L.act (b Y).hom y₁ = y := by
    change (b Y).hom • ((b Y).inv • y) = y
    rw [← CatModule.comp_smul, Iso.inv_hom_id, CatModule.id_smul]
  rw [diagramWeight_unshift_tensor_addHom_tmul]
  change diagramWeight_shift_tensor_addHom G hl hr t L X
    (CatTensorProduct.tmul (N := J X) (M := L₀) Y₀ (E' X Y x) y₀) = _
  calc
    _ = CatTensorProduct.tmul (N := J ((Ashift t).obj X)) (M := L)
          Y₁ (E X Y₀ (E' X Y x)) y₁ :=
      diagramWeight_shift_tensor_addHom_tmul G hl hr t L X Y₀ _ y₀
    _ = _ := by
      rw [hx, CatTensorProduct.ract_tmul (N := J ((Ashift t).obj X)) (M := L) (b Y).hom x y₁]
      exact congrArg (CatTensorProduct.tmul (N := J ((Ashift t).obj X)) (M := L) Y x) hy

private theorem diagramWeight_unshift_shift_tmul (X : WeightCategory A)
    (Y : WeightCategory B) (x : (D₀).obj X Y) (y : (L₀).obj Y) :
    diagramWeight_unshift_tensor_addHom G hl hr t L X
      (diagramWeight_shift_tensor_addHom G hl hr t L X
        (CatTensorProduct.tmul (N := J X) (M := L₀) Y x y)) =
    CatTensorProduct.tmul (N := J X) (M := L₀) Y x y := by
  let Y₁ := (Bshift t).obj Y
  let Y₀ := (Bback).obj Y₁
  let y₁ : L.obj Y₁ := y
  let y₀ : (L₀).obj Y₀ := L.act (b Y₁).inv y₁
  let c : Y₀ ≅ Y := (weightShiftCancellation B t (-t) (add_neg_cancel t)).app Y
  have hx : E' X Y₁ (E X Y x) = (J X).ract c.hom x := by
    rw [CatBimodule.right_ract]
    apply Subtype.ext
    change x.val = op (1 : B) • x.val
    rw [op_one, one_smul]
  have hc : (Bshift t).map c.hom = (b Y₁).hom := WeightCategory.hom_ext rfl
  have hy : (L₀).act c.hom y₀ = y := by
    change L.act ((Bshift t).map c.hom) (L.act (b Y₁).inv y₁) = y₁
    rw [hc]
    change (b Y₁).hom • ((b Y₁).inv • y₁) = y₁
    rw [← CatModule.comp_smul, Iso.inv_hom_id, CatModule.id_smul]
  rw [diagramWeight_shift_tensor_addHom_tmul]
  change diagramWeight_unshift_tensor_addHom G hl hr t L X
    (CatTensorProduct.tmul (N := J ((Ashift t).obj X)) (M := L) Y₁ (E X Y x) y₁) = _
  calc
    _ = CatTensorProduct.tmul (N := J X) (M := L₀)
         Y₀ (E' X Y₁ (E X Y x)) y₀ :=
      diagramWeight_unshift_tensor_addHom_tmul G hl hr t L X Y₁ _ y₁
    _ = _ := by
      rw [hx, CatTensorProduct.ract_tmul (N := J X) (M := L₀) c.hom x y₀]
      exact congrArg (CatTensorProduct.tmul (N := J X) (M := L₀) Y x) hy

/-- Internal reindexing of the input to a diagram weight coend reindexes the
output by the same translation. -/
def diagramWeightTensorInternalShiftIso :
    (D₀).tensorObj (L₀) ≅ CatModule.precompObj (Ashift t) ((D₀).tensorObj L) := by
  let f := diagramWeightTensorInternalShiftHom G hl hr t L
  letI : IsIso f := by
    apply CatModule.isIso_of_bijective
    intro X
    let g := diagramWeight_unshift_tensor_addHom G hl hr t L X
    have h₁ : g.comp (f.app X) = AddMonoidHom.id _ :=
      CatTensorProduct.addHom_ext (diagramWeight_unshift_shift_tmul G hl hr t L X)
    have h₂ : (f.app X).comp g = AddMonoidHom.id _ :=
      CatTensorProduct.addHom_ext (diagramWeight_shift_unshift_tmul G hl hr t L X)
    have left : Function.LeftInverse g (f.app X) := fun z => DFunLike.congr_fun h₁ z
    have right : Function.RightInverse g (f.app X) := fun z => DFunLike.congr_fun h₂ z
    exact ⟨left.injective, right.surjective⟩
  exact asIso f

end Tensor



section DerivedInternalShift

universe v

open CatModule.DerivedCategory

variable [CatModule.HasDerivedCategory.{v,u} (WeightCategory A)] [CatModule.HasDerivedCategory.{v,u} (WeightCategory B)]

local notation "F₀" => diagramWeightDerivedTensor G hl hr

/-- The derived diagram tensor transports an internal input shift to an
internal output shift. -/
def diagramWeightDerivedTensorInternalShiftIso (t : ℤ)
    (L : CatModule.DerivedCategory.{v,u} (WeightCategory B)) :
    (F₀).obj ((internalShift B t).obj L) ≅ (internalShift A t).obj ((F₀).obj L) := by
  let K := kProjRep L
  let e := kProjRepIso L
  let hK := isKProjective_kProjRep L
  let K' := CatModule.precompObj (Bshift t) K
  let hK' : CatModule.IsKProjective K' := weightShift_precomp_isKProjective t hK
  let U := (D₀).tensorObj K
  let V := (D₀).tensorObj K'
  let e₁ : (internalShift B t).obj (Q.obj K) ≅ Q.obj K' :=
    (QCompInternalShiftIso B t).app K
  let e₂ : V ≅ CatModule.precompObj (Ashift t) U :=
    diagramWeightTensorInternalShiftIso G hl hr t K
  let e₃ : (internalShift A t).obj (Q.obj U) ≅
      Q.obj (CatModule.precompObj (Ashift t) U) :=
    (QCompInternalShiftIso A t).app U
  exact (F₀).mapIso ((internalShift B t).mapIso e ≪≫ e₁) ≪≫
    diagramWeightDerivedTensorObjIso G hl hr hK' ≪≫ Q.mapIso e₂ ≪≫ e₃.symm ≪≫
    (internalShift A t).mapIso ((diagramWeightDerivedTensorObjIso G hl hr hK).symm ≪≫
      (F₀).mapIso e.symm)

/-- Evaluation at an internal weight after reindexing is evaluation at the
translated weight. -/
def weightInternalShift_cohomologyIso (t : ℤ)
    (L : CatModule.DerivedCategory.{v,u} (WeightCategory A)) (X : WeightCategory A) (n : ℤ) :
    (cohomologyFunctor X n).obj ((internalShift A t).obj L) ≅
      (cohomologyFunctor ((Ashift t).obj X) n).obj L := by
  let K := kProjRep L
  let e := kProjRepIso L
  let K' := CatModule.precompObj (Ashift t) K
  let X' := (Ashift t).obj X
  let e₁ : (internalShift A t).obj (Q.obj K) ≅ Q.obj K' :=
    (QCompInternalShiftIso A t).app K
  let e₂ : (cohomologyFunctor X n).obj (Q.obj K') ≅
      (cohomologyFunctor X' n).obj (Q.obj K) :=
    localizedWeightCohomologyIso X n K' ≪≫ (localizedWeightCohomologyIso X' n K).symm
  exact (cohomologyFunctor X n).mapIso ((internalShift A t).mapIso e ≪≫ e₁) ≪≫ e₂ ≪≫
    (cohomologyFunctor X' n).mapIso e.symm

end DerivedInternalShift

end Categorification
