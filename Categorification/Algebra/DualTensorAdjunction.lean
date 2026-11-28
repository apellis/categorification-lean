/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.RightDualModule
import Categorification.Algebra.ProjectiveKProjective

/-!
# `M^∨ ⊗_A - ⊣ M ⊗_B -` for a finitely generated projective coefficient

Let `M` be an `(A, B)`-bimodule which is finitely generated and projective as a right
`B`-module, and `M^∨ = Hom_{Bᵐᵒᵖ}(M, B)` its dual (`Categorification.RightDualModule`), a
`(B, A)`-bimodule. Both are placed in degree `0`. On dg modules,

`M^∨ ⊗_A - ⊣ M ⊗_B -`

(`Categorification.RightDualModule.dualTensorAdjunction`), with unit
`x ↦ Σ_i e_i ⊗ (φ_i ⊗ x)` for a dual basis `(e_i, φ_i)` of `M` and counit
`φ ⊗ (m ⊗ y) ↦ φ(m) y`. This is the dg form of the classical adjunction for a finitely generated
projective module, used for the derived adjunction `M^∨ ⊗ᴸ_A - ⊣ M ⊗ᴸ_B -`.
-/

noncomputable section

namespace Categorification

open CategoryTheory DG MulOpposite TensorProductOver
open scoped DG.DegreeZero

universe u

namespace RightDualModule

section Tensor

variable {R : Type u} [Ring R] {N : Type u} [AddCommGroup N] [Module Rᵐᵒᵖ N]
  {X : Type u} [AddCommGroup X] [DGAddCommGroup X] [Module R X] [DGModule R X]

/-- The differential of `n ⊗ x` for `n` in degree `0`: `d (n ⊗ x) = n ⊗ d x`. -/
theorem d_tmul_inDegreeZero (n : InDegreeZero N) (x : X) :
    d (tmul R n x) = tmul R n (d x) := by
  rw [TensorProductOver.d_tmul_of_mem (InDegreeZero.mem_grading_zero n), InDegreeZero.d_apply,
    zero_tmul, zero_add, koszulSign_zero, one_smul]

theorem finset_sum_tmul {N' : Type u} [AddCommGroup N'] [Module R N'] {ι : Type*}
    (s : Finset ι) (f : ι → N) (y : N') : tmul R (∑ i ∈ s, f i) y = ∑ i ∈ s, tmul R (f i) y :=
  map_sum ((tmulAddHom R N N').flip y) f s

theorem tmul_finset_sum {N' : Type u} [AddCommGroup N'] [Module R N'] {ι : Type*}
    (s : Finset ι) (n : N) (f : ι → N') : tmul R n (∑ i ∈ s, f i) = ∑ i ∈ s, tmul R n (f i) :=
  map_sum (tmulAddHom R N N' n) f s

theorem tmul_op_smul_left {N' : Type u} [AddCommGroup N'] [Module R N'] (c : Rᵐᵒᵖ) (n : N)
    (y : N') : tmul R (c • n) y = tmul R n (unop c • y) :=
  op_smul_tmul (unop c) n y

theorem tmul_mem_inDegreeZero (n : InDegreeZero N) {k : ℤ} {x : X} (hx : x ∈ grading k) :
    tmul R n x ∈ grading k := by
  simpa using TensorProductOver.tmul_mem_grading (InDegreeZero.mem_grading_zero n) hx

end Tensor

variable (A B : Type u) [Ring A] [Ring B] (M : Type u) [AddCommGroup M] [Module A M]
  [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]

local notation "M₀" => InDegreeZero M
local notation "P₀" => InDegreeZero (RightDualModule B M)

variable {A B M}

/-- The evaluation `φ(m) ∈ B` of a dual vector on a vector, both in degree `0`. -/
def ev₀ (ψ : P₀) (m : M₀) : B :=
  unop ((InDegreeZero.equiv (RightDualModule B M) ψ) (InDegreeZero.equiv M m))

theorem ev₀_add_left (ψ ψ' : P₀) (m : M₀) : ev₀ (ψ + ψ') m = ev₀ ψ m + ev₀ ψ' m := rfl

theorem ev₀_zero_left (m : M₀) : ev₀ (0 : P₀) m = 0 := rfl

theorem ev₀_add_right (ψ : P₀) (m m' : M₀) : ev₀ ψ (m + m') = ev₀ ψ m + ev₀ ψ m' := by
  rw [ev₀, ev₀, ev₀, map_add, map_add, MulOpposite.unop_add]

theorem ev₀_zero_right (ψ : P₀) : ev₀ ψ (0 : M₀) = 0 := by
  rw [ev₀, map_zero, map_zero, MulOpposite.unop_zero]

theorem ev₀_op_smul_right (b : B) (ψ : P₀) (m : M₀) : ev₀ ψ (op b • m) = ev₀ ψ m * b := by
  have h : InDegreeZero.equiv M (op b • m) = op b • InDegreeZero.equiv M m := rfl
  rw [ev₀, ev₀, h, map_smul, smul_eq_mul, MulOpposite.unop_mul, MulOpposite.unop_op]

theorem ev₀_smul_left (b : B) (ψ : P₀) (m : M₀) : ev₀ (b • ψ) m = b * ev₀ ψ m := rfl

theorem ev₀_op_smul_left (a : A) (ψ : P₀) (m : M₀) : ev₀ (op a • ψ) m = ev₀ ψ (a • m) := rfl

/-- `φ ↦ φ(m)` as an additive map, for a fixed dual vector. -/
def ev₀AddHom (ψ : P₀) : M₀ →+ B where
  toFun := ev₀ ψ
  map_zero' := ev₀_zero_right ψ
  map_add' := ev₀_add_right ψ

/-- If `n` lies in degree `i` and `z = 0` whenever `n = 0`, then `(-1)^i z = z`. -/
theorem koszulSign_smul_of_mem {N : Type u} [AddCommGroup N] {i : ℤ} {n : InDegreeZero N}
    (hn : n ∈ grading i) {Z : Type u} [AddCommGroup Z] {z : Z} (hz : n = 0 → z = 0) :
    koszulSign i • z = z := by
  rcases (InDegreeZero.mem_grading_iff _).mp hn with rfl | rfl
  · rw [koszulSign_zero, one_smul]
  · rw [hz rfl, smul_zero]

variable (B) in
/-- The bi-additive map `(m, y) ↦ φ(m) y` for a fixed `φ`, on `M ⊗_B Y`. -/
def dualCounitAux (Y : Type u) [AddCommGroup Y] [Module B Y] (ψ : P₀) :
    TensorProductOver B M₀ Y →+ Y :=
  lift ((smulAddHom B Y).comp (ev₀AddHom ψ)) fun b m y => by
    change ev₀ ψ (op b • m) • y = ev₀ ψ m • b • y
    rw [ev₀_op_smul_right, mul_smul]

theorem dualCounitAux_tmul {Y : Type u} [AddCommGroup Y] [Module B Y] (ψ : P₀) (m : M₀) (y : Y) :
    dualCounitAux B Y ψ (tmul B m y) = ev₀ ψ m • y := rfl

variable (B) in
/-- `φ ↦ (m ⊗ y ↦ φ(m) y)` as an additive map. -/
def dualCounitBil (Y : Type u) [AddCommGroup Y] [Module B Y] :
    P₀ →+ TensorProductOver B M₀ Y →+ Y where
  toFun := dualCounitAux B Y
  map_zero' := addHom_ext fun m y => by
    rw [dualCounitAux_tmul, ev₀_zero_left, zero_smul]
    rfl
  map_add' ψ ψ' := addHom_ext fun m y => by
    rw [AddMonoidHom.add_apply, dualCounitAux_tmul, dualCounitAux_tmul, dualCounitAux_tmul,
      ev₀_add_left, add_smul]

theorem dualCounitBil_balanced {Y : Type u} [AddCommGroup Y] [Module B Y] (a : A) (ψ : P₀)
    (t : TensorProductOver B M₀ Y) :
    dualCounitBil (M := M) B Y (op a • ψ) t = dualCounitBil (M := M) B Y ψ (a • t) := by
  induction t using TensorProductOver.induction_on with
  | zero => rw [map_zero, smul_zero, map_zero]
  | tmul m y =>
    change dualCounitAux B Y _ (tmul B m y) = dualCounitAux B Y ψ (tmul B (a • m) y)
    rw [dualCounitAux_tmul, dualCounitAux_tmul, ev₀_op_smul_left]
  | add t t' ht ht' => rw [map_add, ht, ht', smul_add, map_add]

section DG

variable {Y : Type u} [AddCommGroup Y] [DGAddCommGroup Y] [Module B Y] [DGModule B Y]

theorem dualCounitAux_mem (ψ : P₀) {k : ℤ} {t : TensorProductOver B M₀ Y}
    (ht : t ∈ grading k) : dualCounitAux B Y ψ t ∈ grading k :=
  lift_mem _ _ (fun {i j m y} hm hy => by
    change ev₀ ψ m • y ∈ grading (i + j)
    rcases (InDegreeZero.mem_grading_iff _).mp hm with rfl | rfl
    · simpa using smul_mem_grading (InDegreeZero.ring_mem_grading_zero (ev₀ ψ m)) hy
    · rw [ev₀_zero_right, zero_smul]
      exact zero_mem _) ht

theorem dualCounitAux_d (ψ : P₀) (t : TensorProductOver B M₀ Y) :
    dualCounitAux B Y ψ (d t) = d (dualCounitAux B Y ψ t) :=
  lift_d _ _ (fun {i m} hm y => by
    change d (ev₀ ψ m • y) = ev₀ ψ (d m) • y + koszulSign i • ev₀ ψ m • d y
    rw [InDegreeZero.d_apply, ev₀_zero_right, zero_smul, zero_add,
      koszulSign_smul_of_mem hm (fun h => by rw [h, ev₀_zero_right, zero_smul])]
    exact (InDegreeZero.dLinear B Y).map_smul _ y) t

variable (A M Y) in
/-- The counit `φ ⊗ (m ⊗ y) ↦ φ(m) y` of `M^∨ ⊗_A - ⊣ M ⊗_B -`. -/
def dualCounitHom : TensorProductOver A P₀ (TensorProductOver B M₀ Y) →ᵈᵍ[B] Y where
  toFun := lift (dualCounitBil (M := M) B Y) dualCounitBil_balanced
  map_add' := map_add _
  map_smul' b z := by
    induction z using TensorProductOver.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | tmul ψ t =>
      induction t using TensorProductOver.induction_on with
      | zero => rw [tmul_zero, smul_zero, map_zero, smul_zero]
      | tmul m y =>
        change dualCounitAux B Y (b • ψ) (tmul B m y) = b • dualCounitAux B Y ψ (tmul B m y)
        rw [dualCounitAux_tmul, dualCounitAux_tmul, ev₀_smul_left, mul_smul]
      | add t t' ht ht' =>
        rw [tmul_add, smul_add, map_add, map_add, ht, ht', smul_add]
    | add z z' hz hz' => rw [smul_add, map_add, map_add, hz, hz', smul_add]
  map_mem' hz := lift_mem _ _ (fun {i j ψ t} hψ ht => by
    change dualCounitAux B Y ψ t ∈ grading (i + j)
    rcases (InDegreeZero.mem_grading_iff _).mp hψ with rfl | rfl
    · simpa using dualCounitAux_mem ψ ht
    · exact (congrArg (· t) (dualCounitBil (M := M) B Y).map_zero).symm ▸ zero_mem _) hz
  map_d' z := lift_d _ _ (fun {i ψ} hψ t => by
    change d (dualCounitAux B Y ψ t) = dualCounitAux B Y (d ψ) t +
      koszulSign i • dualCounitAux B Y ψ (d t)
    have h0 : dualCounitAux B Y (0 : P₀) t = 0 :=
      congrArg (· t) (dualCounitBil (M := M) B Y).map_zero
    rw [InDegreeZero.d_apply, h0, zero_add, dualCounitAux_d,
      koszulSign_smul_of_mem hψ (fun h => by
        rw [h, h0]
        exact map_zero _)]) z

theorem dualCounitHom_tmul (ψ : P₀) (m : M₀) (y : Y) :
    dualCounitHom A M Y (tmul A ψ (tmul B m y)) = ev₀ ψ m • y := rfl

end DG

section Unit

variable [Module.Projective Bᵐᵒᵖ M] [Module.Finite Bᵐᵒᵖ M]

variable (B M) in
/-- The vectors of the chosen dual basis, in degree `0`. -/
abbrev vec₀ (i : Fin (dualRank B M)) : InDegreeZero M := dualBasisVec B M i

variable (B M) in
/-- The coordinates of the chosen dual basis, in degree `0`. -/
abbrev coord₀ (i : Fin (dualRank B M)) : InDegreeZero (RightDualModule B M) :=
  dualBasisCoord B M i

/-- `Σ_i a e_i ⊗ φ_i = Σ_i e_i ⊗ φ_i a`, tensored with `x`: the canonical element of
`M ⊗_B M^∨` commutes with `A`. -/
theorem sum_smul_tmul_tmul {X : Type u} [AddCommGroup X] [Module A X] (a : A) (x : X) :
    ∑ i, tmul B (a • vec₀ B M i) (tmul A (coord₀ B M i) x) =
      ∑ i, tmul B (vec₀ B M i) (tmul A (coord₀ B M i) (a • x)) := by
  have hl (i : Fin (dualRank B M)) : tmul B (a • vec₀ B M i) (tmul A (coord₀ B M i) x) =
      ∑ j, tmul B (vec₀ B M j)
        (tmul A (unop (dualBasisCoord B M j (a • dualBasisVec B M i)) • coord₀ B M i) x) := by
    have h1 : (a • vec₀ B M i : M₀) =
        ∑ j, dualBasisCoord B M j (a • dualBasisVec B M i) • vec₀ B M j :=
      (sum_dualBasis B M _).symm
    rw [h1, finset_sum_tmul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [tmul_op_smul_left, smul_tmul]
  have hr (i : Fin (dualRank B M)) : tmul B (vec₀ B M i) (tmul A (coord₀ B M i) (a • x)) =
      ∑ j, tmul B (vec₀ B M i)
        (tmul A (unop (dualBasisCoord B M i (a • dualBasisVec B M j)) • coord₀ B M j) x) := by
    have h2 : (op a • coord₀ B M i : P₀) =
        ∑ j, unop (dualBasisCoord B M i (a • dualBasisVec B M j)) • coord₀ B M j :=
      (sum_dualBasis_dual B M _).symm
    rw [← op_smul_tmul, h2, finset_sum_tmul, tmul_finset_sum]
  rw [Finset.sum_congr rfl fun i _ => hl i, Finset.sum_congr rfl fun i _ => hr i,
    Finset.sum_comm]

variable (A M) in
/-- The unit `x ↦ Σ_i e_i ⊗ (φ_i ⊗ x)` of `M^∨ ⊗_A - ⊣ M ⊗_B -`. -/
def dualUnitHom (X : Type u) [AddCommGroup X] [DGAddCommGroup X] [Module A X] [DGModule A X] :
    X →ᵈᵍ[A] TensorProductOver B M₀ (TensorProductOver A P₀ X) where
  toFun x := ∑ i, tmul B (vec₀ B M i) (tmul A (coord₀ B M i) x)
  map_add' x y := by simp only [tmul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    rw [RingHom.id_apply, Finset.smul_sum]
    simp only [smul_tmul]
    exact (sum_smul_tmul_tmul a x).symm
  map_mem' hx := AddSubgroup.sum_mem _ fun i _ =>
    tmul_mem_inDegreeZero _ (tmul_mem_inDegreeZero _ hx)
  map_d' x := by simp only [map_sum, d_tmul_inDegreeZero]

theorem dualUnitHom_apply {X : Type u} [AddCommGroup X] [DGAddCommGroup X] [Module A X]
    [DGModule A X] (x : X) :
    dualUnitHom A M X x = ∑ i, tmul B (vec₀ B M i) (tmul A (coord₀ B M i) x) := rfl

theorem ev₀_coord₀ (i : Fin (dualRank B M)) (m : M₀) :
    op (ev₀ (coord₀ B M i) m) = dualBasisCoord B M i m := rfl

theorem sum_ev₀_smul_coord₀ (ψ : P₀) : ∑ i, ev₀ ψ (vec₀ B M i) • coord₀ B M i = ψ :=
  sum_dualBasis_dual B M ψ

theorem sum_op_ev₀_smul_vec₀ (m : M₀) : ∑ i, op (ev₀ (coord₀ B M i) m) • vec₀ B M i = m :=
  sum_dualBasis B M m

variable (A M) in
open DGModuleCat in
/-- **`M^∨ ⊗_A - ⊣ M ⊗_B -`** on dg modules, for an `(A, B)`-bimodule `M` which is finitely
generated and projective as a right `B`-module, with `M^∨ = Hom_{Bᵐᵒᵖ}(M, B)`; both are in
degree `0`. The unit is `x ↦ Σ_i e_i ⊗ (φ_i ⊗ x)` for the chosen dual basis, the counit
`φ ⊗ (m ⊗ y) ↦ φ(m) y`. -/
def dualTensorAdjunction :
    tensorFunctor (B := A) B P₀ ⊣ tensorFunctor (B := B) A M₀ where
  unit :=
    { app X := ofHom (dualUnitHom A M X)
      naturality {X X'} f := hom_ext_apply fun x => by
        change dualUnitHom A M X' (f x) = DGModuleHom.lTensor A M₀
          (DGModuleHom.lTensor B P₀ f.hom) (dualUnitHom A M X x)
        rw [dualUnitHom_apply, dualUnitHom_apply, map_sum]
        rfl }
  counit :=
    { app Y := ofHom (dualCounitHom A M Y)
      naturality {Y Y'} g := tensor_hom_ext fun ψ t => by
        change dualCounitHom A M Y' (tmul A ψ (DGModuleHom.lTensor A M₀ g.hom t)) =
          g.hom (dualCounitHom A M Y (tmul A ψ t))
        induction t using TensorProductOver.induction_on with
        | zero => rw [map_zero, tmul_zero, map_zero, tmul_zero, map_zero, map_zero]
        | tmul m y =>
          rw [DGModuleHom.lTensor_tmul, dualCounitHom_tmul, dualCounitHom_tmul, map_smul]
        | add t t' ht ht' => rw [map_add, tmul_add, map_add, ht, ht', tmul_add, map_add,
            map_add] }
  left_triangle_components X := tensor_hom_ext fun ψ x => by
    change dualCounitHom A M _ (tmul A ψ (dualUnitHom A M X x)) = tmul A ψ x
    rw [dualUnitHom_apply, tmul_finset_sum, map_sum]
    simp only [dualCounitHom_tmul, smul_tmul]
    rw [← finset_sum_tmul, sum_ev₀_smul_coord₀]
  right_triangle_components Y := tensor_hom_ext fun m y => by
    change DGModuleHom.lTensor A M₀ (dualCounitHom A M Y)
      (dualUnitHom A M _ (tmul B m y)) = tmul B m y
    rw [dualUnitHom_apply, map_sum]
    change ∑ i, tmul B (vec₀ B M i) (dualCounitHom A M Y (tmul A (coord₀ B M i) (tmul B m y))) =
      _
    simp only [dualCounitHom_tmul, ← op_smul_tmul]
    rw [← finset_sum_tmul, sum_op_ev₀_smul_vec₀]

theorem dualTensorAdjunction_unit_app_apply (X : DGModuleCat.{u} A) (x : X) :
    (dualTensorAdjunction A M).unit.app X x = ∑ i, tmul B (vec₀ B M i) (tmul A (coord₀ B M i) x) :=
  rfl

theorem dualTensorAdjunction_counit_app_tmul (Y : DGModuleCat.{u} B) (ψ : P₀) (m : M₀) (y : Y) :
    (dualTensorAdjunction A M).counit.app Y (tmul A ψ (tmul B m y)) = ev₀ ψ m • y :=
  rfl

end Unit

end RightDualModule

end Categorification
