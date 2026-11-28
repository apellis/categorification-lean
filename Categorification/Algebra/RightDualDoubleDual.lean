/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.RightDualModule
import DG.Module.TensorProductOver

/-!
# Homomorphisms out of a dual are tensor products

Let `P` be a finitely generated projective right `D`-module and `W` a left `D`-module. Then
`p ⊗ w ↦ (φ ↦ φ(p) w)` identifies `P ⊗_D W` with `Hom_D(P^∨, W)`, the left `D`-linear maps
out of the dual `P^∨ = Hom_{Dᵐᵒᵖ}(P, D)` (`tensorHomDualEquiv`). If `P` also carries a
commuting left `C`-action, the identification takes `c t` to `φ ↦ f(φ c)`
(`tensorHomDualEquiv_smul`).

This is the double-duality step that turns the dual layers `Hom_D(e_L C̃, W)`, with
`e_L C̃ ≅ (C̃ e_R)^∨`, into the induced modules `C̃ e_R ⊗_D W` in B. Webster, *Knot invariants
and higher representation theory*, arXiv:1309.3796v3, proof of Lemma 7.19.
-/

open MulOpposite DG

namespace Categorification.RightDualModule

variable {D : Type*} [Ring D] {P : Type*} [AddCommGroup P] [Module Dᵐᵒᵖ P]
  {W : Type*} [AddCommGroup W] [Module D W]

/-- The evaluation `φ ↦ φ(p) w` as a left linear map out of the dual. -/
def evalTensor (p : P) (w : W) : RightDualModule D P →ₗ[D] W where
  toFun φ := unop (φ p) • w
  map_add' φ ψ := by rw [add_apply, unop_add, add_smul]
  map_smul' d φ := by
    rw [smul_apply, unop_mul, unop_op, mul_smul]
    rfl

@[simp]
theorem evalTensor_apply (p : P) (w : W) (φ : RightDualModule D P) :
    evalTensor p w φ = unop (φ p) • w := rfl

variable (D P W) in
/-- The comparison map `P ⊗_D W → Hom_D(P^∨, W)`, `p ⊗ w ↦ (φ ↦ φ(p) w)`. -/
def tensorHomDual : TensorProductOver D P W →+ (RightDualModule D P →ₗ[D] W) :=
  TensorProductOver.lift
    { toFun := fun p =>
        { toFun := fun w => evalTensor p w
          map_zero' := LinearMap.ext fun φ => smul_zero _
          map_add' := fun w w' => LinearMap.ext fun φ => smul_add _ _ _ }
      map_zero' := by
        ext w φ
        simp
      map_add' := fun p p' => by
        ext w φ
        simp [map_add, unop_add, add_smul] }
    (fun d p w => LinearMap.ext fun φ => by
      change unop (φ (op d • p)) • w = unop (φ p) • d • w
      rw [map_smul, smul_eq_mul, unop_mul, unop_op, mul_smul])

@[simp]
theorem tensorHomDual_tmul (p : P) (w : W) (φ : RightDualModule D P) :
    tensorHomDual D P W (TensorProductOver.tmul D p w) φ = unop (φ p) • w := rfl

variable [Module.Projective Dᵐᵒᵖ P] [Module.Finite Dᵐᵒᵖ P]

variable (D P W) in
/-- The inverse `f ↦ Σ_i e_i ⊗ f(φ_i)`, for the chosen dual basis `(e_i, φ_i)`. -/
noncomputable def tensorHomDualInv : (RightDualModule D P →ₗ[D] W) →+ TensorProductOver D P W where
  toFun f := ∑ i, TensorProductOver.tmul D (dualBasisVec D P i) (f (dualBasisCoord D P i))
  map_zero' := by simp [TensorProductOver.tmul_zero]
  map_add' f f' := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => TensorProductOver.tmul_add _ _ _

theorem tensorHomDual_inv (f : RightDualModule D P →ₗ[D] W) :
    tensorHomDual D P W (tensorHomDualInv D P W f) = f := by
  ext φ
  change tensorHomDual D P W (∑ i, TensorProductOver.tmul D (dualBasisVec D P i)
    (f (dualBasisCoord D P i))) φ = f φ
  rw [map_sum, LinearMap.sum_apply]
  conv_rhs => rw [← sum_dualBasis_dual D P φ, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [tensorHomDual_tmul, map_smul]

theorem tensorHomDualInv_tmul (p : P) (w : W) :
    tensorHomDualInv D P W (tensorHomDual D P W (TensorProductOver.tmul D p w)) =
      TensorProductOver.tmul D p w := by
  change ∑ i, TensorProductOver.tmul D (dualBasisVec D P i)
    (unop (dualBasisCoord D P i p) • w) = _
  conv_rhs => rw [← sum_dualBasis D P p]
  change _ = (TensorProductOver.tmulAddHom D P W).flip w (∑ i, _)
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [AddMonoidHom.flip_apply, TensorProductOver.tmulAddHom_apply, ← TensorProductOver.op_smul_tmul,
    op_unop]

variable (D P W) in
/-- **Double duality**: `P ⊗_D W ≅ Hom_D(P^∨, W)` for a finitely generated projective right
module `P`. -/
noncomputable def tensorHomDualEquiv :
    TensorProductOver D P W ≃+ (RightDualModule D P →ₗ[D] W) where
  toFun := tensorHomDual D P W
  invFun := tensorHomDualInv D P W
  left_inv t := by
    induction t using TensorProductOver.induction_on with
    | zero => simp
    | tmul p w => exact tensorHomDualInv_tmul p w
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  right_inv f := tensorHomDual_inv f
  map_add' := map_add _

@[simp]
theorem tensorHomDualEquiv_tmul (p : P) (w : W) (φ : RightDualModule D P) :
    tensorHomDualEquiv D P W (TensorProductOver.tmul D p w) φ = unop (φ p) • w := rfl

/-- The double-duality identification intertwines the left `C`-action on `P ⊗_D W` with the
action `(c f)(φ) = f(φ c)` on `Hom_D(P^∨, W)`. -/
theorem tensorHomDualEquiv_smul {C : Type*} [Ring C] [Module C P] [SMulCommClass C Dᵐᵒᵖ P]
    (c : C) (t : TensorProductOver D P W) (φ : RightDualModule D P) :
    tensorHomDualEquiv D P W (c • t) φ = tensorHomDualEquiv D P W t (op c • φ) := by
  induction t using TensorProductOver.induction_on with
  | zero => simp
  | tmul p w => rfl
  | add x y hx hy =>
    rw [smul_add, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hx, hy]

end Categorification.RightDualModule
