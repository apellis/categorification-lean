/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongBimodule

/-!
# Restriction as a tensor product with a bimodule

For a nonunital ring map `ψ : A' →ₙ+* A` with idempotent `e' = ψ 1`, restriction
`N ↦ e' N` is tensoring with the `(A', A)`-bimodule `e' A`, realized as `Res ψ A`:
`Res_ψ N ≅ Res_ψ A ⊗_A N`, `r ⊗ n ↦ r n` (`resTensor`). With `resIndTensor` and
`indResTensor` this expresses Webster's functors `Eᵢ`, `Fᵢ` and their composites on modules over
the tensor product algebras as tensor products with bimodules (arXiv:1309.3796v3, §4.6 and the
proof of Proposition 5.5).
-/

namespace Categorification

open MulOpposite

noncomputable section

namespace InductionAlong

universe u

variable {A' : Type u} [Ring A'] {A : Type u} [Ring A] (ψ : A' →ₙ+* A)
  (N : Type u) [AddCommGroup N] [Module A N]

theorem resActOn_op_smul (a : A) (n : N) (r : Res ψ A) :
    resActOn ψ N n (op a • r) = resActOn ψ N (a • n) r := by
  apply Res.ext
  change (r.val * a) • n = r.val • a • n
  rw [mul_smul]

/-- The `ℤ`-bilinear map `(r, n) ↦ r n`. -/
def resBil : Res ψ A →ₗ[ℤ] N →ₗ[ℤ] Res ψ N :=
  LinearMap.mk₂ ℤ (fun r n => resActOn ψ N n r)
    (fun r r' n => map_add (resActOn ψ N n) r r')
    (fun c r n => by
      apply Res.ext
      rw [res_val_zsmul, resActOn_val, resActOn_val, res_val_zsmul, smul_assoc])
    (fun r n n' => Res.ext (smul_add r.val n n'))
    (fun c r n => by
      apply Res.ext
      rw [res_val_zsmul, resActOn_val, resActOn_val]
      exact smul_comm r.val c n)

/-- The backward map `Res_ψ A ⊗_A N → Res_ψ N`, `r ⊗ n ↦ r n`. -/
def resBwd : BalancedTensor ℤ A' A (Res ψ A) N →ₗ[A'] Res ψ N :=
  BalancedTensor.liftB (resBil ψ N)
    (fun r a n => resActOn_op_smul ψ N a n r)
    (fun a r n => map_smul (resActOn ψ N n) a r)

theorem resBwd_tmul (r : Res ψ A) (n : N) :
    resBwd ψ N (BalancedTensor.tmul r n) = resActOn ψ N n r :=
  rfl

/-- **Restriction is tensoring with `e' A`**: `Res_ψ N ≅ Res_ψ A ⊗_A N`. -/
def resTensor : Res ψ N ≃ₗ[A'] BalancedTensor ℤ A' A (Res ψ A) N :=
  LinearEquiv.symm
    { resBwd ψ N with
      invFun := fun m => BalancedTensor.tmul (resUnit ψ) m.val
      left_inv := fun t => by
        induction t using BalancedTensor.induction_on with
        | zero =>
          change BalancedTensor.tmul (resUnit ψ) (resBwd ψ N 0).val = 0
          rw [map_zero, Res.val_zero, BalancedTensor.tmul_zero]
        | tmul r n =>
          change BalancedTensor.tmul (resUnit ψ) (r.val • n) = BalancedTensor.tmul r n
          rw [← BalancedTensor.op_smul_tmul, op_smul_resUnit]
        | add s t hs ht =>
          change BalancedTensor.tmul (resUnit ψ) (resBwd ψ N (s + t)).val = s + t
          rw [map_add, Res.val_add, BalancedTensor.tmul_add]
          exact congrArg₂ (· + ·) hs ht
      right_inv := fun m => Res.ext (m.prop) }

theorem resTensor_apply (m : Res ψ N) :
    resTensor ψ N m = BalancedTensor.tmul (resUnit ψ) m.val :=
  rfl

theorem resTensor_symm_tmul (r : Res ψ A) (n : N) :
    (resTensor ψ N).symm (BalancedTensor.tmul r n) = resActOn ψ N n r :=
  rfl

end InductionAlong

end

end Categorification
