/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.BalancedTensor

/-!
# Balanced tensor products with a line on which the algebra acts by scalars

If `L` is free of rank one over `k` and every element of `A` acts on `L` and on `N` by one and
the same scalar, then `L ⊗_A N ≅ N` (`BalancedTensor.scalarEquiv`). This is the case of no red
strands in the standardization of Definition 5.4 of Webster, arXiv:1309.3796v3.
-/

namespace Categorification

open scoped TensorProduct
open MulOpposite

noncomputable section

variable {k : Type*} [CommRing k] {B : Type*} [Ring B] [Algebra k B] {A : Type*} [Ring A]
  {L : Type*} [AddCommGroup L] [Module k L] [Module B L] [IsScalarTower k B L] [Module Aᵐᵒᵖ L]
  [SMulCommClass B Aᵐᵒᵖ L] {N : Type*} [AddCommGroup N] [Module k N] [Module A N]

namespace BalancedTensor

/-- **`L ⊗_A N ≅ N`** for a line `L ≅ k` on which `A` acts, as on `N`, by scalars. -/
def scalarEquiv (φ : L ≃ₗ[k] k)
    (hA : ∀ a : A, ∃ c : k, (∀ l : L, op a • l = c • l) ∧ ∀ n : N, a • n = c • n) :
    BalancedTensor k B A L N ≃ₗ[k] N :=
  LinearEquiv.ofLinearMap
    (lift ((LinearMap.lsmul k N).comp φ.toLinearMap) fun l a n => by
      obtain ⟨c, hl, hn⟩ := hA a
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.lsmul_apply, hl, hn,
        map_smul, LinearMap.smul_apply])
    ((mkBil k B A L N (φ.symm 1)))
    (LinearMap.ext fun n => by
      simp [LinearMap.comp_apply])
    (ext fun l n => by
      simp only [LinearMap.comp_apply, lift_tmul, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearMap.lsmul_apply, mkBil_apply, LinearMap.id_apply]
      rw [tmul_smul, ← smul_tmul, ← map_smul, smul_eq_mul, mul_one,
        LinearEquiv.symm_apply_apply])

theorem scalarEquiv_tmul (φ : L ≃ₗ[k] k)
    (hA : ∀ a : A, ∃ c : k, (∀ l : L, op a • l = c • l) ∧ ∀ n : N, a • n = c • n)
    (l : L) (n : N) :
    scalarEquiv (B := B) φ hA (tmul l n) = φ l • n := rfl

theorem scalarEquiv_symm_apply (φ : L ≃ₗ[k] k)
    (hA : ∀ a : A, ∃ c : k, (∀ l : L, op a • l = c • l) ∧ ∀ n : N, a • n = c • n) (n : N) :
    (scalarEquiv (B := B) φ hA).symm n = tmul (φ.symm 1) n := rfl

end BalancedTensor

end

end Categorification
