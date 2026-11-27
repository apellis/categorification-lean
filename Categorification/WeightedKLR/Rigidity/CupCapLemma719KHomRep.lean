/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.BalancedTensor

/-!
# Maps out of a balanced tensor product through a Hom module

Webster, arXiv:1309.3796v3, Lemma 7.19 (K), proof: the inverse `Ψ` of the comparison map is a
map out of `K^σ(S(Y)) = coe^σ ⊗_{T^λ} S(Y)`. Such a map is the same as a `T^λ`-linear map from
`S(Y)` to `Hom_{T^{λ⁺}}(coe^σ, X)`, on which `T^λ` acts by precomposition with its right action
on `coe^σ`. This file sets up that action (`precompRep`) and the induced map
(`liftOfHom`), linear over `T^{λ⁺}`.

## Main definitions

* `BalancedTensor.precompRep`: `T` acting on `M →ₗ[R] X` by precomposition.
* `BalancedTensor.liftOfHom`: the map `M ⊗_T N → X` of an additive map `N → (M →ₗ[R] X)`.
-/

noncomputable section

namespace Categorification.BalancedTensor

open MulOpposite

variable {k : Type*} [CommRing k] {R : Type*} [Ring R] [Algebra k R] {T : Type*} [Ring T]
  [Algebra k T]
  {M : Type*} [AddCommGroup M] [Module R M] [Module Tᵐᵒᵖ M] [SMulCommClass R Tᵐᵒᵖ M]
  {X : Type*} [AddCommGroup X] [Module k X] [Module R X] [IsScalarTower k R X]
  [SMulCommClass R k X]

/-- The right action of `t` on `M`, as an `R`-linear map. -/
def rightActHom (t : T) : M →ₗ[R] M where
  toFun m := op t • m
  map_add' := smul_add _
  map_smul' b m := (smul_comm b (op t) m).symm

theorem rightActHom_apply (t : T) (m : M) : rightActHom (R := R) t m = op t • m := rfl

variable (R M X) in
/-- **`T` acting on `Hom_R(M, X)` by precomposition** with its right action on `M`, when the
scalars act in the same way through `R` and through `T`. -/
def precompRep (hM : ∀ (c : k) (m : M), op (algebraMap k T c) • m = algebraMap k R c • m) :
    T →ₐ[k] Module.End k (M →ₗ[R] X) where
  toFun t :=
    { toFun := fun φ => φ.comp (rightActHom t)
      map_add' := fun φ φ' => LinearMap.add_comp _ _ _
      map_smul' := fun c φ => LinearMap.smul_comp _ _ _ }
  map_one' := by
    refine LinearMap.ext fun φ => LinearMap.ext fun m => ?_
    change φ (op (1 : T) • m) = φ m
    rw [op_one, one_smul]
  map_mul' t t' := by
    refine LinearMap.ext fun φ => LinearMap.ext fun m => ?_
    change φ (op (t * t') • m) = φ (op t' • op t • m)
    rw [op_mul, mul_smul]
  map_zero' := by
    refine LinearMap.ext fun φ => LinearMap.ext fun m => ?_
    change φ (op (0 : T) • m) = 0
    rw [op_zero, zero_smul, map_zero]
  map_add' t t' := by
    refine LinearMap.ext fun φ => LinearMap.ext fun m => ?_
    change φ (op (t + t') • m) = φ (op t • m) + φ (op t' • m)
    rw [op_add, add_smul, map_add]
  commutes' c := by
    refine LinearMap.ext fun φ => LinearMap.ext fun m => ?_
    change φ (op (algebraMap k T c) • m) = c • φ m
    rw [hM, map_smul, algebraMap_smul]

theorem precompRep_apply (hM : ∀ (c : k) (m : M), op (algebraMap k T c) • m = algebraMap k R c • m)
    (t : T) (φ : M →ₗ[R] X) (m : M) : precompRep R M X hM t φ m = φ (op t • m) := rfl

variable {N : Type*} [AddCommGroup N] [Module T N]

/-- **The map `M ⊗_T N → X` of an additive map `g : N → Hom_R(M, X)`** intertwining the action
of `T` on `N` with its action by precomposition; it is linear over `R`. -/
def liftOfHom (g : N →+ (M →ₗ[R] X))
    (hg : ∀ (t : T) (n : N) (m : M), g (t • n) m = g n (op t • m)) :
    BalancedTensor ℤ R T M N →ₗ[R] X :=
  liftB (LinearMap.mk₂ ℤ (fun m n => g n m)
      (fun m m' n => map_add _ _ _) (fun c m n => map_zsmul (g n) c m)
      (fun m n n' => by rw [map_add, LinearMap.add_apply])
      (fun c m n => by rw [map_zsmul, LinearMap.smul_apply]))
    (fun m t n => (hg t n m).symm)
    (fun b m n => (g n).map_smul b m)

@[simp] theorem liftOfHom_tmul (g : N →+ (M →ₗ[R] X))
    (hg : ∀ (t : T) (n : N) (m : M), g (t • n) m = g n (op t • m)) (m : M) (n : N) :
    liftOfHom g hg (tmul m n : BalancedTensor ℤ R T M N) = g n m := rfl

end Categorification.BalancedTensor
