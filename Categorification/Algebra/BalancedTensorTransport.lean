/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.Tensor

/-!
# Transport of balanced tensor products

For Webster, arXiv:1309.3796v2, Theorems 4.20 and 4.38: an isomorphism of
the balancing rings and compatible linear isomorphisms of the two factors
identify their balanced tensor products. If the left coefficient action is
also transported, the resulting map is semilinear for that action.
-/
noncomputable section
namespace Categorification.BalancedTensor
open MulOpposite
section Change
variable {k : Type*} [CommRing k]
  {A A' B B' : Type*} [Ring A] [Ring A'] [Ring B] [Ring B'] [Algebra k B] [Algebra k B']
  {M M' N N' : Type*}
  [AddCommGroup M] [Module k M] [Module B M] [IsScalarTower k B M] [Module Aᵐᵒᵖ M]
  [AddCommGroup M'] [Module k M'] [Module B' M'] [IsScalarTower k B' M'] [Module A'ᵐᵒᵖ M']
  [AddCommGroup N] [Module k N] [Module A N] [AddCommGroup N'] [Module k N'] [Module A' N']
  [SMulCommClass B Aᵐᵒᵖ M] [SMulCommClass B' A'ᵐᵒᵖ M']
  (σ : A ≃+* A') (f : M ≃ₗ[k] M') (g : N ≃ₗ[k] N')
  (hf : ∀ (a : A) (m : M), f (op a • m) = op (σ a) • f m)
  (hg : ∀ (a : A) (n : N), g (a • n) = σ a • g n)
omit [SMulCommClass B' A'ᵐᵒᵖ M'] in
private def changeRingMap :
    BalancedTensor k B A M N →ₗ[k] BalancedTensor k B' A' M' N' :=
  lift ((mkBil k B' A' M' N').compl₁₂ f.toLinearMap g.toLinearMap) (fun m a n => by
    change tmul (f (op a • m)) (g n) = tmul (f m) (g (a • n))
    rw [hf, hg, op_smul_tmul])

/-- Transport both factors and the ring acting between them. -/
def changeRingEquiv : BalancedTensor k B A M N ≃ₗ[k] BalancedTensor k B' A' M' N' := by
  let F := changeRingMap (B := B) (B' := B') σ f g hf hg
  let H := changeRingMap (B := B') (B' := B) σ.symm f.symm g.symm
    (fun a m => f.injective (by rw [f.apply_symm_apply, hf, f.apply_symm_apply, σ.apply_symm_apply]))
    (fun a n => g.injective (by rw [g.apply_symm_apply, hg, g.apply_symm_apply, σ.apply_symm_apply]))
  apply LinearEquiv.ofLinearMap F H
  · apply BalancedTensor.ext
    intro m n
    change tmul (f (f.symm m)) (g (g.symm n)) = tmul m n
    rw [f.apply_symm_apply, g.apply_symm_apply]
  · apply BalancedTensor.ext
    intro m n
    change tmul (f.symm (f m)) (g.symm (g n)) = tmul m n
    rw [f.symm_apply_apply, g.symm_apply_apply]

@[simp] theorem changeRingEquiv_tmul (m n) :
    changeRingEquiv (B := B) (B' := B') σ f g hf hg (tmul m n) = tmul (f m) (g n) := rfl

@[simp] theorem changeRingEquiv_symm_tmul (m n) :
    (changeRingEquiv (B := B) (B' := B') σ f g hf hg).symm (tmul m n) = tmul (f.symm m) (g.symm n) := rfl

/-- Left scalar multiplication transports along the upper ring isomorphism. -/
theorem changeRingEquiv_smul (τ : B ≃+* B') (h : ∀ (b : B) (m : M), f (b • m) = τ b • f m)
    (b : B) (x : BalancedTensor k B A M N) :
    changeRingEquiv (B := B) (B' := B') σ f g hf hg (b • x) = τ b • changeRingEquiv σ f g hf hg x := by
  induction x using induction_on with
  | zero => simp
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | tmul m n => rw [smul_tmul', changeRingEquiv_tmul, changeRingEquiv_tmul, h, smul_tmul']
open Categorification.Graded

/-- A change of the balancing ring preserves degree when both factor maps preserve degree. -/
theorem changeRingEquiv_mem {ℳ : ℤ → Submodule k M} {𝒩 : ℤ → Submodule k N}
    {ℳ' : ℤ → Submodule k M'} {𝒩' : ℤ → Submodule k N'}
    (hm : ∀ ⦃q m⦄, m ∈ ℳ q → f m ∈ ℳ' q)
    (hn : ∀ ⦃q n⦄, n ∈ 𝒩 q → g n ∈ 𝒩' q)
    {q x} (hx : x ∈ balancedGrading B A ℳ 𝒩 q) :
    changeRingEquiv (B := B) (B' := B') σ f g hf hg x ∈ balancedGrading B' A' ℳ' 𝒩' q :=
  balancedGrading_map_mem _ (changeRingEquiv (B := B) (B' := B') σ f g hf hg).toLinearMap
    (fun _ _ _ _ hu hv => tmul_mem_balancedGrading (hm hu) (hn hv)) hx

/-- The inverse transport preserves degree when the inverse maps on both factors do. -/
theorem changeRingEquiv_symm_mem {ℳ : ℤ → Submodule k M} {𝒩 : ℤ → Submodule k N}
    {ℳ' : ℤ → Submodule k M'} {𝒩' : ℤ → Submodule k N'}
    (hm : ∀ ⦃q m⦄, m ∈ ℳ' q → f.symm m ∈ ℳ q)
    (hn : ∀ ⦃q n⦄, n ∈ 𝒩' q → g.symm n ∈ 𝒩 q)
    {q x} (hx : x ∈ balancedGrading B' A' ℳ' 𝒩' q) :
    (changeRingEquiv (B := B) (B' := B') σ f g hf hg).symm x ∈ balancedGrading B A ℳ 𝒩 q :=
  balancedGrading_map_mem _ (changeRingEquiv (B := B) (B' := B') σ f g hf hg).symm.toLinearMap
    (fun _ _ _ _ hu hv => tmul_mem_balancedGrading (hm hu) (hn hv)) hx

end Change
end Categorification.BalancedTensor
