/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.BalancedTensor

/-!
# Right exactness of the balanced tensor product

`M ⊗_A -` is right exact: an exact sequence `N → N' → N'' → 0` of `A`-modules gives an exact
sequence `M ⊗_A N → M ⊗_A N' → M ⊗_A N'' → 0`. Used for the braiding functor of Webster,
arXiv:1309.3796v2, §6.1, Definition 6.6, on short exact sequences (proof of Corollary 6.10).

## Main results

* `Categorification.BalancedTensor.mapRight_exact`
-/

noncomputable section

namespace Categorification.BalancedTensor

open MulOpposite

variable {k : Type*} [CommRing k] {B : Type*} [Ring B] [Algebra k B] {A : Type*} [Ring A]
  [Algebra k A]
  {M : Type*} [AddCommGroup M] [Module k M] [Module B M] [IsScalarTower k B M] [Module Aᵐᵒᵖ M]
  [SMulCommClass B Aᵐᵒᵖ M]
  {N N' N'' : Type*} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
  [AddCommGroup N'] [Module k N'] [Module A N'] [IsScalarTower k A N']
  [AddCommGroup N''] [Module k N''] [Module A N''] [IsScalarTower k A N'']

/-- **Right exactness of `M ⊗_A -`**: for an exact sequence `N → N' → N'' → 0`, the sequence
`M ⊗_A N → M ⊗_A N' → M ⊗_A N''` is exact. -/
theorem mapRight_exact (f : N →ₗ[A] N') (g : N' →ₗ[A] N'') (hfg : Function.Exact f g)
    (hg : Function.Surjective g) :
    Function.Exact (mapRight (k := k) (B := B) (M := M) f) (mapRight (k := k) (B := B) g) := by
  let K : Submodule k (BalancedTensor k B A M N') :=
    (LinearMap.range (mapRight (k := k) (B := B) (M := M) f)).restrictScalars k
  let Φ : M →ₗ[k] N' →ₗ[k] (BalancedTensor k B A M N' ⧸ K) :=
    (mkBil k B A M N').compr₂ K.mkQ
  let gk : N' →ₗ[k] N'' := g.restrictScalars k
  have hker (m : M) : LinearMap.ker gk ≤ LinearMap.ker (Φ m) := by
    intro n hn
    obtain ⟨n₀, rfl⟩ := (hfg n).1 hn
    change K.mkQ (tmul m (f n₀)) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨tmul m n₀, rfl⟩
  let e : (N' ⧸ LinearMap.ker gk) ≃ₗ[k] N'' := gk.quotKerEquivOfSurjective hg
  let ψ (m : M) : N'' →ₗ[k] (BalancedTensor k B A M N' ⧸ K) :=
    ((LinearMap.ker gk).liftQ (Φ m) (hker m)).comp e.symm.toLinearMap
  have hψ (m : M) (n : N') : ψ m (g n) = Φ m n := by
    have : e.symm (g n) = Submodule.Quotient.mk n := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    change (LinearMap.ker gk).liftQ (Φ m) (hker m) (e.symm (g n)) = _
    rw [this, Submodule.liftQ_apply]
  let Ψ : M →ₗ[k] N'' →ₗ[k] (BalancedTensor k B A M N' ⧸ K) :=
    { toFun := ψ
      map_add' := fun m m' => by
        ext n''
        obtain ⟨n, rfl⟩ := hg n''
        rw [LinearMap.add_apply, hψ, hψ, hψ, map_add, LinearMap.add_apply]
      map_smul' := fun c m => by
        ext n''
        obtain ⟨n, rfl⟩ := hg n''
        rw [LinearMap.smul_apply, hψ, hψ, map_smul, LinearMap.smul_apply, RingHom.id_apply] }
  have hbal : ∀ (m : M) (a : A) (n : N''), Ψ (op a • m) n = Ψ m (a • n) := by
    intro m a n''
    obtain ⟨n, rfl⟩ := hg n''
    change ψ (op a • m) (g n) = ψ m (a • g n)
    rw [← g.map_smul, hψ, hψ]
    change K.mkQ (tmul (op a • m) n) = K.mkQ (tmul m (a • n))
    rw [op_smul_tmul]
  let φ := lift (B := B) Ψ hbal
  have hφ (x : BalancedTensor k B A M N') : φ (mapRight (k := k) (B := B) g x) = K.mkQ x := by
    induction x using induction_on with
    | zero => simp
    | tmul m n =>
      rw [mapRight_tmul]
      exact hψ m n
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
  intro x
  constructor
  · intro hx
    have : K.mkQ x = 0 := by rw [← hφ, hx, map_zero]
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
    exact this
  · rintro ⟨y, rfl⟩
    rw [← LinearMap.comp_apply, ← mapRight_comp, hfg.linearMap_comp_eq_zero]
    induction y using induction_on with
    | zero => simp
    | tmul m n => simp
    | add x y hx hy => rw [map_add, hx, hy, add_zero]

end Categorification.BalancedTensor
