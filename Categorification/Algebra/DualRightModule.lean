/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Algebra.Algebra.Opposite

/-!
# Duals of simple right modules

For a `k`-algebra `T` and a right `T`-module `M` (a module over `Tᵐᵒᵖ`) which is a
finite-dimensional `k`-vector space, the `k`-dual `M* = Hom_k(M, k)` is a left `T`-module,
`(t φ)(m) = φ(m t)` (`DualRightModule.dualModule`), simple when `M` is simple
(`DualRightModule.isSimpleModule_dual`). Transposition embeds the endomorphisms of `M` into those
of `M*`, so if every endomorphism of the simple left module `M*` is a scalar, so is every
endomorphism of `M` (`DualRightModule.exists_scalar_of_dual`).

This passes the condition `End(S) = k` on simple modules (Chuang–Rouquier, arXiv:math/0407205v2,
§5.2.1) from left to right modules over Webster's tensor product algebras
(arXiv:1309.3796v2, §5).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.DualRightModule

open MulOpposite

universe u v w

variable (k : Type u) (T : Type w) (M : Type v) [Field k] [Ring T] [Algebra k T]
  [AddCommGroup M] [Module k M] [Module Tᵐᵒᵖ M] [IsScalarTower k Tᵐᵒᵖ M]

/-- Right multiplication by `t` as a `k`-linear endomorphism of a right `T`-module. -/
def opSmulLinear (t : T) : M →ₗ[k] M where
  toFun m := op t • m
  map_add' := smul_add _
  map_smul' c m := smul_algebra_smul_comm c (op t) m

/-- The action of `T` on the `k`-dual of a right `T`-module. -/
def dualRingHom : T →+* Module.End k (Module.Dual k M) where
  toFun t := (opSmulLinear k T M t).dualMap
  map_one' := LinearMap.ext fun φ => LinearMap.ext fun m => by
    simp [opSmulLinear, LinearMap.dualMap_apply]
  map_mul' t₁ t₂ := LinearMap.ext fun φ => LinearMap.ext fun m => by
    simp [opSmulLinear, LinearMap.dualMap_apply, mul_smul]
  map_zero' := LinearMap.ext fun φ => LinearMap.ext fun m => by
    simp [opSmulLinear, LinearMap.dualMap_apply]
  map_add' t₁ t₂ := LinearMap.ext fun φ => LinearMap.ext fun m => by
    simp [opSmulLinear, LinearMap.dualMap_apply, add_smul]

/-- The left `T`-module structure on the `k`-dual of a right `T`-module. -/
@[reducible] def dualModule : Module T (Module.Dual k M) :=
  Module.compHom _ (dualRingHom k T M)

attribute [local instance] dualModule

variable {k T M}

theorem dual_smul_apply (t : T) (φ : Module.Dual k M) (m : M) : (t • φ) m = φ (op t • m) :=
  rfl

theorem isScalarTower_dual : IsScalarTower k T (Module.Dual k M) where
  smul_assoc c t φ := LinearMap.ext fun m => by
    rw [dual_smul_apply, op_smul, smul_assoc, map_smul, LinearMap.smul_apply, dual_smul_apply]

variable (k T M) in
theorem isSimpleModule_dual [FiniteDimensional k M] [IsSimpleModule Tᵐᵒᵖ M] :
    IsSimpleModule T (Module.Dual k M) := by
  have : Nontrivial M := IsSimpleModule.nontrivial Tᵐᵒᵖ M
  obtain ⟨v, hv⟩ := exists_ne (0 : M)
  obtain ⟨φ₀, hφ₀⟩ : ∃ φ : Module.Dual k M, φ v ≠ 0 := by
    by_contra h
    push Not at h
    exact hv ((Module.forall_dual_apply_eq_zero_iff k v).mp h)
  have : Nontrivial (Module.Dual k M) := ⟨⟨φ₀, 0, fun h => hφ₀ (by rw [h]; rfl)⟩⟩
  refine (isSimpleModule_iff _ _).mpr ⟨fun N => ?_⟩
  let W : Submodule Tᵐᵒᵖ M :=
    { carrier := {m | ∀ φ ∈ N, φ m = 0}
      add_mem' := fun ha hb φ hφ => by rw [map_add, ha φ hφ, hb φ hφ, add_zero]
      zero_mem' := fun φ _ => map_zero φ
      smul_mem' := fun b m hm φ hφ => by
        have := hm (b.unop • φ) (N.smul_mem _ hφ)
        rwa [dual_smul_apply, op_unop] at this }
  have := isScalarTower_dual (k := k) (T := T) (M := M)
  rcases IsSimpleOrder.eq_bot_or_eq_top W with h | h
  · right
    have hco : (N.restrictScalars k).dualCoannihilator = ⊥ := by
      refine eq_bot_iff.mpr fun m hm => ?_
      have : m ∈ W := fun φ hφ => (Submodule.mem_dualCoannihilator m).mp hm φ hφ
      rw [h] at this
      exact this
    have hN := Subspace.dualCoannihilator_dualAnnihilator_eq (W := N.restrictScalars k)
    rw [hco, Submodule.dualAnnihilator_bot] at hN
    exact eq_top_iff.mpr fun φ _ => by
      have : φ ∈ N.restrictScalars k := hN ▸ Submodule.mem_top
      exact this
  · left
    refine eq_bot_iff.mpr fun φ hφ => (Submodule.mem_bot T).mpr (LinearMap.ext fun m => ?_)
    have : m ∈ W := h ▸ Submodule.mem_top
    exact this φ hφ

/-- **Scalars on a simple right module from scalars on its dual.** If every `T`-linear
endomorphism of the left `T`-module `M*` is a scalar, then so is every `Tᵐᵒᵖ`-linear
endomorphism of `M`. -/
theorem exists_scalar_of_dual
    (hT : ∀ g : Module.Dual k M →ₗ[T] Module.Dual k M, ∃ c : k, ∀ φ, g φ = c • φ)
    (f : M →ₗ[Tᵐᵒᵖ] M) : ∃ c : k, ∀ v, f v = c • v := by
  let g : Module.Dual k M →ₗ[T] Module.Dual k M :=
    { toFun := fun φ => φ.comp (f.restrictScalars k)
      map_add' := fun _ _ => rfl
      map_smul' := fun t φ => LinearMap.ext fun m => by
        change φ (op t • f m) = φ (f (op t • m))
        rw [f.map_smul] }
  obtain ⟨c, hc⟩ := hT g
  refine ⟨c, fun v => ?_⟩
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff k (f v - c • v)).mp fun φ => ?_
  have := congrArg (fun ψ : Module.Dual k M => ψ v) (hc φ)
  simp only [g, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply, LinearMap.smul_apply, smul_eq_mul] at this
  rw [map_sub, map_smul, this, smul_eq_mul, sub_self]

end Categorification.DualRightModule
