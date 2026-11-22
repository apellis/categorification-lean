/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.Module
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# The vector-space dual twisted by an anti-automorphism

For a `k`-algebra `A` with an anti-homomorphism `τ : A →ₐ[k] Aᵐᵒᵖ` and an `A`-module `M`,
the `k`-dual `Hom_k(M, k)` is again an `A`-module by `(a • f)(m) = f(τ(a) m)` (`TwistDual`).
This is the duality `M ↦ M⋆` of Webster, arXiv:1309.3796v2, before Proposition 5.11, for the
anti-automorphism of `T^λ` reflecting diagrams.

## Main results

* `TwistDual.isSimpleModule`: if `τ` is an involution and `M` is finite-dimensional and
  simple, then so is its twisted dual.
* `TwistDual.doubleDualEquiv`: for an involution `τ`, `M ≅ M⋆⋆` for finite-dimensional `M`.
* `TwistDual.finrank_idemSubspace`: for an idempotent `e` fixed by `τ`, the subspaces `e M⋆`
  and `e M` have the same dimension.
-/

set_option backward.isDefEq.respectTransparency false

namespace Categorification

open _root_.Categorification.Graded

variable {k A : Type*} [Field k] [Ring A] [Algebra k A] (τ : A →ₐ[k] Aᵐᵒᵖ)
  (M : Type*) [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]

/-- The `k`-dual of `M` with the `A`-action `(a • f)(m) = f(τ(a) m)`. -/
@[nolint unusedArguments]
def TwistDual (_τ : A →ₐ[k] Aᵐᵒᵖ) (M : Type*) [AddCommGroup M] [Module k M] :=
  Module.Dual k M

namespace TwistDual

instance : AddCommGroup (TwistDual τ M) := inferInstanceAs (AddCommGroup (Module.Dual k M))

instance : Module k (TwistDual τ M) := inferInstanceAs (Module k (Module.Dual k M))

variable {M}

/-- The action of `b : A` on `M` as a `k`-linear map. -/
abbrev act (b : A) : M →ₗ[k] M := DistribSMul.toLinearMap k M b

/-- The identification of the twisted dual with the `k`-dual. -/
def toDual : TwistDual τ M ≃ₗ[k] Module.Dual k M := LinearEquiv.refl k _

instance : SMul A (TwistDual τ M) where
  smul a f := (toDual τ).symm ((toDual τ f).comp (act (τ a).unop))

theorem smul_apply (a : A) (f : TwistDual τ M) (m : M) :
    toDual τ (a • f) m = toDual τ f ((τ a).unop • m) := rfl

omit [Module A M] [IsScalarTower k A M] in
@[ext] theorem ext {f g : TwistDual τ M} (h : ∀ m, toDual τ f m = toDual τ g m) : f = g :=
  LinearMap.ext h

instance : Module A (TwistDual τ M) where
  one_smul f := ext τ fun m => by simp [smul_apply]
  mul_smul a b f := ext τ fun m => by
    simp only [smul_apply, map_mul, MulOpposite.unop_mul, mul_smul]
  smul_zero a := ext τ fun m => by
    simp only [smul_apply, map_zero, LinearMap.zero_apply]
  smul_add a f g := ext τ fun m => by
    simp only [smul_apply, map_add, LinearMap.add_apply]
  add_smul a b f := ext τ fun m => by
    simp only [smul_apply, map_add, MulOpposite.unop_add, add_smul, LinearMap.add_apply]
  zero_smul f := ext τ fun m => by simp [smul_apply]

instance : IsScalarTower k A (TwistDual τ M) where
  smul_assoc c a f := ext τ fun m => by
    change toDual τ f ((τ (c • a)).unop • m) = c * toDual τ f ((τ a).unop • m)
    rw [map_smul τ c a, MulOpposite.unop_smul, smul_assoc, map_smul (toDual τ f) c,
      smul_eq_mul]

omit [Module A M] [IsScalarTower k A M] in
theorem toDual_smul (c : k) (f : TwistDual τ M) : toDual τ (c • f) = c • toDual τ f := rfl

section Simple

variable [FiniteDimensional k M]

/-- If `τ` is an involution, the `k`-subspace of `M` on which every functional of an
`A`-submodule of the twisted dual vanishes is an `A`-submodule. -/
def coann (hτ : ∀ a, (τ (τ a).unop).unop = a) (N : Submodule A (TwistDual τ M)) :
    Submodule A M where
  carrier := {m | ∀ f ∈ N, toDual τ f m = 0}
  add_mem' ha hb f hf := by rw [map_add, ha f hf, hb f hf, add_zero]
  zero_mem' f _ := map_zero _
  smul_mem' a m hm f hf := by
    have := hm (((τ a).unop) • f) (N.smul_mem _ hf)
    rwa [smul_apply, hτ] at this

/-- **Simplicity of the twisted dual.** -/
theorem isSimpleModule (hτ : ∀ a, (τ (τ a).unop).unop = a) [IsSimpleModule A M] :
    IsSimpleModule A (TwistDual τ M) := by
  have hM : Nontrivial M := IsSimpleModule.nontrivial A M
  have : Nontrivial (TwistDual τ M) := by
    obtain ⟨m, hm⟩ := exists_ne (0 : M)
    obtain ⟨f, hf⟩ := not_forall.mp
      ((Module.forall_dual_apply_eq_zero_iff k m).not.mpr hm)
    exact ⟨⟨(toDual τ).symm f, 0,
      fun h => hf (by simpa using congrArg (toDual τ · m) h)⟩⟩
  refine { toNontrivial := (Submodule.nontrivial_iff A).mpr this, eq_bot_or_eq_top := ?_ }
  intro N
  rcases IsSimpleOrder.eq_bot_or_eq_top (coann τ hτ N) with h | h
  · right
    -- every vector is detected, so the functionals in `N` span the dual
    let N' : Submodule k (Module.Dual k M) := (N.restrictScalars k).map (toDual τ).toLinearMap
    have hc : N'.dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro m hm
      have : m ∈ coann τ hτ N := fun f hf =>
        (Submodule.mem_dualCoannihilator m).mp hm _ ⟨f, hf, rfl⟩
      rwa [h] at this
    have hN' : N' = ⊤ := by
      rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := N'), hc,
        Submodule.dualAnnihilator_bot]
    rw [eq_top_iff]
    intro f _
    obtain ⟨g, hg, hgf⟩ := (hN'.symm ▸ Submodule.mem_top : toDual τ f ∈ N')
    have : g = f := (toDual τ).injective hgf
    exact this ▸ hg
  · left
    rw [eq_bot_iff]
    intro f hf
    refine (Submodule.mem_bot A).mpr (ext τ fun m => ?_)
    have : m ∈ coann τ hτ N := h ▸ Submodule.mem_top
    exact this f hf

/-- The twisted dual of a finite-dimensional module is finite-dimensional. -/
instance : FiniteDimensional k (TwistDual τ M) :=
  inferInstanceAs (FiniteDimensional k (Module.Dual k M))

/-- **Double duality.** If `τ` is an involution, a finite-dimensional module is isomorphic to
its twisted double dual by evaluation. -/
noncomputable def doubleDualEquiv (hτ : ∀ a, (τ (τ a).unop).unop = a) :
    M ≃ₗ[A] TwistDual τ (TwistDual τ M) where
  __ := (Module.evalEquiv k M).trans
    ((LinearEquiv.refl k (Module.Dual k M)).dualMap.trans (toDual τ (M := TwistDual τ M)).symm)
  map_smul' a m := ext τ fun f => by
    change toDual τ f (a • m) = toDual τ (((τ a).unop) • f) m
    rw [smul_apply, hτ]

end Simple

section Idem

theorem idemSubspace_eq_range {e : A} (he : IsIdempotentElem e) :
    idemSubspace k M e = LinearMap.range (act e) := by
  ext m
  refine ⟨fun h => ⟨m, h⟩, ?_⟩
  rintro ⟨n, rfl⟩
  change e • e • n = e • n
  rw [← mul_smul, he.eq]

/-- **Idempotent dimensions of the twisted dual.** For an idempotent `e` with `τ(e) = e`,
`dim e M⋆ = dim e M`. -/
theorem finrank_idemSubspace [FiniteDimensional k M] {e : A} (he : IsIdempotentElem e)
    (hτe : (τ e).unop = e) :
    Module.finrank k (idemSubspace k (TwistDual τ M) e) =
      Module.finrank k (idemSubspace k M e) := by
  have he' : IsIdempotentElem (act (k := k) (M := M) e) := by
    ext m; simp [← mul_smul, he.eq]
  have hD : idemSubspace k (TwistDual τ M) e =
      (LinearMap.range (act (k := k) (M := M) e).dualMap).map (toDual τ).symm.toLinearMap := by
    ext f
    simp only [mem_idemSubspace, Submodule.mem_map, LinearMap.mem_range]
    constructor
    · intro h
      refine ⟨toDual τ f, ⟨toDual τ f, ?_⟩, rfl⟩
      ext m
      have := congrArg (toDual τ · m) h
      simp only [smul_apply, hτe] at this
      simpa [LinearMap.dualMap_apply] using this
    · rintro ⟨g, ⟨g', rfl⟩, rfl⟩
      ext m
      simp only [smul_apply, hτe]
      change g' (e • e • m) = g' (e • m)
      rw [← mul_smul, he.eq]
  rw [hD, LinearEquiv.finrank_map_eq, LinearMap.finrank_range_dualMap_eq_finrank_range,
    idemSubspace_eq_range he]

end Idem

end TwistDual

end Categorification
