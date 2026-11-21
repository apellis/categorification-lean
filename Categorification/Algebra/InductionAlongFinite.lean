/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongTensor

/-!
# Finiteness of induced modules and of quotients with compatible actions

Generic finiteness statements used in the dimension count of Webster, arXiv:1309.3796v3,
proof of Proposition 5.5.

## Main results

* `InductionAlong.IndK.finite`: `IndK k N φ` is a finitely generated `B`-module when `N` is a
  finitely generated `A`-module.
* `InductionAlong.IndK.finite_restrict`: if moreover `B` is a finite `k`-module, then
  `IndK k N φ` is a finite `k`-module.
* `Module.Finite.of_surjective_compatible`: if an additive surjection `π : M → V`
  intertwines the action of `a : A` on `M` with the action of `f a : T` on `V`, and `M` is a
  finitely generated `A`-module, then `V` is a finitely generated `T`-module.
* `Module.Finite.restrictScalars_of_finite`: `RestrictScalars k S X` is a finite `k`-module
  when `S` is a finite `k`-algebra and `X` a finitely generated `S`-module.
* `fixSub_finiteDimensional`: the subspace `f M` of a finite-dimensional module over a field
  is finite-dimensional.
-/

namespace Categorification

open MulOpposite

noncomputable section

namespace InductionAlong

universe u w

variable (k : Type*) [CommRing k] {A : Type u} [Ring A] {B : Type u} [Ring B] [Algebra k B]
  (N : Type w) [AddCommGroup N] [Module A N] (φ : A →ₙ+* B)

/-- **Induction of a finitely generated module is finitely generated**: `B φ(1) ⊗_A N` is a
finitely generated `B`-module when `N` is a finitely generated `A`-module. -/
theorem IndK.finite [Module.Finite A N] : Module.Finite B (IndK k N φ) := by
  have : Module.Finite B (Corner φ) :=
    Module.Finite.of_surjective
      ({ toFun := fun b => ⟨b * φ 1, by rw [mem_lIdeal, mul_assoc, unit_mul_unit]⟩
         map_add' := fun x y => Subtype.ext (add_mul _ _ _)
         map_smul' := fun c x => Subtype.ext (mul_assoc _ _ _) } : B →ₗ[B] Corner φ)
      fun z => ⟨z.1, Subtype.ext z.2⟩
  exact BalancedTensor.finite (k := ℤ)

/-- **Induction of a finitely generated module to a finite `k`-algebra** is a finite
`k`-module. -/
theorem IndK.finite_restrict [Module.Finite A N] [Module.Finite k B] :
    Module.Finite k (IndK k N φ) :=
  haveI := IndK.finite k N φ
  Module.Finite.trans B (IndK k N φ)

end InductionAlong

/-- **Finiteness through a compatible surjection.** Let `π : M → V` be an additive surjection
from an `A`-module to a `T`-module and `f : A → T` a function with
`π (a • m) = f a • π m`. If `M` is a finitely generated `A`-module, then `V` is a finitely
generated `T`-module. -/
theorem Module.Finite.of_surjective_compatible {A T M V : Type*} [Semiring A] [Semiring T]
    [AddCommMonoid M] [Module A M] [AddCommMonoid V] [Module T V] [Module.Finite A M]
    (π : M →+ V) (hπ : Function.Surjective π) (f : A → T)
    (hf : ∀ (a : A) (m : M), π (a • m) = f a • π m) : Module.Finite T V := by
  classical
  obtain ⟨G, hG⟩ := Module.Finite.fg_top (R := A) (M := M)
  refine ⟨⟨G.image π, Submodule.eq_top_iff'.2 fun v => ?_⟩⟩
  obtain ⟨m, rfl⟩ := hπ v
  have hm : m ∈ Submodule.span A (G : Set M) := hG ▸ Submodule.mem_top
  induction hm using Submodule.span_induction with
  | mem x hx =>
    exact Submodule.subset_span (by simpa using ⟨x, hx, rfl⟩)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [hf]; exact Submodule.smul_mem _ _ hx

/-- **Restriction of scalars of a finitely generated module over a finite `k`-algebra** is a
finite `k`-module. -/
theorem Module.Finite.restrictScalars_of_finite (k S X : Type*) [CommSemiring k] [Semiring S]
    [Algebra k S] [AddCommMonoid X] [Module S X] [Module.Finite k S] [Module.Finite S X] :
    Module.Finite k (RestrictScalars k S X) :=
  letI : Module S (RestrictScalars k S X) := RestrictScalars.moduleOrig k S X
  haveI : Module.Finite S (RestrictScalars k S X) := ‹Module.Finite S X›
  Module.Finite.trans S (RestrictScalars k S X)

/-- The subspace `f M = {m | f m = m}` of a finite-dimensional module over a field is
finite-dimensional. -/
theorem fixSub_finiteDimensional (k : Type*) [Field k] {A : Type*} [Ring A] [Algebra k A]
    (M : Type*) [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
    [FiniteDimensional k M] (f : A) : FiniteDimensional k (fixSub k M f) :=
  inferInstance

end

end Categorification
