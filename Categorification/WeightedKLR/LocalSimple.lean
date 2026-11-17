/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongRes
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Simple modules detected by a local corner action

Supporting algebra for the local-chart proof of roadmap A of Webster,
*Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.4,
Theorem 2.19. This file does not assert that Webster states a local-chart
argument or that its geometric inputs have already been established.

For a nonunital map `φ : R → A`, restriction is the `φ(1)`-fixed part of a
module. If the image of `R` acts there as the entire corner `φ(1) A φ(1)`,
a nonzero restriction of a simple `A`-module is simple over `R`. Scalar
endomorphisms on this restriction detect scalar endomorphisms of the original
simple module. The intended application uses a local ordinary KLR algebra
and Khovanov–Lauda I, arXiv:0803.4121v2, §3.2, Corollary 3.19.

The corner-action hypothesis is an explicit intermediate hypothesis. No
local-chart construction or general weighted absolute-irreducibility result
is claimed here.
-/

noncomputable section

namespace Categorification.InductionAlong.Res

universe u z w v

variable {R : Type u} {A : Type z} [Ring R] [Ring A] {φ : R →ₙ+* A}
  {M : Type w} [AddCommGroup M] [Module A M] [IsSimpleModule A M]

/-- A nonzero restriction of a simple module is simple when the image acts as
the whole corner on that restriction. This is the supporting corner step for
the local-chart route to Webster arXiv:1209.2463v4, §2.4, Theorem 2.19 (A).
The corner-action equality is a route hypothesis, not a printed source claim. -/
theorem isSimpleModule_of_corner_action
    (hunit : ∃ m : M, m ≠ 0 ∧ φ 1 • m = m)
    (hcorner : ∀ a : A, ∃ r : R, ∀ m : Res φ M,
      φ r • m.val = φ 1 • (a • m.val)) : IsSimpleModule R (Res φ M) := by
  obtain ⟨m, hm, hfix⟩ := hunit
  have hnontrivial : Nontrivial (Res φ M) :=
    ⟨⟨mk m hfix, 0, fun h => hm (congrArg val h)⟩⟩
  refine isSimpleModule_iff_toSpanSingleton_surjective.2 ⟨hnontrivial, ?_⟩
  intro x hx y
  have hxval : x.val ≠ 0 := fun h => hx (ext h)
  obtain ⟨a, ha⟩ := IsSimpleModule.toSpanSingleton_surjective A hxval y.val
  obtain ⟨r, hr⟩ := hcorner a
  refine ⟨r, ext ?_⟩
  change φ r • x.val = y.val
  rw [hr x]
  change a • x.val = y.val at ha
  rw [ha, y.prop]

variable {k : Type v} [CommRing k] [Algebra k A]
  [Module k M] [IsScalarTower k A M]

/-- Scalar endomorphisms on a nonzero restriction detect scalar endomorphisms
of the original simple module. This is the algebraic concluding step of the
local-chart route to Webster arXiv:1209.2463v4, §2.4, Theorem 2.19 (A),
using KL I arXiv:0803.4121v2, §3.2, Corollary 3.19 on the local algebra.
The scalar-endomorphism property of the restriction is an explicit input. -/
theorem exists_eq_smul_of_scalar_endomorphisms
    (hunit : ∃ m : M, m ≠ 0 ∧ φ 1 • m = m)
    (hEnd : ∀ ψ : Res φ M →ₗ[R] Res φ M,
      ∃ c : k, ∀ m : Res φ M, (ψ m).val = c • m.val)
    (ψ : M →ₗ[A] M) : ∃ c : k, ∀ m : M, ψ m = c • m := by
  obtain ⟨c, hc⟩ := hEnd (map ψ)
  obtain ⟨m, hm, hfix⟩ := hunit
  have hψm : ψ m = c • m := hc (mk m hfix)
  refine ⟨c, fun n => ?_⟩
  obtain ⟨a, rfl⟩ := IsSimpleModule.toSpanSingleton_surjective A hm n
  change ψ (a • m) = c • (a • m)
  rw [map_smul, hψm, smul_comm]

end Categorification.InductionAlong.Res
