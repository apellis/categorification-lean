/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Artinian.Module
import Mathlib.LinearAlgebra.Projection

/-!
# Fitting's lemma for indecomposable modules of finite length

An endomorphism of an indecomposable module of finite length is nilpotent or bijective
(`IsIndecomposableModule.isNilpotent_or_bijective`), by the Fitting decomposition
`M = ker fⁿ ⊕ range fⁿ`. Hence if `T → B → T` is not nilpotent, `T` is a direct summand of `B`
(`IsIndecomposableModule.exists_leftInverse_of_not_isNilpotent`).

This is the first step of Ringel's argument for B. Webster, *Knot invariants and higher
representation theory*, arXiv:1309.3796v3, Theorem 6.14, second clause.
-/

namespace Categorification

variable (R : Type*) [Ring R] (M : Type*) [AddCommGroup M] [Module R M]

/-- A module is **indecomposable** if it is nonzero and its only idempotent endomorphisms are
`0` and `1`. -/
def IsIndecomposableModule : Prop :=
  Nontrivial M ∧ ∀ e : Module.End R M, IsIdempotentElem e → e = 0 ∨ e = 1

namespace IsIndecomposableModule

variable {R M} [IsArtinian R M] [IsNoetherian R M]

/-- **Fitting's lemma**: an endomorphism of an indecomposable module of finite length is
nilpotent or bijective. -/
theorem isNilpotent_or_bijective (hM : IsIndecomposableModule R M) (f : Module.End R M) :
    IsNilpotent f ∨ Function.Bijective f := by
  obtain ⟨n, hn, hn1⟩ :=
    (f.eventually_isCompl_ker_pow_range_pow.and (Filter.eventually_ge_atTop 1)).exists
  let e : Module.End R M := (LinearMap.range (f ^ n)).subtype ∘ₗ
    Submodule.projectionOnto _ _ hn.symm
  have hl : ∀ x ∈ LinearMap.range (f ^ n), e x = x := fun x hx =>
    congrArg Subtype.val (Submodule.projectionOnto_apply_left hn.symm ⟨x, hx⟩)
  have hr : ∀ x ∈ LinearMap.ker (f ^ n), e x = 0 := fun x hx => by
    change ((Submodule.projectionOnto _ _ hn.symm x : _) : M) = 0
    rw [Submodule.projectionOnto_apply_of_mem_right hn.symm hx, Submodule.coe_zero]
  have he : IsIdempotentElem e :=
    LinearMap.ext fun x => hl _ (Submodule.projectionOnto _ _ hn.symm x).2
  rcases hM.2 e he with h0 | h1
  · left
    refine ⟨n, LinearMap.ext fun x => ?_⟩
    have := hl _ (LinearMap.mem_range_self (f ^ n) x)
    rw [h0, LinearMap.zero_apply] at this
    exact this.symm
  · right
    have hk : LinearMap.ker (f ^ n) = ⊥ := by
      refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
      have := hr x hx
      rwa [h1, Module.End.one_apply] at this
    have hs : LinearMap.range (f ^ n) = ⊤ := by
      refine Submodule.eq_top_iff'.2 fun x => ?_
      have : e x = x := by rw [h1, Module.End.one_apply]
      rw [← this]
      exact (Submodule.projectionOnto _ _ hn.symm x).2
    have hinj : Function.Injective (f ^ n) := LinearMap.ker_eq_bot.1 hk
    have hsurj : Function.Surjective (f ^ n) := LinearMap.range_eq_top.1 hs
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    refine ⟨fun x y hxy => hinj ?_, fun y => ?_⟩
    · rw [pow_succ, Module.End.mul_apply, Module.End.mul_apply, hxy]
    · obtain ⟨x, hx⟩ := hsurj y
      refine ⟨(f ^ m) x, ?_⟩
      rw [← hx, pow_succ', Module.End.mul_apply]

/-- **A non-nilpotent composite `T → B → T` splits**: if `T` is indecomposable of finite length
and `g ∘ f` is not nilpotent, then `f` has a left inverse, so `T` is a direct summand of `B`. -/
theorem exists_leftInverse_of_not_isNilpotent (hM : IsIndecomposableModule R M)
    {B : Type*} [AddCommGroup B] [Module R B] (f : M →ₗ[R] B) (g : B →ₗ[R] M)
    (h : ¬ IsNilpotent (g ∘ₗ f)) : ∃ g' : B →ₗ[R] M, g' ∘ₗ f = LinearMap.id := by
  have hb := (hM.isNilpotent_or_bijective (g ∘ₗ f)).resolve_left h
  let φ := LinearEquiv.ofBijective (g ∘ₗ f) hb
  refine ⟨φ.symm.toLinearMap ∘ₗ g, LinearMap.ext fun x => ?_⟩
  exact φ.symm_apply_apply x

end IsIndecomposableModule

end Categorification
