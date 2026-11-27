/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Linear maps over a tensor product of algebras, from generators

An additive map between modules over `A ⊗[k] C` is `A ⊗[k] C`-linear once it commutes with the
actions of the elements `a ⊗ 1` and `1 ⊗ c` (`tensorLinearOfGenerators`). This is how maps of
modules over the factor algebras `T^{λ'}(θ) ⊗ R^{λ_ℓ}(β)` are checked in B. Webster, *Knot
invariants and higher representation theory*, arXiv:1309.3796v3, proof of Proposition 5.5.
-/

open scoped TensorProduct

namespace Categorification

variable {k : Type*} [CommSemiring k] {A : Type*} [Semiring A] [Algebra k A]
  {C : Type*} [Semiring C] [Algebra k C]
  {P : Type*} [AddCommMonoid P] [Module (A ⊗[k] C) P]
  {P' : Type*} [AddCommMonoid P'] [Module (A ⊗[k] C) P']

/-- **An additive map commuting with `a ⊗ 1` and `1 ⊗ c` is `A ⊗ C`-linear.** -/
def tensorLinearOfGenerators (f : P →+ P')
    (hA : ∀ (a : A) (x : P), f ((a ⊗ₜ[k] (1 : C)) • x) = (a ⊗ₜ[k] (1 : C)) • f x)
    (hC : ∀ (c : C) (x : P), f (((1 : A) ⊗ₜ[k] c) • x) = ((1 : A) ⊗ₜ[k] c) • f x) :
    P →ₗ[A ⊗[k] C] P' where
  toFun := f
  map_add' := f.map_add
  map_smul' z x := by
    rw [RingHom.id_apply]
    induction z using TensorProduct.inductionOn with
    | tmul a c =>
      rw [show a ⊗ₜ[k] c = (a ⊗ₜ[k] (1 : C)) * ((1 : A) ⊗ₜ[k] c) by
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul],
        mul_smul, mul_smul, hA, hC]
    | add z z' hz hz' => rw [add_smul, add_smul, map_add, hz, hz']

@[simp] theorem tensorLinearOfGenerators_apply (f : P →+ P')
    (hA : ∀ (a : A) (x : P), f ((a ⊗ₜ[k] (1 : C)) • x) = (a ⊗ₜ[k] (1 : C)) • f x)
    (hC : ∀ (c : C) (x : P), f (((1 : A) ⊗ₜ[k] c) • x) = ((1 : A) ⊗ₜ[k] c) • f x) (x : P) :
    tensorLinearOfGenerators f hA hC x = f x := rfl

end Categorification
