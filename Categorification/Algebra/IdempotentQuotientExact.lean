/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.IdempotentQuotient
import Mathlib.Algebra.Exact.Basic

/-!
# Short exact sequences through quotients by kernels of idempotents

For a short exact sequence `0 → A → X → B → 0` and idempotents `p_A`, `p_X`, `p_B`
intertwined by the maps, the sequence `0 → A / ker p_A → X / ker p_X → B / ker p_B → 0` is
exact. This descends the Mackey filtration of an induced KLR module to Webster's standard
modules (B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
proof of Proposition 5.5).

## Main results

* `IdempotentQuotient.descend_surjective`;
* `IdempotentQuotient.exact_descend`: exactness in the middle.
-/

namespace Categorification

namespace IdempotentQuotient

open Submodule LinearMap

variable {R : Type*} [CommRing R] {A X B : Type*} [AddCommGroup A] [Module R A]
  [AddCommGroup X] [Module R X] [AddCommGroup B] [Module R B]

theorem descend_surjective (p : X →ₗ[R] X) (q : B →ₗ[R] B) (π : X →ₗ[R] B)
    (hπ : ∀ x, π (p x) = q (π x)) (hsurj : Function.Surjective π) :
    Function.Surjective (descend p q π hπ) := by
  intro w
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  obtain ⟨x, rfl⟩ := hsurj b
  exact ⟨Submodule.Quotient.mk x, rfl⟩

variable (pA : A →ₗ[R] A) (pX : X →ₗ[R] X) (pB : B →ₗ[R] B) (φ : A →ₗ[R] X) (π : X →ₗ[R] B)
  (hφ : ∀ a, φ (pA a) = pX (φ a)) (hπ : ∀ x, π (pX x) = pB (π x))

/-- **Exactness in the middle** of `A / ker p_A → X / ker p_X → B / ker p_B`. Exactness of
`A → X → B` is needed only on the image of `p_X`. -/
theorem exact_descend (hX : IsIdempotentElem pX)
    (hex : ∀ x, π (pX x) = 0 ↔ pX x ∈ LinearMap.range φ) :
    Function.Exact (descend pA pX φ hφ) (descend pX pB π hπ) := by
  intro w
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  rw [descend_mk, Submodule.Quotient.mk_eq_zero, mem_ker, ← hπ]
  constructor
  · intro h
    obtain ⟨a, ha⟩ := (hex _).mp h
    refine ⟨Submodule.Quotient.mk (pA a), ?_⟩
    rw [descend_mk, Submodule.Quotient.eq, mem_ker, map_sub, hφ, ha, ← Module.End.mul_apply,
      hX.eq, ← Module.End.mul_apply pX pX, hX.eq, sub_self]
  · rintro ⟨v, hv⟩
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    rw [descend_mk, Submodule.Quotient.eq, mem_ker, map_sub, sub_eq_zero] at hv
    rw [← hv]
    exact (hex _).mpr ⟨pA a, hφ a⟩

end IdempotentQuotient

end Categorification
