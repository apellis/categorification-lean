/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Spans of multiples by a set of scalars

For a set `S` of scalars of a ring `R` and an `R`-module `M`, `spanSmulOf S M` is the submodule
spanned by the elements `b • y` with `b ∈ S`. A surjective linear map carries it onto its
counterpart (`Categorification.map_spanSmulOf`), and on a retract `P` of `M` it restricts to its
counterpart (`Categorification.comap_subtype_spanSmulOf`).

## Main definitions

* `Categorification.spanSmulOf`: the span of `{b • y | b ∈ S}`.
-/

namespace Categorification

variable {R : Type*} [Ring R] (S : Set R) {M M' : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M']

variable (M) in
/-- The span of the multiples `b • y` with `b ∈ S`. -/
def spanSmulOf : Submodule R M :=
  Submodule.span R {x | ∃ b ∈ S, ∃ y : M, x = b • y}

theorem smul_mem_spanSmulOf {b : R} (hb : b ∈ S) (y : M) : b • y ∈ spanSmulOf S M :=
  Submodule.subset_span ⟨b, hb, y, rfl⟩

theorem map_spanSmulOf_le (f : M →ₗ[R] M') : (spanSmulOf S M).map f ≤ spanSmulOf S M' := by
  rw [spanSmulOf, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨b, hb, y, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, map_smul]
  exact smul_mem_spanSmulOf S hb (f y)

/-- A surjective linear map carries `spanSmulOf S M` onto `spanSmulOf S M'`. -/
theorem map_spanSmulOf {f : M →ₗ[R] M'} (hf : Function.Surjective f) :
    (spanSmulOf S M).map f = spanSmulOf S M' := by
  refine le_antisymm (map_spanSmulOf_le S f) (Submodule.span_le.2 ?_)
  rintro _ ⟨b, hb, y, rfl⟩
  obtain ⟨y, rfl⟩ := hf y
  exact ⟨b • y, smul_mem_spanSmulOf S hb y, map_smul f b y⟩

/-- **On a retract, `spanSmulOf` restricts to `spanSmulOf`**: if `π : M → P` fixes the
submodule `P`, the elements of `P` in `spanSmulOf S M` form `spanSmulOf S P`. -/
theorem comap_subtype_spanSmulOf (P : Submodule R M) (π : M →ₗ[R] P)
    (hπ : ∀ p : P, π p = p) :
    (spanSmulOf S M).comap P.subtype = spanSmulOf S P := by
  refine le_antisymm (fun y hy => ?_) ?_
  · rw [← hπ y]
    exact map_spanSmulOf_le S π ⟨y, hy, rfl⟩
  · rw [← Submodule.map_le_iff_le_comap]
    exact map_spanSmulOf_le S P.subtype

end Categorification
