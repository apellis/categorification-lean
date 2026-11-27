/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Tactic.Abel

/-!
# Exactness in the middle from a splitting of the middle term

Let `C₂ → C₁ → C₀` be maps with zero composite. Suppose `C₁ = A + B` for submodules `A`, `B`
such that `d₁` is injective on `B` and every element of `A` is the image under `d₂` of some
element, modulo `B`. Then the sequence is exact at `C₁`
(`LinearMap.ker_le_range_of_sup_eq_top`).

This is the matching argument of algebraic Morse theory in degree one. It is used for the
Koszul vanishing in B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v3, proof of Lemma 6.9 (v2: Lemma 6.8), at (6.21): the degree-one cells of the
cube on a standard module split into those matched downward (`B`) and those matched upward
(`A`).

## Main results

* `LinearMap.ker_le_range_of_sup_eq_top`.
-/

namespace LinearMap

variable {R : Type*} [Ring R] {C₂ C₁ C₀ : Type*} [AddCommGroup C₂] [AddCommGroup C₁]
  [AddCommGroup C₀] [Module R C₂] [Module R C₁] [Module R C₀]

/-- **Exactness from a matching.** If `C₁ = A + B`, `d₁` is injective on `B`, and each element
of `A` lies in `range d₂ + B`, then `ker d₁ ≤ range d₂`. -/
theorem ker_le_range_of_sup_eq_top {d₂ : C₂ →ₗ[R] C₁} {d₁ : C₁ →ₗ[R] C₀}
    (hd : d₁.comp d₂ = 0) {A B : Submodule R C₁} (hAB : A ⊔ B = ⊤)
    (hB : ∀ b ∈ B, d₁ b = 0 → b = 0) (hA : ∀ a ∈ A, ∃ y, d₂ y - a ∈ B) :
    ker d₁ ≤ range d₂ := by
  intro z hz
  have hz' : z ∈ A ⊔ B := hAB ▸ Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hz'
  obtain ⟨y, hy⟩ := hA a ha
  have hmem : a + b - d₂ y ∈ B := by
    have : a + b - d₂ y = b - (d₂ y - a) := by abel
    rw [this]; exact B.sub_mem hb hy
  have hzero : d₁ (a + b - d₂ y) = 0 := by
    rw [map_sub, mem_ker.1 hz, ← comp_apply, hd, zero_apply, sub_zero]
  have := hB _ hmem hzero
  exact ⟨y, (sub_eq_zero.1 this).symm⟩

/-- The same conclusion as exactness of the pair. -/
theorem exact_of_sup_eq_top {d₂ : C₂ →ₗ[R] C₁} {d₁ : C₁ →ₗ[R] C₀}
    (hd : d₁.comp d₂ = 0) {A B : Submodule R C₁} (hAB : A ⊔ B = ⊤)
    (hB : ∀ b ∈ B, d₁ b = 0 → b = 0) (hA : ∀ a ∈ A, ∃ y, d₂ y - a ∈ B) :
    Function.Exact d₂ d₁ := by
  intro z
  constructor
  · intro hz
    obtain ⟨y, hy⟩ := ker_le_range_of_sup_eq_top hd hAB hB hA (mem_ker.2 hz)
    exact ⟨y, hy⟩
  · rintro ⟨y, rfl⟩
    rw [← comp_apply, hd, zero_apply]

end LinearMap
