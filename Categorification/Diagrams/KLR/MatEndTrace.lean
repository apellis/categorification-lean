/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.AmbidextrousTrace
import Categorification.Diagrams.KLR.MatEnd

/-!
# Traces on matrix endomorphism algebras

For a finite family `X : ι → D` and additive maps `τ i : End (X i) → End P`, the diagonal sum
`trace τ M = ∑ i, τ i (M i i)` is an additive map on `MatEnd X`. If every `τ i` is nondegenerate
against the summands (`IsNondegTrace`), the pairing `(M, N) ↦ trace τ (M * N)` kills no nonzero
matrix on either side, and the trace is `k`-linear when every `τ i` is (`trace_smul`). This is
the step from the summands to the whole algebra in Webster,
arXiv:1309.3796v3, proof of Theorem 3.18.
-/

noncomputable section

namespace Categorification.KLR.Diagram.MatEnd

open CategoryTheory AmbidextrousTrace

variable {k : Type*} [CommRing k] {C : Type*} [Category C] {D : Type*} [Category D]
  [Preadditive D] [Linear k D] [Preadditive C] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : ι → D} {P : C}

/-- The diagonal trace `M ↦ ∑ i, τ i (M i i)`. -/
def trace (τ : ∀ i, (X i ⟶ X i) →+ (P ⟶ P)) : MatEnd X →+ (P ⟶ P) where
  toFun M := ∑ i, τ i (M i i)
  map_zero' := by simp
  map_add' M N := by simp [Finset.sum_add_distrib]

/-- The diagonal trace is `k`-linear when every summand trace is. -/
theorem trace_smul [Linear k C] (τ : ∀ i, (X i ⟶ X i) →+ (P ⟶ P))
    (hτ : ∀ i (c : k) (a : X i ⟶ X i), τ i (c • a) = c • τ i a) (c : k) (M : MatEnd X) :
    trace τ (c • M) = c • trace τ M := by
  change ∑ i, τ i (c • M i i) = c • ∑ i, τ i (M i i)
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => hτ i c (M i i)

theorem trace_mul_single (τ : ∀ i, (X i ⟶ X i) →+ (P ⟶ P)) (M : MatEnd X) (i j : ι)
    (b : X i ⟶ X j) : trace τ (M * single i j b) = τ i (b ≫ M j i) := by
  change ∑ i', τ i' (∑ j', single i j b i' j' ≫ M j' i') = _
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro j' _ hj
      rw [single_apply_of_ne _ (by tauto), Limits.zero_comp]
    · simp
  · intro i' _ hi
    rw [Finset.sum_eq_zero, map_zero]
    intro j' _
    rw [single_apply_of_ne _ (by tauto), Limits.zero_comp]
  · simp

theorem trace_single_mul (τ : ∀ i, (X i ⟶ X i) →+ (P ⟶ P)) (N : MatEnd X) (i j : ι)
    (a : X j ⟶ X i) : trace τ (single j i a * N) = τ i (N i j ≫ a) := by
  change ∑ i', τ i' (∑ j', N i' j' ≫ single j i a j' i') = _
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro j' _ hj
      rw [single_apply_of_ne _ (by tauto), Limits.comp_zero]
    · simp
  · intro i' _ hi
    rw [Finset.sum_eq_zero, map_zero]
    intro j' _
    rw [single_apply_of_ne _ (by tauto), Limits.comp_zero]
  · simp

/-- If every summand trace is nondegenerate, the diagonal trace pairing on `MatEnd X` is
nondegenerate on both sides. -/
theorem trace_nondegenerate (τ : ∀ i, (X i ⟶ X i) →+ (P ⟶ P))
    (hτ : ∀ i, IsNondegTrace P (X i) (τ i) fun Y => ∃ j, X j = Y) :
    (∀ M : MatEnd X, M ≠ 0 → ∃ N, trace τ (M * N) ≠ 0) ∧
      ∀ N : MatEnd X, N ≠ 0 → ∃ M, trace τ (M * N) ≠ 0 := by
  refine ⟨fun M hM => ?_, fun N hN => ?_⟩
  · obtain ⟨j, i, hji⟩ : ∃ j i, M j i ≠ 0 := by
      by_contra h
      push Not at h
      exact hM (ext h)
    obtain ⟨b, hb⟩ := (hτ i).2 (X j) ⟨j, rfl⟩ (M j i) hji
    exact ⟨single i j b, by rwa [trace_mul_single]⟩
  · obtain ⟨i, j, hij⟩ : ∃ i j, N i j ≠ 0 := by
      by_contra h
      push Not at h
      exact hN (ext h)
    obtain ⟨a, ha⟩ := (hτ i).1 (X j) ⟨j, rfl⟩ (N i j) hij
    exact ⟨single j i a, by rwa [trace_single_mul]⟩

end Categorification.KLR.Diagram.MatEnd
