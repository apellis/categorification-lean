/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Projection
import Mathlib.Tactic

/-!
# Minimum squared norm on an affine solution set

Supporting finite-dimensional algebra for the local-chart proof of B. Webster,
*Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, Theorem 2.19 (roadmap A).
This is a supporting lemma, not a statement printed in the source. Over any ordered field,
a nonempty set cut out by linear equations has a point of minimum squared coordinate norm.
The proof uses the orthogonal complement of the common kernel and requires no completeness.
-/

namespace Categorification.WeightedKLR.Geometry

variable {K ι α : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Fintype ι]

/-- The sum of the squares of finitely many coordinates. -/
def squaredNorm (x : ι → K) : K := ∑ i, x i ^ 2

lemma squaredNorm_nonneg (x : ι → K) : 0 ≤ squaredNorm x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

private noncomputable def coordinateBilin : LinearMap.BilinForm K (ι → K) := by
  classical
  exact (dotProductEquiv K ι).toLinearMap

omit [LinearOrder K] [IsStrictOrderedRing K] in
private lemma coordinateBilin_apply (x y : ι → K) :
    coordinateBilin x y = ∑ i, x i * y i := rfl

omit [LinearOrder K] [IsStrictOrderedRing K] in
private lemma coordinateBilin_refl :
    (coordinateBilin (K := K) (ι := ι)).IsRefl := by
  intro x y h
  simpa only [coordinateBilin_apply, mul_comm] using h

private lemma coordinateBilin_self_eq_zero {x : ι → K}
    (h : coordinateBilin x x = 0) : x = 0 := by
  exact dotProduct_self_eq_zero.mp h

/-- Every vector is a sum of a vector in a subspace and one orthogonal to it. This uses
positive definiteness of the coordinate form and finite dimension, over an arbitrary ordered field. -/
lemma exists_orthogonal_decomposition (W : Submodule K (ι → K)) (x : ι → K) :
    ∃ u ∈ W, ∃ p : ι → K, u + p = x ∧ ∀ d ∈ W, (∑ i, d i * p i) = 0 := by
  classical
  let B := coordinateBilin (K := K) (ι := ι)
  have hc : IsCompl W (B.orthogonal W) := by
    apply (B.isCompl_orthogonal_iff_disjoint coordinateBilin_refl).2
    rw [Submodule.disjoint_def]
    intro v hv hw
    exact coordinateBilin_self_eq_zero (hw v hv)
  obtain ⟨u, p, hup, _⟩ := W.existsUnique_add_of_isCompl hc x
  exact ⟨u, u.property, p, hup, p.property⟩

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Pythagoras for the squared coordinate norm. -/
lemma squaredNorm_add_of_orthogonal (x y : ι → K)
    (h : (∑ i, x i * y i) = 0) :
    squaredNorm (x + y) = squaredNorm x + squaredNorm y := by
  have he : squaredNorm (x + y) = squaredNorm x + squaredNorm y +
      2 * ∑ i, x i * y i := by
    unfold squaredNorm
    simp only [Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, h, mul_zero, add_zero]

/-- A nonempty affine solution set has a point orthogonal to its direction kernel, and
Pythagoras holds with that point as origin. This is supporting algebra for Webster 2.19. -/
theorem exists_affine_minimum (ℓ : α → (ι → K) →ₗ[K] K) (b : α → K)
    (hne : ∃ x, ∀ i, ℓ i x = b i) :
    ∃ p : ι → K, (∀ i, ℓ i p = b i) ∧
      (∀ d : ι → K, (∀ i, ℓ i d = 0) → (∑ j, p j * d j) = 0) ∧
      (∀ x : ι → K, (∀ i, ℓ i x = b i) →
        squaredNorm x = squaredNorm p + squaredNorm (x - p)) := by
  classical
  obtain ⟨y, hy⟩ := hne
  let W : Submodule K (ι → K) := ⨅ i, LinearMap.ker (ℓ i)
  have memW (d : ι → K) : d ∈ W ↔ ∀ i, ℓ i d = 0 := by
    simp [W]
  obtain ⟨u, hu, p, hup, hp⟩ := exists_orthogonal_decomposition W y
  have hp_eq (i : α) : ℓ i p = b i := by
    have h := congrArg (ℓ i) hup
    rw [map_add, (memW u).1 hu i, zero_add, hy i] at h
    exact h
  have hp_orth (d : ι → K) (hd : ∀ i, ℓ i d = 0) : (∑ j, p j * d j) = 0 := by
    simpa only [mul_comm] using hp d ((memW d).2 hd)
  refine ⟨p, hp_eq, hp_orth, ?_⟩
  intro x hx
  have hd : ∀ i, ℓ i (x - p) = 0 := by
    intro i
    rw [map_sub, hx i, hp_eq i, sub_self]
  have h := squaredNorm_add_of_orthogonal p (x - p) (hp_orth _ hd)
  simpa only [add_sub_cancel] using h

/-- Minimum-norm formulation of `exists_affine_minimum`, used for the active-set proof of
polyhedral minimum existence in the local-chart proof of Webster 2.19. -/
theorem exists_affine_minimum_le (ℓ : α → (ι → K) →ₗ[K] K) (b : α → K)
    (hne : ∃ x, ∀ i, ℓ i x = b i) :
    ∃ p : ι → K, (∀ i, ℓ i p = b i) ∧
      ∀ x : ι → K, (∀ i, ℓ i x = b i) → squaredNorm p ≤ squaredNorm x := by
  obtain ⟨p, hp, _, hpy⟩ := exists_affine_minimum ℓ b hne
  refine ⟨p, hp, ?_⟩
  intro x hx
  rw [hpy x hx]
  exact le_add_of_nonneg_right (squaredNorm_nonneg _)

end Categorification.WeightedKLR.Geometry
