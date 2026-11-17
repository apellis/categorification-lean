/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Geometry.AffineProjection

/-!
# Minimum squared norm on a finite polyhedron

Supporting geometry for roadmap A of Webster, arXiv:1209.2463v4, Theorem 2.19.
This is part of the local-chart argument, not a statement printed in
Webster. A finite system of non-strict linear inequalities over an ordered field
has a point of minimum squared Euclidean norm whenever it is nonempty. The proof
uses affine projections and a finite active-constraint argument, without an
Archimedean or completeness hypothesis.
-/

noncomputable section

namespace Categorification.WeightedKLR.Geometry

section ActiveConstraints

variable {K V τ : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup V] [Module K V] [Fintype τ] [DecidableEq τ]

private def inactive (ℓ : τ → V →ₗ[K] K) (b : τ → K) (y : V) : Finset τ :=
  Finset.univ.filter fun i => ℓ i y ≠ b i

private theorem first_boundary (ℓ : τ → V →ₗ[K] K) (b : τ → K) (y p : V)
    (hy : ∀ i, ℓ i y ≤ b i)
    (hp : ∀ i, ℓ i y = b i → ℓ i p = b i)
    (hbad : ¬ ∀ i, ℓ i p ≤ b i) :
    ∃ t : K, 0 < t ∧ t < 1 ∧
      (∀ i, ℓ i ((1 - t) • y + t • p) ≤ b i) ∧
      inactive ℓ b ((1 - t) • y + t • p) ⊂ inactive ℓ b y := by
  classical
  let bad : Finset τ := Finset.univ.filter fun i => b i < ℓ i p
  have hbadne : bad.Nonempty := by
    push Not at hbad
    obtain ⟨i, hi⟩ := hbad
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩
  let ratio : τ → K := fun i => (b i - ℓ i y) / (ℓ i p - ℓ i y)
  obtain ⟨j, hj, hmin⟩ := bad.exists_min_image ratio hbadne
  have hratio : ∀ i ∈ bad, 0 < ratio i ∧ ratio i < 1 := by
    intro i hi
    have hip : b i < ℓ i p := (Finset.mem_filter.1 hi).2
    have hiy : ℓ i y < b i := lt_of_le_of_ne (hy i) fun he => by
      have := hp i he
      linarith
    have hden : 0 < ℓ i p - ℓ i y := by linarith
    constructor
    · exact div_pos (sub_pos.2 hiy) hden
    · exact (div_lt_one hden).2 (by linarith)
  let t := ratio j
  have ht : 0 < t ∧ t < 1 := hratio j hj
  have heval : ∀ i, ℓ i ((1 - t) • y + t • p) =
      (1 - t) * ℓ i y + t * ℓ i p := by
    intro i
    simp only [map_add, map_smul, smul_eq_mul]
  have hz : ∀ i, ℓ i ((1 - t) • y + t • p) ≤ b i := by
    intro i
    rw [heval]
    by_cases hi : i ∈ bad
    · have hip : b i < ℓ i p := (Finset.mem_filter.1 hi).2
      have hden : 0 < ℓ i p - ℓ i y := by linarith [hy i]
      have hbound : t * (ℓ i p - ℓ i y) ≤ b i - ℓ i y :=
        (le_div_iff₀ hden).1 (hmin i hi)
      nlinarith
    · have hip : ℓ i p ≤ b i := by
        simpa only [bad, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] using hi
      have h₁ := mul_le_mul_of_nonneg_left (hy i) (by linarith : 0 ≤ 1 - t)
      have h₂ := mul_le_mul_of_nonneg_left hip ht.1.le
      nlinarith
  have hactive : ∀ i, ℓ i y = b i → ℓ i ((1 - t) • y + t • p) = b i := by
    intro i hi
    rw [heval, hi, hp i hi]
    ring
  have hjactive : ℓ j ((1 - t) • y + t • p) = b j := by
    have hjp : b j < ℓ j p := (Finset.mem_filter.1 hj).2
    have hden : ℓ j p - ℓ j y ≠ 0 := ne_of_gt (by linarith [hy j])
    have htj : t * (ℓ j p - ℓ j y) = b j - ℓ j y := div_mul_cancel₀ _ hden
    rw [heval]
    nlinarith
  refine ⟨t, ht.1, ht.2, hz, ?_⟩
  apply Finset.ssubset_iff_subset_ne.2
  constructor
  · intro i hi
    simp only [inactive, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact fun h => hi (hactive i h)
  · intro heq
    have hjy : j ∈ inactive ℓ b y := by
      simp only [inactive, Finset.mem_filter, Finset.mem_univ, true_and]
      intro h
      have := hp j h
      have hjp := (Finset.mem_filter.1 hj).2
      linarith
    have hjz := heq ▸ hjy
    exact (Finset.mem_filter.1 hjz).2 hjactive

/-- Finite active-constraint reduction: affine face minima suffice to minimize a
convex function on a finite system of linear inequalities. -/
theorem exists_feasible_face_minimum (ℓ : τ → V →ₗ[K] K) (b : τ → K)
    (q : V → K) (p : Finset τ → V)
    (hproj : ∀ s y, (∀ i ∈ s, ℓ i y = b i) →
      (∀ i ∈ s, ℓ i (p s) = b i) ∧ q (p s) ≤ q y)
    (hconv : ∀ y z (t : K), 0 ≤ t → t ≤ 1 → q z ≤ q y →
      q ((1 - t) • y + t • z) ≤ q y)
    {y : V} (hy : ∀ i, ℓ i y ≤ b i) :
    ∃ s : Finset τ, (∀ i, ℓ i (p s) ≤ b i) ∧ q (p s) ≤ q y := by
  classical
  suffices h : ∀ s : Finset τ, ∀ y : V, inactive ℓ b y = s →
      (∀ i, ℓ i y ≤ b i) →
      ∃ t : Finset τ, (∀ i, ℓ i (p t) ≤ b i) ∧ q (p t) ≤ q y by
    exact h _ y rfl hy
  intro s
  refine Finset.strongInductionOn s ?_
  intro s ih y hys hy
  let a := Finset.univ \ s
  have ha : ∀ i ∈ a, ℓ i y = b i := by
    intro i hi
    have his := (Finset.mem_sdiff.1 hi).2
    rw [← hys] at his
    simpa only [inactive, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using his
  obtain ⟨hp, hq⟩ := hproj a y ha
  by_cases hfeas : ∀ i, ℓ i (p a) ≤ b i
  · exact ⟨a, hfeas, hq⟩
  · have hp' : ∀ i, ℓ i y = b i → ℓ i (p a) = b i := by
      intro i hi
      apply hp i
      simp only [a, Finset.mem_sdiff, Finset.mem_univ, true_and, ← hys,
        inactive, Finset.mem_filter, Finset.mem_univ, true_and, not_not]
      exact hi
    obtain ⟨t, ht0, ht1, hz, hsmall⟩ := first_boundary ℓ b y (p a) hy hp' hfeas
    rw [hys] at hsmall
    obtain ⟨u, hu, hqu⟩ := ih _ hsmall _ rfl hz
    exact ⟨u, hu, hqu.trans (hconv y (p a) t ht0.le ht1.le hq)⟩

end ActiveConstraints

section SquaredNorm

variable {K ι τ : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [Fintype ι] [Fintype τ] [DecidableEq τ]

/-- Moving toward a point of no greater squared norm cannot increase squared norm. -/
theorem squaredNorm_combo_le (y z : ι → K) {t : K}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hq : squaredNorm z ≤ squaredNorm y) :
    squaredNorm ((1 - t) • y + t • z) ≤ squaredNorm y := by
  have hcv : squaredNorm ((1 - t) • y + t • z) ≤
      (1 - t) * squaredNorm y + t * squaredNorm z := by
    unfold squaredNorm
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have := mul_nonneg (mul_nonneg ht0 (sub_nonneg.2 ht1)) (sq_nonneg (y i - z i))
    nlinarith
  have := mul_le_mul_of_nonneg_left hq ht0
  nlinarith

/-- A nonempty finite polyhedron over any ordered field has a point of minimum
squared coordinate norm. This is supporting geometry for roadmap A of Webster,
arXiv:1209.2463v4, Theorem 2.19, in the local-chart argument. -/
theorem exists_squaredNorm_minimum (ℓ : τ → (ι → K) →ₗ[K] K) (b : τ → K)
    (hne : ∃ x, ∀ i, ℓ i x ≤ b i) :
    ∃ p : ι → K, (∀ i, ℓ i p ≤ b i) ∧
      ∀ x : ι → K, (∀ i, ℓ i x ≤ b i) → squaredNorm p ≤ squaredNorm x := by
  classical
  have hp : ∀ s : Finset τ, ∃ p : ι → K,
      ∀ y, (∀ i ∈ s, ℓ i y = b i) →
        (∀ i ∈ s, ℓ i p = b i) ∧ squaredNorm p ≤ squaredNorm y := by
    intro s
    by_cases hs : ∃ y, ∀ i ∈ s, ℓ i y = b i
    · obtain ⟨y, hy⟩ := hs
      obtain ⟨p, hp, hmin⟩ := exists_affine_minimum_le
        (fun i : {i // i ∈ s} => ℓ i) (fun i : {i // i ∈ s} => b i)
        ⟨y, fun i => hy i i.property⟩
      exact ⟨p, fun z hz => ⟨fun i hi => hp ⟨i, hi⟩,
        hmin z fun i => hz i i.property⟩⟩
    · exact ⟨0, fun y hy => (hs ⟨y, hy⟩).elim⟩
  choose p hp using hp
  let candidates : Finset (Finset τ) := Finset.univ.filter fun s => ∀ i, ℓ i (p s) ≤ b i
  have hcan : candidates.Nonempty := by
    obtain ⟨y, hy⟩ := hne
    obtain ⟨s, hs, _⟩ := exists_feasible_face_minimum ℓ b squaredNorm p hp
      (fun y z t ht0 ht1 hq => squaredNorm_combo_le y z ht0 ht1 hq) hy
    exact ⟨s, Finset.mem_filter.2 ⟨Finset.mem_univ _, hs⟩⟩
  obtain ⟨s, hs, hmin⟩ := candidates.exists_min_image (fun s => squaredNorm (p s)) hcan
  refine ⟨p s, (Finset.mem_filter.1 hs).2, ?_⟩
  intro x hx
  obtain ⟨t, ht, hq⟩ := exists_feasible_face_minimum ℓ b squaredNorm p hp
    (fun y z t ht0 ht1 hq => squaredNorm_combo_le y z ht0 ht1 hq) hx
  exact (hmin t (Finset.mem_filter.2 ⟨Finset.mem_univ _, ht⟩)).trans hq

end SquaredNorm

end Categorification.WeightedKLR.Geometry
