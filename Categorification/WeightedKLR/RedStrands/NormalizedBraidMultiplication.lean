/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.RedPermutationGrading

/-!
# Multiplication of normalized braid coefficients

If no red pair changes order twice in a concatenation, the boundary
degree offsets add. The multiplication of the actual rectangular
coefficients is homogeneous in the normalized grading.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

variable {ℓ : ℕ}

/-- In a reduced concatenation each red pair changes order at most once. -/
theorem redWordInversions_union {lower middle upper : List (Fin ℓ)}
    (hL : ∀ r, r ∈ lower) (hM : ∀ r, r ∈ middle) (hU : ∀ r, r ∈ upper)
    (h : ∀ r d, lower.idxOf r < lower.idxOf d → middle.idxOf d < middle.idxOf r →
      ¬ upper.idxOf r < upper.idxOf d) :
    redWordInversions lower upper =
      redWordInversions lower middle ∪ redWordInversions middle upper := by
  ext ⟨r, d⟩
  simp only [Finset.mem_union, mem_redWordInversions]
  have total (xs : List (Fin ℓ)) (hx : ∀ r, r ∈ xs) (hne : r ≠ d) :
      xs.idxOf r < xs.idxOf d ∨ xs.idxOf d < xs.idxOf r :=
    lt_or_gt_of_ne fun he => hne ((List.idxOf_inj (hx r)).mp he)
  constructor
  · rintro ⟨hl, hu⟩
    rcases total middle hM (fun he => by simp [he] at hl) with hm | hm
    · exact Or.inr ⟨hm, hu⟩
    · exact Or.inl ⟨hl, hm⟩
  · rintro (⟨hl, hm⟩ | ⟨hm, hu⟩)
    · refine ⟨hl, ?_⟩
      exact (total upper hU (fun he => by simp [he] at hl)).resolve_left (h r d hl hm)
    · refine ⟨?_, hu⟩
      exact (total lower hL (fun he => by simp [he] at hm)).resolve_right
        (fun hl => h d r hl hm hu)

/-- The degree corrections add when no red pair changes order twice. -/
theorem redWordOffset_add {H : Type*} [AddCommGroup H] [Module ℂ H]
    (B : LinearMap.BilinForm ℂ (Module.Dual ℂ H)) (η : Fin ℓ → Module.Dual ℂ H)
    {lower middle upper : List (Fin ℓ)}
    (hL : ∀ r, r ∈ lower) (hM : ∀ r, r ∈ middle) (hU : ∀ r, r ∈ upper)
    (h : ∀ r d, lower.idxOf r < lower.idxOf d → middle.idxOf d < middle.idxOf r →
      ¬ upper.idxOf r < upper.idxOf d) :
    redWordOffset B η lower upper = redWordOffset B η lower middle + redWordOffset B η middle upper := by
  have hd : Disjoint (redWordInversions lower middle) (redWordInversions middle upper) := by
    rw [Finset.disjoint_left]
    intro p ha hb
    exact lt_asymm ((mem_redWordInversions _ _ _).mp ha).2 ((mem_redWordInversions _ _ _).mp hb).1
  unfold redWordOffset
  rw [redWordInversions_union hL hM hU h, Finset.sum_union hd]

section DiagramMultiplication

open KLR QuantumGroup

variable {I : Type} {k : Type*} [DecidableEq I] [Field k]
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
  (C : CartanDatum I) (hQ : IsRouquierQ C Q)
  {H : Type*} [AddCommGroup H] [Module ℂ H]
  (B : LinearMap.BilinForm ℂ (Module.Dual ℂ H)) (η : Fin ℓ → Module.Dual ℂ H)

local notation "Co" a:arg b:arg => braidingBimodule k Q Λ ν a b
local notation "W" a:arg b:arg => redPermutationWeight (Λ := Λ) (ν := ν) C hQ B η a b
local notation "δ" a:arg b:arg => redWordOffset B η a b

/-- Multiply diagrams with a shared intermediate red order. -/
def braidingCoefficientMul {lower middle upper : List (Fin ℓ)}
    (x : Co upper middle) (y : Co middle lower) : Co upper lower :=
  ⟨x.val * y.val, mem_cornerBimodule.mpr
    ⟨by rw [← mul_assoc, (mem_cornerBimodule.mp x.property).1],
      by rw [mul_assoc, (mem_cornerBimodule.mp y.property).2]⟩⟩

/-- Diagram multiplication adds the normalized degrees in a concatenation
in which no pair of red strands crosses twice. -/
theorem braidingCoefficientMul_mem_weight {lower middle upper : List (Fin ℓ)}
    (hL : ∀ r, r ∈ lower) (hM : ∀ r, r ∈ middle) (hU : ∀ r, r ∈ upper)
    (h : ∀ r d, lower.idxOf r < lower.idxOf d → middle.idxOf d < middle.idxOf r →
      ¬ upper.idxOf r < upper.idxOf d)
    {i j : ℤ} {x : Co upper middle} {y : Co middle lower}
    (hx : x ∈ (W middle upper) ((i : ℂ) + δ middle upper))
    (hy : y ∈ (W lower middle) ((j : ℂ) + δ lower middle)) :
    braidingCoefficientMul x y ∈ (W lower upper)
      (((i : ℂ) + δ middle upper) + ((j : ℂ) + δ lower middle)) := by
  have he : ((i : ℂ) + δ middle upper) + ((j : ℂ) + δ lower middle) =
      ((i + j : ℤ) : ℂ) + δ lower upper := by
    rw [redWordOffset_add B η hL hM hU h, Int.cast_add]
    ring
  rw [he, redPermutationWeight_intAdd]
  rw [redPermutationWeight_intAdd] at hx hy
  exact SetLike.GradedMul.mul_mem (A := violAuxiliaryGrade
    (stendhalGradingDatum Λ hQ.gradingDatum (UDot.di C)
      (fun i => (hQ.gradingDatum_degX i).trans (UDot.two_mul_di C i).symm))) hx hy

end DiagramMultiplication

end Categorification.Stendhal.BraidedStendhalAlgebra
