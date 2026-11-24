/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockShufflePermutation
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Triangularity of the right crossing

For the kernel test in Webster (arXiv:1309.3796v2), §6.1, Lemma 6.8, distinct
external and internal shuffles have distinct leading targets. Once the
right multiplications in the leading coefficients are injective on their
supports, the lower crossing-filtration errors cannot cancel a nonzero leading term.
-/

namespace Categorification.Stendhal.RedBlock

open scoped BigOperators

variable {k ι κ : Type*} [CommSemiring k] [Fintype ι]
  {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module k (M i)]
  {N : κ → Type*} [∀ a, AddCommGroup (N a)] [∀ a, Module k (N a)]

/-- A sum of crossing-coordinate maps is injective when each input has an injective
leading coordinate and only strictly higher priority inputs can contribute there. -/
private theorem injective_sum_of_leading_coordinates
    (weight : ι → ℕ) (lead : ι → κ) (T : ∀ i a, M i →ₗ[k] N a)
    (hdiag : ∀ i, Function.Injective (T i (lead i)))
    (htri : ∀ i j, i ≠ j → weight i ≤ weight j → T i (lead j) = 0) :
    Function.Injective (fun x : ∀ i, M i => fun a => ∑ i, T i a (x i)) := by
  classical
  intro x y heq
  by_contra hne
  let s := Finset.univ.filter (fun i => x i ≠ y i)
  have hs : s.Nonempty := by
    by_contra hn
    apply hne
    funext i
    by_contra hi
    exact hn ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image s weight hs
  have hg (i : ι) (hi : i ≠ j) : T i (lead j) (x i) = T i (lead j) (y i) := by
    by_cases h : x i = y i
    · rw [h]
    · have hle := hmax i (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
      simp only [htri i j hi hle, LinearMap.zero_apply]
  have hf := congrFun heq (lead j)
  change (∑ i, T i (lead j) (x i)) = (∑ i, T i (lead j) (y i)) at hf
  have hd : T j (lead j) (x j) = T j (lead j) (y j) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ j)] at hf
    have ho : (∑ i ∈ Finset.univ.erase j, T i (lead j) (x i)) =
        ∑ i ∈ Finset.univ.erase j, T i (lead j) (y i) :=
      Finset.sum_congr rfl fun i hi => hg i (Finset.ne_of_mem_erase hi)
    rw [ho, add_left_inj] at hf
    exact hf
  exact (Finset.mem_filter.1 hj).2 (hdiag j hd)

end Categorification.Stendhal.RedBlock

namespace Categorification.Stendhal.RedBlock

open Categorification.TypeA

variable {I : Type} {ℓ : ℕ}

/-- The leading shuffle assignment at a right ascent is injective on supported inputs.
An internal leading index retains its input block ownership; an external leading
index still comes from two different blocks. -/
theorem rightAscentLeading_injective (row : List (RedBlock I ℓ)) {ι : Type*}
    {src : ι → ShuffleIndex row} (hsrc : Function.Injective src) (lead : ι → ShuffleIndex row)
    (j : ℕ) (hj : j + 1 < (weightSum row).card)
    (ht : ∀ i, (lead i = src i ∧ SameInputBlock row (lead i) j hj) ∨
      (shufflePerm row (lead i) = shufflePerm row (src i) * sadj _ j ∧
        ¬ SameInputBlock row (lead i) j hj)) : Function.Injective lead := by
  intro i i' he
  rcases ht i with ⟨local₁, hsame₁⟩ | ⟨ext₁, hdiff₁⟩ <;>
    rcases ht i' with ⟨local₂, hsame₂⟩ | ⟨ext₂, hdiff₂⟩
  · exact hsrc (local₁.symm.trans (he.trans local₂))
  · exact (hdiff₂ (he ▸ hsame₁)).elim
  · exact (hdiff₁ (he.symm ▸ hsame₂)).elim
  · have h := congrArg (shufflePerm row) he
    rw [ext₁, ext₂] at h
    exact hsrc (shufflePerm_injective row (mul_right_cancel h))

variable {k A : Type*} [CommRing k] [Ring A] [Algebra k A]

/-- A leading row-shuffle map with injective diagonal multipliers separates
the supported coefficients. The remaining terms may have any coefficients
strictly below the leading degree. -/
theorem injective_sum_of_rightAscentCoordinates
    (row : List (RedBlock I ℓ)) {n : ℕ} (index : Fin n ≃ ShuffleIndex row)
    {ι : Type*} [Fintype ι] (src : ι ↪ Fin n) (lead : ι → Fin n)
    (j : ℕ) (hj : j + 1 < (weightSum row).card)
    (M : ι → Submodule k A) (C : ι → Fin n → A)
    (ht : ∀ i, (lead i = src i ∧ SameInputBlock row (index (lead i)) j hj) ∨
      (shufflePerm row (index (lead i)) = shufflePerm row (index (src i)) * sadj _ j ∧
        ¬ SameInputBlock row (index (lead i)) j hj))
    (hlen : ∀ i, (shuffleWord row (index (src i))).length ≤ (shuffleWord row (index (lead i))).length)
    (herror : ∀ i d, ((shuffleWord row (index (src i))).length ≤ 1 ∨
      (shuffleWord row (index (src i))).length - 2 < (shuffleWord row (index d)).length) →
      d ≠ lead i → C i d = 0)
    (hdiag : ∀ i, Function.Injective (fun x : M i => (x : A) * C i (lead i))) :
    Function.Injective (fun x : ∀ i, M i => fun d => ∑ i, (x i : A) * C i d) := by
  have hi : Function.Injective lead := by
    apply Function.Injective.of_comp (f := index)
    apply rightAscentLeading_injective row (index.injective.comp src.injective) _ j hj
    intro i
    rcases ht i with ⟨h, hm⟩ | he
    · exact Or.inl ⟨congrArg index h, hm⟩
    · exact Or.inr he
  let T : ∀ i, Fin n → M i →ₗ[k] A := fun i d =>
    (LinearMap.mulRight k (C i d)).comp (M i).subtype
  apply injective_sum_of_leading_coordinates
    (fun i => (shuffleWord row (index (lead i))).length) lead T hdiag
  intro i i' hne hle
  have valid : (shuffleWord row (index (src i))).length ≤ 1 ∨
      (shuffleWord row (index (src i))).length - 2 < (shuffleWord row (index (lead i'))).length := by
    have h := hlen i
    omega
  have hz := herror i (lead i') valid (fun he => hne (hi he.symm))
  ext x
  change (x : A) * C i (lead i') = 0
  rw [hz, mul_zero]

end Categorification.Stendhal.RedBlock
