/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TypeA.NormalForm
import Categorification.TypeA.WeakOrder

namespace Categorification.TypeA
open Equiv

/-- The reduced four-slot exits exchanging the endpoints, with the two
intervening strands retained in both relative orders at the middle exit. -/
def fourSlotExitWords : List (List ℕ) := [[2, 1, 0], [1, 2, 0], [0, 1, 2], [1, 2, 0, 1]]

private theorem fourSlotExit_cover_checked :
    ∀ w : Perm (Fin 4), w 3 < w 0 →
      ∃ ρ ∈ fourSlotExitWords, invSet 4 (wordProd 4 ρ) ⊆ invSet 4 w := by
  decide +kernel

theorem fourSlotExitWords_reduced :
    ∀ ρ ∈ fourSlotExitWords, IsReduced 4 ρ ∧
      (wordProd 4 ρ 0 : ℕ) = (wordProd 4 ρ 3 : ℕ) + 1 := by
  intro ρ hρ
  simp only [fourSlotExitWords, List.mem_cons, List.not_mem_nil, or_false] at hρ
  rcases hρ with rfl | rfl | rfl | rfl <;>
    refine ⟨⟨by simp [ValidWord], ?_⟩, by decide +kernel⟩ <;>
    rw [length_eq_invCount] <;> decide +kernel

/-- The four exits are pairwise incomparable in the right weak order. -/
theorem fourSlotExitWords_incomparable (ρ σ : List ℕ)
    (hρ : ρ ∈ fourSlotExitWords) (hσ : σ ∈ fourSlotExitWords)
    (h : invSet 4 (wordProd 4 ρ) ⊆ invSet 4 (wordProd 4 σ)) : ρ = σ := by
  simp only [fourSlotExitWords, List.mem_cons, List.not_mem_nil, or_false] at hρ hσ
  rcases hρ with rfl | rfl | rfl | rfl <;> rcases hσ with rfl | rfl | rfl | rfl
  all_goals
    first | rfl | exact False.elim ((by decide +kernel : ¬ _) h)

/-- Every permutation exchanging the endpoint red strands of a four-slot
interval has a reduced expression ending in one of the four exits. -/
theorem exists_fourSlotExit_reduced_suffix (w : Perm (Fin 4)) (hw : w 3 < w 0) :
    ∃ ρ ∈ fourSlotExitWords,
      IsReduced 4 (canWord 4 (w * (wordProd 4 ρ)⁻¹) ++ ρ) ∧
      wordProd 4 (canWord 4 (w * (wordProd 4 ρ)⁻¹) ++ ρ) = w := by
  obtain ⟨ρ, hρ, hs⟩ := fourSlotExit_cover_checked w hw
  have hred := (fourSlotExitWords_reduced ρ hρ).1
  have hprod : wordProd 4 (canWord 4 (w * (wordProd 4 ρ)⁻¹) ++ ρ) = w := by
    rw [wordProd_append, wordProd_canWord, inv_mul_cancel_right]
  refine ⟨ρ, hρ, ⟨validWord_append.2 ⟨validWord_canWord _ _, hred.1⟩, ?_⟩, hprod⟩
  rw [List.length_append, length_canWord, hred.2, hprod]
  exact length_add_of_invSet_subset hs

end Categorification.TypeA
