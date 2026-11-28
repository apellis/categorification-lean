/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PrependRedStandardDegree
import Categorification.WeightedKLR.RedStrands.TildeLeftRedInduction
import Categorification.WeightedKLR.RedStrands.StandardBlockAction

/-!
# Adding a red strand on the left of the blocks of a root function

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1, for
the comparison of `T̃^λ` with `T^{(λ₀, λ)}` used in the proof of Corollary 5.23. Adding a red
strand `λ₀` on the left of the blocks `b_0, …, b_ℓ` gives the blocks `0, b_0, …, b_ℓ`
(`consBlocks`): the old block `b_j` becomes the block `j + 1`, starting one position later
(`blockStart_consBlocks`). The root function becomes `(0, α)` (`blockRoot_consBlocks`), and the
sequences of root function `(0, α)` are exactly the `λ₀ s` with `s` of root function `α`
(`rootSet_cons`). Hence adding the red strand sends `e_α` to `e_{(0, α)}`
(`prependRedStendhal_rootIdem`).

## Main definitions

* `consBlocks`: the blocks `0, b_0, …, b_ℓ`.

## Main results

* `blockPrefix_consBlocks`, `blockStart_consBlocks`, `blockRoot_consBlocks`.
* `blackCount_prependRedLoading`, `exists_prependRedLoading_of_blackCount_zero`.
* `rootSet_cons`, `prependRedStendhal_rootIdem`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR StendhalAlgebra

section Blocks

variable {I : Type*} {ℓ : ℕ} (b : Fin (ℓ + 1) → Multiset I)

/-- The blocks `0, b_0, …, b_ℓ`: the blocks of `b` after adding a red strand on the left. -/
def consBlocks : Fin (ℓ + 2) → Multiset I := Fin.cons 0 b

theorem consBlocks_zero : consBlocks b ⟨0, Nat.succ_pos _⟩ = 0 := rfl

theorem consBlocks_succ {j : ℕ} (hj : j + 1 < ℓ + 2) :
    consBlocks b ⟨j + 1, hj⟩ = b ⟨j, by omega⟩ := rfl

theorem blockPrefix_consBlocks : ∀ j, blockPrefix (consBlocks b) (j + 1) = blockPrefix b j
  | 0 => by
    rw [blockPrefix_succ (consBlocks b) (by omega), blockPrefix_zero, blockPrefix_zero,
      consBlocks_zero, add_zero]
  | j + 1 => by
    by_cases hj : j < ℓ + 1
    · rw [blockPrefix_succ (consBlocks b) (by omega), blockPrefix_consBlocks j,
        blockPrefix_succ b hj, consBlocks_succ]
    · rw [blockPrefix_of_le _ (by omega), blockPrefix_of_le _ (by omega), Fin.sum_univ_succ]
      exact zero_add _

theorem blockStart_consBlocks (j : ℕ) :
    blockStart (consBlocks b) (j + 1) = blockStart b j + 1 := by
  rw [blockStart, blockStart, blockPrefix_consBlocks]
  omega

theorem blockRoot_consBlocks [DecidableEq I] :
    blockRoot (consBlocks b) = Fin.cons (0 : I → ℕ) (blockRoot b) := by
  funext r i
  cases r using Fin.cases with
  | zero =>
    rw [blockRoot, Fin.val_zero, blockPrefix_consBlocks, blockPrefix_zero]
    rfl
  | succ r =>
    rw [blockRoot, Fin.val_succ, blockPrefix_consBlocks, Fin.cons_succ]
    rfl

end Blocks

section Loadings

variable {I : Type*} [DecidableEq I] {ℓ : ℕ} {ν : Multiset I}

theorem blackCount_prependRedLoading (s : Seq (stendhalWeight ℓ ν)) :
    blackCount (prependRedLoading s) = Fin.cons (0 : I → ℕ) (blackCount s) := by
  funext r i
  cases r using Fin.cases with
  | zero => exact blackCount_prependRedLoading_zero s i
  | succ r => exact blackCount_prependRedLoading_succ s r i

/-- A red-ordered sequence with no black strand left of the first red strand begins with it. -/
theorem lbl_firstPosition_of_blackCount_zero (s' : Seq (stendhalWeight (ℓ + 1) ν))
    (hs' : IsRedOrdered s') (h0 : ∀ i, blackCount s' 0 i = 0) :
    s'.lbl (firstPosition ℓ ν) = .inr 0 := by
  obtain ⟨b0, hb0⟩ := exists_lbl_eq_inr s' 0
  have hlt : ∀ x, s'.lbl (firstPosition ℓ ν) = x → x ≠ .inr 0 → firstPosition ℓ ν < b0 := by
    intro x hx hne
    refine lt_of_le_of_ne (Nat.zero_le _) fun h => hne ?_
    rw [← hx, ← hb0]
    exact congrArg s'.lbl h
  rcases hx : s'.lbl (firstPosition ℓ ν) with i | r
  · exfalso
    have hpos : 0 < blackCount s' 0 i := by
      refine Finset.card_pos.2 ⟨firstPosition ℓ ν, Finset.mem_filter.2 ⟨Finset.mem_univ _, hx,
        fun c hc => ?_⟩⟩
      refine lt_of_le_of_ne (Nat.zero_le _) fun h => ?_
      have : s'.lbl (firstPosition ℓ ν) = s'.lbl c := congrArg s'.lbl h
      rw [hx, hc] at this
      cases this
    exact absurd (h0 i) hpos.ne'
  · by_contra hr
    have hr0 : r ≠ 0 := fun h => hr (by rw [h])
    exact Fin.not_lt_zero _ (hs' _ _ r 0 (hlt _ hx hr) hx hb0)

theorem exists_prependRedLoading_of_blackCount_zero (s' : Seq (stendhalWeight (ℓ + 1) ν))
    (hs' : IsRedOrdered s') (h0 : ∀ i, blackCount s' 0 i = 0) :
    ∃ s, prependRedLoading s = s' :=
  prependRedLoading_surjOn s' (lbl_firstPosition_of_blackCount_zero s' hs' h0)

theorem mem_rootSet_cons_iff (α : Fin ℓ → I → ℕ) (s' : Seq (stendhalWeight (ℓ + 1) ν)) :
    s' ∈ rootSet ν (Fin.cons (0 : I → ℕ) α) ↔ ∃ s ∈ rootSet ν α, prependRedLoading s = s' := by
  constructor
  · intro h
    obtain ⟨hs', hc⟩ := mem_rootSet.1 h
    obtain ⟨s, rfl⟩ := exists_prependRedLoading_of_blackCount_zero s' hs' fun i => by
      rw [hc]; rfl
    refine ⟨s, mem_rootSet.2 ⟨(prependRedLoading_ordered_iff s).1 hs', ?_⟩, rfl⟩
    rw [blackCount_prependRedLoading] at hc
    exact Fin.cons_right_injective _ hc
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨hs1, hs2⟩ := mem_rootSet.1 hs
    exact mem_rootSet.2 ⟨(prependRedLoading_ordered_iff s).2 hs1,
      by rw [blackCount_prependRedLoading, hs2]⟩

/-- The sequences of root function `(0, α)` are the `λ₀ s` with `s` of root function `α`. -/
theorem rootSet_cons (α : Fin ℓ → I → ℕ) :
    rootSet ν (Fin.cons (0 : I → ℕ) α) =
      (rootSet ν α).map ⟨prependRedLoading, prependRedLoading_injective⟩ := by
  ext s'
  rw [mem_rootSet_cons_iff, Finset.mem_map]
  rfl

end Loadings

section Idempotent

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I)

/-- Adding the red strand sends `e_α` to `e_{(0, α)}`. -/
theorem prependRedStendhal_rootIdem (α : Fin ℓ → I → ℕ) :
    prependRedStendhal Q Λ ν (StendhalAlgebra.rootIdem Q (Λ ∘ Fin.succ) α) =
      StendhalAlgebra.rootIdem Q Λ (Fin.cons (0 : I → ℕ) α) := by
  apply Subtype.ext
  change prependRedValue Q Λ ν (∑ s ∈ rootSet ν α, StendhalAlgebraAllOrders.e s) =
    ∑ s ∈ rootSet ν (Fin.cons (0 : I → ℕ) α), StendhalAlgebraAllOrders.e s
  rw [map_sum, rootSet_cons, Finset.sum_map]
  exact Finset.sum_congr rfl fun s _ => prependRedValue_e Q Λ ν s

end Idempotent

end Categorification.Stendhal
