/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidedFactorizationGeneral

/-!
# The length condition of Webster's Lemma 6.5 as inversion sets

Webster, arXiv:1309.3796v2, Lemma 6.5 assumes `ℓ(ww') = ℓ(w) + ℓ(w')`. For permutations this
says that every pair of strands crossed by `w'` is still crossed by `ww'`, i.e. the inversion
set of `w'` is contained in that of `ww'`. In the red-word model with `κ₁ = w' κ₀` and
`κ₂ = w κ₁`, where `κ₀` has no repeated labels, this reads: every pair of labels that `κ₀` reads
as `x, y` and `κ₁` reads as `y, x` is also read as `y, x` by `κ₂`.

We show that this condition produces a `RedCrossingPath` from `κ₀` to `κ₁` (bubble sort, one
inverted adjacent pair at a time), so Lemma 6.5 holds under it.

## Main results

* `BraidedStendhalAlgebra.redCrossingPath_of_inversions`: the inversion-set condition gives a
  path of red crossings.
* `BraidedStendhalAlgebra.tensorMult_bijective_of_inversions`: Lemma 6.5 under the
  inversion-set form of the length condition.
-/

namespace Categorification.Stendhal

open scoped List

namespace RedWord

variable {α : Type*}

theorem pair_sublist_cons {x y c : α} {t : List α} :
    [x, y] <+ c :: t ↔ [x, y] <+ t ∨ (x = c ∧ y ∈ t) := by
  simp [List.sublist_cons_iff]

theorem pair_sublist_append {x y : α} {L R : List α} :
    [x, y] <+ L ++ R ↔ [x, y] <+ L ∨ [x, y] <+ R ∨ (x ∈ L ∧ y ∈ R) := by
  induction L with
  | nil => simp
  | cons c t ih =>
    rw [List.cons_append, pair_sublist_cons, pair_sublist_cons, ih, List.mem_append,
      List.mem_cons]
    constructor
    · rintro ((h | h | ⟨hx, hy⟩) | ⟨rfl, hy | hy⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨Or.inr hx, hy⟩)
      · exact Or.inl (Or.inr ⟨rfl, hy⟩)
      · exact Or.inr (Or.inr ⟨Or.inl rfl, hy⟩)
    · rintro ((h | ⟨rfl, hy⟩) | h | ⟨hx | hx, hy⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inr ⟨rfl, Or.inl hy⟩
      · exact Or.inl (Or.inr (Or.inl h))
      · exact Or.inr ⟨hx, Or.inr hy⟩
      · exact Or.inl (Or.inr (Or.inr ⟨hx, hy⟩))

/-- A list without repetitions does not read two distinct labels in both orders. -/
theorem eq_of_pair_sublist_of_pair_sublist {x y : α} {l : List α} (hl : l.Nodup)
    (h : [x, y] <+ l) (h' : [y, x] <+ l) : x = y := by
  induction l with
  | nil => simp at h
  | cons c t ih =>
    rw [List.nodup_cons] at hl
    rw [pair_sublist_cons] at h h'
    rcases h with h | ⟨rfl, hy⟩ <;> rcases h' with h' | ⟨rfl, hx⟩
    · exact ih hl.2 h h'
    · exact absurd (h.subset (by simp)) hl.1
    · exact absurd (h'.subset (by simp)) hl.1
    · rfl

/-- Exchanging an adjacent pair `a, b` changes only the relative order of `a` and `b`. -/
theorem pair_sublist_of_swap {x y a b : α} {L M : List α} (h : [x, y] <+ L ++ b :: a :: M)
    (hne : ¬(x = b ∧ y = a)) : [x, y] <+ L ++ a :: b :: M := by
  simp only [pair_sublist_append, pair_sublist_cons, List.mem_cons] at h ⊢
  tauto

/-- Two different arrangements of the same labels differ at some adjacent pair: some adjacent
pair `a, b` of `κ₀` is read as `b, a` by `κ₁`. -/
theorem exists_adjacent_inversion {κ₀ κ₁ : List α} (h0 : κ₀.Nodup) (hp : κ₀.Perm κ₁)
    (hne : κ₀ ≠ κ₁) : ∃ L a b M, κ₀ = L ++ a :: b :: M ∧ [b, a] <+ κ₁ := by
  induction κ₀ generalizing κ₁ with
  | nil => exact absurd (List.Perm.nil_eq hp) hne
  | cons c t ih =>
    obtain _ | ⟨d, t'⟩ := κ₁
    · exact absurd hp.length_eq (by simp)
    by_cases hcd : c = d
    · subst hcd
      have ht : t ≠ t' := fun h => hne (h ▸ rfl)
      obtain ⟨L, a, b, M, rfl, hba⟩ :=
        ih (List.nodup_cons.1 h0).2 ((List.perm_cons c).1 hp) ht
      exact ⟨c :: L, a, b, M, rfl, hba.cons c⟩
    · have hd : d ∈ t := by
        have := hp.mem_iff.2 (List.mem_cons_self (a := d) (l := t'))
        rcases List.mem_cons.1 this with h | h
        · exact absurd h.symm hcd
        · exact h
      obtain ⟨P, Q, rfl⟩ := List.append_of_mem hd
      obtain h | ⟨R, e, hR⟩ := List.eq_nil_or_concat (c :: P)
      · simp at h
      rw [List.concat_eq_append] at hR
      have hκ : c :: (P ++ d :: Q) = R ++ e :: d :: Q := by
        rw [← List.cons_append, hR, List.append_assoc]; rfl
      refine ⟨R, e, d, Q, hκ, ?_⟩
      have he : e ∈ d :: t' := hp.mem_iff.1 (by rw [hκ]; simp)
      have hed : e ≠ d := by
        rw [hκ] at h0
        have := (List.nodup_append.1 h0).2.1
        exact fun h => (List.nodup_cons.1 this).1 (by simp [h])
      rcases List.mem_cons.1 he with h | h
      · exact absurd h hed
      · exact List.cons_sublist_cons.2 (List.singleton_sublist.2 h)

end RedWord

open RedWord

namespace BraidedStendhalAlgebra

variable {ℓ : ℕ}

/-- The pairs of labels that `κ₀` reads as `x, y` and `κ₁` reads as `y, x`. -/
def inversions (κ₀ κ₁ : List (Fin ℓ)) : Finset (Fin ℓ × Fin ℓ) :=
  Finset.univ.filter fun p => [p.1, p.2] <+ κ₀ ∧ [p.2, p.1] <+ κ₁

theorem redCrossingPath_of_inversions_aux {κ₂ κ₁ : List (Fin ℓ)} (n : ℕ) :
    ∀ κ₀ : List (Fin ℓ), (inversions κ₀ κ₁).card = n → κ₀.Nodup → κ₀.Perm κ₁ →
      (∀ x y, [x, y] <+ κ₀ → [y, x] <+ κ₁ → [y, x] <+ κ₂) → RedCrossingPath κ₂ κ₁ κ₀ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro κ₀ hn h0 hp H
  by_cases he : κ₀ = κ₁
  · subst he; exact .refl
  obtain ⟨L, a, b, M, rfl, hba⟩ := exists_adjacent_inversion h0 hp he
  have hab : a ≠ b := by
    have := (List.nodup_append.1 h0).2.1
    exact fun h => (List.nodup_cons.1 this).1 (by simp [h])
  have hp' : (L ++ b :: a :: M).Perm (L ++ a :: b :: M) :=
    List.Perm.append_left L (List.Perm.swap a b M)
  have h0' := h0.perm hp'.symm
  have h1 := h0.perm hp
  -- the swapped pair `b, a` is not inverted again
  have hnot : ∀ x y, [y, x] <+ κ₁ → ¬(x = b ∧ y = a) := by
    rintro x y hyx ⟨rfl, rfl⟩
    exact hab (eq_of_pair_sublist_of_pair_sublist h1 hyx hba)
  have hab0 : [a, b] <+ L ++ a :: b :: M := by
    simp
  refine .cross rfl rfl hba (H a b hab0 hba) (ih _ ?_ _ rfl h0' (hp'.trans hp) ?_)
  · rw [← hn]
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨(a, b), ?_, ?_⟩
      · simp [inversions, hab0, hba]
      · simp only [inversions, Finset.mem_filter, Finset.mem_univ, true_and, not_and]
        intro h
        have : [b, a] <+ L ++ b :: a :: M := by
          simp
        exact fun _ => hab (eq_of_pair_sublist_of_pair_sublist h0' h this)
    · intro p hp
      simp only [inversions, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact ⟨pair_sublist_of_swap hp.1 (hnot _ _ hp.2), hp.2⟩
  · intro x y hxy hyx
    exact H x y (pair_sublist_of_swap hxy (hnot _ _ hyx)) hyx

/-- The inversion-set form of the length condition of Webster's Lemma 6.5 gives a path of red
crossings: if `κ₀` has no repeated labels, `κ₁` rearranges `κ₀`, and every pair of labels
crossed from `κ₀` to `κ₁` is still crossed in `κ₂`, then `κ₁` is reached from `κ₀` by
adjacent crossings of pairs that `κ₁` and `κ₂` both read in the crossed order. -/
theorem redCrossingPath_of_inversions {κ₂ κ₁ κ₀ : List (Fin ℓ)} (h0 : κ₀.Nodup)
    (hp : κ₀.Perm κ₁) (H : ∀ x y, [x, y] <+ κ₀ → [y, x] <+ κ₁ → [y, x] <+ κ₂) :
    RedCrossingPath κ₂ κ₁ κ₀ :=
  redCrossingPath_of_inversions_aux _ κ₀ rfl h0 hp H

open KLR TypeA

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
  {ρ : Equiv.Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}

/-- **Webster, Lemma 6.5** (arXiv:1309.3796v2) with the length condition
`ℓ(ww') = ℓ(w) + ℓ(w')` in inversion-set form: multiplication
`B̃(κ₂, κ₁) ⊗ B̃(κ₁, κ₀) → B̃(κ₂, κ₀)` is bijective when every pair of red strands crossed from
`κ₀` to `κ₁` is still crossed in `κ₂`. -/
theorem tensorMult_bijective_of_inversions (hρ : IsReducedChoice ρ) (hQ : KLRSymm Q)
    {κ₂ κ₁ κ₀ : List (Fin ℓ)} (h0 : κ₀.Nodup) (hp : κ₀.Perm κ₁)
    (H : ∀ x y, [x, y] <+ κ₀ → [y, x] <+ κ₁ → [y, x] <+ κ₂) :
    Function.Bijective (tensorMult k Q Λ ν κ₂ κ₁ κ₀) :=
  tensorMult_bijective_of_path hρ hQ (redCrossingPath_of_inversions h0 hp H)

end BraidedStendhalAlgebra

end Categorification.Stendhal
