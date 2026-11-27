/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicStandardProjectiveFiltration

/-!
# The word of a loading

The word of a sequence `s` of weight `ν` is the list `s₁ … sₙ` of its labels, read from left
to right. This file computes the words of the loadings obtained by appending a black strand at
the right (`appendBlackLoading`) or a new last red strand (`appendRedLoading`), and of a
transported sequence (`Seq.cast`). These words describe the terms of the projective resolution
of Webster's Proposition 7.6 (arXiv:1309.3796v3, §7.1).

## Main definitions and results

* `KLR.Seq.word`: the word of a sequence.
* `KLR.Seq.word_cast`, `KLR.Seq.word_append`, `KLR.Seq.word_map`.
* `Stendhal.seqWord_appendBlackLoading`, `Stendhal.seqWord_appendRedLoading`.
-/

namespace Categorification

namespace KLR.Seq

variable {α : Type*} {ν ν' : Multiset α}

/-- The word of a sequence: its labels from left to right. -/
def word (s : Seq ν) : List α := List.ofFn s.1

@[simp] theorem length_word (s : Seq ν) : s.word.length = Multiset.card ν := List.length_ofFn

@[simp] theorem word_cast (h : ν = ν') (s : Seq ν) : (Seq.cast h s).word = s.word := by
  subst h; rfl

theorem word_append (s : Seq ν) (t : Seq ν') : (s.append t).word = s.word ++ t.word := by
  apply List.ext_getElem
  · simp [word]
  · intro n h₁ h₂
    simp only [word, List.getElem_ofFn]
    by_cases hn : n < Multiset.card ν
    · rw [List.getElem_append_left (by simpa using hn), List.getElem_ofFn,
        Seq.append_apply_lt _ _ _ hn]
    · rw [List.getElem_append_right (by simpa using hn), List.getElem_ofFn,
        Seq.append_apply_ge _ _ _ (le_of_not_gt hn)]
      simp

theorem word_map {β : Type*} (f : α → β) (s : Seq ν) : (Seq.map f s).word = s.word.map f := by
  simp only [word, Seq.map, List.map_ofFn]
  exact (List.ofFn_congr (Multiset.card_map f ν).symm (f ∘ s.1)).symm

theorem word_singleton (a : α) (s : Seq ({a} : Multiset α)) : s.word = [a] := by
  apply List.ext_getElem
  · simp
  · intro n h₁ h₂
    simp only [word, List.getElem_ofFn, List.getElem_singleton]
    exact Multiset.mem_singleton.mp (s.mem _)

end KLR.Seq

namespace Stendhal

open KLR

variable {I : Type*} {ℓ : ℕ}

theorem seqWord_appendBlackLoading (i : I) (ν : Multiset I) (s : Seq (stendhalWeight ℓ ν)) :
    (appendBlackLoading i ν s).word = s.word ++ [Sum.inl i] := by
  rw [appendBlackLoading, Seq.word_cast, Seq.word_append, Seq.word_singleton]

theorem seqWord_appendRedLoading {ν : Multiset I} (s : Seq (stendhalWeight ℓ ν)) :
    (appendRedLoading s).word = s.word.map (addRedColor ℓ) ++ [Sum.inr (Fin.last ℓ)] := by
  rw [appendRedLoading, Seq.word_cast, Seq.word_append, Seq.word_map, Seq.word_singleton]

end Stendhal

end Categorification
