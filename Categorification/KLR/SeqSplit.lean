/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.ConcatAssoc
import Categorification.KLR.MackeySubquot

/-!
# Splitting a loading at a position

A loading `s` of a weight `μ` and a position `n ≤ |μ|` give the weights `prefixWt s n` and
`suffixWt s n` of the labels of `s` before and after `n`, with `prefixWt + suffixWt = μ`, and
loadings `prefixSeq`, `suffixSeq` of them whose concatenation is `s`
(`seqCast_append_prefixSeq_suffixSeq`). Used for a top cut `ν | ν'` adapted to a given
loading in the Mackey filtration (Khovanov–Lauda I, arXiv:0803.4121v2, Prop. 2.18), for
Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19.

## Main definitions

* `KLR.Seq.prefixWt`, `KLR.Seq.suffixWt`, `KLR.Seq.prefixSeq`, `KLR.Seq.suffixSeq`.

## Main results

* `KLR.Seq.prefixWt_add_suffixWt`, `KLR.Seq.seqCast_append_prefixSeq_suffixSeq`.
-/

namespace Categorification.KLR.Seq

variable {I : Type*} {μ : Multiset I} (s : Seq μ) (n : ℕ) (hn : n ≤ Multiset.card μ)

/-- The weight of the labels of `s` at the positions `< n`. -/
def prefixWt : Multiset I := Finset.univ.val.map fun a : Fin n => s.1 (Fin.castLE hn a)

/-- The weight of the labels of `s` at the positions `≥ n`. -/
def suffixWt : Multiset I :=
  Finset.univ.val.map fun b : Fin (Multiset.card μ - n) => s.1 ⟨n + b.val, by omega⟩

theorem card_prefixWt : Multiset.card (prefixWt s n hn) = n := by
  simp [prefixWt]

theorem card_suffixWt : Multiset.card (suffixWt s n hn) = Multiset.card μ - n := by
  simp [suffixWt]

theorem prefixWt_add_suffixWt : prefixWt s n hn + suffixWt s n hn = μ := by
  let e : Fin n ⊕ Fin (Multiset.card μ - n) ≃ Fin (Multiset.card μ) :=
    finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' hn))
  have h1 : Finset.univ.val.map (s.1 ∘ e) = μ := by
    rw [← Multiset.map_map, Multiset.map_univ_val_equiv, s.2]
  refine Eq.trans ?_ h1
  rw [← Finset.univ_disjSum_univ, Finset.val_disjSum, Multiset.disjSum, Multiset.map_add,
    Multiset.map_map, Multiset.map_map]
  congr 1

/-- The loading of `prefixWt s n` given by the labels of `s` before `n`. -/
def prefixSeq : Seq (prefixWt s n hn) :=
  ⟨fun a => s.1 (Fin.castLE hn (Fin.cast (card_prefixWt s n hn) a)), by
    exact (Multiset.map_map (fun a : Fin n => s.1 (Fin.castLE hn a)) _ _).symm.trans
      (congrArg (Multiset.map _) (Multiset.map_univ_val_equiv (finCongr (card_prefixWt s n hn))))⟩

/-- The loading of `suffixWt s n` given by the labels of `s` after `n`. -/
def suffixSeq : Seq (suffixWt s n hn) :=
  ⟨fun b => s.1 ⟨n + (Fin.cast (card_suffixWt s n hn) b).val, by
    have := (Fin.cast (card_suffixWt s n hn) b).2; omega⟩, by
    exact (Multiset.map_map (fun b : Fin (Multiset.card μ - n) => s.1 ⟨n + b.val, by omega⟩)
      _ _).symm.trans (congrArg (Multiset.map _)
        (Multiset.map_univ_val_equiv (finCongr (card_suffixWt s n hn))))⟩

theorem prefixSeq_apply (a : Fin (Multiset.card (prefixWt s n hn))) :
    (prefixSeq s n hn).1 a = s.1 ⟨a.val, by
      have := a.2; have h' := card_prefixWt s n hn; omega⟩ :=
  congrArg s.1 (Fin.ext rfl)

theorem suffixSeq_apply (b : Fin (Multiset.card (suffixWt s n hn))) :
    (suffixSeq s n hn).1 b = s.1 ⟨n + b.val, by
      have := b.2; have h' := card_suffixWt s n hn; omega⟩ :=
  congrArg s.1 (Fin.ext rfl)

/-- **A loading is the concatenation of its prefix and suffix.** -/
theorem seqCast_append_prefixSeq_suffixSeq :
    KLRAlgebra.seqCast (prefixWt_add_suffixWt s n hn)
      ((prefixSeq s n hn).append (suffixSeq s n hn)) = s := by
  apply Subtype.ext
  funext x
  rw [KLR.seqCast_apply]
  by_cases hx : x.val < n
  · rw [append_apply_lt _ _ _ (by simpa [card_prefixWt] using hx), prefixSeq_apply]
    exact congrArg s.1 (Fin.ext rfl)
  · rw [append_apply_ge _ _ _ (by simpa [card_prefixWt] using hx), suffixSeq_apply]
    exact congrArg s.1 (Fin.ext (by simp [card_prefixWt]; omega))

end Categorification.KLR.Seq
