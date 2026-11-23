/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TypeA.ExitsPrefix

/-!
# Red crossings supported on the interval between the two red strands

For the adjacent block of Webster, arXiv:1309.3796v2, §6.1, Lemma 6.8, one needs a
factor of a reduced diagram which performs the red crossing without changing any exterior
block boundary. The prefix exit of `ExitsPrefix` fixes the suffix as well: its predecessors
are all strictly before the second red strand. Thus it and its final red crossing are
supported on the closed interval between the two red strands.
-/

namespace Categorification.TypeA

open Equiv

variable {m : ℕ} {τ : Perm (Fin m)} {R : Finset (Fin m)} {q p : Fin m}

private theorem lt_of_mem_prefixSet (hqp : q < p) {t : Fin m}
    (ht : t ∈ prefixSet τ R q p) : t < p := by
  classical
  rcases Finset.mem_union.1 ht with h | h
  · rcases (Finset.mem_filter.1 h).2.2.2 with h | h
    · exact (lt_of_transGen_prec h).trans hqp
    · exact lt_of_transGen_prec h
  · exact ((Finset.mem_filter.1 h).2).trans hqp

private theorem setPerm_prefixSet_of_gt (hqp : q < p) {t : Fin m} (ht : p < t) :
    setPerm q p (prefixSet τ R q p) t = t := by
  let A := prefixSet τ R q p
  have hclass : ∀ s, p < s → setClass q p A s = 4 := by
    intro s hs
    have hnot : s ∉ A := fun h => (lt_asymm hs (lt_of_mem_prefixSet hqp h))
    simp [setClass, hnot, (hqp.trans hs).ne', hs.ne']
  have key : (Finset.univ.filter fun s =>
      classKey (setClass q p A) s < classKey (setClass q p A) t) = Finset.Iio t := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, classKey_lt_iff,
      Finset.mem_Iio, hclass t ht]
    by_cases hs : p < s
    · simp [hclass s hs]
    · have hst := lt_of_le_of_lt (not_lt.mp hs) ht
      simp only [setClass, hst, and_true, iff_true]
      split_ifs <;> decide
  apply Fin.ext
  change (classPerm (setClass q p A) t : ℕ) = t
  rw [classPerm_val, rankNat, key, Fin.card_Iio]

/-- A permutation that fixes the complement of `[q,p]` maps `[q,p]` into itself. -/
theorem mem_Icc_of_perm_fix_outside {v : Perm (Fin m)}
    (hfix : ∀ t, t < q ∨ p < t → v t = t) {t : Fin m} (ht : t ∈ Set.Icc q p) :
    v t ∈ Set.Icc q p := by
  have h : ¬ (v t < q ∨ p < v t) := fun h => by
    have he := v.injective (hfix (v t) h)
    rw [he] at h
    exact h.elim (not_lt.mpr ht.1) (not_lt.mpr ht.2)
  exact ⟨not_lt.mp (fun hl => h (.inl hl)), not_lt.mp (fun hr => h (.inr hr))⟩

/-- **Interval-supported red crossing** (Webster, arXiv:1309.3796v2, proof of Lemma 6.8).
For adjacent red strands inverted by `τ`, a reduced factor of `τ` crosses that red pair alone
and fixes every position strictly outside the interval of the pair. -/
theorem exists_isSwapBelow_interval (hqp : q < p) (hT : (q, p) ∈ invSet m τ)
    (hcons : ∀ t ∈ R, q < t → t < p → False) :
    ∃ v, IsSwapBelow τ R q p v ∧ ∀ t, t < q ∨ p < t → v t = t := by
  let e := setPerm q p (prefixSet τ R q p)
  have he : IsExit τ R q p e := isExit_setPerm hqp hT (isValid_prefixSet hqp hT hcons)
  have hfix : ∀ t, t < q ∨ p < t → e t = t := fun _ ht =>
    ht.elim setPerm_prefixSet_of_lt (setPerm_prefixSet_of_gt hqp)
  have hq := mem_Icc_of_perm_fix_outside hfix (t := q) ⟨le_rfl, hqp.le⟩
  have hp := mem_Icc_of_perm_fix_outside hfix (t := p) ⟨hqp.le, le_rfl⟩
  have hadj := he.adj
  have hx : (e q : ℕ) + 1 < m := by have := (e p).isLt; omega
  refine ⟨_, he.isSwapBelow hqp hT hx, fun t ht => ?_⟩
  rw [Perm.mul_apply, hfix _ ht]
  apply sadj_apply_of_ne
  · intro h
    exact ht.elim (fun hl => hl.not_ge (Fin.ext h ▸ hq.1))
      (fun hr => hr.not_ge (Fin.ext h ▸ hq.2))
  · intro h
    have htp : t = e p := Fin.ext (h.trans hadj.symm)
    exact ht.elim (fun hl => hl.not_ge (htp ▸ hp.1)) (fun hr => hr.not_ge (htp ▸ hp.2))

end Categorification.TypeA
