/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TypeA.SwapConnected

/-!
# Exits fixing the strands left of a crossing

Let `q < p` be consecutive red strands crossing in `τ`. Among the exits of `τ` for `q, p`
(`TypeA.IsExit`) there is one fixing every strand to the left of `q`: list those strands first,
then the strands that must be moved left of `q`, then `q` and `p`. The swap-below permutation
built from it (`TypeA.IsExit.isSwapBelow`) fixes the same strands.

This is used for the quotient bimodules `B_w` of Webster, arXiv:1309.3796v2, §6: the frames of
Lemma 6.5 can be chosen not to move a black strand at the left edge, so that they preserve
violated idempotents.

## Main results

* `TypeA.exists_isSwapBelow_fix` : a swap-below permutation fixing the strands left of `q`.
-/

namespace Categorification.TypeA

open Equiv

variable {m : ℕ}

section Prefix

variable (τ : Perm (Fin m)) (R : Finset (Fin m)) (q p : Fin m)

/-- The smallest valid set together with all strands left of `q`. -/
noncomputable def prefixSet : Finset (Fin m) :=
  minSet τ R q p ∪ Finset.univ.filter (· < q)

variable {τ R q p}

theorem isValid_prefixSet (hqp : q < p) (hT : (q, p) ∈ invSet m τ)
    (hcons : ∀ t ∈ R, q < t → t < p → False) : IsValid τ R q p (prefixSet τ R q p) := by
  have hA := isValid_minSet hqp hT hcons
  refine ⟨?_, ?_, fun u v huv hbad hv => ?_⟩
  · simp [prefixSet, hA.q_notMem]
  · simp [prefixSet, hA.p_notMem, hqp.le]
  · simp only [prefixSet, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    by_cases hvq : v < q
    · exact Or.inr (huv.trans hvq)
    · refine Or.inl (hA.closed u v huv hbad ?_)
      rcases hv with (h | h) | h | h
      · exact Or.inl h
      · exact absurd h hvq
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)

theorem setPerm_prefixSet_of_lt {t : Fin m} (ht : t < q) :
    setPerm q p (prefixSet τ R q p) t = t := by
  have htA : t ∈ prefixSet τ R q p := by simp [prefixSet, ht]
  have key : (Finset.univ.filter fun s =>
      classKey (setClass q p (prefixSet τ R q p)) s <
        classKey (setClass q p (prefixSet τ R q p)) t) = Finset.Iio t := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, classKey_lt_iff, Finset.mem_Iio]
    simp only [setClass, htA, ite_true]
    constructor
    · rintro (h | ⟨-, h⟩)
      · omega
      · exact h
    · intro hs
      have hsA : s ∈ prefixSet τ R q p := by simp [prefixSet, hs.trans ht]
      exact Or.inr ⟨by simp [hsA], hs⟩
  ext
  rw [setPerm, classPerm_val, rankNat, key, Fin.card_Iio]

/-- **A swap-below permutation fixing the strands left of `q`.** -/
theorem exists_isSwapBelow_fix (hqp : q < p) (hT : (q, p) ∈ invSet m τ)
    (hcons : ∀ t ∈ R, q < t → t < p → False) :
    ∃ v, IsSwapBelow τ R q p v ∧ ∀ t, t < q → v t = t := by
  set e := setPerm q p (prefixSet τ R q p)
  have he : IsExit τ R q p e := isExit_setPerm hqp hT (isValid_prefixSet hqp hT hcons)
  have hx : (e q : ℕ) + 1 < m := by have := he.adj; have := (e p).2; omega
  have hfix : ∀ t, t < q → e t = t := fun t ht => setPerm_prefixSet_of_lt ht
  have hq : (q : ℕ) ≤ e q := by
    by_contra h
    have h' : e q < q := by rw [Fin.lt_def]; omega
    have := hfix _ h'
    exact (lt_irrefl _) (by rwa [e.injective this] at h')
  refine ⟨_, he.isSwapBelow hqp hT hx, fun t ht => ?_⟩
  rw [Perm.mul_apply, hfix t ht]
  have : (t : ℕ) < q := ht
  exact sadj_apply_of_ne _ (by omega) (by omega)

end Prefix

end Categorification.TypeA
