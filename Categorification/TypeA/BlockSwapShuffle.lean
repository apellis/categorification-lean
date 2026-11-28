/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TypeA.DoubleCoset

/-!
# The shuffle that moves a whole block across the other

For the top blocks `(m, N)` and the bottom blocks `(N, m)` of `S_M`, `M = m + N`, the double coset
of `(S_m × S_N) \ S_M / (S_N × S_m)` with `m` crossing strands consists of the permutations
taking the last `m` bottom positions to the first `m` top positions. Its minimal representative
`w_L` moves the second bottom block across the first one. This file shows that a minimal left
coset representative (`IsShuffle`) with `crossCount m N u = m` is already a minimal double coset
representative, hence is `w_L` (`isDoubleShuffle_of_crossCount_eq`, `eq_of_crossCount_eq`).

This is the input of Webster, arXiv:1309.3796v3, proof of Lemma 7.19, (IC), that the summand
`D ψ_{w_L}` of the left coset decomposition of `e_L T̃ e_R` is a single summand.
-/

namespace Categorification.TypeA

open Equiv Finset

variable {m N M : ℕ} (hM : m + N = M) (hK : N + m = M)

private theorem card_ge (p : ℕ) (hp : p ≤ M) :
    (univ.filter fun q : Fin M => p ≤ q.val).card = M - p := by
  have h1 := Finset.card_filter_add_card_filter_not (s := univ)
    (fun q : Fin M => q.val < p)
  have h2 : (univ.filter fun q : Fin M => q.val < p).card = p := by
    rw [Fin.card_filter_val_lt]; omega
  simp only [not_lt, card_univ, Fintype.card_fin] at h1
  omega

private theorem card_lt_image (u : Perm (Fin M)) (n : ℕ) (hn : n ≤ M) :
    (univ.filter fun q : Fin M => (u q).val < n).card = n := by
  rw [Finset.card_filter, Equiv.sum_comp u (fun x : Fin M => if x.val < n then 1 else 0),
    ← Finset.card_filter, Fin.card_filter_val_lt]
  omega

include hM in
/-- With `m` crossing strands, every strand starting at a bottom position `≥ N` ends at a top
position `< m`. -/
theorem lt_of_crossCount_eq {u : Perm (Fin M)} (hc : crossCount m N u = m) {p : Fin M}
    (hp : N ≤ p.val) : (u p).val < m := by
  by_contra hup
  have hsub : (univ.filter fun q : Fin M => N ≤ q.val ∧ (u q).val < m) ⊆
      (univ.filter fun q : Fin M => N ≤ q.val).erase p := by
    intro q hq
    simp only [mem_filter, mem_univ, true_and] at hq
    refine mem_erase.2 ⟨fun h => hup (h ▸ hq.2), by simpa using hq.1⟩
  have h1 := card_le_card hsub
  rw [card_erase_of_mem (by simpa using hp), card_ge N (by omega)] at h1
  change crossCount m N u ≤ _ at h1
  omega

include hM in
/-- With `m` crossing strands, every strand starting at a bottom position `< N` ends at a top
position `≥ m`. -/
theorem le_of_crossCount_eq {u : Perm (Fin M)} (hc : crossCount m N u = m) {p : Fin M}
    (hp : p.val < N) : m ≤ (u p).val := by
  by_contra hup
  have hnot : p ∉ univ.filter fun q : Fin M => N ≤ q.val ∧ (u q).val < m := by
    simp only [mem_filter, mem_univ, true_and, not_and]
    intro h; omega
  have hsub : insert p (univ.filter fun q : Fin M => N ≤ q.val ∧ (u q).val < m) ⊆
      univ.filter fun q : Fin M => (u q).val < m := by
    intro q hq
    rcases mem_insert.1 hq with rfl | hq
    · simp only [mem_filter, mem_univ, true_and]; omega
    · simp only [mem_filter, mem_univ, true_and] at hq ⊢; exact hq.2
  have h1 := card_le_card hsub
  rw [card_insert_of_notMem hnot, card_lt_image u m (by omega)] at h1
  change crossCount m N u + 1 ≤ _ at h1
  omega

include hM hK in
/-- **A shuffle with `m` crossing strands is a minimal double coset representative.** -/
theorem isDoubleShuffle_of_crossCount_eq {u : Perm (Fin M)} (hu : IsShuffle hM u)
    (hc : crossCount m N u = m) : IsDoubleShuffle hM hK u := by
  refine ⟨hu, (isShuffle_iff_forall hK).2 fun j hj hb => ?_⟩
  simp only [inv_inv]
  set p : Fin M := ⟨j, by omega⟩
  set q : Fin M := ⟨j + 1, hj⟩
  have hxy : (u p).val < m ↔ (u q).val < m := by
    rcases hb with hb | hb
    · have h1 := le_of_crossCount_eq hM hc (p := p) (by simp [p]; omega)
      have h2 := le_of_crossCount_eq hM hc (p := q) hb
      omega
    · have h1 := lt_of_crossCount_eq hM hc (p := p) hb
      have h2 := lt_of_crossCount_eq hM hc (p := q) (by simp [q]; omega)
      omega
  have := hu.inv_lt_inv_iff hM hxy
  have e1 : u⁻¹ (u p) = p := by simp
  have e2 : u⁻¹ (u q) = q := by simp
  rw [e1, e2] at this
  exact this.1 (by simp [p, q, Fin.lt_def])

include hM hK in
/-- **The shuffle with `m` crossing strands is unique**: it is the minimal double coset
representative `w_L`. -/
theorem eq_of_crossCount_eq {u d : Perm (Fin M)} (hu : IsShuffle hM u)
    (hc : crossCount m N u = m) (hd : IsDoubleShuffle hM hK d) (hcd : crossCount m N d = m) :
    u = d :=
  ((isDoubleShuffle_of_crossCount_eq hM hK hu hc).eq_of_crossCount_eq hM hK hd
    (hc.trans hcd.symm))

end Categorification.TypeA
