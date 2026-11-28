/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TypeA.BlockSwapShuffle
import Categorification.TypeA.WeakOrder

/-!
# Lengths around the block swap `w_L`

For the top blocks `(m, N)` and the bottom blocks `(N, m)` of `S_M`, let `w_L` be the minimal
double coset representative with `m` crossing strands: it moves the second bottom block across
the first one. This file records the two length facts used in the matrix of Webster,
arXiv:1309.3796v3, proof of Lemma 7.19, (IC), step 3.

* Every permutation `v` with `m` crossing strands has all inversions of `w_L`, so
  `ℓ(w_L) ≤ ℓ(v)`, with equality only for `v = w_L` (`eq_of_crossCount_eq_of_length_le`).
* For a shuffle `u` for the blocks `(N, m)`, `ℓ(w_L u) + ℓ(u) = ℓ(w_L)`
  (`length_mul_add_length`): the inversions of `u⁻¹` are pairs of strands from different blocks,
  and these are inversions of `w_L`.
-/

namespace Categorification.TypeA

open Equiv Finset

variable {m N M : ℕ} (hM : m + N = M) (hK : N + m = M)

include hM hK in
/-- A permutation with `m` crossing strands has every inversion of `w_L`. -/
theorem invSet_subset_of_crossCount_eq {d v : Perm (Fin M)} (hd : IsDoubleShuffle hM hK d)
    (hv : crossCount m N v = m) : invSet M d ⊆ invSet M v := by
  intro x hx
  rw [hd.mem_invSet_iff hM hK x] at hx
  obtain ⟨h1, h2, -, -⟩ := hx
  have a1 := lt_of_crossCount_eq hM hv (p := x.2) h2
  have a2 := le_of_crossCount_eq hM hv (p := x.1) h1
  rw [mem_invSet, Fin.lt_def, Fin.lt_def]
  omega

include hM hK in
/-- **`w_L` is the only permutation with `m` crossing strands and length at most `ℓ(w_L)`.** -/
theorem eq_of_crossCount_eq_of_length_le {d v : Perm (Fin M)} (hd : IsDoubleShuffle hM hK d)
    (hv : crossCount m N v = m) (hl : length M v ≤ length M d) : v = d := by
  have hsub := invSet_subset_of_crossCount_eq hM hK hd hv
  have hcard : (invSet M v).card ≤ (invSet M d).card := by
    rw [← invCount, ← invCount, ← length_eq_invCount, ← length_eq_invCount]
    exact hl
  exact (eq_of_invSet_eq (Finset.eq_of_subset_of_card_le hsub hcard)).symm

include hM hK in
/-- The inversions of `u⁻¹`, `u` a shuffle for the blocks `(N, m)`, are inversions of `w_L`. -/
theorem invSet_inv_subset_of_isShuffle {d u : Perm (Fin M)} (hd : IsDoubleShuffle hM hK d)
    (hcd : crossCount m N d = m) (hu : IsShuffle hK u) : invSet M u⁻¹ ⊆ invSet M d := by
  intro x hx
  rw [mem_invSet] at hx
  obtain ⟨hlt, hinv⟩ := hx
  have hblock : ¬ (x.1.val < N ↔ x.2.val < N) := by
    intro hxy
    have := (hu.inv_lt_inv_iff hK hxy).2 hlt
    exact absurd hinv (not_lt.2 this.le)
  rw [hd.mem_invSet_iff hM hK x]
  have hd1 := le_of_crossCount_eq hM hcd (p := x.1)
  have hd2 := lt_of_crossCount_eq hM hcd (p := x.2)
  rw [Fin.lt_def] at hlt
  have h1 : x.1.val < N := by
    by_contra h; exact hblock ⟨fun h' => absurd h' h, fun h' => by omega⟩
  have h2 : N ≤ x.2.val := by
    by_contra h; exact hblock ⟨fun _ => by omega, fun _ => h1⟩
  exact ⟨h1, h2, hd2 h2, hd1 h1⟩

include hM hK in
/-- **`ℓ(w_L u) + ℓ(u) = ℓ(w_L)`** for a shuffle `u` for the blocks `(N, m)`. -/
theorem length_mul_add_length {d u : Perm (Fin M)} (hd : IsDoubleShuffle hM hK d)
    (hcd : crossCount m N d = m) (hu : IsShuffle hK u) :
    length M (d * u) + length M u = length M d := by
  have h := invSet_subset_iff.1 (invSet_inv_subset_of_isShuffle hM hK hd hcd hu)
  rwa [inv_inv, length_inv] at h

end Categorification.TypeA
