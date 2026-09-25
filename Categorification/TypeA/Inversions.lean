/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TypeA.Length

/-!
# Inversions and length in the symmetric group

The inversion count of `w : Equiv.Perm (Fin m)` is the number of pairs `a < b` with
`w b < w a`. We show it equals the Coxeter length `TypeA.length m w`, which gives a practical
lower bound for lengths and an exact criterion for when multiplying by an adjacent
transposition increases the length.

## Main results

* `TypeA.invCount_mul_sadj_of_lt` : if `w k < w (k + 1)` then `w * s_k` has one more inversion.
* `TypeA.length_eq_invCount` : `length m w = invCount m w`.
* `TypeA.length_mul_sadj_of_lt`, `TypeA.length_mul_sadj_of_gt`,
  `TypeA.length_sadj_mul_of_lt`, `TypeA.length_sadj_mul_of_gt` : the descent criterion for
  `length (w * s_k)` and `length (s_k * w)`.
-/

namespace Categorification.TypeA

open Equiv

variable {m : ℕ}

/-- The inversion set of `w`: pairs `(a, b)` with `a < b` and `w b < w a`. -/
def invSet (m : ℕ) (w : Perm (Fin m)) : Finset (Fin m × Fin m) :=
  Finset.univ.filter fun p => p.1 < p.2 ∧ w p.2 < w p.1

/-- The number of inversions of `w`. -/
def invCount (m : ℕ) (w : Perm (Fin m)) : ℕ := (invSet m w).card

theorem mem_invSet {w : Perm (Fin m)} {p : Fin m × Fin m} :
    p ∈ invSet m w ↔ p.1 < p.2 ∧ w p.2 < w p.1 := by
  simp [invSet]

@[simp] theorem invCount_one (m : ℕ) : invCount m 1 = 0 := by
  simp only [invCount, Finset.card_eq_zero, Finset.eq_empty_iff_forall_not_mem, mem_invSet,
    Perm.one_apply]
  exact fun p h => lt_asymm h.1 h.2

/-- Outside the pair `{k, k + 1}`, the transposition `s_k` preserves the order of pairs. -/
private theorem lt_iff_sadj_lt {k : ℕ} (hk : k + 1 < m) {a b : Fin m}
    (h₁ : ¬ ((a : ℕ) = k ∧ (b : ℕ) = k + 1)) (h₂ : ¬ ((a : ℕ) = k + 1 ∧ (b : ℕ) = k)) :
    a < b ↔ sadj m k a < sadj m k b := by
  rw [Fin.lt_iff_val_lt_val, Fin.lt_iff_val_lt_val, sadj_val_of_lt hk, sadj_val_of_lt hk]
  have := swapNat_cases k a
  have := swapNat_cases k b
  generalize swapNat k a = x at *
  generalize swapNat k b = y at *
  omega

/-- If `w k < w (k + 1)`, then `w * s_k` has exactly one more inversion than `w`. -/
theorem invCount_mul_sadj_of_lt {k : ℕ} (hk : k + 1 < m) {w : Perm (Fin m)}
    (hlt : w ⟨k, by omega⟩ < w ⟨k + 1, hk⟩) : invCount m (w * sadj m k) = invCount m w + 1 := by
  have hk0 : k < m := by omega
  set φ : Fin m × Fin m ≃ Fin m × Fin m := Equiv.prodCongr (sadj m k) (sadj m k)
  set P : Fin m × Fin m := (⟨k, hk0⟩, ⟨k + 1, hk⟩)
  have hφ : ∀ p, φ.symm p = φ p := fun p => by
    simp only [φ, Equiv.prodCongr_symm, Equiv.prodCongr_apply, Prod.map]
    rw [← Perm.inv_def, sadj_inv]
  have hP : P ∉ (invSet m w).map φ.toEmbedding := by
    rw [Finset.mem_map_equiv, hφ, mem_invSet]
    simp only [φ, P, Equiv.prodCongr_apply, Prod.map, sadj_apply_left hk, sadj_apply_right hk]
    exact fun h => absurd h.1 (by simp [Fin.lt_iff_val_lt_val])
  have hset : invSet m (w * sadj m k) = insert P ((invSet m w).map φ.toEmbedding) := by
    ext ⟨a, b⟩
    rw [Finset.mem_insert, Finset.mem_map_equiv, hφ, mem_invSet, mem_invSet]
    simp only [φ, P, Equiv.prodCongr_apply, Prod.map, Perm.mul_apply, Prod.mk.injEq]
    by_cases h₁ : (a : ℕ) = k ∧ (b : ℕ) = k + 1
    · obtain rfl : a = ⟨k, hk0⟩ := Fin.ext h₁.1
      obtain rfl : b = ⟨k + 1, hk⟩ := Fin.ext h₁.2
      simp only [sadj_apply_left hk, sadj_apply_right hk, and_self, true_or, iff_true]
      exact ⟨by simp [Fin.lt_iff_val_lt_val], hlt⟩
    by_cases h₂ : (a : ℕ) = k + 1 ∧ (b : ℕ) = k
    · obtain rfl : a = ⟨k + 1, hk⟩ := Fin.ext h₂.1
      obtain rfl : b = ⟨k, hk0⟩ := Fin.ext h₂.2
      simp only [sadj_apply_left hk, sadj_apply_right hk]
      simp only [Fin.lt_iff_val_lt_val, Fin.ext_iff]
      constructor
      · rintro ⟨h, -⟩; omega
      · rintro (⟨h, -⟩ | ⟨-, h⟩)
        · omega
        · exact absurd (Fin.lt_iff_val_lt_val.2 h) (lt_asymm hlt)
    have hne : ¬ (a = ⟨k, hk0⟩ ∧ b = ⟨k + 1, hk⟩) := fun h => h₁ ⟨by rw [h.1], by rw [h.2]⟩
    simp only [hne, false_or, lt_iff_sadj_lt hk h₁ h₂]
  rw [invCount, hset, Finset.card_insert_of_not_mem hP, Finset.card_map, invCount]

/-- Right multiplication by an adjacent transposition changes the inversion count by one,
according to whether `k` is an ascent or a descent of `w`. -/
theorem invCount_mul_sadj_of_gt {k : ℕ} (hk : k + 1 < m) {w : Perm (Fin m)}
    (hgt : w ⟨k + 1, hk⟩ < w ⟨k, by omega⟩) : invCount m (w * sadj m k) + 1 = invCount m w := by
  have := invCount_mul_sadj_of_lt hk (w := w * sadj m k)
    (by simpa [Perm.mul_apply, sadj_apply_left hk, sadj_apply_right hk] using hgt)
  rwa [mul_assoc, sadj_mul_self, mul_one, eq_comm] at this

theorem invCount_mul_sadj_le (k : ℕ) (w : Perm (Fin m)) :
    invCount m (w * sadj m k) ≤ invCount m w + 1 := by
  by_cases hk : k + 1 < m
  · rcases lt_or_gt_of_ne (w.injective.ne (show (⟨k, by omega⟩ : Fin m) ≠ ⟨k + 1, hk⟩ by
      simp)) with h | h
    · exact (invCount_mul_sadj_of_lt hk h).le
    · have := invCount_mul_sadj_of_gt hk h; omega
  · simp [sadj_of_not_lt hk]

/-- A valid word has at least as many letters as its permutation has inversions. -/
theorem invCount_wordProd_le {ρ : List ℕ} : invCount m (wordProd m ρ) ≤ ρ.length := by
  induction ρ using List.reverseRecOn with
  | nil => simp
  | append_singleton ρ k ih =>
    rw [wordProd_append, wordProd_singleton, List.length_append, List.length_singleton]
    exact (invCount_mul_sadj_le k _).trans (by omega)

theorem invCount_le_length (w : Perm (Fin m)) : invCount m w ≤ length m w := by
  obtain ⟨ρ, _, hw, hl⟩ := exists_word_length_eq m w
  rw [← hl, ← hw]
  exact invCount_wordProd_le

/-- A permutation other than the identity has a descent. -/
theorem exists_descent {w : Perm (Fin m)} (hw : w ≠ 1) :
    ∃ k, ∃ hk : k + 1 < m, w ⟨k + 1, hk⟩ < w ⟨k, by omega⟩ := by
  by_contra! H
  apply hw
  rcases m with _ | n
  · exact Subsingleton.elim _ _
  have hmono : StrictMono w := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    exact lt_of_le_of_ne (H i (by omega)) (w.injective.ne (Fin.castSucc_lt_succ i).ne)
  have hid : (w : Fin (n + 1) → Fin (n + 1)) = id :=
    (hmono.range_inj strictMono_id).1 (by rw [EquivLike.range_eq_univ, Set.range_id])
  ext i
  rw [Perm.one_apply, show w i = i from congrFun hid i]

theorem length_le_invCount (w : Perm (Fin m)) : length m w ≤ invCount m w := by
  induction h : invCount m w using Nat.strong_induction_on generalizing w with
  | _ n ih =>
    by_cases hw : w = 1
    · subst hw; simp
    obtain ⟨k, hk, hd⟩ := exists_descent hw
    have e := invCount_mul_sadj_of_gt hk hd
    have h1 := ih _ (by omega) (w * sadj m k) rfl
    have h2 := length_mul_sadj_le k (w * sadj m k)
    rw [mul_assoc, sadj_mul_self, mul_one] at h2
    omega

/-- **Length equals the number of inversions.** -/
theorem length_eq_invCount (w : Perm (Fin m)) : length m w = invCount m w :=
  le_antisymm (length_le_invCount w) (invCount_le_length w)

/-- If `w k < w (k + 1)` then `length (w * s_k) = length w + 1`. -/
theorem length_mul_sadj_of_lt {k : ℕ} (hk : k + 1 < m) {w : Perm (Fin m)}
    (hlt : w ⟨k, by omega⟩ < w ⟨k + 1, hk⟩) : length m (w * sadj m k) = length m w + 1 := by
  rw [length_eq_invCount, length_eq_invCount, invCount_mul_sadj_of_lt hk hlt]

/-- If `w (k + 1) < w k` then `length (w * s_k) + 1 = length w`. -/
theorem length_mul_sadj_of_gt {k : ℕ} (hk : k + 1 < m) {w : Perm (Fin m)}
    (hgt : w ⟨k + 1, hk⟩ < w ⟨k, by omega⟩) : length m (w * sadj m k) + 1 = length m w := by
  rw [length_eq_invCount, length_eq_invCount, invCount_mul_sadj_of_gt hk hgt]

/-- If `w⁻¹ k < w⁻¹ (k + 1)` then `length (s_k * w) = length w + 1`. -/
theorem length_sadj_mul_of_lt {k : ℕ} (hk : k + 1 < m) {w : Perm (Fin m)}
    (hlt : w⁻¹ ⟨k, by omega⟩ < w⁻¹ ⟨k + 1, hk⟩) : length m (sadj m k * w) = length m w + 1 := by
  have := length_mul_sadj_of_lt hk hlt
  rwa [← sadj_inv, ← mul_inv_rev, length_inv, length_inv] at this

/-- If `w⁻¹ (k + 1) < w⁻¹ k` then `length (s_k * w) + 1 = length w`. -/
theorem length_sadj_mul_of_gt {k : ℕ} (hk : k + 1 < m) {w : Perm (Fin m)}
    (hgt : w⁻¹ ⟨k + 1, hk⟩ < w⁻¹ ⟨k, by omega⟩) : length m (sadj m k * w) + 1 = length m w := by
  have := length_mul_sadj_of_gt hk hgt
  rwa [← sadj_inv, ← mul_inv_rev, length_inv, length_inv] at this

end Categorification.TypeA
