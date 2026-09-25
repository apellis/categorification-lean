/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TypeA.Basic

/-!
# Coxeter length in the symmetric group

Basic properties of `TypeA.length m w`, the minimal length of a valid word in adjacent
transpositions representing `w : Equiv.Perm (Fin m)`.

## Main results

* `TypeA.length_le_of_wordProd_eq`, `TypeA.length_wordProd_le` : any valid word bounds the length.
* `TypeA.exists_reduced` : every permutation has a reduced word.
* `TypeA.length_one`, `TypeA.length_eq_zero_iff`, `TypeA.length_sadj`, `TypeA.length_inv`,
  `TypeA.length_mul_le`.
* `TypeA.sign_eq_neg_one_pow_length` : `sign w = (-1) ^ length m w`.
* `TypeA.length_sadj_mul`, `TypeA.length_mul_sadj` : multiplying by an adjacent transposition
  changes the length by exactly one.
* `TypeA.length_wordProd_add_two_le_of_hasRepeat` : a word with two equal adjacent letters is
  at least two letters longer than the length of the permutation it represents.
-/

namespace Categorification.TypeA

open Equiv

variable {m : ℕ}

/-- Some valid word of length `length m w` represents `w`. -/
theorem exists_word_length_eq (m : ℕ) (w : Perm (Fin m)) :
    ∃ ρ, ValidWord m ρ ∧ wordProd m ρ = w ∧ ρ.length = length m w := by
  classical
  unfold length
  exact Nat.find_spec (p := fun n => ∃ ρ, ValidWord m ρ ∧ wordProd m ρ = w ∧ ρ.length = n) _

/-- The length of `w` is at most the length of any valid word representing `w`. -/
theorem length_le_of_wordProd_eq {ρ : List ℕ} {w : Perm (Fin m)} (hv : ValidWord m ρ)
    (hw : wordProd m ρ = w) : length m w ≤ ρ.length := by
  classical
  unfold length
  exact Nat.find_min' (p := fun n => ∃ ρ, ValidWord m ρ ∧ wordProd m ρ = w ∧ ρ.length = n) _
    ⟨ρ, hv, hw, rfl⟩

/-- A valid word is at least as long as the permutation it represents. -/
theorem length_wordProd_le {ρ : List ℕ} (hv : ValidWord m ρ) :
    length m (wordProd m ρ) ≤ ρ.length :=
  length_le_of_wordProd_eq hv rfl

/-- Every permutation has a reduced word. -/
theorem exists_reduced (m : ℕ) (w : Perm (Fin m)) : ∃ ρ, IsReduced m ρ ∧ wordProd m ρ = w := by
  obtain ⟨ρ, hv, hw, hl⟩ := exists_word_length_eq m w
  exact ⟨ρ, ⟨hv, by rw [hw, hl]⟩, hw⟩

theorem IsReduced.validWord {ρ : List ℕ} (h : IsReduced m ρ) : ValidWord m ρ := h.1

theorem IsReduced.length_eq {ρ : List ℕ} (h : IsReduced m ρ) :
    ρ.length = length m (wordProd m ρ) := h.2

/-- A valid word is reduced iff it is no longer than the length of its permutation. -/
theorem isReduced_iff_length_le {ρ : List ℕ} (hv : ValidWord m ρ) :
    IsReduced m ρ ↔ ρ.length ≤ length m (wordProd m ρ) :=
  ⟨fun h => h.2.le, fun h => ⟨hv, le_antisymm h (length_wordProd_le hv)⟩⟩

@[simp] theorem length_one (m : ℕ) : length m 1 = 0 :=
  Nat.le_zero.1 (length_le_of_wordProd_eq (ρ := []) (validWord_nil m) rfl)

theorem length_eq_zero_iff {w : Perm (Fin m)} : length m w = 0 ↔ w = 1 := by
  refine ⟨fun h => ?_, fun h => h ▸ length_one m⟩
  obtain ⟨ρ, _, hw, hl⟩ := exists_word_length_eq m w
  rw [h, List.length_eq_zero_iff] at hl
  rw [← hw, hl, wordProd_nil]

theorem length_inv_le (w : Perm (Fin m)) : length m w⁻¹ ≤ length m w := by
  obtain ⟨ρ, hv, hw, hl⟩ := exists_word_length_eq m w
  rw [← hl, ← List.length_reverse]
  exact length_le_of_wordProd_eq (validWord_reverse.2 hv) (by rw [wordProd_reverse, hw])

@[simp] theorem length_inv (w : Perm (Fin m)) : length m w⁻¹ = length m w :=
  le_antisymm (length_inv_le w) (by simpa using length_inv_le w⁻¹)

/-- Length is subadditive. -/
theorem length_mul_le (v w : Perm (Fin m)) : length m (v * w) ≤ length m v + length m w := by
  obtain ⟨ρ, hv, hρ, hl⟩ := exists_word_length_eq m v
  obtain ⟨σ, hv', hσ, hl'⟩ := exists_word_length_eq m w
  rw [← hl, ← hl', ← List.length_append]
  exact length_le_of_wordProd_eq (validWord_append.2 ⟨hv, hv'⟩) (by rw [wordProd_append, hρ, hσ])

theorem length_sadj_le (m k : ℕ) : length m (sadj m k) ≤ 1 := by
  by_cases hk : k + 1 < m
  · exact length_le_of_wordProd_eq (ρ := [k]) (by simp [hk]) (wordProd_singleton m k)
  · simp [sadj_of_not_lt hk]

theorem length_sadj_mul_le (k : ℕ) (w : Perm (Fin m)) :
    length m (sadj m k * w) ≤ length m w + 1 :=
  (length_mul_le _ _).trans (by have := length_sadj_le m k; omega)

theorem length_mul_sadj_le (k : ℕ) (w : Perm (Fin m)) :
    length m (w * sadj m k) ≤ length m w + 1 :=
  (length_mul_le _ _).trans (by have := length_sadj_le m k; omega)

/-- The sign of a permutation is `(-1)` to the power of its length. -/
theorem sign_eq_neg_one_pow_length (w : Perm (Fin m)) : Perm.sign w = (-1) ^ length m w := by
  obtain ⟨ρ, hv, hw, hl⟩ := exists_word_length_eq m w
  rw [← hw, sign_wordProd hv, hl, hw]

theorem length_sadj {k : ℕ} (hk : k + 1 < m) : length m (sadj m k) = 1 := by
  refine le_antisymm (length_sadj_le m k) (Nat.one_le_iff_ne_zero.2 fun h => ?_)
  have := sign_eq_neg_one_pow_length (sadj m k)
  rw [h, sign_sadj hk, pow_zero] at this
  exact absurd this (by decide)

private theorem length_ne_of_sign {v w : Perm (Fin m)} (h : Perm.sign v = -Perm.sign w) :
    length m v ≠ length m w := by
  intro hl
  rw [sign_eq_neg_one_pow_length, sign_eq_neg_one_pow_length, hl] at h
  rcases Int.units_eq_one_or ((-1 : ℤˣ) ^ length m w) with h' | h' <;>
    rw [h'] at h <;> exact absurd h (by decide)

/-- Left multiplication by an adjacent transposition changes the length by exactly one. -/
theorem length_sadj_mul {k : ℕ} (hk : k + 1 < m) (w : Perm (Fin m)) :
    length m (sadj m k * w) = length m w + 1 ∨ length m (sadj m k * w) + 1 = length m w := by
  have h1 := length_sadj_mul_le k w
  have h2 := length_sadj_mul_le k (sadj m k * w)
  rw [← mul_assoc, sadj_mul_self, one_mul] at h2
  have h3 : length m (sadj m k * w) ≠ length m w :=
    length_ne_of_sign (by rw [map_mul, sign_sadj hk, neg_one_mul])
  omega

/-- Right multiplication by an adjacent transposition changes the length by exactly one. -/
theorem length_mul_sadj {k : ℕ} (hk : k + 1 < m) (w : Perm (Fin m)) :
    length m (w * sadj m k) = length m w + 1 ∨ length m (w * sadj m k) + 1 = length m w := by
  have := length_sadj_mul hk w⁻¹
  have e : sadj m k * w⁻¹ = (w * sadj m k)⁻¹ := by rw [mul_inv_rev, sadj_inv]
  rwa [e, length_inv, length_inv] at this

/-- A valid word containing two equal adjacent letters is at least two letters longer than the
length of the permutation it represents; in particular it is not reduced. -/
theorem length_wordProd_add_two_le_of_hasRepeat {σ : List ℕ} (hv : ValidWord m σ)
    (h : HasRepeat σ) : length m (wordProd m σ) + 2 ≤ σ.length := by
  obtain ⟨α, β, a, rfl⟩ := h
  have hv' : ValidWord m (α ++ β) := by
    simp only [validWord_append] at hv ⊢; exact ⟨hv.1.1, hv.2⟩
  rw [wordProd_repeat]
  have := length_wordProd_le hv'
  simp only [List.length_append, List.length_cons, List.length_nil] at this ⊢
  omega

theorem HasRepeat.not_isReduced {σ : List ℕ} (h : HasRepeat σ) : ¬ IsReduced m σ := fun hr => by
  have := length_wordProd_add_two_le_of_hasRepeat hr.1 h
  rw [← hr.2] at this
  omega

end Categorification.TypeA
