/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TypeA.Inversions

/-!
# The left weak order on the symmetric group

For `σ τ : Equiv.Perm (Fin m)`, the inversion set of `σ` is contained in that of `τ` exactly
when `τ = u * σ` with `length u + length σ = length τ`. This is the standard description of the
weak order by inversion sets (see e.g. Björner–Brenti, *Combinatorics of Coxeter groups*,
Prop. 3.1.3, stated there for the right weak order and the left inversion sets).

## Main results

* `TypeA.invSet_sadj_mul_of_lt` : left multiplication by `s_k` at an ascent of `w⁻¹` adds
  exactly one inversion.
* `TypeA.invSet_subset_iff` : `invSet σ ⊆ invSet τ ↔ length (τ * σ⁻¹) + length σ = length τ`.
* `TypeA.exists_peel` : a left descent of `τ` removing an inversion not in `invSet σ`.
* `TypeA.eq_of_invSet_eq` : a permutation is determined by its inversion set.
-/

namespace Categorification.TypeA

open Equiv

variable {m : ℕ}

/-- Order of values after applying `s_k`. -/
private theorem sadj_lt_sadj_iff {k : ℕ} (hk : k + 1 < m) (x y : Fin m) :
    sadj m k y < sadj m k x ↔
      (y < x ∧ ¬ ((y : ℕ) = k ∧ (x : ℕ) = k + 1)) ∨ ((y : ℕ) = k + 1 ∧ (x : ℕ) = k) := by
  rw [Fin.lt_def, Fin.lt_def, sadj_val_of_lt hk, sadj_val_of_lt hk]
  have := swapNat_cases k x
  have := swapNat_cases k y
  generalize swapNat k x = x' at *
  generalize swapNat k y = y' at *
  omega

/-- If `w⁻¹ k < w⁻¹ (k + 1)`, left multiplication by `s_k` adds the single inversion
`(w⁻¹ k, w⁻¹ (k + 1))`. -/
theorem invSet_sadj_mul_of_lt {k : ℕ} (hk : k + 1 < m) {w : Perm (Fin m)}
    (hlt : w⁻¹ ⟨k, by omega⟩ < w⁻¹ ⟨k + 1, hk⟩) :
    invSet m (sadj m k * w) = insert (w⁻¹ ⟨k, by omega⟩, w⁻¹ ⟨k + 1, hk⟩) (invSet m w) := by
  ext ⟨a, b⟩
  rw [Finset.mem_insert, mem_invSet, mem_invSet, Perm.mul_apply, Perm.mul_apply,
    sadj_lt_sadj_iff hk, Prod.mk.injEq]
  have ea : ∀ j : Fin m, w a = j ↔ a = w⁻¹ j := fun j => by
    constructor <;> intro h <;> subst h <;> simp
  have eb : ∀ j : Fin m, w b = j ↔ b = w⁻¹ j := fun j => by
    constructor <;> intro h <;> subst h <;> simp
  have hk0 : ∀ j : Fin m, (j : ℕ) = k ↔ j = ⟨k, by omega⟩ := fun j => by simp [Fin.ext_iff]
  have hk1 : ∀ j : Fin m, (j : ℕ) = k + 1 ↔ j = ⟨k + 1, hk⟩ := fun j => by simp [Fin.ext_iff]
  simp only [hk0, hk1, ea, eb]
  constructor
  · rintro ⟨hab, (⟨h, -⟩ | ⟨hb, ha⟩)⟩
    · exact Or.inr ⟨hab, h⟩
    · exact Or.inl ⟨ha, hb⟩
  · rintro (⟨ha, hb⟩ | ⟨hab, h⟩)
    · subst ha hb; exact ⟨hlt, Or.inr ⟨rfl, rfl⟩⟩
    · refine ⟨hab, Or.inl ⟨h, ?_⟩⟩
      rintro ⟨hb, ha⟩
      subst ha hb
      exact absurd hlt (lt_asymm hab)

/-- If `w⁻¹ k < w⁻¹ (k + 1)`, then `invSet w ⊆ invSet (s_k * w)`. -/
theorem invSet_subset_sadj_mul {k : ℕ} (hk : k + 1 < m) {w : Perm (Fin m)}
    (hlt : w⁻¹ ⟨k, by omega⟩ < w⁻¹ ⟨k + 1, hk⟩) : invSet m w ⊆ invSet m (sadj m k * w) := by
  rw [invSet_sadj_mul_of_lt hk hlt]; exact Finset.subset_insert _ _

/-- A permutation other than the identity has a left descent. -/
theorem exists_left_descent {u : Perm (Fin m)} (hu : u ≠ 1) :
    ∃ k, ∃ hk : k + 1 < m, u⁻¹ ⟨k + 1, hk⟩ < u⁻¹ ⟨k, by omega⟩ :=
  exists_descent (inv_ne_one.2 hu)

/-- Inversion sets increase along the left weak order. -/
theorem invSet_subset_of_length_add {u σ : Perm (Fin m)}
    (h : length m u + length m σ = length m (u * σ)) : invSet m σ ⊆ invSet m (u * σ) := by
  induction hn : length m u using Nat.strong_induction_on generalizing u with
  | _ n ih =>
    by_cases hu : u = 1
    · subst hu; simp
    obtain ⟨k, hk, hd⟩ := exists_left_descent hu
    set u' := sadj m k * u
    have hu' : length m u' + 1 = length m u := length_sadj_mul_of_gt hk hd
    have e : u = sadj m k * u' := by simp [u', ← mul_assoc]
    have h1 := length_mul_le u' σ
    have h2 := length_sadj_mul_le k (u' * σ)
    rw [← mul_assoc, ← e] at h2
    have h3 : length m u' + length m σ = length m (u' * σ) := by omega
    refine (ih _ (by omega) h3 rfl).trans ?_
    rw [e, mul_assoc]
    refine invSet_subset_sadj_mul hk ?_
    -- the length of `s_k * (u' * σ)` is one more than that of `u' * σ`
    by_contra hc
    have hgt : (u' * σ)⁻¹ ⟨k + 1, hk⟩ < (u' * σ)⁻¹ ⟨k, by omega⟩ := by
      refine lt_of_le_of_ne (not_lt.1 hc) ?_
      exact (u' * σ)⁻¹.injective.ne (by simp [Fin.ext_iff])
    have := length_sadj_mul_of_gt hk hgt
    rw [← mul_assoc, ← e] at this
    omega

/-- **Peeling.** If `invSet σ ⊊ invSet τ`, some left descent `k` of `τ` removes an inversion
of `τ` that is not an inversion of `σ`. -/
theorem exists_peel {σ τ : Perm (Fin m)} (h : invSet m σ ⊆ invSet m τ) (hne : τ ≠ σ) :
    ∃ k, ∃ hk : k + 1 < m,
      τ⁻¹ ⟨k + 1, hk⟩ < τ⁻¹ ⟨k, by omega⟩ ∧
      (sadj m k * τ)⁻¹ ⟨k, by omega⟩ < (sadj m k * τ)⁻¹ ⟨k + 1, hk⟩ ∧
      (τ⁻¹ ⟨k + 1, hk⟩, τ⁻¹ ⟨k, by omega⟩) ∉ invSet m σ ∧
      invSet m τ = insert (τ⁻¹ ⟨k + 1, hk⟩, τ⁻¹ ⟨k, by omega⟩) (invSet m (sadj m k * τ)) ∧
      invSet m σ ⊆ invSet m (sadj m k * τ) ∧
      length m (sadj m k * τ * σ⁻¹) + 1 = length m (τ * σ⁻¹) := by
  have hu : τ * σ⁻¹ ≠ 1 := fun h' => hne (mul_inv_eq_one.1 h')
  obtain ⟨k, hk, hd⟩ := exists_left_descent hu
  set a := τ⁻¹ ⟨k + 1, hk⟩
  set b := τ⁻¹ ⟨k, by omega⟩
  have hσa : σ a = (τ * σ⁻¹)⁻¹ ⟨k + 1, hk⟩ := by simp [a]
  have hσb : σ b = (τ * σ⁻¹)⁻¹ ⟨k, by omega⟩ := by simp [b]
  have hab : a ≠ b := τ⁻¹.injective.ne (by simp [Fin.ext_iff])
  have hlt : a < b := by
    by_contra hc
    have hba : b < a := lt_of_le_of_ne (not_lt.1 hc) hab.symm
    have hmem : (b, a) ∈ invSet m σ := mem_invSet.2 ⟨hba, by rw [hσa, hσb]; exact hd⟩
    have := (mem_invSet.1 (h hmem)).2
    simp [a, b, Fin.lt_def] at this
  set τ' := sadj m k * τ
  have hτ : τ = sadj m k * τ' := by simp [τ', ← mul_assoc]
  have e1 : τ'⁻¹ ⟨k, by omega⟩ = a := by
    simp only [τ', mul_inv_rev, sadj_inv, Perm.mul_apply, sadj_apply_left hk, a]
  have e2 : τ'⁻¹ ⟨k + 1, hk⟩ = b := by
    simp only [τ', mul_inv_rev, sadj_inv, Perm.mul_apply, sadj_apply_right hk, b]
  have hlt' : τ'⁻¹ ⟨k, by omega⟩ < τ'⁻¹ ⟨k + 1, hk⟩ := by rw [e1, e2]; exact hlt
  have hset := invSet_sadj_mul_of_lt hk hlt'
  rw [← hτ] at hset
  have hP : (τ'⁻¹ ⟨k, by omega⟩, τ'⁻¹ ⟨k + 1, hk⟩) = (a, b) := by rw [e1, e2]
  rw [hP] at hset
  have hnot : (a, b) ∉ invSet m σ := fun hm => by
    have := (mem_invSet.1 hm).2
    rw [hσa, hσb] at this
    exact lt_asymm this hd
  have hsub : invSet m σ ⊆ invSet m τ' := fun p hp => by
    have := h hp
    rw [hset, Finset.mem_insert] at this
    rcases this with rfl | h'
    · exact absurd hp hnot
    · exact h'
  refine ⟨k, hk, hlt, hlt', hnot, hset, hsub, ?_⟩
  have := length_sadj_mul_of_gt hk hd
  rwa [← mul_assoc] at this

/-- If `invSet σ ⊆ invSet τ`, then `length (τ * σ⁻¹) + length σ = length τ`. -/
theorem length_add_of_invSet_subset {σ τ : Perm (Fin m)} (h : invSet m σ ⊆ invSet m τ) :
    length m (τ * σ⁻¹) + length m σ = length m τ := by
  induction hn : length m τ using Nat.strong_induction_on generalizing τ with
  | _ n ih =>
    by_cases hne : τ = σ
    · subst hne; rw [mul_inv_cancel, length_one, zero_add, hn]
    obtain ⟨k, hk, -, hlt', -, -, hsub, hu'⟩ := exists_peel h hne
    have hl : length m τ = length m (sadj m k * τ) + 1 := by
      have := length_sadj_mul_of_lt hk hlt'
      rwa [← mul_assoc, sadj_mul_self, one_mul] at this
    have hih := ih _ (by omega) hsub rfl
    omega

/-- **Inversion sets and the left weak order.** `invSet σ ⊆ invSet τ` iff
`length (τ * σ⁻¹) + length σ = length τ`. -/
theorem invSet_subset_iff {σ τ : Perm (Fin m)} :
    invSet m σ ⊆ invSet m τ ↔ length m (τ * σ⁻¹) + length m σ = length m τ := by
  refine ⟨length_add_of_invSet_subset, fun h => ?_⟩
  have := invSet_subset_of_length_add (u := τ * σ⁻¹) (σ := σ) (by simpa using h)
  simpa using this

/-- A permutation is determined by its inversion set. -/
theorem eq_of_invSet_eq {σ τ : Perm (Fin m)} (h : invSet m σ = invSet m τ) : σ = τ := by
  have h1 := length_add_of_invSet_subset h.le
  have h2 : length m σ = length m τ := by
    rw [length_eq_invCount, length_eq_invCount, invCount, invCount, h]
  rw [h2, Nat.add_eq_right, length_eq_zero_iff, mul_inv_eq_one] at h1
  exact h1.symm

end Categorification.TypeA
