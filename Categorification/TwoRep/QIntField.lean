/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Quantum integers in a field

Let `K` be a field and `q ∈ K` a *generic parameter* (`IsGenericParam`: `q ≠ 0` and `q^{2m} ≠ 1`
for `m ≠ 0`). The quantum integer `[m] = (q^m - q^{-m}) / (q - q^{-1})` (`qIntZ`) is nonzero for
`m ≠ 0` (`qIntZ_ne_zero`), and `[k] = ∑_{j<k} q^{k-1-2j}` (`sum_zpow_eq_qIntZ`). The variable `q` of
`ℚ((q))` (`qL`) is generic (`isGenericParam_q`).

These are used through the evaluation `ℚ[q, q⁻¹] → ℚ((q))` of `TorsionSeq.lean`, which transports
identities between quantum integers.
-/

noncomputable section

namespace Categorification.TwoRep

open Finset

section QInt

variable {K : Type*} [Field K]

/-- The quantum integer `[m] = (q^m - q^{-m}) / (q - q^{-1})`, `m ∈ ℤ`. -/
def qIntZ (q : K) (m : ℤ) : K := (q ^ m - q ^ (-m)) / (q - q⁻¹)

/-- `q` is **generic**: nonzero and `q^{2m} ≠ 1` for `m ≠ 0` (e.g. the variable of `ℚ((q))`). -/
structure IsGenericParam (q : K) : Prop where
  ne_zero : q ≠ 0
  pow_ne_one : ∀ m : ℤ, m ≠ 0 → q ^ (2 * m) ≠ 1

variable {q : K}

theorem IsGenericParam.sq_ne_one (hq : IsGenericParam q) : q ^ 2 ≠ 1 := by
  simpa using hq.pow_ne_one 1 one_ne_zero

theorem IsGenericParam.sub_inv_ne_zero (hq : IsGenericParam q) : q - q⁻¹ ≠ 0 := by
  intro h
  apply hq.sq_ne_one
  have := hq.ne_zero
  field_simp at h
  linear_combination h

theorem qIntZ_neg (q : K) (m : ℤ) : qIntZ q (-m) = -qIntZ q m := by
  rw [qIntZ, qIntZ, neg_neg, ← neg_div, neg_sub]

/-- `∑_{j<k} q^{k-1-2j} = [k]`: the class of `⊕_{[k]} X` is `[k]` times the class of `X`. -/
theorem sum_zpow_eq_qIntZ (hq : IsGenericParam q) (k : ℕ) :
    ∑ j ∈ range k, q ^ ((k : ℤ) - 1 - 2 * (j : ℤ)) = qIntZ q k := by
  have hq0 := hq.ne_zero
  rw [qIntZ, eq_div_iff hq.sub_inv_ne_zero]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ']
    have : ∀ j ∈ range k, q ^ (((k + 1 : ℕ) : ℤ) - 1 - 2 * ((j + 1 : ℕ) : ℤ)) =
        q⁻¹ * q ^ ((k : ℤ) - 1 - 2 * (j : ℤ)) := by
      intro j _
      rw [← zpow_neg_one, ← zpow_add₀ hq0]; congr 1; push_cast; ring
    rw [sum_congr rfl this, ← mul_sum, add_mul, mul_assoc, ih]
    have e1 : q ^ (((k + 1 : ℕ) : ℤ) - 1 - 2 * ((0 : ℕ) : ℤ)) = q ^ k := by
      rw [← zpow_natCast]; congr 1; push_cast; ring
    have e2 : q ^ (((k + 1 : ℕ) : ℤ)) = q ^ k * q := by
      rw [← zpow_natCast q k, ← zpow_add_one₀ hq0, Nat.cast_succ]
    have e3 : q ^ (-((k + 1 : ℕ) : ℤ)) = (q ^ k)⁻¹ * q⁻¹ := by
      rw [zpow_neg, e2, mul_inv]
    rw [e1, e2, e3, zpow_neg, zpow_natCast]
    field_simp
    ring

theorem qIntZ_ne_zero (hq : IsGenericParam q) {m : ℤ} (hm : m ≠ 0) : qIntZ q m ≠ 0 := by
  have hq0 := hq.ne_zero
  rw [qIntZ, div_ne_zero_iff]
  refine ⟨fun h => hq.pow_ne_one m hm ?_, hq.sub_inv_ne_zero⟩
  rw [sub_eq_zero, zpow_neg] at h
  have hm0 : q ^ m ≠ 0 := zpow_ne_zero _ hq0
  rw [mul_comm, zpow_mul, zpow_ofNat]
  field_simp at h
  exact h

end QInt

/-! ## Laurent series -/

/-- The coefficient field `ℚ((q))`. -/
abbrev LSer := LaurentSeries ℚ

/-- The variable `q = single 1 1 ∈ ℚ((q))`. -/
def qL : LSer := HahnSeries.single 1 1

theorem qL_zpow (n : ℤ) : qL ^ n = HahnSeries.single n 1 := by
  rw [qL, ← RatFunc.single_zpow]

theorem isGenericParam_q : IsGenericParam qL where
  ne_zero := HahnSeries.single_ne_zero one_ne_zero
  pow_ne_one m hm := by
    rw [qL_zpow, ← HahnSeries.single_zero_one]
    intro h
    have := congrArg (fun s : LSer => s.coeff (2 * m)) h
    simp only [HahnSeries.coeff_single_same] at this
    rw [HahnSeries.coeff_single_of_ne (by omega)] at this
    exact one_ne_zero this

end Categorification.TwoRep
