/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Field.Power
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Weight modules for `U̇(sl₂)` with bounded weights: `E`-equivariance implies `F`-equivariance

This file is pure linear algebra; it is the representation-theoretic input of the numerical
adjunction (`NumericalAdjunction.lean`), used for S. Cautis, A. D. Lauda, *Implicit structure in
2-representations of quantum groups*, arXiv:1111.1431v3, §3 (the adjoint induction, Proposition 3.9
`prop:lradj`, hypothesis (3.2) `eq:ind_hyp`).

Let `K` be a field and `q ∈ K` a *generic parameter* (`IsGenericParam`: `q ≠ 0` and `q^{2m} ≠ 1`
for `m ≠ 0`), and `[m] = (q^m - q^{-m}) / (q - q^{-1})` (`qIntZ`). A `WtModule K q V` is a
`K`-module `V` with endomorphisms `E`, `F` and weight subspaces `V_t` (`Wt t`, of weight
`n₀ + 2t`) such that `E V_t ⊆ V_{t+1}`, `F V_{t+1} ⊆ V_t`, `EF - FE = [n₀ + 2t]` on `V_t`, and
`V_t = 0` for `|t| ≫ 0` (weights bounded). No finite-dimensionality or semisimplicity is assumed.

## Main result

* `WtModule.F_comm_of_E_comm`: **a weight-preserving linear map between two such modules (with the
  same weights) which commutes with `E` also commutes with `F`.**

Proof (elementary; no complete reducibility is used). Put `δ = Φ F - F Φ`. The relation gives
`δ E = E δ` (`δ_E`). Weight boundedness gives (`eq_zero_of_E_pow_eq_zero`): *if `v` has weight
`μ` and `E^j v = 0` with `j ≤ -μ`, then `v = 0`* (induction from the lowest weight, via `F v`).
For a highest weight vector `u` (`E u = 0`) of weight `m ≥ 0`, `δ(F^m u)` has weight `-m - 2` and
is killed by `E^{m+1}`, hence vanishes, and then so does every `δ(F^i u)`, `i ≤ m`
(`δ_F_pow_eq_zero`). Finally induct on the least `a` with `E^a v = 0`: `v - c⁻¹ F^{a-1} E^{a-1} v`
is killed by `E^{a-1}` for the nonzero scalar `c` with `E^{a-1} F^{a-1} E^{a-1} v = c E^{a-1} v`.
The scalars that must be nonzero are the sums `∑_{i<j} [μ + 2i] = [j][μ + j - 1]`
(`sum_qIntZ_ne_zero`) and `∑_{k<j} [μ - 2k]`.
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

theorem zpow_lin (hq : q ≠ 0) (μ : ℤ) (n : ℕ) (a b c : ℤ) :
    q ^ (a * μ + b * (n : ℤ) + c) = (q ^ μ) ^ a * (q ^ n) ^ b * q ^ c := by
  rw [zpow_add₀ hq, zpow_add₀ hq, zpow_mul', zpow_mul', zpow_natCast]

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

/-- The same sum with `q^{-1}` in place of `q`. -/
theorem sum_zpow_neg_eq_qIntZ (hq : IsGenericParam q) (k : ℕ) :
    ∑ j ∈ range k, q ^ (-((k : ℤ) - 1 - 2 * (j : ℤ))) = qIntZ q k := by
  rw [← sum_zpow_eq_qIntZ hq k, ← sum_range_reflect]
  refine sum_congr rfl fun j hj => ?_
  rw [mem_range] at hj
  congr 1
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast; ring

theorem qIntZ_ne_zero (hq : IsGenericParam q) {m : ℤ} (hm : m ≠ 0) : qIntZ q m ≠ 0 := by
  have hq0 := hq.ne_zero
  rw [qIntZ, div_ne_zero_iff]
  refine ⟨fun h => hq.pow_ne_one m hm ?_, hq.sub_inv_ne_zero⟩
  rw [sub_eq_zero, zpow_neg] at h
  have hm0 : q ^ m ≠ 0 := zpow_ne_zero _ hq0
  rw [mul_comm, zpow_mul, zpow_ofNat]
  field_simp at h
  exact h

/-- **The sum `∑_{i<n} [μ + 2i]` (`= [n][μ + n - 1]`) is nonzero** when `n ≥ 1` and
`μ + n - 1 ≠ 0`. -/
theorem sum_qIntZ_ne_zero (hq : IsGenericParam q) (μ : ℤ) {n : ℕ} (hn : 0 < n)
    (hμ : μ + n - 1 ≠ 0) : ∑ i ∈ range n, qIntZ q (μ + 2 * i) ≠ 0 := by
  have hq0 := hq.ne_zero
  have hd := hq.sub_inv_ne_zero
  have hμ0 : q ^ μ ≠ 0 := zpow_ne_zero _ hq0
  have key : ∀ n : ℕ, (∑ i ∈ range n, qIntZ q (μ + 2 * i)) * (q - q⁻¹) * (q ^ 2 - 1) =
      (q ^ (2 * n) - 1) * (q ^ μ - (q ^ μ)⁻¹ * (q ^ n)⁻¹ ^ 2 * q ^ 2) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, add_mul, add_mul, ih, qIntZ, div_mul_cancel₀ _ hd]
      have e1 : q ^ (μ + 2 * ((n : ℕ) : ℤ)) = (q ^ μ) ^ (1 : ℤ) * (q ^ n) ^ (2 : ℤ) * q ^ (0 : ℤ) := by
        rw [← zpow_lin hq0]; congr 1; ring
      have e2 : q ^ (-(μ + 2 * ((n : ℕ) : ℤ))) =
          (q ^ μ) ^ (-1 : ℤ) * (q ^ n) ^ (-2 : ℤ) * q ^ (0 : ℤ) := by
        rw [← zpow_lin hq0]; congr 1; ring
      rw [e1, e2]
      have hn0 : q ^ n ≠ 0 := pow_ne_zero _ hq0
      simp only [zpow_neg, zpow_ofNat, pow_succ]
      field_simp
      ring
  intro h
  have k := key n
  rw [h, zero_mul, zero_mul, eq_comm, mul_eq_zero] at k
  rcases k with h1 | h1
  · apply hq.pow_ne_one n (by exact_mod_cast hn.ne')
    rw [show (2 : ℤ) * n = ((2 * n : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
    exact sub_eq_zero.1 h1
  · apply hq.pow_ne_one (μ + n - 1) hμ
    have hn0 : q ^ n ≠ 0 := pow_ne_zero _ hq0
    have : q ^ (2 * (μ + ↑n - 1)) = (q ^ μ) ^ (2 : ℤ) * (q ^ n) ^ (2 : ℤ) * q ^ (-2 : ℤ) := by
      rw [← zpow_lin hq0]; congr 1; ring
    rw [this]
    rw [sub_eq_zero] at h1
    simp only [zpow_neg, zpow_ofNat]
    field_simp at h1 ⊢
    linear_combination h1

/-- The sum `∑_{k<n} [μ - 2k]` (`= [n][μ - n + 1]`) is nonzero when `n ≥ 1` and `μ - n + 1 ≠ 0`. -/
theorem sum_qIntZ_sub_ne_zero (hq : IsGenericParam q) (μ : ℤ) {n : ℕ} (hn : 0 < n)
    (hμ : μ - n + 1 ≠ 0) : ∑ k ∈ range n, qIntZ q (μ - 2 * k) ≠ 0 := by
  have : ∑ k ∈ range n, qIntZ q (μ - 2 * k) = -∑ k ∈ range n, qIntZ q (-μ + 2 * k) := by
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun k _ => ?_
    rw [← qIntZ_neg]; congr 1; ring
  rw [this, neg_ne_zero]
  exact sum_qIntZ_ne_zero hq (-μ) hn (by omega)

end QInt

/-- **A weight module for `U̇(sl₂)` with bounded weights** over a field `K` with parameter `q`:
endomorphisms `E`, `F` of the `K`-module `V` and weight subspaces `Wt t` (of weight `n₀ + 2t`)
with `E (Wt t) ⊆ Wt (t + 1)`, `F (Wt (t + 1)) ⊆ Wt t`, `EF - FE = [n₀ + 2t]` on `Wt t`, and
`Wt t = 0` for `|t|` large. -/
structure WtModule (K : Type*) [Field K] (q : K) (V : Type*) [AddCommGroup V] [Module K V] where
  /-- The weight of `Wt 0`. -/
  n₀ : ℤ
  /-- The raising operator. -/
  E : V →ₗ[K] V
  /-- The lowering operator. -/
  F : V →ₗ[K] V
  /-- The weight subspaces; `Wt t` has weight `n₀ + 2t`. -/
  Wt : ℤ → Submodule K V
  E_mem : ∀ t, ∀ v ∈ Wt t, E v ∈ Wt (t + 1)
  F_mem : ∀ t, ∀ v ∈ Wt (t + 1), F v ∈ Wt t
  rel : ∀ t, ∀ v ∈ Wt t, E (F v) - F (E v) = qIntZ q (n₀ + 2 * t) • v
  bdd : ∃ N : ℕ, ∀ t : ℤ, (N : ℤ) ≤ |t| → ∀ v ∈ Wt t, v = 0

namespace WtModule

variable {K : Type*} [Field K] {q : K} {V : Type*} [AddCommGroup V] [Module K V]
  (M : WtModule K q V)

/-- The weight `n₀ + 2t` of `Wt t`. -/
def wt (t : ℤ) : ℤ := M.n₀ + 2 * t

theorem F_mem' {t : ℤ} {v : V} (hv : v ∈ M.Wt t) : M.F v ∈ M.Wt (t - 1) :=
  M.F_mem (t - 1) v (by rwa [sub_add_cancel])

theorem E_pow_mem {t : ℤ} {v : V} (hv : v ∈ M.Wt t) : ∀ i : ℕ, (M.E ^ i) v ∈ M.Wt (t + i)
  | 0 => by simpa using hv
  | i + 1 => by
    rw [pow_succ', Module.End.mul_apply]
    have := M.E_mem _ _ (E_pow_mem hv i)
    rwa [Nat.cast_succ, ← add_assoc]

theorem F_pow_mem {t : ℤ} {v : V} (hv : v ∈ M.Wt t) : ∀ i : ℕ, (M.F ^ i) v ∈ M.Wt (t - i)
  | 0 => by simpa using hv
  | i + 1 => by
    rw [pow_succ', Module.End.mul_apply]
    have := M.F_mem' (F_pow_mem hv i)
    rwa [Nat.cast_succ, ← sub_sub]

theorem eq_zero_of_abs_le {t : ℤ} {v : V} (hv : v ∈ M.Wt t) {N : ℕ}
    (hN : ∀ t : ℤ, (N : ℤ) ≤ |t| → ∀ v ∈ M.Wt t, v = 0) (ht : (N : ℤ) ≤ |t|) : v = 0 :=
  hN t ht v hv

/-- **Commutation of `F` with powers of `E`**: on `Wt t`,
`E^{j+1} F - F E^{j+1} = (∑_{i ≤ j} [wt t + 2i]) E^j`. -/
theorem comm_E_pow {t : ℤ} {v : V} (hv : v ∈ M.Wt t) : ∀ j : ℕ,
    (M.E ^ (j + 1)) (M.F v) - M.F ((M.E ^ (j + 1)) v) =
      (∑ i ∈ range (j + 1), qIntZ q (M.wt t + 2 * i)) • (M.E ^ j) v
  | 0 => by simpa [wt] using M.rel t v hv
  | j + 1 => by
    have ih := sub_eq_iff_eq_add.1 (comm_E_pow hv j)
    have hw := M.E_pow_mem hv (j + 1)
    have hr := sub_eq_iff_eq_add.1 (M.rel _ _ hw)
    have hE : M.E ((M.E ^ j) v) = (M.E ^ (j + 1)) v := by rw [pow_succ', Module.End.mul_apply]
    have hL : (M.E ^ (j + 1 + 1)) (M.F v) = M.E ((M.E ^ (j + 1)) (M.F v)) := by
      rw [pow_succ' M.E (j + 1), Module.End.mul_apply]
    have hL' : M.F ((M.E ^ (j + 1 + 1)) v) = M.F (M.E ((M.E ^ (j + 1)) v)) := by
      rw [pow_succ' M.E (j + 1), Module.End.mul_apply]
    have hi : M.n₀ + 2 * (t + ↑(j + 1)) = M.wt t + 2 * ↑(j + 1) := by simp only [wt]; ring
    rw [hi] at hr
    rw [hL, hL', ih, map_add, map_smul, hE, hr, sum_range_succ _ (j + 1), add_smul]
    abel

/-- **Commutation of `E` with powers of `F`**: on `Wt t`,
`E F^{j+1} - F^{j+1} E = (∑_{k ≤ j} [wt t - 2k]) F^j`. -/
theorem comm_F_pow {t : ℤ} {v : V} (hv : v ∈ M.Wt t) : ∀ j : ℕ,
    M.E ((M.F ^ (j + 1)) v) - (M.F ^ (j + 1)) (M.E v) =
      (∑ k ∈ range (j + 1), qIntZ q (M.wt t - 2 * k)) • (M.F ^ j) v
  | 0 => by simpa [wt] using M.rel t v hv
  | j + 1 => by
    have ih := sub_eq_iff_eq_add.1 (comm_F_pow hv j)
    have hu := M.F_pow_mem hv (j + 1)
    have hr := sub_eq_iff_eq_add.1 (M.rel _ _ hu)
    have hF : M.F ((M.F ^ j) v) = (M.F ^ (j + 1)) v := by rw [pow_succ', Module.End.mul_apply]
    have hL : M.E ((M.F ^ (j + 1 + 1)) v) = M.E (M.F ((M.F ^ (j + 1)) v)) := by
      rw [pow_succ' M.F (j + 1), Module.End.mul_apply]
    have hL' : (M.F ^ (j + 1 + 1)) (M.E v) = M.F ((M.F ^ (j + 1)) (M.E v)) := by
      rw [pow_succ' M.F (j + 1), Module.End.mul_apply]
    have hi : M.n₀ + 2 * (t - ↑(j + 1)) = M.wt t - 2 * ↑(j + 1) := by simp only [wt]; ring
    rw [hi] at hr
    rw [hL, hL', hr, ih, map_add, map_smul, hF, sum_range_succ _ (j + 1), add_smul]
    abel

/-- Every weight vector is killed by a power of `E`. -/
theorem exists_E_pow_eq_zero {t : ℤ} {v : V} (hv : v ∈ M.Wt t) : ∃ a : ℕ, (M.E ^ a) v = 0 := by
  obtain ⟨N, hN⟩ := M.bdd
  refine ⟨N + t.natAbs, hN _ ?_ _ (M.E_pow_mem hv _)⟩
  push_cast
  rw [le_abs]
  left
  linarith [neg_abs_le t]

variable {M}

/-- If `F v = 0` and `E^{i+1} v = 0` for a weight vector `v` of weight `μ` with `μ + i ≠ 0`, then
`E^i v = 0`. -/
theorem E_pow_eq_zero_of_F_eq_zero (hq : IsGenericParam q) {t : ℤ} {v : V} (hv : v ∈ M.Wt t)
    (hF : M.F v = 0) {i : ℕ} (hi : M.wt t + i ≠ 0) (h : (M.E ^ (i + 1)) v = 0) :
    (M.E ^ i) v = 0 := by
  have hc := M.comm_E_pow hv i
  rw [hF, map_zero, h, map_zero, sub_zero, eq_comm] at hc
  refine (smul_eq_zero.1 hc).resolve_left (sum_qIntZ_ne_zero hq _ (Nat.succ_pos i) ?_)
  push_cast; omega

/-- **Lemma P**: a weight vector `v` of weight `μ` with `E^j v = 0` for some `j ≤ -μ` is zero. -/
theorem eq_zero_of_E_pow_eq_zero (hq : IsGenericParam q) :
    ∀ {t : ℤ} {v : V}, v ∈ M.Wt t → ∀ j : ℕ, (j : ℤ) ≤ -M.wt t → (M.E ^ j) v = 0 → v = 0 := by
  obtain ⟨N, hN⟩ := M.bdd
  suffices H : ∀ d : ℕ, ∀ {t : ℤ} {v : V}, t ≤ -(N : ℤ) + d → v ∈ M.Wt t →
      ∀ j : ℕ, (j : ℤ) ≤ -M.wt t → (M.E ^ j) v = 0 → v = 0 by
    intro t v hv j hj h
    exact H (t + N).toNat (by omega) hv j hj h
  intro d
  induction d with
  | zero =>
    intro t v ht hv _ _ _
    refine hN t ?_ v hv
    rw [le_abs]; right; push_cast at ht; omega
  | succ d ih =>
    intro t v ht hv j hj h
    -- `F v` has weight `μ - 2` and is killed by `E^{j+1}`
    have hFv : M.F v = 0 := by
      refine ih (t := t - 1) (by push_cast at ht ⊢; omega) (M.F_mem' hv) (j + 1)
        (by simp only [wt] at hj ⊢; push_cast; omega) ?_
      have hc := M.comm_E_pow hv j
      have h1 : (M.E ^ (j + 1)) v = 0 := by rw [pow_succ', Module.End.mul_apply, h, map_zero]
      rw [h1, h, map_zero, sub_zero, smul_zero] at hc
      exact hc
    -- descend: `E^j v = 0 ⇒ E^{j-1} v = 0 ⇒ ⋯ ⇒ v = 0`
    have key : ∀ k : ℕ, k ≤ j → (M.E ^ (j - k)) v = 0 := by
      intro k
      induction k with
      | zero => intro _; simpa using h
      | succ k ihk =>
        intro hk
        have h' := ihk (by omega)
        rw [show j - k = (j - (k + 1)) + 1 by omega] at h'
        refine E_pow_eq_zero_of_F_eq_zero hq hv hFv ?_ h'
        simp only [wt] at hj ⊢
        omega
    simpa using key j le_rfl

/-- For `E v = 0`: `E F^{k+1} v = (∑_{i ≤ k} [wt t - 2i]) F^k v`. -/
theorem E_F_pow_of_E_eq_zero {t : ℤ} {v : V} (hv : v ∈ M.Wt t) (hE : M.E v = 0) (k : ℕ) :
    M.E ((M.F ^ (k + 1)) v) = (∑ i ∈ range (k + 1), qIntZ q (M.wt t - 2 * i)) • (M.F ^ k) v := by
  have := M.comm_F_pow hv k
  rwa [hE, map_zero, sub_zero] at this

/-- For `E v = 0` and `i ≤ m`: `E^i F^m v = c F^{m-i} v` with
`c = ∏_{k<i} ∑_{l<m-k} [wt t - 2l]`. -/
theorem E_pow_F_pow_of_E_eq_zero {t : ℤ} {v : V} (hv : v ∈ M.Wt t) (hE : M.E v = 0) (m : ℕ) :
    ∀ i : ℕ, i ≤ m → (M.E ^ i) ((M.F ^ m) v) =
      (∏ k ∈ range i, ∑ l ∈ range (m - k), qIntZ q (M.wt t - 2 * l)) • (M.F ^ (m - i)) v
  | 0, _ => by simp
  | i + 1, hi => by
    rw [pow_succ', Module.End.mul_apply, E_pow_F_pow_of_E_eq_zero hv hE m i (by omega), map_smul,
      show m - i = (m - (i + 1)) + 1 by omega, E_F_pow_of_E_eq_zero hv hE, smul_smul,
      prod_range_succ, show m - (i + 1) + 1 = m - i by omega]

theorem prod_ne_zero_aux (hq : IsGenericParam q) (μ : ℤ) (m i : ℕ) (hi : i ≤ m)
    (hμ : ∀ k, k < i → μ - (m - k : ℕ) + 1 ≠ 0) :
    ∏ k ∈ range i, ∑ l ∈ range (m - k), qIntZ q (μ - 2 * l) ≠ 0 := by
  rw [prod_ne_zero_iff]
  intro k hk
  rw [mem_range] at hk
  exact sum_qIntZ_sub_ne_zero hq μ (by omega) (hμ k hk)

section Equivariance

variable {V' : Type*} [AddCommGroup V'] [Module K V'] {M' : WtModule K q V'}
  (hn : M.n₀ = M'.n₀) (Φ : V →ₗ[K] V') (hΦ : ∀ t, ∀ v ∈ M.Wt t, Φ v ∈ M'.Wt t)
  (hΦE : ∀ v, Φ (M.E v) = M'.E (Φ v))

variable (M M') in
/-- The defect `δ v = Φ (F v) - F (Φ v)`. -/
def δ (v : V) : V' := Φ (M.F v) - M'.F (Φ v)

include hΦ in
theorem δ_mem {t : ℤ} {v : V} (hv : v ∈ M.Wt t) : δ M M' Φ v ∈ M'.Wt (t - 1) :=
  sub_mem (hΦ _ _ (M.F_mem' hv)) (M'.F_mem' (hΦ _ _ hv))

theorem δ_smul (c : K) (v : V) : δ M M' Φ (c • v) = c • δ M M' Φ v := by
  simp only [δ, map_smul, smul_sub]

theorem δ_sub (v w : V) : δ M M' Φ (v - w) = δ M M' Φ v - δ M M' Φ w := by
  simp only [δ, map_sub]; abel

theorem δ_zero : δ M M' Φ (0 : V) = 0 := by simp [δ]

include hn hΦ hΦE in
/-- **`δ` commutes with `E`**. -/
theorem δ_E {t : ℤ} {v : V} (hv : v ∈ M.Wt t) : δ M M' Φ (M.E v) = M'.E (δ M M' Φ v) := by
  have h1 := M.rel t v hv
  have h2 := M'.rel t (Φ v) (hΦ t v hv)
  rw [← hn] at h2
  simp only [δ, map_sub, ← hΦE]
  rw [sub_eq_iff_eq_add.1 h1, sub_eq_iff_eq_add.1 h2, map_add, map_smul, ← hΦE]
  abel

include hn hΦ hΦE in
theorem δ_E_pow {t : ℤ} {v : V} (hv : v ∈ M.Wt t) :
    ∀ i : ℕ, δ M M' Φ ((M.E ^ i) v) = (M'.E ^ i) (δ M M' Φ v)
  | 0 => rfl
  | i + 1 => by
    rw [pow_succ', Module.End.mul_apply, δ_E hn Φ hΦ hΦE (M.E_pow_mem hv i), δ_E_pow hv i,
      pow_succ', Module.End.mul_apply]

include hn hΦ hΦE in
/-- **Highest weight vectors**: if `E u = 0` and `u` has weight `m ≥ 0`, then `δ (F^i u) = 0`
for all `i ≤ m`. -/
theorem δ_F_pow_eq_zero (hq : IsGenericParam q) {t : ℤ} {u : V} (hu : u ∈ M.Wt t)
    (hE : M.E u = 0) {m : ℕ} (hm : (m : ℤ) = M.wt t) {i : ℕ} (hi : i ≤ m) :
    δ M M' Φ ((M.F ^ i) u) = 0 := by
  have hw : δ M M' Φ ((M.F ^ m) u) = 0 := by
    refine M'.eq_zero_of_E_pow_eq_zero hq (t := t - m - 1) ?_ (m + 1) ?_ ?_
    · have := δ_mem Φ hΦ (M.F_pow_mem hu m)
      rwa [sub_sub] at this ⊢
    · simp only [wt] at hm ⊢; rw [← hn]; push_cast; omega
    · rw [← δ_E_pow hn Φ hΦ hΦE (M.F_pow_mem hu m), pow_succ', Module.End.mul_apply,
        E_pow_F_pow_of_E_eq_zero hu hE m m le_rfl, Nat.sub_self, pow_zero, map_smul,
        Module.End.one_apply, hE, smul_zero, δ_zero]
  have h := δ_E_pow hn Φ hΦ hΦE (M.F_pow_mem hu m) (m - i)
  rw [hw, map_zero, E_pow_F_pow_of_E_eq_zero hu hE m (m - i) (by omega), δ_smul,
    show m - (m - i) = i by omega] at h
  refine (smul_eq_zero.1 h).resolve_left (prod_ne_zero_aux hq _ m (m - i) (by omega) ?_)
  intro k hk
  omega

include hn hΦ hΦE in
/-- **`E`-equivariance implies `F`-equivariance** (main theorem, by induction on the least `a`
with `E^a v = 0`). -/
theorem δ_eq_zero (hq : IsGenericParam q) :
    ∀ a : ℕ, ∀ {t : ℤ} {v : V}, v ∈ M.Wt t → (M.E ^ a) v = 0 → δ M M' Φ v = 0 := by
  intro a
  induction a with
  | zero => intro t v _ h; simp only [pow_zero, Module.End.one_apply] at h; rw [h, δ_zero]
  | succ a ih =>
    intro t v hv h
    by_cases hμ : M.wt t + (a + 1 : ℕ) ≤ 0
    · rw [M.eq_zero_of_E_pow_eq_zero hq hv (a + 1) (by omega) h, δ_zero]
    push Not at hμ
    set u := (M.E ^ a) v with hu_def
    have hu : u ∈ M.Wt (t + a) := M.E_pow_mem hv a
    have hEu : M.E u = 0 := by rw [hu_def, ← Module.End.mul_apply, ← pow_succ']; exact h
    have hwu : M.wt (t + a) = M.wt t + 2 * a := by simp only [wt]; ring
    set c := ∏ k ∈ range a, ∑ l ∈ range (a - k), qIntZ q (M.wt (t + a) - 2 * l) with hc_def
    have hc : c ≠ 0 := prod_ne_zero_aux hq _ a a le_rfl (fun k hk => by push_cast at hμ ⊢; omega)
    have hFu : (M.F ^ a) u ∈ M.Wt t := by
      have := M.F_pow_mem hu a
      rwa [add_sub_cancel_right] at this
    have hEF : (M.E ^ a) ((M.F ^ a) u) = c • u := by
      rw [E_pow_F_pow_of_E_eq_zero hu hEu a a le_rfl, Nat.sub_self, pow_zero, Module.End.one_apply]
    have h1 : δ M M' Φ (v - c⁻¹ • (M.F ^ a) u) = 0 := by
      refine ih (sub_mem hv (Submodule.smul_mem _ _ hFu)) ?_
      rw [map_sub, map_smul, hEF, smul_smul, inv_mul_cancel₀ hc, one_smul, sub_self]
    have h2 : δ M M' Φ ((M.F ^ a) u) = 0 :=
      δ_F_pow_eq_zero hn Φ hΦ hΦE hq hu hEu (m := (M.wt (t + a)).toNat) (by omega) (by omega)
    rw [δ_sub, δ_smul, h2, smul_zero, sub_zero] at h1
    exact h1

include hn hΦ hΦE in
/-- **Main theorem**: a weight-preserving linear map `Φ : V → V'` between weight modules with
bounded weights (same weights, generic `q`) that commutes with `E` also commutes with `F`. -/
theorem F_comm_of_E_comm (hq : IsGenericParam q) {t : ℤ} {v : V} (hv : v ∈ M.Wt t) :
    Φ (M.F v) = M'.F (Φ v) := by
  obtain ⟨a, ha⟩ := M.exists_E_pow_eq_zero hv
  exact sub_eq_zero.1 (δ_eq_zero hn Φ hΦ hΦE hq a hv ha)

end Equivariance

end WtModule

end Categorification.TwoRep
