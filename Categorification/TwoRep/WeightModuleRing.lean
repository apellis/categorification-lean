/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.TorsionSeq

/-!
# Weight modules over a commutative ring in which the quantum integers are units

The ring version of `WeightModule.lean` (used for S. Cautis, A. D. Lauda, *Implicit structure in
2-representations of quantum groups*, arXiv:1111.1431v3, §3, Proposition 3.9 `prop:lradj`): the
coefficient ring `K` is any commutative ring with a family of "quantum integers" `Q.qi : ℤ → K`
(`QInts`) such that `[-m] = -[m]` and the sums `∑_{i<n} [μ + 2i]` (`= [n][μ + n - 1]`) are units
whenever `n ≥ 1` and `μ + n - 1 ≠ 0`. No finiteness, freeness or torsion-freeness is assumed.
The proof is that of `WeightModule.lean`, with "nonzero" replaced by "unit".

## Main results

* `WtModuleR.F_comm_of_E_comm`: **a weight-preserving `K`-linear map between two weight modules
  with bounded weights which commutes with `E` also commutes with `F`.**
* `WtModuleR.homDual`: linear maps from a weight module (spanned by its weight spaces) to any
  `K`-module form a weight module, with `E^† φ = φ ∘ F`, `F^† φ = φ ∘ E`.
* `Tors.qInts`: the quantum integers of `Tors.Rq = ℚ[T, T⁻¹][[n]⁻¹ : n ≥ 1]` (`TorsionSeq.lean`).
-/

noncomputable section

namespace Categorification.TwoRep

open Finset

/-- **Quantum integers in a commutative ring** with the unit conditions used by the `sl₂` lemma. -/
structure QInts (K : Type*) [CommRing K] where
  /-- The quantum integer `[m]`. -/
  qi : ℤ → K
  qi_neg : ∀ m, qi (-m) = -qi m
  /-- `∑_{i<n} [μ + 2i] = [n][μ + n - 1]` is a unit for `n ≥ 1`, `μ + n - 1 ≠ 0`. -/
  sum_isUnit : ∀ (μ : ℤ) (n : ℕ), 0 < n → μ + n - 1 ≠ 0 →
    IsUnit (∑ i ∈ range n, qi (μ + 2 * i))

namespace QInts

variable {K : Type*} [CommRing K] (Q : QInts K)

/-- The sum `∑_{k<n} [μ - 2k]` is a unit when `n ≥ 1` and `μ - n + 1 ≠ 0`. -/
theorem sum_sub_isUnit (μ : ℤ) {n : ℕ} (hn : 0 < n) (hμ : μ - n + 1 ≠ 0) :
    IsUnit (∑ k ∈ range n, Q.qi (μ - 2 * k)) := by
  have : ∑ k ∈ range n, Q.qi (μ - 2 * k) = -∑ k ∈ range n, Q.qi (-μ + 2 * k) := by
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun k _ => ?_
    rw [← Q.qi_neg]; congr 1; ring
  rw [this]
  exact (Q.sum_isUnit (-μ) n hn (by omega)).neg

end QInts

/-- The quantum integers of `Tors.Rq`. -/
def Tors.qInts : QInts Tors.Rq where
  qi := Tors.qiR
  qi_neg := Tors.qiR_neg
  sum_isUnit μ n hn hμ := by
    rw [Tors.sum_qiR]
    exact (Tors.isUnit_qiR (by omega)).mul (Tors.isUnit_qiR hμ)

/-- **A weight module for `U̇(sl₂)` with bounded weights** over a commutative ring `K` with quantum integers `Q`:
endomorphisms `E`, `F` of the `K`-module `V` and weight subspaces `Wt t` (of weight `n₀ + 2t`)
with `E (Wt t) ⊆ Wt (t + 1)`, `F (Wt (t + 1)) ⊆ Wt t`, `EF - FE = [n₀ + 2t]` on `Wt t`, and
`Wt t = 0` for `|t|` large. -/
structure WtModuleR (K : Type*) [CommRing K] (Q : QInts K) (V : Type*) [AddCommGroup V] [Module K V] where
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
  rel : ∀ t, ∀ v ∈ Wt t, E (F v) - F (E v) = Q.qi (n₀ + 2 * t) • v
  bdd : ∃ N : ℕ, ∀ t : ℤ, (N : ℤ) ≤ |t| → ∀ v ∈ Wt t, v = 0

namespace WtModuleR

variable {K : Type*} [CommRing K] {Q : QInts K} {V : Type*} [AddCommGroup V] [Module K V]
  (M : WtModuleR K Q V)

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
      (∑ i ∈ range (j + 1), Q.qi (M.wt t + 2 * i)) • (M.E ^ j) v
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
      (∑ k ∈ range (j + 1), Q.qi (M.wt t - 2 * k)) • (M.F ^ j) v
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
theorem E_pow_eq_zero_of_F_eq_zero {t : ℤ} {v : V} (hv : v ∈ M.Wt t)
    (hF : M.F v = 0) {i : ℕ} (hi : M.wt t + i ≠ 0) (h : (M.E ^ (i + 1)) v = 0) :
    (M.E ^ i) v = 0 := by
  have hc := M.comm_E_pow hv i
  rw [hF, map_zero, h, map_zero, sub_zero, eq_comm] at hc
  refine (Q.sum_isUnit _ _ (Nat.succ_pos i) ?_).smul_eq_zero.1 hc
  push_cast; omega

/-- **Lemma P**: a weight vector `v` of weight `μ` with `E^j v = 0` for some `j ≤ -μ` is zero. -/
theorem eq_zero_of_E_pow_eq_zero :
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
        refine E_pow_eq_zero_of_F_eq_zero hv hFv ?_ h'
        simp only [wt] at hj ⊢
        omega
    simpa using key j le_rfl

/-- For `E v = 0`: `E F^{k+1} v = (∑_{i ≤ k} [wt t - 2i]) F^k v`. -/
theorem E_F_pow_of_E_eq_zero {t : ℤ} {v : V} (hv : v ∈ M.Wt t) (hE : M.E v = 0) (k : ℕ) :
    M.E ((M.F ^ (k + 1)) v) = (∑ i ∈ range (k + 1), Q.qi (M.wt t - 2 * i)) • (M.F ^ k) v := by
  have := M.comm_F_pow hv k
  rwa [hE, map_zero, sub_zero] at this

/-- For `E v = 0` and `i ≤ m`: `E^i F^m v = c F^{m-i} v` with
`c = ∏_{k<i} ∑_{l<m-k} [wt t - 2l]`. -/
theorem E_pow_F_pow_of_E_eq_zero {t : ℤ} {v : V} (hv : v ∈ M.Wt t) (hE : M.E v = 0) (m : ℕ) :
    ∀ i : ℕ, i ≤ m → (M.E ^ i) ((M.F ^ m) v) =
      (∏ k ∈ range i, ∑ l ∈ range (m - k), Q.qi (M.wt t - 2 * l)) • (M.F ^ (m - i)) v
  | 0, _ => by simp
  | i + 1, hi => by
    rw [pow_succ', Module.End.mul_apply, E_pow_F_pow_of_E_eq_zero hv hE m i (by omega), map_smul,
      show m - i = (m - (i + 1)) + 1 by omega, E_F_pow_of_E_eq_zero hv hE, smul_smul,
      prod_range_succ, show m - (i + 1) + 1 = m - i by omega]

theorem prod_isUnit_aux (μ : ℤ) (m i : ℕ) (hi : i ≤ m)
    (hμ : ∀ k, k < i → μ - (m - k : ℕ) + 1 ≠ 0) :
    IsUnit (∏ k ∈ range i, ∑ l ∈ range (m - k), Q.qi (μ - 2 * l)) := by
  refine Finset.prod_induction _ IsUnit (fun _ _ ha hb => ha.mul hb) isUnit_one ?_
  intro k hk
  rw [mem_range] at hk
  exact Q.sum_sub_isUnit μ (by omega) (hμ k hk)

section Equivariance

variable {V' : Type*} [AddCommGroup V'] [Module K V'] {M' : WtModuleR K Q V'}
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
theorem δ_F_pow_eq_zero {t : ℤ} {u : V} (hu : u ∈ M.Wt t)
    (hE : M.E u = 0) {m : ℕ} (hm : (m : ℤ) = M.wt t) {i : ℕ} (hi : i ≤ m) :
    δ M M' Φ ((M.F ^ i) u) = 0 := by
  have hw : δ M M' Φ ((M.F ^ m) u) = 0 := by
    refine M'.eq_zero_of_E_pow_eq_zero (t := t - m - 1) ?_ (m + 1) ?_ ?_
    · have := δ_mem Φ hΦ (M.F_pow_mem hu m)
      rwa [sub_sub] at this ⊢
    · simp only [wt] at hm ⊢; rw [← hn]; push_cast; omega
    · rw [← δ_E_pow hn Φ hΦ hΦE (M.F_pow_mem hu m), pow_succ', Module.End.mul_apply,
        E_pow_F_pow_of_E_eq_zero hu hE m m le_rfl, Nat.sub_self, pow_zero, map_smul,
        Module.End.one_apply, hE, smul_zero, δ_zero]
  have h := δ_E_pow hn Φ hΦ hΦE (M.F_pow_mem hu m) (m - i)
  rw [hw, map_zero, E_pow_F_pow_of_E_eq_zero hu hE m (m - i) (by omega), δ_smul,
    show m - (m - i) = i by omega] at h
  refine (prod_isUnit_aux _ m (m - i) (by omega) ?_).smul_eq_zero.1 h
  intro k hk
  omega

include hn hΦ hΦE in
/-- **`E`-equivariance implies `F`-equivariance** (main theorem, by induction on the least `a`
with `E^a v = 0`). -/
theorem δ_eq_zero :
    ∀ a : ℕ, ∀ {t : ℤ} {v : V}, v ∈ M.Wt t → (M.E ^ a) v = 0 → δ M M' Φ v = 0 := by
  intro a
  induction a with
  | zero => intro t v _ h; simp only [pow_zero, Module.End.one_apply] at h; rw [h, δ_zero]
  | succ a ih =>
    intro t v hv h
    by_cases hμ : M.wt t + (a + 1 : ℕ) ≤ 0
    · rw [M.eq_zero_of_E_pow_eq_zero hv (a + 1) (by omega) h, δ_zero]
    push Not at hμ
    set u := (M.E ^ a) v with hu_def
    have hu : u ∈ M.Wt (t + a) := M.E_pow_mem hv a
    have hEu : M.E u = 0 := by rw [hu_def, ← Module.End.mul_apply, ← pow_succ']; exact h
    have hwu : M.wt (t + a) = M.wt t + 2 * a := by simp only [wt]; ring
    set c := ∏ k ∈ range a, ∑ l ∈ range (a - k), Q.qi (M.wt (t + a) - 2 * l) with hc_def
    have hc : IsUnit c := prod_isUnit_aux _ a a le_rfl (fun k hk => by push_cast at hμ ⊢; omega)
    have hFu : (M.F ^ a) u ∈ M.Wt t := by
      have := M.F_pow_mem hu a
      rwa [add_sub_cancel_right] at this
    have hEF : (M.E ^ a) ((M.F ^ a) u) = c • u := by
      rw [E_pow_F_pow_of_E_eq_zero hu hEu a a le_rfl, Nat.sub_self, pow_zero, Module.End.one_apply]
    have h1 : δ M M' Φ (v - ((hc.unit⁻¹ : Kˣ) : K) • (M.F ^ a) u) = 0 := by
      refine ih (sub_mem hv (Submodule.smul_mem _ _ hFu)) ?_
      rw [map_sub, map_smul, hEF, smul_smul, hc.val_inv_mul, one_smul, sub_self]
    have h2 : δ M M' Φ ((M.F ^ a) u) = 0 :=
      δ_F_pow_eq_zero hn Φ hΦ hΦE hu hEu (m := (M.wt (t + a)).toNat) (by omega) (by omega)
    rw [δ_sub, δ_smul, h2, smul_zero, sub_zero] at h1
    exact h1

include hn hΦ hΦE in
/-- **Main theorem**: a weight-preserving linear map `Φ : V → V'` between weight modules with
bounded weights (same weights, quantum integers units) that commutes with `E` also commutes with `F`. -/
theorem F_comm_of_E_comm {t : ℤ} {v : V} (hv : v ∈ M.Wt t) :
    Φ (M.F v) = M'.F (Φ v) := by
  obtain ⟨a, ha⟩ := M.exists_E_pow_eq_zero hv
  exact sub_eq_zero.1 (δ_eq_zero hn Φ hΦ hΦE a hv ha)

end Equivariance

end WtModuleR


namespace WtModuleR

variable {K : Type*} [CommRing K] {Q : QInts K} {V : Type*} [AddCommGroup V] [Module K V]
  (M : WtModuleR K Q V) (P : Type*) [AddCommGroup P] [Module K P]

/-- The linear maps supported on the weight space `Wt t`. -/
def homWt (t : ℤ) : Submodule K (V →ₗ[K] P) where
  carrier := {φ | ∀ s : ℤ, s ≠ t → ∀ v ∈ M.Wt s, φ v = 0}
  add_mem' := fun {φ ψ} hφ hψ s hs v hv => by
    rw [LinearMap.add_apply, hφ s hs v hv, hψ s hs v hv, add_zero]
  zero_mem' := fun _ _ _ _ => rfl
  smul_mem' := fun c φ hφ s hs v hv => by rw [LinearMap.smul_apply, hφ s hs v hv, smul_zero]

/-- **The `P`-valued dual of a weight module** spanned by its weight spaces: `E^† φ = φ ∘ F`,
`F^† φ = φ ∘ E`, and the weight-`t` maps are those supported on `Wt t`. -/
def homDual (hspan : ⨆ t, M.Wt t = ⊤) : WtModuleR K Q (V →ₗ[K] P) where
  n₀ := M.n₀
  E := LinearMap.lcomp K P M.F
  F := LinearMap.lcomp K P M.E
  Wt := M.homWt P
  E_mem t φ hφ s hs v hv := by
    rw [LinearMap.lcomp_apply]
    exact hφ (s - 1) (by omega) _ (M.F_mem' hv)
  F_mem t φ hφ s hs v hv := by
    rw [LinearMap.lcomp_apply]
    exact hφ (s + 1) (by omega) _ (M.E_mem s v hv)
  rel t φ hφ := by
    have key : ∀ v : V, v ∈ (⊤ : Submodule K V) →
        v ∈ LinearMap.ker ((φ ∘ₗ M.E) ∘ₗ M.F - (φ ∘ₗ M.F) ∘ₗ M.E - Q.qi (M.n₀ + 2 * t) • φ) := by
      rw [← hspan]
      intro v hv
      refine (iSup_le fun s => ?_ : ⨆ s, M.Wt s ≤ _) hv
      intro w hw
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
        ← map_sub, M.rel s w hw, map_smul]
      by_cases hs : s = t
      · subst hs; exact sub_self _
      · rw [hφ s hs w hw, smul_zero, smul_zero, sub_zero]
    ext v
    have := LinearMap.mem_ker.1 (key v Submodule.mem_top)
    rw [LinearMap.sub_apply, LinearMap.sub_apply, sub_eq_zero] at this
    simp only [LinearMap.sub_apply, LinearMap.lcomp_apply]
    exact this
  bdd := by
    obtain ⟨N, hN⟩ := M.bdd
    refine ⟨N, fun t ht φ hφ => ?_⟩
    have key : ∀ v : V, v ∈ (⊤ : Submodule K V) → v ∈ LinearMap.ker φ := by
      rw [← hspan]
      intro v hv
      refine (iSup_le fun s => ?_ : ⨆ s, M.Wt s ≤ _) hv
      intro w hw
      rw [LinearMap.mem_ker]
      by_cases hs : s = t
      · subst hs; rw [hN s ht w hw, map_zero]
      · exact hφ s hs w hw
    ext v
    exact LinearMap.mem_ker.1 (key v Submodule.mem_top)

end WtModuleR

end Categorification.TwoRep
