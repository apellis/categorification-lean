/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.QuantumGroup.QBinomial

/-!
# The bilinear form on divided powers

Lusztig, *Introduction to quantum groups*, 1.4.4:
`(θ_i^{(a)}, θ_i^{(a)}) = ∏_{s=1}^a (1 - v_i^{-2s})^{-1}` for Lusztig's normalisation
`(θ_i, θ_i) = (1 - v_i^{-2})^{-1}`.

In Khovanov–Lauda, arXiv:0803.4121v2, the corresponding quantity is the graded dimension of
the nilHecke algebra (the pairing `([P_{i^{(a)}}], [P_{i^{(a)}}])`, compare KL I §2.5 and
Prop. 3.3); with KL's `q = v⁻¹` the formula reads `∏_{s=1}^a (1 - q^{2s})^{-1}`
(`CartanDatum.form_dpow_dpow`, `KL.form_dpow_dpow`).

## Main results

* `PreF.d_θ_pow` — `d_i (θ_i^{a+1}) = (Σ_{k ≤ a} v^{(i·i) k}) θ_i^a`;
* `PreF.form_θ_pow_self` — `(θ_i^a, θ_i^a) = ∏_{s=1}^a c_i (1 + v^{i·i} + ⋯ + v^{(s-1)(i·i)})`
  for arbitrary `c_i = (θ_i, θ_i)` over any commutative ring;
* `PreF.form_dpow_dpow` — Lusztig 1.4.4 over a field, given `[a]_{v_i}^! ≠ 0` and
  `1 - v_i^{-2} ≠ 0`; `CartanDatum.form_dpow_dpow` — unconditionally over `ℚ(v)`.
-/

noncomputable section

namespace Categorification.QuantumGroup

open Finset

namespace PreF

section CommRing

variable {I : Type*} {K : Type*} [CommRing K] {dot : I → I → ℤ} {v : Kˣ}

/-- `d_i (θ_i^{a+1}) = (1 + v^{i·i} + ⋯ + v^{a (i·i)}) θ_i^a`. -/
theorem d_θ_pow (i : I) (a : ℕ) :
    d dot v i ((θ i : PreF K I) ^ (a + 1)) =
      (∑ k ∈ range (a + 1), ((v ^ (dot i i * k) : Kˣ) : K)) • (θ i : PreF K I) ^ a := by
  induction a with
  | zero => simp [d_θ]
  | succ a ih =>
    rw [pow_succ' _ (a + 1), d_θ_mul, if_pos rfl, ih, mul_smul_comm, ← pow_succ', smul_smul,
      sum_range_succ' _ (a + 1)]
    have e : ∑ k ∈ range (a + 1), ((v ^ (dot i i * ((k + 1 : ℕ) : ℤ)) : Kˣ) : K) =
        ((v ^ dot i i : Kˣ) : K) * ∑ k ∈ range (a + 1), ((v ^ (dot i i * k) : Kˣ) : K) := by
      rw [mul_sum]
      refine sum_congr rfl fun k _ => ?_
      rw [← val_zpow_add]
      congr 2
      push_cast
      ring
    rw [e, Nat.cast_zero, mul_zero, zpow_zero, Units.val_one, add_smul, one_smul, add_comm]

/-- `(θ_i^a, θ_i^a) = ∏_{s=1}^a c_i (1 + v^{i·i} + ⋯ + v^{(s-1)(i·i)})`. -/
theorem form_θ_pow_self (c : I → K) (i : I) (a : ℕ) :
    form dot v c ((θ i : PreF K I) ^ a) (θ i ^ a) =
      ∏ s ∈ range a, (c i * ∑ k ∈ range (s + 1), ((v ^ (dot i i * k) : Kˣ) : K)) := by
  induction a with
  | zero => simp [form_one_one]
  | succ a ih =>
    rw [pow_succ' _ a, form_θ_mul, ← pow_succ', d_θ_pow, map_smul, smul_eq_mul, ih,
      prod_range_succ]
    ring

end CommRing

section Field

variable {I : Type*} {K : Type*} [Field K] {dot : I → I → ℤ} {v : Kˣ}

/-- The single-factor identity behind Lusztig 1.4.4:
`(1 - t^{-2})^{-1} (1 + t² + ⋯ + t^{2(n-1)}) [n]_t^{-2} = (1 - t^{-2n})^{-1}`. -/
theorem lusztig_factor (t : Kˣ) (n : ℕ) (hq : qint t n ≠ 0)
    (h1 : 1 - ((t ^ (-2 : ℤ) : Kˣ) : K) ≠ 0) :
    (1 - ((t ^ (-2 : ℤ) : Kˣ) : K))⁻¹ * (∑ k ∈ range n, ((t : K) ^ 2) ^ k) *
        (qint t n)⁻¹ * (qint t n)⁻¹ =
      (1 - ((t ^ (-(2 * (n : ℤ))) : Kˣ) : K))⁻¹ := by
  have hu : (t : K) ≠ 0 := Units.ne_zero t
  have hg := geom_sum_mul ((t : K) ^ 2) n
  set S := ∑ k ∈ range n, ((t : K) ^ 2) ^ k with hS
  have hS0 : S ≠ 0 := by
    intro h0; apply hq; rw [qint, ← hS, h0, mul_zero]
  have hq' : qint t n = ((t ^ (1 - (n : ℤ)) : Kˣ) : K) * S := rfl
  rw [hq']
  simp only [Units.val_zpow_eq_zpow_val] at h1 ⊢
  have e1 : (t : K) ^ (1 - (n : ℤ)) = (t : K) * ((t : K) ^ n)⁻¹ := by
    rw [zpow_sub₀ hu, zpow_one, zpow_natCast, div_eq_mul_inv]
  have e2 : (t : K) ^ (-(2 * (n : ℤ))) = (((t : K) ^ 2) ^ n)⁻¹ := by
    rw [zpow_neg, ← pow_mul, ← zpow_natCast]; push_cast; ring_nf
  have e3 : (t : K) ^ (-2 : ℤ) = ((t : K) ^ 2)⁻¹ := by
    rw [zpow_neg, zpow_ofNat]
  rw [e1, e2, e3]
  rw [e3] at h1
  have h1' : (t : K) ^ 2 - 1 ≠ 0 := by
    intro h0; apply h1; rw [sub_eq_zero] at h0 ⊢; rw [h0, inv_one]
  have hpow : ((t : K) ^ 2) ^ n - 1 ≠ 0 := by
    rw [← hg]; exact mul_ne_zero hS0 h1'
  have hA : (1 : K) - ((t : K) ^ 2)⁻¹ = ((t : K) ^ 2 - 1) / (t : K) ^ 2 := by
    field_simp
  have hB : (1 : K) - (((t : K) ^ 2) ^ n)⁻¹ = (((t : K) ^ 2) ^ n - 1) / ((t : K) ^ 2) ^ n := by
    field_simp
  rw [hA, hB, ← hg]
  field_simp
  ring

variable (dot v) in
/-- Lusztig 1.4.4 normalisation check: `v^{(i·i) k} = (v_i²)^k` when `i · i` is even. -/
theorem val_zpow_dot_mul (i : I) (hev : Even (dot i i)) (k : ℕ) :
    ((v ^ (dot i i * k) : Kˣ) : K) = ((vi dot v i : K) ^ 2) ^ k := by
  obtain ⟨h, hh⟩ := hev
  have e : dot i i / 2 = h := by omega
  rw [vi, e, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← pow_mul,
    ← zpow_natCast, ← zpow_mul, hh]
  congr 2
  push_cast
  ring

/-- **Lusztig 1.4.4**: with Lusztig's normalisation `(θ_i, θ_i) = (1 - v_i^{-2})^{-1}`,
`(θ_i^{(a)}, θ_i^{(a)}) = ∏_{s=1}^a (1 - v_i^{-2s})^{-1}`, provided `i · i` is even,
`[a]_{v_i}^! ≠ 0` and `1 - v_i^{-2} ≠ 0` (all automatic for a Cartan datum over `ℚ(v)`). -/
theorem form_dpow_dpow (i : I) (hev : Even (dot i i)) {a : ℕ} (hq : qfact (vi dot v i) a ≠ 0)
    (h1 : 1 - ((vi dot v i ^ (-2 : ℤ) : Kˣ) : K) ≠ 0) :
    form dot v (lusztigC dot v) (dpow dot v i a) (dpow dot v i a) =
      ∏ s ∈ range a, (1 - ((vi dot v i ^ (-(2 * ((s + 1 : ℕ) : ℤ))) : Kˣ) : K))⁻¹ := by
  have hc : lusztigC dot v i = (1 - ((vi dot v i ^ (-2 : ℤ) : Kˣ) : K))⁻¹ := by
    obtain ⟨h, hh⟩ := hev
    have e : dot i i / 2 = h := by omega
    rw [lusztigC, vi, e, ← zpow_mul, hh]
    congr 4
    ring
  simp only [dpow, map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [form_θ_pow_self, qfact, ← prod_inv_distrib, ← mul_assoc, ← prod_mul_distrib,
    ← prod_mul_distrib]
  refine prod_congr rfl fun s hs => ?_
  have hqs : qint (vi dot v i) (s + 1) ≠ 0 := by
    intro h0; apply hq; rw [qfact]; exact prod_eq_zero hs h0
  rw [← lusztig_factor (vi dot v i) (s + 1) hqs h1, hc]
  simp only [val_zpow_dot_mul dot v i hev]
  ring

end Field

end PreF

namespace CartanDatum

variable {I : Type*} (C : CartanDatum I)

theorem one_sub_vi_ne_zero (i : I) :
    1 - ((PreF.vi C.dot vQ i ^ (-2 : ℤ) : (RatFunc ℚ)ˣ) : RatFunc ℚ) ≠ 0 := by
  rw [PreF.vi, ← zpow_mul]
  refine one_sub_vQ_zpow_ne_zero ?_
  have h2 : 0 < C.dot i i / 2 := by
    obtain ⟨k, hk⟩ := C.dot_self_even i
    have := C.dot_self_pos i
    omega
  omega

/-- **Lusztig 1.4.4 over `ℚ(v)`** for a Cartan datum:
`(θ_i^{(a)}, θ_i^{(a)}) = ∏_{s=1}^a (1 - v_i^{-2s})^{-1}`. -/
theorem form_dpow_dpow (i : I) (a : ℕ) :
    C.form (PreF.dpow C.dot vQ i a) (PreF.dpow C.dot vQ i a) =
      ∏ s ∈ range a,
        (1 - ((PreF.vi C.dot vQ i ^ (-(2 * ((s + 1 : ℕ) : ℤ))) : (RatFunc ℚ)ˣ) : RatFunc ℚ))⁻¹ :=
  PreF.form_dpow_dpow i (C.dot_self_even i) (C.qfact_ne_zero i a) (C.one_sub_vi_ne_zero i)

end CartanDatum

namespace KL

variable {I : Type*} [DecidableEq I] (Γ : SimpleGraph I) [DecidableRel Γ.Adj]

/-- KL I normalisation (`i · i = 2`, `q = v⁻¹`):
`(θ_i^{(a)}, θ_i^{(a)}) = ∏_{s=1}^a (1 - q^{2s})^{-1}`. -/
theorem form_dpow_dpow (i : I) (a : ℕ) :
    (C Γ).form (PreF.dpow (C Γ).dot vQ i a) (PreF.dpow (C Γ).dot vQ i a) =
      ∏ s ∈ range a, (1 - ((vQ⁻¹ : (RatFunc ℚ)ˣ) : RatFunc ℚ) ^ (2 * (s + 1)))⁻¹ := by
  rw [CartanDatum.form_dpow_dpow]
  refine prod_congr rfl fun s _ => ?_
  have e : PreF.vi (C Γ).dot vQ i = vQ := by
    simp [PreF.vi]
  rw [e]
  congr 2

end KL

end Categorification.QuantumGroup

end
