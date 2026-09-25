/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.QuantumGroup.QBinomial
import Categorification.QuantumGroup.Serre

/-!
# The quantum Serre relations in divided-power form

Lusztig, *Introduction to quantum groups*, Proposition 1.4.3: for `i ≠ j` in a Cartan datum
and `N = 1 - 2 (i·j)/(i·i)`,
`Σ_{p + p' = N} (-1)^{p'} θ_i^{(p)} θ_j θ_i^{(p')} = 0` in `f`.
Khovanov–Lauda, arXiv:0803.4121v2, §3.1, use the simply-laced instances (`N = 1, 2`); for
`i · j = -1` this is `θ_i θ_j θ_i = θ_i^{(2)} θ_j + θ_j θ_i^{(2)}`, matching
`[P_{iji}] = [P_{i^{(2)}j}] + [P_{ji^{(2)}}]` in the proof of KL I Prop. 3.4
(`KL.serre_divided`).

`Categorification.QuantumGroup.Serre` proves the relation for the iterated twisted commutator
`x_N = serreSeq dot v i j N` (`x₀ = θ_j`, `x_{m+1} = θ_i x_m - v^{(j + m i)·i} x_m θ_i`).
Here we expand `x_m` (`PreF.serreSeq_eq_sum`):
`x_m = Σ_{p + p' = m} (-1)^{p'} v^{(j·i) p'} v_i^{p'(m-1)} [m choose p']_{v_i} θ_i^p θ_j θ_i^{p'}`,
and deduce, for `2 (i·j) = (i·i)(1 - N)`, the identity **with no extra powers of `v`**
`x_N = [N]_{v_i}^! · Σ_{p + p' = N} (-1)^{p'} θ_i^{(p)} θ_j θ_i^{(p')}`
(`PreF.serreSeq_eq_qfact_smul_serreDiv`). Hence Lusztig's divided-power Serre element lies in
the radical whenever `[N]_{v_i}^! ≠ 0` (`PreF.serreDiv_mem_radical`), in particular for every
Cartan datum over `ℚ(v)` (`CartanDatum.serreDiv_eq_zero`, `CartanDatum.serre_divided`).
-/

noncomputable section

namespace Categorification.QuantumGroup

open Finset

namespace PreF

variable {I : Type*} {K : Type*} [CommRing K] {dot : I → I → ℤ} {v : Kˣ}

variable (dot v) in
/-- The coefficients of the expansion of `x_m = serreSeq dot v i j m`: the coefficient of
`(-1)^{p'} θ_i^{m-p'} θ_j θ_i^{p'}` is `serreCoef dot v i j m p'`. -/
def serreCoef (i j : I) : ℕ → ℕ → K
  | _, 0 => 1
  | 0, _ + 1 => 0
  | m + 1, p + 1 => serreCoef i j m (p + 1) +
      ((v ^ (dot j i + m * dot i i) : Kˣ) : K) * serreCoef i j m p

@[simp] theorem serreCoef_zero_right (i j : I) (m : ℕ) : serreCoef dot v i j m 0 = (1 : K) := by
  cases m <;> rfl

theorem serreCoef_succ_succ (i j : I) (m p : ℕ) :
    serreCoef dot v i j (m + 1) (p + 1) = serreCoef dot v i j m (p + 1) +
      ((v ^ (dot j i + m * dot i i) : Kˣ) : K) * serreCoef dot v i j m p := rfl

theorem serreCoef_eq_zero_of_lt (i j : I) {m p : ℕ} (h : m < p) :
    serreCoef dot v i j m p = (0 : K) := by
  induction m generalizing p with
  | zero => obtain ⟨p, rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩; rfl
  | succ m ih =>
    obtain ⟨p, rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    rw [serreCoef_succ_succ, ih (by omega), ih (by omega), mul_zero, add_zero]

/-- The expansion of the iterated twisted commutator:
`x_m = Σ_{p + p' = m} (-1)^{p'} serreCoef m p' · θ_i^p θ_j θ_i^{p'}`. -/
theorem serreSeq_eq_sum (i j : I) (m : ℕ) :
    serreSeq dot v i j m = ∑ p ∈ antidiagonal m,
      ((-1 : K) ^ p.2 * serreCoef dot v i j m p.2) • (θ i ^ p.1 * θ j * θ i ^ p.2) := by
  induction m with
  | zero => simp [serreSeq_zero]
  | succ m ih =>
    have hT1 : ∑ p ∈ antidiagonal (m + 1),
        ((-1 : K) ^ p.2 * serreCoef dot v i j m p.2) • (θ i ^ p.1 * θ j * θ i ^ p.2) =
          θ i * serreSeq dot v i j m := by
      rw [Finset.Nat.sum_antidiagonal_succ, serreCoef_eq_zero_of_lt i j (Nat.lt_succ_self m),
        mul_zero, zero_smul, zero_add, ih, mul_sum]
      refine sum_congr rfl fun p _ => ?_
      rw [mul_smul_comm, pow_succ', mul_assoc, mul_assoc, mul_assoc]
    have hT2 : ∑ p ∈ antidiagonal (m + 1),
        ((-1 : K) ^ p.2 * serreCoef dot v i j m p.2) • (θ i ^ p.1 * θ j * θ i ^ p.2) =
          (θ i : PreF K I) ^ (m + 1) * θ j + ∑ p ∈ antidiagonal m,
            ((-1 : K) ^ (p.2 + 1) * serreCoef dot v i j m (p.2 + 1)) •
              (θ i ^ p.1 * θ j * θ i ^ (p.2 + 1)) := by
      rw [Finset.Nat.sum_antidiagonal_succ']
      simp
    rw [Finset.Nat.sum_antidiagonal_succ', serreSeq_succ, ← hT1, hT2, ih, sum_mul, smul_sum]
    simp only [serreCoef_zero_right, pow_zero, mul_one, one_smul, serreCoef_succ_succ, mul_add,
      add_smul, sum_add_distrib, add_assoc, sub_eq_add_neg, ← sum_neg_distrib]
    congr 2
    refine sum_congr rfl fun p _ => ?_
    rw [smul_mul_assoc, smul_smul, ← neg_smul, pow_succ (θ i : PreF K I), mul_assoc _ _ (θ i)]
    congr 1
    ring

/-- Closed form of the coefficients, for `i · i = 2 h` and `v_i = v^h`:
`serreCoef m p = v^{(j·i) p} v_i^{p (m - 1)} [m choose p]_{v_i}`. -/
theorem serreCoef_eq (i j : I) (hev : dot i i = 2 * (dot i i / 2)) (m p : ℕ) :
    serreCoef dot v i j m p =
      ((v ^ (dot j i * p + dot i i / 2 * p * ((m : ℤ) - 1)) : Kˣ) : K) *
        qbinom (v ^ (dot i i / 2)) m p := by
  induction m generalizing p with
  | zero => cases p <;> simp [serreCoef]
  | succ m ih =>
    cases p with
    | zero => simp
    | succ p =>
      rw [serreCoef_succ_succ, ih, ih, qbinom_succ_succ, ← zpow_mul, ← zpow_mul, mul_add,
        ← mul_assoc, ← mul_assoc, ← mul_assoc, ← val_zpow_add, ← val_zpow_add, ← val_zpow_add]
      congr 4
      · push_cast; ring
      · push_cast; linear_combination (m : ℤ) * hev

variable {K : Type*} [Field K] {v : Kˣ}

variable (dot v) in
/-- Lusztig's Serre element in divided-power form (Lusztig 1.4.3):
`Σ_{p + p' = N} (-1)^{p'} θ_i^{(p)} θ_j θ_i^{(p')}`. -/
def serreDiv (i j : I) (N : ℕ) : PreF K I :=
  ∑ p ∈ antidiagonal N, ((-1 : K) ^ p.2) • (dpow dot v i p.1 * θ j * dpow dot v i p.2)

/-- **The iterated twisted commutator is `[N]_{v_i}^!` times Lusztig's divided-power Serre
element**, with no additional powers of `v`: if `i · i` is even, `2 (i·j) = (i·i)(1 - N)` and
`[N]_{v_i}^! ≠ 0`, then
`x_N = [N]_{v_i}^! · Σ_{p + p' = N} (-1)^{p'} θ_i^{(p)} θ_j θ_i^{(p')}`. -/
theorem serreSeq_eq_qfact_smul_serreDiv (hdot : ∀ i j, dot i j = dot j i) (i j : I)
    (hev : Even (dot i i)) {N : ℕ} (hN : 2 * dot i j = dot i i * (1 - N))
    (hq : qfact (vi dot v i) N ≠ 0) :
    serreSeq dot v i j N = qfact (vi dot v i) N • serreDiv dot v i j N := by
  have hev' : dot i i = 2 * (dot i i / 2) := by
    obtain ⟨k, hk⟩ := hev; omega
  have he : dot j i = dot i i / 2 * (1 - N) := by
    rw [← hdot i j]
    have : 2 * dot i j = 2 * (dot i i / 2 * (1 - N)) := by rw [hN]; nth_rewrite 1 [hev']; ring
    omega
  rw [serreSeq_eq_sum, serreDiv, smul_sum]
  refine sum_congr rfl fun p hp => ?_
  obtain ⟨a, b⟩ := p
  rw [mem_antidiagonal] at hp
  subst hp
  simp only
  rw [serreCoef_eq i j hev', he]
  have e0 : dot i i / 2 * (1 - ((a + b : ℕ) : ℤ)) * (b : ℤ) +
      dot i i / 2 * b * (((a + b : ℕ) : ℤ) - 1) = 0 := by ring
  rw [e0, zpow_zero, Units.val_one, one_mul]
  have hqv : qbinom (v ^ (dot i i / 2)) (a + b) b =
      qfact (vi dot v i) (a + b) * (qfact (vi dot v i) a)⁻¹ * (qfact (vi dot v i) b)⁻¹ :=
    qbinom_eq_div (vi dot v i) hq
  rw [hqv]
  have ha := qfact_ne_zero_of_add_left _ hq
  have hb := qfact_ne_zero_of_add_right _ hq
  simp only [dpow, smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  field_simp
  ring

/-- **Lusztig, Proposition 1.4.3** (divided-power form): if `i ≠ j`, `i · i` is even,
`N ≥ 1`, `2 (i·j) = (i·i)(1 - N)` and `[N]_{v_i}^! ≠ 0`, then
`Σ_{p + p' = N} (-1)^{p'} θ_i^{(p)} θ_j θ_i^{(p')}` lies in the radical of `( , )`. -/
theorem serreDiv_mem_radical (c : I → K) (hdot : ∀ i j, dot i j = dot j i) {i j : I}
    (hij : i ≠ j) (hev : Even (dot i i)) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : 2 * dot i j = dot i i * (1 - N)) (hq : qfact (vi dot v i) N ≠ 0) :
    serreDiv dot v i j N ∈ radical dot v c := by
  have h := serreSeq_mem_radical (v := v) c hdot hij hN1 hN
  rw [serreSeq_eq_qfact_smul_serreDiv hdot i j hev hN hq] at h
  rw [← inv_smul_smul₀ hq (serreDiv dot v i j N), Algebra.smul_def]
  exact Ideal.mul_mem_left _ _ h

end PreF

namespace CartanDatum

variable {I : Type*} (C : CartanDatum I)

/-- **Lusztig 1.4.3 for a Cartan datum over `ℚ(v)`** (divided-power form): for `i ≠ j` and
`N = 1 - 2(i·j)/(i·i)`, the element `Σ_{p + p' = N} (-1)^{p'} θ_i^{(p)} θ_j θ_i^{(p')}` of `'f`
maps to zero in `f`. -/
theorem serreDiv_eq_zero {i j : I} (hij : i ≠ j) :
    PreF.π C.dot vQ C.c (PreF.serreDiv C.dot vQ i j (C.serreN i j)) = 0 :=
  PreF.π_eq_zero_iff.2 (PreF.serreDiv_mem_radical C.c C.symm hij (C.dot_self_even i)
    (C.one_le_serreN hij) (C.two_mul_dot_eq hij) (C.qfact_ne_zero i _))

/-- **Lusztig 1.4.3 in `f`**: `Σ_{p + p' = N} (-1)^{p'} θ_i^{(p)} θ_j θ_i^{(p')} = 0` for
`i ≠ j`, `N = 1 - 2(i·j)/(i·i)`, with the divided powers taken in `f`. -/
theorem serre_divided {i j : I} (hij : i ≠ j) :
    ∑ p ∈ Finset.antidiagonal (C.serreN i j), ((-1 : RatFunc ℚ) ^ p.2) •
      (PreF.dpowF C.dot vQ C.c i p.1 * PreF.π C.dot vQ C.c (PreF.θ j) *
        PreF.dpowF C.dot vQ C.c i p.2) = 0 := by
  have h := C.serreDiv_eq_zero hij
  simp only [PreF.serreDiv, map_sum, map_smul, map_mul] at h
  exact h

/-- The Serre relation `x_N = 0` in `f` is equivalent to the divided-power form: over `ℚ(v)`,
`x_N = [N]_{v_i}^! · Σ_{p + p' = N} (-1)^{p'} θ_i^{(p)} θ_j θ_i^{(p')}` in `'f`. -/
theorem serreSeq_eq_qfact_smul_serreDiv {i j : I} (hij : i ≠ j) :
    PreF.serreSeq C.dot vQ i j (C.serreN i j) =
      qfact (PreF.vi C.dot vQ i) (C.serreN i j) • PreF.serreDiv C.dot vQ i j (C.serreN i j) :=
  PreF.serreSeq_eq_qfact_smul_serreDiv C.symm i j (C.dot_self_even i) (C.two_mul_dot_eq hij)
    (C.qfact_ne_zero i _)

end CartanDatum

namespace KL

variable {I : Type*} [DecidableEq I] (Γ : SimpleGraph I) [DecidableRel Γ.Adj]

theorem serreN_of_adj {i j : I} (h : Γ.Adj i j) : (C Γ).serreN i j = 2 := by
  simp [CartanDatum.serreN, CartanDatum.ofGraph_dot_of_adj Γ h]

/-- KL I §3.1 (proof of Prop. 3.4): for `i — j` an edge of `Γ`,
`θ_i θ_j θ_i = θ_i^{(2)} θ_j + θ_j θ_i^{(2)}` in `f`, matching
`[P_{iji}] = [P_{i^{(2)}j}] + [P_{ji^{(2)}}]`. -/
theorem serre_divided {i j : I} (h : Γ.Adj i j) :
    π Γ (PreF.θ i) * π Γ (PreF.θ j) * π Γ (PreF.θ i) =
      PreF.dpowF (C Γ).dot vQ (C Γ).c i 2 * π Γ (PreF.θ j) +
        π Γ (PreF.θ j) * PreF.dpowF (C Γ).dot vQ (C Γ).c i 2 := by
  have hs := (C Γ).serre_divided h.ne
  rw [serreN_of_adj Γ h] at hs
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hs
  simp only [sum_range_succ, sum_range_zero, zero_add] at hs
  norm_num [PreF.dpowF] at hs
  rw [← sub_eq_zero, ← neg_eq_zero, ← hs]
  simp only [PreF.dpowF]
  abel

end KL

end Categorification.QuantumGroup

end
