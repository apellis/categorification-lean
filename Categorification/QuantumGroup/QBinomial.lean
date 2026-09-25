/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.QuantumGroup.KLSpecialization

/-!
# Quantum binomial coefficients and products of divided powers

Lusztig, *Introduction to quantum groups*, 1.3.1 (quantum binomial coefficients) and 1.4.1(a)
(`θ_i^{(a)} θ_i^{(b)} = [a+b choose a]_i θ_i^{(a+b)}`); Khovanov–Lauda, arXiv:0803.4121v2,
§1 and §3.1 (divided powers generating `_𝒜 f`).

## Main definitions and results

* `qbinom t n k = [n choose k]_t`, defined by the recursion
  `[n+1 choose k+1]_t = t^{-(k+1)} [n choose k+1]_t + t^{n-k} [n choose k]_t`
  (with `[n choose 0]_t = 1` and `[0 choose k+1]_t = 0`), over any commutative ring;
* `qint_add` — `[a + b]_t = t^{-b} [a]_t + t^a [b]_t`;
* `qbinom_mul_qfact` — `[a+b choose b]_t [a]_t^! [b]_t^! = [a+b]_t^!`, so that
  `[n choose k]_t = [n]_t^! / ([k]_t^! [n-k]_t^!)` whenever the factorials are invertible
  (Lusztig 1.3.1(c)); `qbinom_comm_of_ne_zero` gives the symmetry
  `[a+b choose a]_t = [a+b choose b]_t` in that case;
* `qbinomial_theorem` — the quantum binomial theorem: if `Y X = t² X Y` in a `K`-algebra, then
  `(X + Y)^n = Σ_{s+s'=n} t^{s s'} [n choose s']_t X^s Y^{s'}` (compare Lusztig 1.3.5);
* `PreF.dpow_mul_dpow` — Lusztig 1.4.1(a): `θ_i^{(a)} θ_i^{(b)} = [a+b choose a]_{v_i}
  θ_i^{(a+b)}` in `'f`, and `PreF.dpowF_mul_dpowF` — the same in `f`; for a Cartan datum over
  `ℚ(v)` these hold unconditionally (`CartanDatum.dpowF_mul_dpowF`).
-/

noncomputable section

namespace Categorification.QuantumGroup

open Finset

section QBinom

variable {K : Type*} [CommRing K]

theorem val_zpow_add (t : Kˣ) (m n : ℤ) :
    ((t ^ (m + n) : Kˣ) : K) = ((t ^ m : Kˣ) : K) * ((t ^ n : Kˣ) : K) := by
  rw [zpow_add, Units.val_mul]

/-- `[a + b]_t = t^{-b} [a]_t + t^a [b]_t`. -/
theorem qint_add (t : Kˣ) (a b : ℕ) :
    qint t (a + b) =
      ((t ^ (-(b : ℤ)) : Kˣ) : K) * qint t a + ((t ^ (a : ℤ) : Kˣ) : K) * qint t b := by
  simp only [qint]
  rw [sum_range_add]
  have h1 : ((t ^ (1 - ((a + b : ℕ) : ℤ)) : Kˣ) : K) =
      ((t ^ (-(b : ℤ)) : Kˣ) : K) * ((t ^ (1 - (a : ℤ)) : Kˣ) : K) := by
    rw [← val_zpow_add]; congr 2; push_cast; ring
  have h2 : ((t ^ (1 - ((a + b : ℕ) : ℤ)) : Kˣ) : K) * ((t : K) ^ 2) ^ a =
      ((t ^ (a : ℤ) : Kˣ) : K) * ((t ^ (1 - (b : ℤ)) : Kˣ) : K) := by
    rw [← pow_mul, ← Units.val_pow_eq_pow_val, ← zpow_natCast, ← Units.val_mul, ← Units.val_mul,
      ← zpow_add, ← zpow_add]
    congr 2; push_cast; ring
  simp only [pow_add, ← mul_sum]
  linear_combination (∑ i ∈ range a, ((t : K) ^ 2) ^ i) * h1 +
    (∑ i ∈ range b, ((t : K) ^ 2) ^ i) * h2

/-- The quantum binomial coefficient `[n choose k]_t` (Lusztig 1.3.1), by the recursion
`[n+1 choose k+1]_t = t^{-(k+1)} [n choose k+1]_t + t^{n-k} [n choose k]_t`. -/
def qbinom (t : Kˣ) : ℕ → ℕ → K
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => ((t ^ (-((k : ℤ) + 1)) : Kˣ) : K) * qbinom t n (k + 1) +
      ((t ^ ((n : ℤ) - k) : Kˣ) : K) * qbinom t n k

@[simp] theorem qbinom_zero_right (t : Kˣ) (n : ℕ) : qbinom t n 0 = 1 := by
  cases n <;> rfl

@[simp] theorem qbinom_zero_succ (t : Kˣ) (k : ℕ) : qbinom t 0 (k + 1) = 0 := rfl

theorem qbinom_succ_succ (t : Kˣ) (n k : ℕ) :
    qbinom t (n + 1) (k + 1) = ((t ^ (-((k : ℤ) + 1)) : Kˣ) : K) * qbinom t n (k + 1) +
      ((t ^ ((n : ℤ) - k) : Kˣ) : K) * qbinom t n k := rfl

theorem qbinom_eq_zero_of_lt (t : Kˣ) {n k : ℕ} (h : n < k) : qbinom t n k = 0 := by
  induction n generalizing k with
  | zero => obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩; rfl
  | succ n ih =>
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [qbinom_succ_succ, ih (by omega), ih (by omega), mul_zero, mul_zero, add_zero]

@[simp] theorem qbinom_self (t : Kˣ) (n : ℕ) : qbinom t n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [qbinom_succ_succ, qbinom_eq_zero_of_lt t (Nat.lt_succ_self n), ih, sub_self, zpow_zero,
      Units.val_one]
    ring

/-- `[a+b choose b]_t [a]_t^! [b]_t^! = [a+b]_t^!` (Lusztig 1.3.1(c)). -/
theorem qbinom_mul_qfact (t : Kˣ) (a b : ℕ) :
    qbinom t (a + b) b * qfact t a * qfact t b = qfact t (a + b) := by
  induction b generalizing a with
  | zero => simp
  | succ k ihk =>
    induction a with
    | zero => simp
    | succ a iha =>
      have e : a + 1 + (k + 1) = (a + (k + 1)) + 1 := by omega
      rw [e, qbinom_succ_succ, qfact_succ t a, qfact_succ t k, qfact_succ t (a + (k + 1))]
      have h2 := ihk (a + 1)
      rw [show a + 1 + k = a + (k + 1) by omega, qfact_succ t a] at h2
      rw [qfact_succ t k] at iha
      have hsub : ((a + (k + 1) : ℕ) : ℤ) - k = ((a + 1 : ℕ) : ℤ) := by push_cast; ring
      have hk : (-((k : ℤ) + 1)) = -((k + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [hsub, hk, show a + (k + 1) + 1 = (a + 1) + (k + 1) by omega, qint_add t (a + 1) (k + 1)]
      linear_combination
        (((t ^ (-((k + 1 : ℕ) : ℤ)) : Kˣ) : K) * qint t (a + 1)) * iha +
          (((t ^ ((a + 1 : ℕ) : ℤ) : Kˣ) : K) * qint t (k + 1)) * h2

/-- Over a field, `[a+b choose b]_t = [a+b]_t^! / ([a]_t^! [b]_t^!)` when `[a+b]_t^! ≠ 0`. -/
theorem qbinom_eq_div {K : Type*} [Field K] (t : Kˣ) {a b : ℕ} (h : qfact t (a + b) ≠ 0) :
    qbinom t (a + b) b = qfact t (a + b) * (qfact t a)⁻¹ * (qfact t b)⁻¹ := by
  have e := qbinom_mul_qfact t a b
  have ha : qfact t a ≠ 0 := fun h0 => h (by rw [← e, h0]; ring)
  have hb : qfact t b ≠ 0 := fun h0 => h (by rw [← e, h0]; ring)
  rw [← e]
  field_simp
  ring

theorem qfact_ne_zero_of_add_left {K : Type*} [Field K] (t : Kˣ) {a b : ℕ}
    (h : qfact t (a + b) ≠ 0) : qfact t a ≠ 0 := fun h0 =>
  h (by rw [← qbinom_mul_qfact t a b, h0]; ring)

theorem qfact_ne_zero_of_add_right {K : Type*} [Field K] (t : Kˣ) {a b : ℕ}
    (h : qfact t (a + b) ≠ 0) : qfact t b ≠ 0 := fun h0 =>
  h (by rw [← qbinom_mul_qfact t a b, h0]; ring)

/-- Symmetry `[a+b choose a]_t = [a+b choose b]_t` over a field when `[a+b]_t^! ≠ 0`. -/
theorem qbinom_comm_of_ne_zero {K : Type*} [Field K] (t : Kˣ) {a b : ℕ}
    (h : qfact t (a + b) ≠ 0) : qbinom t (a + b) a = qbinom t (a + b) b := by
  have h' : qfact t (b + a) ≠ 0 := by rwa [add_comm]
  have e1 := qbinom_eq_div t h'
  rw [add_comm b a] at e1
  rw [e1, qbinom_eq_div t h]
  ring

theorem qbinom_two_one (t : Kˣ) : qbinom t 2 1 = (t : K) + ((t⁻¹ : Kˣ) : K) := by
  rw [qbinom_succ_succ, qbinom_self, qbinom_zero_right]
  simp only [Nat.cast_zero, zero_add, Nat.cast_one, sub_zero, zpow_one, zpow_neg, mul_one]
  ring

/-! ### The quantum binomial theorem -/

/-- The coefficient `t^{s s'} [s + s' choose s']_t` of `X^s Y^{s'}` in `(X + Y)^{s+s'}`. -/
def qbinomCoef (t : Kˣ) (s s' : ℕ) : K :=
  ((t ^ ((s : ℤ) * s') : Kˣ) : K) * qbinom t (s + s') s'

@[simp] theorem qbinomCoef_zero_right (t : Kˣ) (s : ℕ) : qbinomCoef t s 0 = 1 := by
  simp [qbinomCoef]

@[simp] theorem qbinomCoef_zero_left (t : Kˣ) (s : ℕ) : qbinomCoef t 0 s = 1 := by
  simp [qbinomCoef]

/-- Pascal's rule for `qbinomCoef`. -/
theorem qbinomCoef_succ_succ (t : Kˣ) (s s' : ℕ) :
    qbinomCoef t (s + 1) (s' + 1) =
      qbinomCoef t s (s' + 1) + ((t ^ (2 * ((s : ℤ) + 1)) : Kˣ) : K) * qbinomCoef t (s + 1) s' := by
  simp only [qbinomCoef]
  have e : s + 1 + (s' + 1) = (s + 1 + s') + 1 := by omega
  rw [e, qbinom_succ_succ]
  have e2 : s + 1 + s' = s + (s' + 1) := by omega
  rw [e2, mul_add, ← mul_assoc, ← mul_assoc, ← val_zpow_add, ← val_zpow_add]
  have e3 : ((s + (s' + 1) : ℕ) : ℤ) - s' = (s : ℤ) + 1 := by push_cast; ring
  rw [e3, ← e2, ← mul_assoc, ← val_zpow_add]
  congr 3 <;> push_cast <;> ring_nf

section Algebra

variable {A : Type*} [Ring A] [Algebra K A]

theorem mul_pow_of_qcomm (t : Kˣ) {X Y : A}
    (h : Y * X = ((t ^ (2 : ℤ) : Kˣ) : K) • (X * Y)) (s : ℕ) :
    Y * X ^ s = ((t ^ (2 * (s : ℤ)) : Kˣ) : K) • (X ^ s * Y) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [pow_succ, ← mul_assoc, ih, smul_mul_assoc, mul_assoc, h, mul_smul_comm, smul_smul,
      ← val_zpow_add, ← mul_assoc, ← pow_succ]
    congr 3

/-- **The quantum binomial theorem.** If `Y X = t² X Y`, then
`(X + Y)^n = Σ_{s + s' = n} t^{s s'} [n choose s']_t X^s Y^{s'}`. -/
theorem qbinomial_theorem (t : Kˣ) {X Y : A}
    (h : Y * X = ((t ^ (2 : ℤ) : Kˣ) : K) • (X * Y)) (n : ℕ) :
    (X + Y) ^ n = ∑ p ∈ antidiagonal n, qbinomCoef t p.1 p.2 • (X ^ p.1 * Y ^ p.2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    -- split the coefficients by Pascal's rule
    have hsplit : ∀ p ∈ antidiagonal (n + 1), qbinomCoef t p.1 p.2 =
        (if p.1 = 0 then 0 else qbinomCoef t (p.1 - 1) p.2) +
          (if p.2 = 0 then 0 else
            ((t ^ (2 * (p.1 : ℤ)) : Kˣ) : K) * qbinomCoef t p.1 (p.2 - 1)) := by
      rintro ⟨s, s'⟩ hp
      rw [Finset.mem_antidiagonal] at hp
      simp only at hp ⊢
      rcases s with _ | s
      · rcases s' with _ | s'
        · omega
        · simp
      · rcases s' with _ | s'
        · simp
        · simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
          rw [qbinomCoef_succ_succ]
          push_cast
          ring_nf
    rw [sum_congr rfl fun p hp => by rw [hsplit p hp]]
    simp only [add_smul, sum_add_distrib]
    rw [Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ']
    simp only [if_true, zero_smul, zero_add, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    rw [pow_succ', ih, add_mul, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · refine sum_congr rfl fun p _ => ?_
      rw [mul_smul_comm, ← mul_assoc, ← pow_succ']
    · refine sum_congr rfl fun p _ => ?_
      rw [mul_smul_comm, ← mul_assoc, mul_pow_of_qcomm t h, smul_mul_assoc, mul_assoc,
        ← pow_succ', smul_smul, mul_comm]

end Algebra

end QBinom

/-! ### Products of divided powers -/

namespace PreF

variable {I : Type*} {K : Type*} [Field K] {dot : I → I → ℤ} {v : Kˣ}

/-- **Lusztig 1.4.1(a)** in `'f`: `θ_i^{(a)} θ_i^{(b)} = [a+b choose a]_{v_i} θ_i^{(a+b)}`,
provided `[a+b]_{v_i}^! ≠ 0` (automatic over `ℚ(v)`). -/
theorem dpow_mul_dpow (i : I) {a b : ℕ} (h : qfact (vi dot v i) (a + b) ≠ 0) :
    dpow dot v i a * dpow dot v i b = qbinom (vi dot v i) (a + b) a • dpow dot v i (a + b) := by
  rw [qbinom_comm_of_ne_zero _ h, qbinom_eq_div _ h]
  have ha := qfact_ne_zero_of_add_left _ h
  have hb := qfact_ne_zero_of_add_right _ h
  simp only [dpow, smul_mul_smul_comm, ← pow_add, smul_smul]
  congr 1
  field_simp

variable (c : I → K)

/-- **Lusztig 1.4.1(a)** in `f`. -/
theorem dpowF_mul_dpowF (i : I) {a b : ℕ} (h : qfact (vi dot v i) (a + b) ≠ 0) :
    dpowF dot v c i a * dpowF dot v c i b =
      qbinom (vi dot v i) (a + b) a • dpowF dot v c i (a + b) := by
  simp only [dpowF, ← map_mul, ← map_smul, dpow_mul_dpow i h]

end PreF

namespace CartanDatum

variable {I : Type*} (C : CartanDatum I)

/-- **Lusztig 1.4.1(a)** in `f` over `ℚ(v)` for a Cartan datum:
`θ_i^{(a)} θ_i^{(b)} = [a+b choose a]_{v_i} θ_i^{(a+b)}`. -/
theorem dpowF_mul_dpowF (i : I) (a b : ℕ) :
    PreF.dpowF C.dot vQ C.c i a * PreF.dpowF C.dot vQ C.c i b =
      qbinom (PreF.vi C.dot vQ i) (a + b) a • PreF.dpowF C.dot vQ C.c i (a + b) :=
  PreF.dpowF_mul_dpowF C.c i (C.qfact_ne_zero i (a + b))

end CartanDatum

end Categorification.QuantumGroup

end
