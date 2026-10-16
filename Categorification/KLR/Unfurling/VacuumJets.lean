/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Unfurling.BubbleMultiplicity

/-!
# Jets of powers against the dual of a confluent Vandermonde matrix

The scalar part of the computation of the bubbles on the generating object `𝕍` of an
unfurled cyclotomic representation. B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*,
arXiv:1603.06311v3, proof of the theorem with label `nondegenerate`, uses that on `𝕍` the
bubbles of the colour `i` act by the coefficients of
`∏_{π j = i} (1 - z_j t)^{-Λ_j}`.

On `𝕍` the cups `𝟙 → F_i E_i 𝕍` with `t < N = ∑ Λ_j` dots form a basis. Modulo nilpotent
closed diagrams, the cup of label `j` with `m` dots pairs with the shifted dot
`(z_j + x)^n` through the Taylor coefficient `[x^m] (z_j + x)^n = C(n, m) z_j^{n-m}`. The bubbles
are the `(N-1)`-st coordinate functional applied to the cups with `n` dots. This file computes
the resulting scalars. Let `ψ` be the functional with

  `∑_{(a, m)} ψ_{a,m} C(t, m) u_a^{t-m} = δ_{t, N-1}`  for `t < N = ∑ₐ hₐ`

(the last row of the inverse of the confluent Vandermonde matrix of the points `u_a` with
multiplicities `hₐ`). Then for every `n`,

  `∑_{(a, m)} ψ_{a,m} C(n, m) u_a^{n-m} = [t^{n+1-N}] ∏ₐ (1 - u_a t)^{-hₐ}`,

which is `0` for `n < N - 1` (`jetSum_eq_coeff`). In other words, the generating function of the
left side is `t^{N-1} / ∏ₐ (1 - u_a t)^{hₐ}`. The identity holds over any commutative ring, and
no distinctness of the `u_a` is needed; distinctness is what makes such a `ψ` exist.

**Proof (ours).** `∑_n C(n, m) u^{n-m} tⁿ = t^m / (1 - u t)^{m+1}` (`jetSeries_mul`). Hence the
generating function `G` of the left side satisfies: `G · ∏ₐ (1 - u_a t)^{hₐ}` is a polynomial of
degree `< N`. The hypothesis says `G ≡ t^{N-1}` modulo `t^N`, so this polynomial is `t^{N-1}`.

## Main definitions and results

* `jetCoeff u m n = C(n, m) u^{n-m}`, the coefficient of `x^m` in `(u + x)^n`.
* `jetSeries_mul`: `(∑_n jetCoeff u m n tⁿ) (1 - u t)^{m+1} = t^m`.
* `jetSum_eq_coeff`: the identity above.
-/

open PowerSeries

namespace Categorification.KLR.Unfurling

variable {k : Type*} [CommRing k]

/-- `[x^m] (u + x)^n = C(n, m) u^{n-m}`. -/
def jetCoeff (u : k) (m n : ℕ) : k := (n.choose m : k) * u ^ (n - m)

/-- `∑_n C(n, m) u^{n-m} tⁿ`. -/
noncomputable def jetSeries (u : k) (m : ℕ) : PowerSeries k := mk fun n => jetCoeff u m n

theorem jetSeries_zero_mul (u : k) : jetSeries u 0 * (1 - C u * X) = 1 := by
  ext n
  rw [mul_sub, mul_one, map_sub, ← mul_assoc, coeff_one]
  rcases n with _ | n
  · simp [jetSeries, jetCoeff]
  · rw [coeff_succ_mul_X, coeff_mul_C]
    simp [jetSeries, jetCoeff, pow_succ]

theorem jetSeries_succ_mul (u : k) (m : ℕ) :
    jetSeries u (m + 1) * (1 - C u * X) = X * jetSeries u m := by
  ext n
  rw [mul_sub, mul_one, map_sub, ← mul_assoc]
  rcases n with _ | n
  · simp [jetSeries, jetCoeff]
  · rw [coeff_succ_mul_X, coeff_mul_C, coeff_succ_X_mul]
    simp only [jetSeries, jetCoeff, coeff_mk, Nat.choose_succ_succ, Nat.cast_add, add_mul]
    by_cases hmn : m + 1 ≤ n
    · rw [show n + 1 - (m + 1) = n - m by omega, show n - m = n - (m + 1) + 1 by omega,
        pow_succ]
      ring
    · rw [Nat.choose_eq_zero_of_lt (by omega : n < m + 1)]
      simp

/-- `(∑_n C(n, m) u^{n-m} tⁿ) (1 - u t)^{m+1} = t^m`. -/
theorem jetSeries_mul (u : k) (m : ℕ) : jetSeries u m * (1 - C u * X) ^ (m + 1) = X ^ m := by
  induction m with
  | zero => simpa using jetSeries_zero_mul u
  | succ m ih =>
    rw [pow_succ', ← mul_assoc, jetSeries_succ_mul, mul_assoc, ih, pow_succ']

/-! ### Power series with bounded support -/

/-- All coefficients of index `> d` vanish. -/
def DegLE (d : ℕ) (f : PowerSeries k) : Prop := ∀ n, d < n → coeff n f = 0

theorem DegLE.mul {d e : ℕ} {f g : PowerSeries k} (hf : DegLE d f) (hg : DegLE e g) :
    DegLE (d + e) (f * g) := by
  intro n hn
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  by_cases h : d < p.1
  · rw [hf _ h, zero_mul]
  · rw [hg _ (by omega), mul_zero]

theorem DegLE.mono {d e : ℕ} {f : PowerSeries k} (hf : DegLE d f) (h : d ≤ e) : DegLE e f :=
  fun n hn => hf n (by omega)

theorem degLE_one : DegLE 0 (1 : PowerSeries k) := fun n hn => by
  rw [coeff_one, ite_eq_right (by omega)]

theorem degLE_X_pow (m : ℕ) : DegLE m (X ^ m : PowerSeries k) := fun n hn => by
  rw [coeff_X_pow, ite_eq_right (by omega)]

theorem degLE_one_sub (u : k) : DegLE 1 (1 - C u * X : PowerSeries k) := fun n hn => by
  rw [map_sub, coeff_one, ite_eq_right (by omega), mul_comm, coeff_mul_C, coeff_X,
    ite_eq_right (by omega)]
  simp

theorem DegLE.pow {d : ℕ} {f : PowerSeries k} (hf : DegLE d f) (e : ℕ) : DegLE (d * e) (f ^ e) := by
  induction e with
  | zero => simpa using degLE_one
  | succ e ih => rw [pow_succ, mul_add, mul_one]; exact ih.mul hf

theorem degLE_prod {ι : Type*} (s : Finset ι) (f : ι → PowerSeries k) (d : ι → ℕ)
    (h : ∀ i ∈ s, DegLE (d i) (f i)) : DegLE (∑ i ∈ s, d i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using degLE_one
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).mul (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-! ### The identity -/

variable {A : Type*} [Fintype A] (u : A → k) (hp : A → ℕ)

/-- `∑_{(a, m)} ψ_{a,m} C(n, m) u_a^{n-m}`. -/
def jetSum (ψ : (Σ a, Fin (hp a)) → k) (n : ℕ) : k :=
  ∑ x, ψ x * jetCoeff (u x.1) x.2 n

/-- `∏ₐ (1 - u_a t)^{hₐ}`. -/
noncomputable def vandSeries : PowerSeries k := ∏ a, (1 - C (u a) * X) ^ hp a

theorem vandSeries_eq : vandSeries u hp =
    ((∏ a, oneSubUnit (u a) ^ hp a : (PowerSeries k)ˣ) : PowerSeries k) := by
  simp [vandSeries]

theorem constantCoeff_vandSeries : constantCoeff (vandSeries u hp) = 1 := by
  simp [vandSeries, map_prod]

theorem degLE_jetSeries_mul_vandSeries [DecidableEq A] (x : Σ a, Fin (hp a)) :
    DegLE (∑ a, hp a - 1) (jetSeries (u x.1) x.2 * vandSeries u hp) := by
  obtain ⟨a, m⟩ := x
  have hm := m.2
  have e : vandSeries u hp = (1 - C (u a) * X) ^ ((m : ℕ) + 1) *
      ((1 - C (u a) * X) ^ (hp a - m - 1) *
        ∏ a' ∈ Finset.univ.erase a, (1 - C (u a') * X) ^ hp a') := by
    rw [vandSeries, ← Finset.mul_prod_erase _ _ (Finset.mem_univ a), ← mul_assoc, ← pow_add,
      show (m : ℕ) + 1 + (hp a - m - 1) = hp a by omega]
  rw [e, ← mul_assoc, jetSeries_mul]
  have hsum : ∑ a', hp a' = hp a + ∑ a' ∈ Finset.univ.erase a, hp a' :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ a)).symm
  refine ((degLE_X_pow (m : ℕ)).mul (((degLE_one_sub (u a)).pow (hp a - m - 1)).mul
    (degLE_prod _ _ _ fun a' _ => (degLE_one_sub (u a')).pow (hp a')))).mono ?_
  simp only [one_mul]
  omega

/-- **Jets of powers against the dual of a confluent Vandermonde matrix.** If
`∑_{(a, m)} ψ_{a,m} C(t, m) u_a^{t-m} = δ_{t, N-1}` for `t < N = ∑ₐ hₐ > 0`, then for every `n`

  `∑_{(a, m)} ψ_{a,m} C(n, m) u_a^{n-m} = [t^{n+1-N}] ∏ₐ (1 - u_a t)^{-hₐ}`  (`0` if `n + 1 < N`).

The bubble values on the generating object of an unfurled cyclotomic representation
(Webster, arXiv:1603.06311v3, proof of the theorem with label `nondegenerate`). -/
theorem jetSum_eq_coeff (ψ : (Σ a, Fin (hp a)) → k) (hN : 0 < ∑ a, hp a)
    (hψ : ∀ t < ∑ a, hp a, jetSum u hp ψ t = if t + 1 = ∑ a, hp a then 1 else 0) (n : ℕ) :
    jetSum u hp ψ n = if ∑ a, hp a ≤ n + 1 then
      coeff (n + 1 - ∑ a, hp a)
        ((∏ a, oneSubUnit (u a) ^ (-(hp a : ℤ)) : (PowerSeries k)ˣ) : PowerSeries k)
      else 0 := by
  classical
  set N := ∑ a, hp a with hNdef
  set G : PowerSeries k := mk (jetSum u hp ψ)
  set Q := vandSeries u hp
  have hG : G = ∑ x, C (ψ x) * jetSeries (u x.1) x.2 := by
    ext n
    simp [G, jetSum, jetSeries, map_sum]
  -- `G · Q` is a polynomial of degree `< N`
  have hdeg : DegLE (N - 1) (G * Q) := by
    intro n hn
    rw [hG, Finset.sum_mul, map_sum]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [mul_assoc, coeff_C_mul, degLE_jetSeries_mul_vandSeries u hp x n hn, mul_zero]
  -- `G ≡ t^{N-1}` modulo `t^N`
  obtain ⟨R, hR⟩ : X ^ N ∣ G - X ^ (N - 1) := by
    rw [X_pow_dvd_iff]
    intro t ht
    rw [map_sub, coeff_mk, hψ t ht, coeff_X_pow]
    split_ifs with h1 h2 h2 <;> first | rfl | omega | simp
  have hGQ : G * Q = X ^ (N - 1) := by
    ext n
    by_cases hn : N - 1 < n
    · rw [hdeg n hn, coeff_X_pow, ite_eq_right (by omega)]
    · have hn' : n < N := by omega
      rw [show G = X ^ (N - 1) + X ^ N * R from (sub_eq_iff_eq_add'.mp hR), add_mul, map_add,
        mul_assoc (X ^ N), coeff_X_pow_mul' (R * Q), ite_eq_right (by omega), add_zero,
        coeff_X_pow_mul', coeff_X_pow]
      by_cases he : n = N - 1
      · rw [ite_eq_left (by omega), ite_eq_left he, he, Nat.sub_self,
          coeff_zero_eq_constantCoeff_apply, constantCoeff_vandSeries]
      · rw [ite_eq_right (by omega), ite_eq_right he]
  -- `G = t^{N-1} Q⁻¹`
  set U : (PowerSeries k)ˣ := ∏ a, oneSubUnit (u a) ^ hp a
  have hQU : Q = (U : PowerSeries k) := vandSeries_eq u hp
  have hinv : (∏ a, oneSubUnit (u a) ^ (-(hp a : ℤ)) : (PowerSeries k)ˣ) = U⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [zpow_neg, zpow_natCast]
  have hGeq : G = X ^ (N - 1) * ((U⁻¹ : (PowerSeries k)ˣ) : PowerSeries k) := by
    rw [← hGQ, hQU, mul_assoc, Units.mul_inv, mul_one]
  have hc := congrArg (coeff n) hGeq
  rw [coeff_mk] at hc
  rw [hc, hinv, coeff_X_pow_mul']
  by_cases h : N ≤ n + 1
  · rw [ite_eq_left (by omega), ite_eq_left h, show n + 1 - N = n - (N - 1) by omega]
  · rw [ite_eq_right (by omega), ite_eq_right h]

end Categorification.KLR.Unfurling
