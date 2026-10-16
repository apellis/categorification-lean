/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Unfurling.VacuumMixed

/-!
# The highest weight labels on the generating object

B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3, proof of the
theorem with label `nondegenerate`. Two inputs to the bubble theorem `ev_comp_eq_lwSeq` on the
generating object `𝕍`:

* On a label `b` for which `𝕍` is highest weight, `F_b E_b 𝕍 = 0`, so Rouquier's inverse for
  `b` (Brundan (1.8)) decomposes `P_b = E_b F_b 𝕍` by the caps `yᵐ ≫ κ` (`m < Λ_b`) with dual
  cups `g_m`. If the caps `yᵐ ≫ κ` with `m ≥ Λ_b` vanish on the cups, then `g_m ≫ y = g_{m-1}`
  (`chain_comp_dot`), and the dot `ϖ_b(y)` of `g` acts on the cups triangularly:
  `g_m ≫ ϖ_b(y) = ∑_{j ≤ m} [ϖ_b]_{m-j} g_j` (`chain_comp_aeval`). This is the chain of
  `chainSum_comp_sigma`, with `β_{m+1,m} = [ϖ_b]₁`.
* If a polynomial `p` kills `x` and `p(z)` is a unit, then `x - z` is invertible
  (`exists_inverse_sub_algebraMap`). On `F E 𝕍 = ⊕ₐ F_a E_a 𝕍` the dot is killed by
  `∏ₐ (X - z_a)^{h_a}`, so `D - z_b` is invertible when `z_b ≠ z_a` for all `a`.

## Main results

* `chain_comp_dot`, `chain_comp_pow`, `chain_comp_aeval`, `chain_comp_aeval_sub`.
* `exists_inverse_sub_algebraMap`.
-/

namespace Categorification.KLR.Unfurling

open CategoryTheory Polynomial

section Inverse

variable {L : Type*} [CommRing L] {A : Type*} [Ring A] [Algebra L A]

/-- **Inverting `x - z`**: if `p(x) = 0` and `p(z)` is a unit, then `x - z` has a two-sided
inverse. -/
theorem exists_inverse_sub_algebraMap (x : A) (p : L[X]) (hp : aeval x p = 0) (z : L)
    (hz : IsUnit (p.eval z)) :
    ∃ w : A, (x - algebraMap L A z) * w = 1 ∧ w * (x - algebraMap L A z) = 1 := by
  obtain ⟨q, hq⟩ := X_sub_C_dvd_sub_C_eval (p := p) (a := z)
  have h := congrArg (aeval x) hq
  rw [map_sub, hp, aeval_C, map_mul, map_sub, aeval_X, aeval_C, zero_sub] at h
  obtain ⟨u, hu⟩ := hz
  have hcomm : aeval x q * (x - algebraMap L A z) = (x - algebraMap L A z) * aeval x q := by
    have hx : x - algebraMap L A z = aeval x (X - C z) := by simp
    rw [hx, ← map_mul, ← map_mul, mul_comm]
  refine ⟨-(algebraMap L A ↑u⁻¹ * aeval x q), ?_, ?_⟩
  · rw [mul_neg, ← mul_assoc, ← Algebra.commutes, mul_assoc, ← h, mul_neg, neg_neg, ← map_mul,
      ← hu, Units.inv_mul, map_one]
  · rw [neg_mul, mul_assoc, hcomm, ← h, mul_neg, neg_neg, ← map_mul, ← hu, Units.inv_mul,
      map_one]

end Inverse

section Chain

variable {L : Type*} [CommRing L] {C : Type*} [Category C] [Preadditive C] [Linear L C]

/-- **The cups of a highest weight label lower the dot**: if `∑_{m<Λ} (yᵐ ≫ κ) ≫ g_m = 1` and
`g_m ≫ y^{m'} ≫ κ = δ_{m m'}` for `m < Λ` and all `m'`, then `g_m ≫ y = g_{m-1}`
(`0` for `m = 0`). -/
theorem chain_comp_dot {V P : C} (κ : P ⟶ V) (y : End P) (Λ : ℕ) (g : ℕ → (V ⟶ P))
    (htot : ∑ m ∈ Finset.range Λ, ((y ^ m : End P) ≫ κ) ≫ g m = 𝟙 P)
    (hgg : ∀ m m', m < Λ → g m ≫ (y ^ m' : End P) ≫ κ = if m' = m then 𝟙 V else 0)
    (m : ℕ) (hm : m < Λ) : g m ≫ y = if m = 0 then 0 else g (m - 1) := by
  have h : g m ≫ y = ∑ m' ∈ Finset.range Λ, (g m ≫ (y ^ (m' + 1) : End P) ≫ κ) ≫ g m' := by
    conv_lhs => rw [← Category.comp_id y, ← htot]
    rw [Preadditive.comp_sum, Preadditive.comp_sum]
    refine Finset.sum_congr rfl fun m' _ => ?_
    rw [pow_succ, End.mul_def]
    simp only [Category.assoc]
  rw [h]
  simp only [hgg m _ hm]
  rcases m with _ | m
  · exact Finset.sum_eq_zero fun m' _ => by
      simp only [show m' + 1 ≠ 0 by omega, ↓reduceIte, Limits.zero_comp]
  · rw [Finset.sum_eq_single m (fun m' _ hm' => by
        simp only [show m' + 1 ≠ m + 1 by omega, ↓reduceIte, Limits.zero_comp])
      (fun h' => absurd (Finset.mem_range.mpr (by omega)) h')]
    simp

variable {V P : C} (κ : P ⟶ V) (y : End P) (Λ : ℕ) (g : ℕ → (V ⟶ P))
  (htot : ∑ m ∈ Finset.range Λ, ((y ^ m : End P) ≫ κ) ≫ g m = 𝟙 P)
  (hgg : ∀ m m', m < Λ → g m ≫ (y ^ m' : End P) ≫ κ = if m' = m then 𝟙 V else 0)
include htot hgg

/-- Powers of the dot on the cups of a highest weight label: `g_m ≫ yⁿ = g_{m-n}`. -/
theorem chain_comp_pow (n m : ℕ) (hm : m < Λ) :
    g m ≫ (y ^ n : End P) = if n ≤ m then g (m - n) else 0 := by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, End.mul_def, ← Category.assoc, chain_comp_dot κ y Λ g htot hgg m hm]
    rcases m with _ | m
    · simp
    · simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, ih m (by omega),
        Nat.add_le_add_iff_right, Nat.add_sub_add_right]

/-- **The dot `p(y)` on the cups of a highest weight label**:
`g_m ≫ p(y) = ∑_{j ≤ m} p_{m-j} g_j`. -/
theorem chain_comp_aeval (p : L[X]) (m : ℕ) (hm : m < Λ) :
    g m ≫ (aeval y p : End P) = ∑ j ∈ Finset.range (m + 1), p.coeff (m - j) • g j := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, Preadditive.comp_add, hp, hq, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [coeff_add, add_smul]
  | monomial n a =>
    rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      Linear.comp_smul, chain_comp_pow κ y Λ g htot hgg n m hm]
    simp only [coeff_monomial]
    by_cases hn : n ≤ m
    · simp only [hn, ↓reduceIte]
      rw [Finset.sum_eq_single (m - n)]
      · simp only [show m - (m - n) = n by omega, ↓reduceIte]
      · intro j hj hjn
        simp only [show n ≠ m - j by have := Finset.mem_range.mp hj; omega, ↓reduceIte, zero_smul]
      · intro h'
        exact absurd (Finset.mem_range.mpr (by omega)) h'
    · simp only [hn, ↓reduceIte, smul_zero]
      exact (Finset.sum_eq_zero fun j hj => by
        simp only [show n ≠ m - j by have := Finset.mem_range.mp hj; omega, ↓reduceIte,
          zero_smul]).symm

/-- The chain of `chainSum_comp_sigma`: with `z = p₀`,
`g_m ≫ (p(y) - z) = ∑_{j < m} p_{m-j} g_j`. -/
theorem chain_comp_aeval_sub (p : L[X]) (m : ℕ) (hm : m < Λ) :
    g m ≫ (aeval y p - algebraMap L (End P) (p.coeff 0) : End P) =
      ∑ j ∈ Finset.range m, p.coeff (m - j) • g j := by
  rw [Preadditive.comp_sub, chain_comp_aeval κ y Λ g htot hgg p m hm, Finset.sum_range_succ,
    Nat.sub_self, Algebra.algebraMap_eq_smul_one, Linear.comp_smul, End.one_def,
    Category.comp_id, add_sub_cancel_right]

end Chain

end Categorification.KLR.Unfurling
