/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.Dimension

/-!
# Geometric series `(1 - q^d)⁻¹` and graded dimensions of polynomial rings

In `ℤ((q))`, for `d > 0` the element `1 - q^d` is invertible with inverse the geometric series
`∑_{n ≥ 0} q^{d n}` (`geomSeries d`, `one_sub_mul_geomSeries`). For positive weights
`w : Fin n → ℤ`, the coefficient of `q^e` in `∏_a (1 - q^{w a})⁻¹` is the number of monomials
`x^u` of weighted degree `∑_a u_a w_a = e` (`coeff_prod_geomSeries`): this is the graded dimension
of the polynomial ring `k[x_1, …, x_n]` with `deg x_a = w_a`, as used in Khovanov–Lauda I
(arXiv:0803.4121v2), §2.5, e.g. `gdim (1_j R(ν) 1_i) = ∑_{w • i = j} q^{deg(ψ_w 1_i)}
∏_a (1 - q^{deg x_{a,i}})⁻¹`.
-/

namespace Categorification.Graded

open Finset

/-- A shortcut instance: without it, finding `CommMonoid (LaurentSeries ℤ)` (needed for finite
products) can time out. It is the instance of `HahnSeries ℤ ℤ`. -/
noncomputable instance instCommMonoidLaurentSeriesInt : CommMonoid (LaurentSeries ℤ) :=
  inferInstanceAs (CommMonoid (HahnSeries ℤ ℤ))

/-- The geometric series `∑_{n ≥ 0} q^{d n} ∈ ℤ((q))`; for `d > 0` it is `(1 - q^d)⁻¹`
(`one_sub_mul_geomSeries`). -/
noncomputable def geomSeries (d : ℤ) : LaurentSeries ℤ :=
  HahnSeries.ofPowerSeries ℤ ℤ (PowerSeries.mk fun n => if d ∣ (n : ℤ) then 1 else 0)

theorem one_sub_X_pow_mul_mk {n : ℕ} (hn : 0 < n) :
    (1 - PowerSeries.X ^ n) * PowerSeries.mk (fun k => if (n : ℤ) ∣ (k : ℤ) then (1 : ℤ) else 0)
      = 1 := by
  ext k
  rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_mk,
    PowerSeries.coeff_one]
  simp only [Int.natCast_dvd_natCast, PowerSeries.coeff_mk]
  by_cases hk : k = 0
  · subst hk
    simp [show ¬ n ≤ 0 by omega]
  · rw [if_neg hk]
    by_cases hle : n ≤ k
    · have h : n ∣ k ↔ n ∣ k - n := by
        rw [← Nat.dvd_add_self_right (m := n) (n := k - n), Nat.sub_add_cancel hle]
      simp only [if_pos hle, h, sub_self]
    · have h : ¬ n ∣ k := fun h => hk (Nat.eq_zero_of_dvd_of_lt h (by omega))
      simp [h, hle]

/-- `(1 - q^d) · ∑_{n ≥ 0} q^{d n} = 1` for `d > 0`. -/
theorem one_sub_mul_geomSeries {d : ℤ} (hd : 0 < d) :
    (1 - HahnSeries.single d 1) * geomSeries d = 1 := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, d = n := ⟨d.toNat, by omega⟩
  have hn : 0 < n := by exact_mod_cast hd
  rw [geomSeries, ← HahnSeries.ofPowerSeries_X_pow, ← map_one (HahnSeries.ofPowerSeries ℤ ℤ),
    ← map_sub, ← map_mul, one_sub_X_pow_mul_mk hn, map_one]

/-- The coefficient of `q^e` in `ofPowerSeries F` for negative `e` vanishes. -/
theorem coeff_ofPowerSeries_of_neg (F : PowerSeries ℤ) {e : ℤ} (he : e < 0) :
    (HahnSeries.ofPowerSeries ℤ ℤ F).coeff e = 0 := by
  rw [HahnSeries.ofPowerSeries_apply]
  exact HahnSeries.embDomain_notin_range (by
    rintro ⟨n, hn⟩
    simp only [RelEmbedding.coe_mk, Function.Embedding.coeFn_mk] at hn
    omega)

/-- The weighted degree `∑_a u_a w_a` of a monomial `x^u` is at least each `u_a` when all
weights are positive. -/
theorem le_weight {n : ℕ} {w : Fin n → ℤ} (hw : ∀ a, 0 < w a) (u : Fin n →₀ ℕ) (a : Fin n) :
    (u a : ℤ) ≤ Finsupp.weight w u := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  calc (u a : ℤ) ≤ u a • w a := by
        rw [nsmul_eq_mul]; nlinarith [hw a, (Nat.cast_nonneg (u a) : (0 : ℤ) ≤ u a)]
    _ ≤ ∑ b, u b • w b :=
        Finset.single_le_sum (fun b _ => nsmul_nonneg (hw b).le _) (Finset.mem_univ a)

theorem weight_eq_sum {n : ℕ} (w : Fin n → ℤ) (u : Fin n →₀ ℕ) :
    Finsupp.weight w u = ∑ a, (u a : ℤ) * w a := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [nsmul_eq_mul]

theorem weight_nonneg {n : ℕ} {w : Fin n → ℤ} (hw : ∀ a, 0 ≤ w a) (u : Fin n →₀ ℕ) :
    0 ≤ Finsupp.weight w u := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  exact Finset.sum_nonneg fun b _ => nsmul_nonneg (hw b) _

/-- For positive weights there are finitely many monomials of each weighted degree. -/
theorem finite_weight_eq {n : ℕ} {w : Fin n → ℤ} (hw : ∀ a, 0 < w a) (e : ℤ) :
    {u : Fin n →₀ ℕ | Finsupp.weight w u = e}.Finite := by
  refine ((Set.Finite.pi (t := fun _ : Fin n => Set.Iic e.toNat) fun _ =>
    Set.finite_Iic _).image Finsupp.equivFunOnFinite.symm).subset ?_
  intro u hu
  refine ⟨u, fun a _ => ?_, by simp⟩
  have := le_weight hw u a
  rw [Set.mem_setOf_eq] at hu
  rw [hu] at this
  simp only [Set.mem_Iic]
  omega

/-- **Graded dimension of a weighted polynomial ring.** For positive weights `w`, the coefficient
of `q^e` in `∏_a (1 - q^{w a})⁻¹` is the number of monomials of weighted degree `e`. -/
theorem coeff_prod_geomSeries {n : ℕ} (w : Fin n → ℤ) (hw : ∀ a, 0 < w a) (e : ℤ) :
    (∏ a, geomSeries (w a)).coeff e = Nat.card {u : Fin n →₀ ℕ | Finsupp.weight w u = e} := by
  simp only [geomSeries]
  rw [← map_prod]
  rcases lt_or_le e 0 with he | he
  · rw [coeff_ofPowerSeries_of_neg _ he]
    have : {u : Fin n →₀ ℕ | Finsupp.weight w u = e} = ∅ :=
      Set.eq_empty_iff_forall_not_mem.2 fun u hu => by
        have := weight_nonneg (fun a => (hw a).le) u
        rw [Set.mem_setOf_eq] at hu
        omega
    rw [this]; simp
  obtain ⟨N, rfl⟩ : ∃ N : ℕ, e = N := ⟨e.toNat, by omega⟩
  rw [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_prod]
  simp only [PowerSeries.coeff_mk, Finset.prod_boole]
  have key : ∀ {R : Type} [CommSemiring R] (s : Finset (Fin n →₀ ℕ)) (P : (Fin n →₀ ℕ) → Prop)
      (inst : DecidablePred P), (∑ x ∈ s, @ite R (P x) (inst x) 1 0) = ((s.filter P).card : R) :=
    fun s P _ => (Finset.natCast_card_filter P s).symm
  refine (key (R := ℤ) _ _ _).trans ?_
  rw [Finset.filter_congr_decidable]
  -- the monomials of weighted degree `N` correspond to the `l` in the antidiagonal with
  -- `w a ∣ l a`, via `l a = u a * w a`
  set w' : Fin n → ℕ := fun a => (w a).toNat
  have hw' : ∀ a, (w a : ℤ) = w' a := fun a => by simp only [w']; have := hw a; omega
  have hw'pos : ∀ a, 0 < w' a := fun a => by have := hw' a; have := hw a; omega
  have hweight : ∀ u : Fin n →₀ ℕ, Finsupp.weight w u = ((∑ a, u a * w' a : ℕ) : ℤ) := by
    intro u
    rw [weight_eq_sum]
    push_cast
    exact Finset.sum_congr rfl fun a _ => by rw [hw']
  congr 1
  rw [← Nat.card_eq_finsetCard]
  refine Nat.card_congr ?_
  exact {
    toFun := fun l => ⟨Finsupp.equivFunOnFinite.symm fun a => (l : Fin n →₀ ℕ) a / w' a, by
      have hl := Finset.mem_filter.1 l.2
      have hsum := (Finset.mem_finsuppAntidiag.1 hl.1).1
      rw [Set.mem_setOf_eq, hweight]
      have : (∑ a, (Finsupp.equivFunOnFinite.symm fun a => (l : Fin n →₀ ℕ) a / w' a) a * w' a)
          = univ.sum ⇑(l : Fin n →₀ ℕ) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        have hdvd : w' a ∣ (l : Fin n →₀ ℕ) a := by
          have := hl.2 a (Finset.mem_univ a); rw [hw'] at this; exact_mod_cast this
        simp only [Finsupp.equivFunOnFinite_symm_apply_toFun]
        exact Nat.div_mul_cancel hdvd
      rw [this, hsum]⟩
    invFun := fun u => ⟨Finsupp.equivFunOnFinite.symm fun a => (u : Fin n →₀ ℕ) a * w' a, by
      have hu : Finsupp.weight w (u : Fin n →₀ ℕ) = N := u.2
      rw [hweight] at hu
      rw [Finset.mem_filter, Finset.mem_finsuppAntidiag]
      refine ⟨⟨?_, by simp⟩, fun a _ => ?_⟩
      · exact_mod_cast hu
      · simp only [Finsupp.equivFunOnFinite_symm_apply_toFun, hw']
        exact_mod_cast Dvd.intro_left _ rfl⟩
    left_inv := fun l => by
      have hl := Finset.mem_filter.1 l.2
      refine Subtype.ext (Finsupp.ext fun a => ?_)
      have hdvd : w' a ∣ (l : Fin n →₀ ℕ) a := by
        have := hl.2 a (Finset.mem_univ a); rw [hw'] at this; exact_mod_cast this
      simp [Nat.div_mul_cancel hdvd]
    right_inv := fun u => by
      refine Subtype.ext (Finsupp.ext fun a => ?_)
      simp [Nat.mul_div_cancel _ (hw'pos a)] }

end Categorification.Graded
