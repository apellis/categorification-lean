/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Polynomial.Basic

/-!
# The partial-fraction matrix of the `sl₂` coproduct

The scalar part of the proof that Rouquier's map of a direct sum of `sl₂` data with separated
dots is invertible (B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*,
arXiv:1603.06311v3, Theorem `th:coproduct` and Lemma `lem:many-sl2`; the categorical part is in
`Categorification.TwoRep.RouqCoproduct`). After Gaussian elimination, the invertibility comes
down to a scalar matrix over the ground field.

Fix pairwise distinct `u a ∈ k` (`a ∈ A`), multiplicities `hp a`, `hn a` with
`hp a = 0 ∨ hn a = 0`, and `N` with `∑ hp = N + ∑ hn`. The matrix `crtMatrix` has rows `(a, m)`,
`m < hp a`, and columns `t < N` and `(e, m')`, `m' < hn e`. Its entries are the Taylor
coefficients `[zᵐ]` at `u a` of `Zᵗ` and of `(Z - u e)^{-(m'+1)}`. In other words, it sends a
rational function `p(Z) + ∑ c_{e,m'} (Z - u e)^{-(m'+1)}` (with `deg p < N`) to its jets of
order `hp a` at the points `u a`.

The matrix is square and injective, so it is invertible (`crtMatrix_mulVec_injective`,
`crtMatrix_exists_inv`). Proof: multiplying by `∏ₑ (Z - u e)^{hn e}` gives a polynomial of
degree `< ∑ hp`. It is divisible by `(Z - u a)^{hp a}` for every `a`, so it vanishes. Then the
partial fraction decomposition is unique.

The coefficients `telCoeff d i j = [zⁱ] (d + z)^{-(j+1)}` are also the coefficients of
`1 / (d + z - w)`, the inverse of a dumbbell, `telCoeff_rec`.
-/

noncomputable section

namespace Categorification.TwoRep

open Polynomial

variable {k : Type*} [Field k]

/-- `telCoeff d i j = [zⁱ] (d + z)^{-(j + 1)}`, the coefficient of `zⁱ wʲ` in `1 / (d + z - w)`. -/
def telCoeff (d : k) (i j : ℕ) : k :=
  PowerSeries.coeff i ((PowerSeries.C d + PowerSeries.X)⁻¹ ^ (j + 1))

/-- The recursion expressing `(d + z - w) · ∑ telCoeff d i j zⁱ wʲ = 1`. -/
theorem telCoeff_rec {d : k} (hd : d ≠ 0) (i j : ℕ) :
    d * telCoeff d i j + (if i = 0 then 0 else telCoeff d (i - 1) j) =
      if j = 0 then (if i = 0 then 1 else 0) else telCoeff d i (j - 1) := by
  set q : PowerSeries k := PowerSeries.C d + PowerSeries.X
  have hq : q * q⁻¹ = 1 := PowerSeries.mul_inv_cancel _ (by simp [q, hd])
  have key : q * q⁻¹ ^ (j + 1) = q⁻¹ ^ j := by
    rw [pow_succ', ← mul_assoc, hq, one_mul]
  have hc := congrArg (PowerSeries.coeff i) key
  have hl : PowerSeries.coeff i (q * q⁻¹ ^ (j + 1)) =
      d * telCoeff d i j + (if i = 0 then 0 else telCoeff d (i - 1) j) := by
    simp only [q, add_mul, map_add, PowerSeries.coeff_C_mul, telCoeff]
    congr 1
    rcases i with _ | i
    · simp
    · rw [PowerSeries.coeff_succ_X_mul]
      simp
  rw [hl] at hc
  rw [hc]
  rcases j with _ | j
  · simp [PowerSeries.coeff_one]
  · rw [ite_eq_right (Nat.succ_ne_zero j)]
    rfl

variable {A : Type*} [Fintype A] [DecidableEq A] (u : A → k) (hp hn : A → ℕ) (N : ℕ)

/-- **The partial-fraction matrix**: rows `(a, m)` with `m < hp a`, columns `t < N` (entry
`[zᵐ] (u a + z)ᵗ`) and `(e, m')` with `m' < hn e` (entry `[zᵐ] (u a - u e + z)^{-(m'+1)}`). -/
def crtMatrix : Matrix (Σ a, Fin (hp a)) (Fin N ⊕ Σ e, Fin (hn e)) k :=
  Matrix.of fun x y =>
    Sum.elim (fun t : Fin N => ((t : ℕ).choose x.2 : k) * u x.1 ^ ((t : ℕ) - x.2))
      (fun y : Σ e, Fin (hn e) => telCoeff (u x.1 - u y.1) x.2 y.2) y

section Poly

/-- The Taylor expansion at `r`, as a ring homomorphism into power series. -/
def taylorSeries (r : k) : k[X] →+* PowerSeries k :=
  (Polynomial.coeToPowerSeries.ringHom).comp (taylorEquiv r).toRingHom

theorem taylorSeries_apply (r : k) (p : k[X]) : taylorSeries r p = ((taylor r p : k[X]) : PowerSeries k) :=
  rfl

theorem taylorSeries_X_sub_C (r s : k) :
    taylorSeries r (X - C s) = PowerSeries.C (r - s) + PowerSeries.X := by
  rw [taylorSeries_apply, map_sub, taylor_X, taylor_C]
  simp only [Polynomial.coe_sub, Polynomial.coe_add, Polynomial.coe_C, Polynomial.coe_X, map_sub]
  ring

theorem taylorEquiv_symm_X (r : k) : (taylorEquiv r).symm X = X - C r := by
  rw [AlgEquiv.symm_apply_eq]
  change X = taylor r (X - C r)
  rw [map_sub, taylor_X, taylor_C]
  ring

/-- If the Taylor series at `r` is divisible by `zⁿ`, the polynomial is divisible by `(X - r)ⁿ`. -/
theorem X_sub_C_pow_dvd_of_taylorSeries {r : k} {p : k[X]} {n : ℕ}
    (h : PowerSeries.X ^ n ∣ taylorSeries r p) : (X - C r) ^ n ∣ p := by
  rw [PowerSeries.X_pow_dvd_iff] at h
  have h' : X ^ n ∣ taylorEquiv r p := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    have := h d hd
    rwa [taylorSeries_apply, Polynomial.coeff_coe] at this
  have := map_dvd (taylorEquiv r).symm h'
  rwa [map_pow, taylorEquiv_symm_X, AlgEquiv.symm_apply_apply] at this

/-- The polynomial attached to the first `N` coordinates. -/
def vPoly (v : Fin N ⊕ (Σ e, Fin (hn e)) → k) : k[X] :=
  ∑ t : Fin N, C (v (Sum.inl t)) * X ^ (t : ℕ)

/-- `∏ₑ (X - u e)^{hn e}`. -/
def piPoly : k[X] := ∏ e, (X - C (u e)) ^ hn e

/-- `∏ₑ (X - u e)^{hn e} / (X - u e)^{m + 1}`. -/
def gPoly (e : A) (m : ℕ) : k[X] :=
  (∏ e' ∈ Finset.univ.erase e, (X - C (u e')) ^ hn e') * (X - C (u e)) ^ (hn e - 1 - m)

omit [DecidableEq A] in
theorem piPoly_monic : (piPoly u hn).Monic :=
  monic_prod_of_monic _ _ fun e _ => (monic_X_sub_C (u e)).pow (hn e)

omit [DecidableEq A] in
theorem natDegree_piPoly : (piPoly u hn).natDegree = ∑ e, hn e := by
  rw [piPoly, natDegree_prod_of_monic _ _ fun e _ => (monic_X_sub_C (u e)).pow (hn e)]
  simp [natDegree_pow]

theorem gPoly_mul {e : A} {m : ℕ} (hm : m < hn e) :
    gPoly u hn e m * (X - C (u e)) ^ (m + 1) = piPoly u hn := by
  rw [gPoly, mul_assoc, ← pow_add, show hn e - 1 - m + (m + 1) = hn e by omega, piPoly,
    Finset.prod_erase_mul _ _ (Finset.mem_univ e)]

theorem gPoly_ne_zero {e : A} {m : ℕ} (hm : m < hn e) : gPoly u hn e m ≠ 0 := by
  intro h0
  have := gPoly_mul u hn hm
  rw [h0, zero_mul] at this
  exact (piPoly_monic u hn).ne_zero this.symm

theorem natDegree_gPoly_lt {e : A} {m : ℕ} (hm : m < hn e) :
    (gPoly u hn e m).natDegree < ∑ e, hn e := by
  have h := congrArg natDegree (gPoly_mul u hn hm)
  rw [natDegree_mul (gPoly_ne_zero u hn hm) (pow_ne_zero _ (X_sub_C_ne_zero _)),
    natDegree_pow, natDegree_X_sub_C, natDegree_piPoly] at h
  omega

/-- The polynomial `p · ∏ₑ (X - u e)^{hn e} + ∑ c_{e,m} ∏ₑ (X - u e)^{hn e} / (X - u e)^{m+1}`. -/
def fPoly (v : Fin N ⊕ (Σ e, Fin (hn e)) → k) : k[X] :=
  vPoly hn N v * piPoly u hn + ∑ y : Σ e, Fin (hn e), C (v (Sum.inr y)) * gPoly u hn y.1 y.2

theorem degree_C_mul_le' (c : k) (p : k[X]) : (C c * p).degree ≤ p.degree := by
  by_cases hc : c = 0
  · simp [hc]
  · rw [degree_C_mul hc]

theorem degree_lt_of_natDegree_lt {p : k[X]} {n : ℕ} (h : p.natDegree < n) : p.degree < n :=
  (degree_le_natDegree).trans_lt (by exact_mod_cast h)

theorem fPoly_degree_lt (v : Fin N ⊕ (Σ e, Fin (hn e)) → k) :
    (fPoly u hn N v).degree < ((N + ∑ e, hn e : ℕ) : WithBot ℕ) := by
  rw [← mem_degreeLT]
  refine Submodule.add_mem _ ?_ (Submodule.sum_mem _ fun y _ => ?_)
  · rw [vPoly, Finset.sum_mul]
    refine Submodule.sum_mem _ fun t _ => ?_
    rw [mem_degreeLT, mul_assoc]
    refine (degree_C_mul_le' _ _).trans_lt (degree_lt_of_natDegree_lt ?_)
    rw [natDegree_mul (pow_ne_zero _ X_ne_zero) (piPoly_monic u hn).ne_zero, natDegree_X_pow,
      natDegree_piPoly]
    omega
  · rw [mem_degreeLT]
    refine (degree_C_mul_le' _ _).trans_lt (degree_lt_of_natDegree_lt ?_)
    have := natDegree_gPoly_lt u hn y.2.2
    omega

end Poly

section Injective

variable {u hp hn N}

omit [Fintype A] [DecidableEq A] in
theorem coeff_taylorSeries_vPoly (r : k) (v : Fin N ⊕ (Σ e, Fin (hn e)) → k) (m : ℕ) :
    PowerSeries.coeff m (taylorSeries r (vPoly hn N v)) =
      ∑ t : Fin N, v (Sum.inl t) * (((t : ℕ).choose m : k) * r ^ ((t : ℕ) - m)) := by
  rw [taylorSeries_apply, Polynomial.coeff_coe, vPoly, map_sum, finsetSum_coeff]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [taylor_mul, taylor_pow, taylor_X, taylor_C, coeff_C_mul, coeff_X_add_C_pow]
  ring

/-- **The partial-fraction matrix is injective.** -/
theorem crtMatrix_mulVec_injective (hu : Function.Injective u)
    (hdisj : ∀ a, hp a = 0 ∨ hn a = 0) (hN : ∑ a, hp a = N + ∑ a, hn a)
    (v : Fin N ⊕ (Σ e, Fin (hn e)) → k) (hv : (crtMatrix u hp hn N).mulVec v = 0) : v = 0 := by
  -- Step 1: the jets.
  have hdiv : ∀ a, (X - C (u a)) ^ hp a ∣ fPoly u hn N v := by
    intro a
    rcases Nat.eq_zero_or_pos (hp a) with h0 | hpos
    · rw [h0, pow_zero]; exact one_dvd _
    have hna : hn a = 0 := (hdisj a).resolve_left (by omega)
    have hne : ∀ y : Σ e, Fin (hn e), u a - u y.1 ≠ 0 := by
      rintro ⟨e, me⟩ hy
      have := hu (sub_eq_zero.mp hy)
      subst this
      rw [hna] at me
      exact me.elim0
    set R : PowerSeries k := taylorSeries (u a) (vPoly hn N v) +
      ∑ y : Σ e, Fin (hn e), PowerSeries.C (v (Sum.inr y)) *
        (PowerSeries.C (u a - u y.1) + PowerSeries.X)⁻¹ ^ ((y.2 : ℕ) + 1) with hRdef
    have hR : ∀ m < hp a, PowerSeries.coeff m R = 0 := by
      intro m hm
      have hvm := congrFun hv ⟨a, ⟨m, hm⟩⟩
      rw [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Pi.zero_apply] at hvm
      rw [hRdef, map_add, coeff_taylorSeries_vPoly, map_sum]
      simp only [PowerSeries.coeff_C_mul]
      rw [← hvm]
      simp only [crtMatrix, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, telCoeff]
      congr 1
      · exact Finset.sum_congr rfl fun t _ => mul_comm _ _
      · exact Finset.sum_congr rfl fun y _ => mul_comm _ _
    have hF : taylorSeries (u a) (fPoly u hn N v) = taylorSeries (u a) (piPoly u hn) * R := by
      have hg : ∀ y : Σ e, Fin (hn e), taylorSeries (u a) (gPoly u hn y.1 y.2) =
          taylorSeries (u a) (piPoly u hn) *
            (PowerSeries.C (u a - u y.1) + PowerSeries.X)⁻¹ ^ ((y.2 : ℕ) + 1) := by
        intro y
        set q : PowerSeries k := PowerSeries.C (u a - u y.1) + PowerSeries.X
        have hq : q * q⁻¹ = 1 := PowerSeries.mul_inv_cancel _ (by simp [q, hne y])
        have h1 := congrArg (taylorSeries (u a)) (gPoly_mul u hn y.2.2)
        rw [map_mul, map_pow, taylorSeries_X_sub_C] at h1
        rw [← h1, mul_assoc, ← mul_pow, hq, one_pow, mul_one]
      rw [fPoly, map_add, map_mul, map_sum, hRdef, mul_add, Finset.mul_sum, mul_comm]
      congr 1
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [map_mul, hg, taylorSeries_apply (u a) (C _), taylor_C, Polynomial.coe_C]
      ring
    apply X_sub_C_pow_dvd_of_taylorSeries
    rw [hF]
    exact Dvd.dvd.mul_left (PowerSeries.X_pow_dvd_iff.mpr hR) _
  -- Step 2: the polynomial vanishes.
  have hF0 : fPoly u hn N v = 0 := by
    have hprod : (∏ a, (X - C (u a)) ^ hp a) ∣ fPoly u hn N v := by
      refine Finset.prod_dvd_of_coprime ?_ fun a _ => hdiv a
      intro a _ b _ hab
      exact (isCoprime_X_sub_C_of_isUnit_sub
        (sub_ne_zero.mpr (hu.ne hab)).isUnit).pow
    refine eq_zero_of_dvd_of_degree_lt hprod ?_
    have hmon : (∏ a, (X - C (u a)) ^ hp a).Monic :=
      monic_prod_of_monic _ _ fun a _ => (monic_X_sub_C (u a)).pow (hp a)
    rw [degree_eq_natDegree hmon.ne_zero, natDegree_prod_of_monic _ _ fun a _ =>
      (monic_X_sub_C (u a)).pow (hp a)]
    simp only [natDegree_pow, natDegree_X_sub_C, mul_one]
    rw [hN]
    exact fPoly_degree_lt u hn N v
  -- Step 3: uniqueness of partial fractions.
  have hc : ∀ y : Σ e, Fin (hn e), v (Sum.inr y) = 0 := by
    rintro ⟨e, i⟩
    have hH : 0 < (hn e) := lt_of_le_of_lt (Nat.zero_le _) i.2
    set Q : k[X] := ∏ e' ∈ Finset.univ.erase e, (X - C (u e')) ^ hn e'
    set S : k[X] := ∑ m' : Fin (hn e), C (v (Sum.inr ⟨e, m'⟩)) * (X - C (u e)) ^ ((hn e) - 1 - m')
    have hsplit : ∑ y : Σ e, Fin (hn e), C (v (Sum.inr y)) * gPoly u hn y.1 y.2 =
        Q * S + ∑ e' ∈ Finset.univ.erase e, ∑ m' : Fin (hn e'),
          C (v (Sum.inr ⟨e', m'⟩)) * gPoly u hn e' m' := by
      rw [Fintype.sum_sigma, ← Finset.add_sum_erase _ _ (Finset.mem_univ e)]
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m' _ => ?_
      rw [gPoly]
      ring
    have hdQ : ∀ e' ∈ Finset.univ.erase e, ∀ m' : Fin (hn e'),
        (X - C (u e)) ^ (hn e) ∣ gPoly u hn e' m' := by
      intro e' he' m'
      exact Dvd.dvd.mul_right (Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr
        ⟨(Finset.ne_of_mem_erase he').symm, Finset.mem_univ e⟩)) _
    have hdS : (X - C (u e)) ^ (hn e) ∣ Q * S := by
      have h0 := hF0
      rw [fPoly, hsplit] at h0
      have hpi : (X - C (u e)) ^ (hn e) ∣ piPoly u hn :=
        Finset.dvd_prod_of_mem _ (Finset.mem_univ e)
      have hrest : (X - C (u e)) ^ (hn e) ∣ ∑ e' ∈ Finset.univ.erase e, ∑ m' : Fin (hn e'),
          C (v (Sum.inr ⟨e', m'⟩)) * gPoly u hn e' m' :=
        Finset.dvd_sum fun e' he' => Finset.dvd_sum fun m' _ =>
          Dvd.dvd.mul_left (hdQ e' he' m') _
      have : Q * S = -(vPoly hn N v * piPoly u hn) - ∑ e' ∈ Finset.univ.erase e,
          ∑ m' : Fin (hn e'), C (v (Sum.inr ⟨e', m'⟩)) * gPoly u hn e' m' := by
        rw [← sub_eq_zero, ← h0]; ring
      rw [this]
      exact dvd_sub (dvd_neg.mpr (Dvd.dvd.mul_left hpi _)) hrest
    have hcop : IsCoprime ((X - C (u e)) ^ (hn e)) Q :=
      IsCoprime.prod_right fun e' he' => (isCoprime_X_sub_C_of_isUnit_sub
        (sub_ne_zero.mpr (hu.ne (Finset.ne_of_mem_erase he').symm)).isUnit).pow
    have hS : S = 0 := by
      refine eq_zero_of_dvd_of_degree_lt (hcop.dvd_of_dvd_mul_left hdS) ?_
      rw [degree_eq_natDegree ((monic_X_sub_C (u e)).pow (hn e)).ne_zero, natDegree_pow, natDegree_X_sub_C,
        mul_one, ← mem_degreeLT]
      refine Submodule.sum_mem _ fun m' _ => ?_
      rw [mem_degreeLT]
      refine (degree_C_mul_le' _ _).trans_lt ?_
      rw [degree_pow, degree_X_sub_C, nsmul_one]
      exact_mod_cast (show (hn e) - 1 - (m' : ℕ) < (hn e) by omega)
    have hT := congrArg (fun p => (taylor (u e) p).coeff ((hn e) - 1 - i)) hS
    simp only [S, map_sum, taylor_mul, taylor_pow, map_sub, taylor_X, taylor_C, add_sub_cancel_right,
      finsetSum_coeff, coeff_C_mul, coeff_X_pow, map_zero, coeff_zero] at hT
    rw [Finset.sum_eq_single i] at hT
    · simpa using hT
    · intro m' _ hm'
      rw [ite_eq_right (by intro h; apply hm'; ext; have := m'.2; have := i.2; omega), mul_zero]
    · intro hm; exact (hm (Finset.mem_univ _)).elim
  have hvP : vPoly hn N v = 0 := by
    have h0 := hF0
    rw [fPoly] at h0
    have hs : ∑ y : Σ e, Fin (hn e), C (v (Sum.inr y)) * gPoly u hn y.1 y.2 = 0 :=
      Finset.sum_eq_zero fun y _ => by rw [hc y, map_zero, zero_mul]
    rw [hs, add_zero] at h0
    exact (mul_eq_zero.mp h0).resolve_right (piPoly_monic u hn).ne_zero
  funext x
  rcases x with t | y
  · have := congrArg (fun p => p.coeff t) hvP
    simp only [vPoly, finsetSum_coeff, coeff_C_mul, coeff_X_pow, coeff_zero] at this
    rw [Finset.sum_eq_single t] at this
    · simpa using this
    · intro t' _ ht'
      rw [ite_eq_right (by intro h; exact ht' (Fin.ext h.symm)), mul_zero]
    · intro ht; exact (ht (Finset.mem_univ _)).elim
  · exact hc y

/-- **The partial-fraction matrix is invertible.** -/
theorem crtMatrix_exists_inv (hu : Function.Injective u)
    (hdisj : ∀ a, hp a = 0 ∨ hn a = 0) (hN : ∑ a, hp a = N + ∑ a, hn a) :
    ∃ D : Matrix (Fin N ⊕ Σ e, Fin (hn e)) (Σ a, Fin (hp a)) k,
      crtMatrix u hp hn N * D = 1 ∧ D * crtMatrix u hp hn N = 1 := by
  have hcard : Fintype.card (Fin N ⊕ Σ e, Fin (hn e)) = Fintype.card (Σ a, Fin (hp a)) := by
    simp [Fintype.card_sigma, hN]
  let eq : (Fin N ⊕ Σ e, Fin (hn e)) ≃ (Σ a, Fin (hp a)) := Fintype.equivOfCardEq hcard
  set M := crtMatrix u hp hn N
  let M' : Matrix (Σ a, Fin (hp a)) (Σ a, Fin (hp a)) k := M.submatrix id eq.symm
  have hinj : Function.Injective M'.mulVec := by
    intro w₁ w₂ hw
    have h : M.mulVec (w₁ ∘ eq - w₂ ∘ eq) = 0 := by
      have e1 : ∀ w, M'.mulVec w = M.mulVec (w ∘ eq) := by
        intro w
        funext x
        simp only [M', Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id]
        rw [← Equiv.sum_comp eq]
        simp
      rw [Matrix.mulVec_sub, ← e1, ← e1, hw, sub_self]
    have := crtMatrix_mulVec_injective hu hdisj hN _ h
    funext x
    have := congrFun this (eq.symm x)
    simpa [sub_eq_zero] using this
  have hunit : IsUnit M' := (Matrix.mulVec_injective_iff_isUnit).mp hinj
  obtain ⟨M'', h1, h2⟩ : ∃ M'' : Matrix (Σ a, Fin (hp a)) (Σ a, Fin (hp a)) k,
      M' * M'' = 1 ∧ M'' * M' = 1 :=
    ⟨M'⁻¹, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hunit),
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hunit)⟩
  refine ⟨M''.submatrix eq id, ?_, ?_⟩
  · ext x x'
    have := congrFun (congrFun h1 x) x'
    rw [Matrix.mul_apply] at this ⊢
    rw [← this, ← Equiv.sum_comp eq.symm]
    simp [M']
  · ext t t'
    have := congrFun (congrFun h2 (eq t)) (eq t')
    rw [Matrix.mul_apply] at this ⊢
    simp only [Matrix.submatrix_apply, id, M', Equiv.symm_apply_apply] at this ⊢
    rw [this]
    simp [Matrix.one_apply, eq.injective.eq_iff]

end Injective

end Categorification.TwoRep
