/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.NilHeckeSplitting

/-!
# Demazure operators in the nilHecke ring

The Demazure operator `π_j = -∂_j x_{j+1}` acts on `k[x_0, …, x_{m-1}]` by
`f ↦ (x_j s_j f - x_{j+1} f) / (x_j - x_{j+1})`; it is an idempotent of the nilHecke ring
`NH_m` and fixes `1`. Along the reduced word `w0Word n` of the longest element of `S_n`
(`n ≤ m`) the product of the `π_j` is

  `π_{w_0} = (-1)^{n(n-1)/2} ∂_{w_0} x^{ρ}`,  `x^ρ = x_1 x_2^2 ⋯ x_{n-1}^{n-1}`

(`demw_w0Word`). Consequently, in rank `m`, `π_{w_0}` is an idempotent of `NH_m`
(`isIdempotentElem_demIdem`) equivalent to the idempotent `e_m = x^δ ∂_{w_0}` of
`Categorification.Algebra.NilHeckeIdempotent`: with `a = x^δ π_{w_0}` and `b = ∂_{w_0}` one has
`a b = e_m` and `b a = π_{w_0}` (`demA_mul_ddw`, `ddw_mul_demA`). In the grading `deg x = 2`,
`deg ∂ = -2` the element `a` has degree `m(m-1)` and `b` degree `-m(m-1)`.

Such products of Demazure operators are the divided-power idempotents of Brundan–Ellis,
*Super Kac–Moody 2-categories* (arXiv:1701.04133v2, §11) for even colours.

## Main definitions and results

* `xv k m j`: multiplication by `x_j` (zero for `j ≥ m`); `demOp k m j = -(∂_j x_{j+1})`;
  `demw ρ` the product along a word; `yDelta n = x^ρ`.
* `demw_w0Word` : `π_{w_0} = (-1)^{n choose 2} ∂_{w_0} x^ρ` for `n ≤ m`.
* `demw_apply_one`, `ddw_w0Word_yDelta` : `π_ρ 1 = 1`, hence `∂_{w_0} x^ρ = (-1)^{n choose 2}`.
* `demIdem k m = π_{w_0}` (rank `m`), `isIdempotentElem_demIdem`, `demA_mul_ddw`,
  `ddw_mul_demA`.
-/

namespace Categorification.NilHecke

open MvPolynomial Equiv TypeA

variable {k : Type*} [CommRing k] {m : ℕ}

variable (k m) in
/-- Multiplication by `x_j` (zero-indexed), zero if `j ≥ m`. -/
noncomputable def xv (j : ℕ) : Module.End k (MvPolynomial (Fin m) k) :=
  if h : j < m then mulX k m ⟨j, h⟩ else 0

theorem xv_of_lt {j : ℕ} (h : j < m) : xv k m j = mulX k m ⟨j, h⟩ := dite_eq_left h

theorem xv_mem (j : ℕ) : xv k m j ∈ nilHecke k m := by
  unfold xv
  split_ifs
  · exact mulX_mem _
  · exact zero_mem _

variable (k m) in
/-- The Demazure operator `π_j = -∂_j x_{j+1}`. -/
noncomputable def demOp (j : ℕ) : Module.End k (MvPolynomial (Fin m) k) :=
  (-1 : ℤ) • (dd k m j * xv k m (j + 1))

theorem demOp_mem (j : ℕ) : demOp k m j ∈ nilHecke k m :=
  Subalgebra.zsmul_mem _ (mul_mem (dd_mem j) (xv_mem _)) _

/-- `π_ρ = π_{ρ₀} π_{ρ₁} ⋯` for a word `ρ`. -/
noncomputable def demw (ρ : List ℕ) : Module.End k (MvPolynomial (Fin m) k) :=
  (ρ.map (demOp k m)).prod

@[simp] theorem demw_nil : demw (k := k) (m := m) [] = 1 := rfl

@[simp] theorem demw_cons (j : ℕ) (ρ : List ℕ) :
    demw (k := k) (m := m) (j :: ρ) = demOp k m j * demw ρ := by simp [demw]

@[simp] theorem demw_append (ρ σ : List ℕ) :
    demw (k := k) (m := m) (ρ ++ σ) = demw ρ * demw σ := by simp [demw]

theorem demw_mem (ρ : List ℕ) : demw (k := k) (m := m) ρ ∈ nilHecke k m := by
  induction ρ with
  | nil => exact one_mem _
  | cons j ρ ih => rw [demw_cons]; exact mul_mem (demOp_mem j) ih

/-- The staircase monomial `x^ρ = x_1 x_2^2 ⋯ x_{n-1}^{n-1}` (zero-indexed: `x_a^a` for
`a < n`). -/
noncomputable def yDelta (n : ℕ) : MvPolynomial (Fin m) k :=
  ∏ a : Fin m, X a ^ (if (a : ℕ) < n then (a : ℕ) else 0)

@[simp] theorem yDelta_zero : yDelta (k := k) (m := m) 0 = 1 := by simp [yDelta]

theorem yDelta_succ {n : ℕ} (h : n < m) :
    yDelta (k := k) (m := m) (n + 1) = X ⟨n, h⟩ ^ n * yDelta n := by
  have hf : ∀ a : Fin m, (X a ^ (if (a : ℕ) < n + 1 then (a : ℕ) else 0) :
      MvPolynomial (Fin m) k) = (if a = ⟨n, h⟩ then X a ^ n else 1) *
        X a ^ (if (a : ℕ) < n then (a : ℕ) else 0) := by
    intro a
    by_cases ha : a = ⟨n, h⟩
    · subst ha; simp
    · have : (a : ℕ) ≠ n := fun e => ha (Fin.ext e)
      rw [ite_eq_right ha, one_mul]
      congr 1
      by_cases hl : (a : ℕ) < n
      · rw [ite_eq_left hl, ite_eq_left (by omega)]
      · rw [ite_eq_right hl, ite_eq_right (by omega)]
  rw [yDelta, Finset.prod_congr rfl fun a _ => hf a, Finset.prod_mul_distrib,
    Finset.prod_ite_eq' Finset.univ, ite_eq_left (Finset.mem_univ _), yDelta]

/-! ### Commutation lemmas -/

theorem dd_mul_ddw_comm {b : ℕ} {ρ : List ℕ} (h : ∀ c ∈ ρ, b + 1 < c) :
    dd k m b * ddw ρ = ddw ρ * dd k m b := by
  induction ρ with
  | nil => simp
  | cons c ρ ih =>
    rw [ddw_cons, ← mul_assoc, dd_mul_dd (h c List.mem_cons_self), mul_assoc,
      ih fun c' hc' => h c' (List.mem_cons_of_mem _ hc'), mul_assoc]

theorem commute_xv_dd {a j : ℕ} (h₁ : a ≠ j) (h₂ : a ≠ j + 1) :
    Commute (xv k m a) (dd k m j) := by
  by_cases ha : a < m
  · rw [xv_of_lt ha]
    exact (dd_mul_mulX j ⟨a, ha⟩ h₁ h₂).symm
  · rw [xv, dite_eq_right ha]
    exact Commute.zero_left _

theorem commute_xv_ddw {a : ℕ} {ρ : List ℕ} (h : ∀ c ∈ ρ, a ≠ c ∧ a ≠ c + 1) :
    Commute (xv k m a) (ddw ρ) := by
  induction ρ with
  | nil => exact Commute.one_right _
  | cons c ρ ih =>
    rw [ddw_cons]
    exact (commute_xv_dd (h c List.mem_cons_self).1 (h c List.mem_cons_self).2).mul_right
      (ih fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))

/-- `∂_c ∂_{w_0} = 0` and `∂_c` commutes with powers of `x_n`, for `c + 1 < n ≤ m`. -/
theorem dd_mul_xv_pow_mul_ddw_w0Word {n c : ℕ} (hn : n ≤ m) (hc : c + 1 < n) (p : ℕ) :
    dd k m c * (xv k m n ^ p * ddw (w0Word n)) = 0 := by
  rw [← mul_assoc, ((commute_xv_dd (k := k) (m := m) (a := n) (j := c) (by omega)
    (by omega)).pow_left p).eq.symm, mul_assoc, dd_mul_ddw_w0Word_of_lt hn hc, mul_zero]

/-! ### Moving a dot through a string of divided differences -/

/-- `∂_b x_{b+1} ∂_{b+1} ⋯ ∂_{b+L} M = ∂_b ∂_{b+1} ⋯ ∂_{b+L} x_{b+L+1} M` when every
`∂_c`, `b ≤ c < b + L`, kills `M`. -/
theorem dd_xv_ddw_range' {M : Module.End k (MvPolynomial (Fin m) k)} :
    ∀ (L b : ℕ), b + L + 1 < m → (∀ c, b ≤ c → c < b + L → dd k m c * M = 0) →
      dd k m b * xv k m (b + 1) * ddw (List.range' (b + 1) L) * M =
        dd k m b * ddw (List.range' (b + 1) L) * xv k m (b + 1 + L) * M
  | 0, b, _, _ => by simp
  | L + 1, b, hm, hM => by
    have key : xv k m (b + 1) * dd k m (b + 1) = dd k m (b + 1) * xv k m (b + 1 + 1) + 1 := by
      rw [xv_of_lt (by omega), xv_of_lt (by omega)]
      rw [← sub_eq_iff_eq_add']
      exact mulX_dd_sub_dd_mulX (by omega)
    have ih := dd_xv_ddw_range' L (b + 1) (by omega)
      (fun c h₁ h₂ => hM c (by omega) (by omega))
    have hzero : dd k m b * ddw (List.range' (b + 1 + 1) L) * M = 0 := by
      rw [dd_mul_ddw_comm (fun c hc => by rw [List.mem_range'_1] at hc; omega), mul_assoc,
        hM b le_rfl (by omega), mul_zero]
    rw [List.range'_succ, ddw_cons]
    calc dd k m b * xv k m (b + 1) * (dd k m (b + 1) * ddw (List.range' (b + 1 + 1) L)) * M
        = dd k m b * (xv k m (b + 1) * dd k m (b + 1)) *
            ddw (List.range' (b + 1 + 1) L) * M := by simp only [mul_assoc]
      _ = dd k m b * (dd k m (b + 1) * xv k m (b + 1 + 1) * ddw (List.range' (b + 1 + 1) L) * M)
            + dd k m b * ddw (List.range' (b + 1 + 1) L) * M := by
          rw [key]; simp only [mul_add, add_mul, mul_one, mul_assoc]
      _ = dd k m b * (dd k m (b + 1) * ddw (List.range' (b + 1 + 1) L) *
            xv k m (b + 1 + 1 + L) * M) := by rw [ih, hzero, add_zero]
      _ = _ := by
          rw [show b + 1 + (L + 1) = b + 1 + 1 + L by omega]; simp only [mul_assoc]

/-- `π_a π_{a+1} ⋯ π_{n-1} ∂_{w_0(n)} = (-1)^{n-a} ∂_a ⋯ ∂_{n-1} x_n^{n-a} ∂_{w_0(n)}` for
`n < m`. -/
theorem demw_range'_mul_ddw_w0Word {n : ℕ} (hn : n < m) :
    ∀ (L a : ℕ), a + L = n → demw (List.range' a L) * ddw (k := k) (m := m) (w0Word n) =
      (-1 : ℤ) ^ L • (ddw (List.range' a L) * xv k m n ^ L * ddw (w0Word n))
  | 0, a, _ => by simp
  | L + 1, a, hL => by
    have ih := demw_range'_mul_ddw_w0Word hn L (a + 1) (by omega)
    have hF := dd_xv_ddw_range' (M := xv k m n ^ L * ddw (k := k) (m := m) (w0Word n)) L a
      (by omega) (fun c _ h₂ => dd_mul_xv_pow_mul_ddw_w0Word hn.le (by omega) L)
    rw [show a + 1 + L = n by omega] at hF
    rw [List.range'_succ, demw_cons, ddw_cons, mul_assoc, ih, demOp, mul_smul_comm,
      smul_mul_assoc, smul_smul, pow_succ]
    congr 1
    simp only [mul_assoc] at hF ⊢
    rw [hF, pow_succ', mul_assoc]

/-- **Products of Demazure operators**: `π_{w_0} = (-1)^{n choose 2} ∂_{w_0} x^ρ` along the
reduced word `w0Word n`, for `n ≤ m`. -/
theorem demw_w0Word : ∀ {n : ℕ}, n ≤ m →
    demw (k := k) (m := m) (w0Word n) =
      (-1 : ℤ) ^ n.choose 2 • (ddw (w0Word n) * mulPoly k m (yDelta n))
  | 0, _ => by simp [w0Word]
  | n + 1, h => by
    have ih := demw_w0Word (n := n) (by omega)
    have hE := demw_range'_mul_ddw_w0Word (k := k) (m := m) (n := n) (by omega) n 0
      (by omega)
    have hc : Commute (xv k m n ^ n) (ddw (k := k) (m := m) (w0Word n)) :=
      (commute_xv_ddw fun c hc => by have := lt_of_mem_w0Word hc; omega).pow_left n
    rw [w0Word_succ, demw_append, ih, mul_smul_comm, ← mul_assoc, List.range_eq_range', hE,
      smul_mul_assoc, smul_smul, mul_assoc (ddw _), hc.eq, ddw_append, choose_two_succ,
      pow_add, yDelta_succ (by omega), map_mul, map_pow, mulPoly_X, ← xv_of_lt (by omega)]
    simp only [mul_assoc]

/-! ### Values on `1` -/

theorem demOp_apply_one {j : ℕ} (h : j + 1 < m) : demOp k m j 1 = 1 := by
  have hne : (⟨j, by omega⟩ : Fin m) ≠ ⟨j + 1, h⟩ := by simp [Fin.ext_iff]
  simp [demOp, xv_of_lt h, dd_of_lt h, ddiff_X_right hne]

theorem demw_apply_one {ρ : List ℕ} (h : ∀ j ∈ ρ, j + 1 < m) :
    demw (k := k) (m := m) ρ 1 = 1 := by
  induction ρ with
  | nil => rfl
  | cons j ρ ih =>
    rw [demw_cons, Module.End.mul_apply, ih fun l hl => h l (List.mem_cons_of_mem _ hl),
      demOp_apply_one (h j List.mem_cons_self)]

/-- `∂_{w_0} x^ρ = (-1)^{n choose 2}` for `n ≤ m`. -/
theorem ddw_w0Word_yDelta {n : ℕ} (h : n ≤ m) :
    ddw (k := k) (m := m) (w0Word n) (yDelta n) = (-1 : ℤ) ^ n.choose 2 • 1 := by
  have h1 := demw_apply_one (k := k) (m := m) (ρ := w0Word n)
    (fun j hj => by have := lt_of_mem_w0Word hj; omega)
  rw [demw_w0Word h, LinearMap.smul_apply, Module.End.mul_apply, mulPoly_apply, mul_one] at h1
  rw [← h1, smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]

/-! ### The Demazure idempotent of `NH_m` -/

variable (k m) in
/-- The Demazure idempotent `π_{w_0}` of `NH_m`, along `w0Word m`. -/
noncomputable def demIdem : Module.End k (MvPolynomial (Fin m) k) := demw (w0Word m)

theorem demIdem_mem : demIdem k m ∈ nilHecke k m := demw_mem _

/-- The normalized staircase `(-1)^{m choose 2} x^ρ`, with `∂_{w_0}` value `1`. -/
noncomputable def yDeltaSign (m : ℕ) : MvPolynomial (Fin m) k :=
  (-1 : ℤ) ^ m.choose 2 • yDelta m

theorem demIdem_eq : demIdem k m = ddw (w0Word m) * mulPoly k m (yDeltaSign m) := by
  rw [demIdem, demw_w0Word le_rfl, yDeltaSign, map_zsmul, mul_smul_comm]

theorem ddw_w0Word_yDeltaSign : ddw (k := k) (m := m) (w0Word m) (yDeltaSign m) = 1 := by
  rw [yDeltaSign, map_zsmul, ddw_w0Word_yDelta le_rfl, smul_smul, ← pow_add, ← two_mul,
    pow_mul, neg_one_sq, one_pow, one_smul]

/-- `(∂_{w_0} p)(∂_{w_0} q) = ∂_{w_0} q` when `∂_{w_0} p = 1`. -/
theorem ddw_mulPoly_mul_ddw_mulPoly {p : MvPolynomial (Fin m) k}
    (hp : ddw (w0Word m) p = 1) (q : MvPolynomial (Fin m) k) :
    ddw (w0Word m) * mulPoly k m p * (ddw (w0Word m) * mulPoly k m q) =
      ddw (w0Word m) * mulPoly k m q := by
  rw [← mul_assoc, ddw_w0Word_mul_mulPoly_mul_ddw_w0Word, hp, map_one, one_mul]

/-- `π_{w_0}` is an idempotent of `NH_m`. -/
theorem isIdempotentElem_demIdem : IsIdempotentElem (demIdem k m) := by
  rw [IsIdempotentElem, demIdem_eq]
  exact ddw_mulPoly_mul_ddw_mulPoly ddw_w0Word_yDeltaSign _

theorem demIdem_mul_idemNH' : demIdem k m * idemNH' k m = idemNH' k m := by
  rw [demIdem_eq, idemNH']
  exact ddw_mulPoly_mul_ddw_mulPoly ddw_w0Word_yDeltaSign _

theorem idemNH'_mul_demIdem : idemNH' k m * demIdem k m = demIdem k m := by
  rw [demIdem_eq, idemNH']
  exact ddw_mulPoly_mul_ddw_mulPoly ddw_w0Word_xDelta _

variable (k m) in
/-- `a = x^δ π_{w_0}`, half of the equivalence between `e_m` and `π_{w_0}`. -/
noncomputable def demA : Module.End k (MvPolynomial (Fin m) k) :=
  mulPoly k m (xDelta m) * demIdem k m

theorem demA_mem : demA k m ∈ nilHecke k m := mul_mem (mulPoly_mem _) demIdem_mem

/-- `(x^δ π_{w_0}) ∂_{w_0} = e_m`. -/
theorem demA_mul_ddw : demA k m * ddw (w0Word m) = idemNH k m := by
  rw [demA, demIdem_eq, idemNH, mul_assoc, ddw_w0Word_mul_mulPoly_mul_ddw_w0Word,
    ddw_w0Word_yDeltaSign, map_one, one_mul]

/-- `∂_{w_0} (x^δ π_{w_0}) = π_{w_0}`. -/
theorem ddw_mul_demA : ddw (w0Word m) * demA k m = demIdem k m := by
  rw [demA, demIdem_eq, ← mul_assoc, ← mul_assoc, ddw_w0Word_mul_xDelta_mul_ddw_w0Word]

end Categorification.NilHecke
