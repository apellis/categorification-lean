/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.KL2.Datum

/-!
# Cautis–Lauda's choice of scalars `Q` and the KLR polynomials `Q_ij`

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, §2.1.1 (TeX label `sec:datum`, p. 5) and §2.3 (`sec:KLR`, pp. 6–8).

## The Cartan datum

CL fix a Cartan datum with a weight lattice `X`, simple roots `α_i`, coroots `h_i` and a bilinear
form `(·,·)` on `X`, and write `⟨i, λ⟩ = ⟨h_i, λ⟩ = 2 (α_i, λ)/(α_i, α_i)`,
`d_{ij} = -⟨i, α_j⟩` and `d_i = (α_i, α_i)/2`. In this library the bilinear form on the simple
roots is Lusztig's Cartan datum `C : CartanDatum I` (`i · j = (α_i, α_j)`), so
`d_{ij} = -2 (i · j)/(i · i)`, which is `CartanDatum.dij C i j` for `i ≠ j` (a natural number; CL's
`d_{ii} = -2` is never used, and `CartanDatum.dij C i i = 0`).

## The choice of scalars (`sec:datum`, p. 5)

A choice of scalars `Q` consists of

* `t_{ij} ∈ 𝕜` for all `i, j ∈ I`, with `t_{ii} = 1`, `t_{ij} ∈ 𝕜ˣ` for `i ≠ j`, and
  `t_{ij} = t_{ji}` when `d_{ij} = 0`;
* `s_{ij}^{pq} ∈ 𝕜` for `i ≠ j`, `0 ≤ p < d_{ij}`, `0 ≤ q < d_{ji}`, with `s_{ij}^{pq} = s_{ji}^{qp}`,
  extended by `0` outside this range;
* `r_i ∈ 𝕜ˣ` for all `i ∈ I`.

`CLScalars C k` records `t` as a family of units (so `t_{ii} = 1` is the unit `1`), `s` as a
function on all of `I × I × ℕ × ℕ` (the values outside the range `p < d_{ij}`, `q < d_{ji}` are
never used, so no vanishing condition is imposed on them), and `r` as units. The condition
`t_{ij} = t_{ji}` when `d_{ij} = 0` is stated as `i · j = 0 → t_{ij} = t_{ji}`, which is the same
condition for `i ≠ j` (`CartanDatum.dij_eq_zero_iff`) and is vacuous for `i = j`.

**Misprint in the source** (`sec:datum`, p. 5, line "We set `s_{ij}^{pq} = 0` when `p, q < 0` or
`d_{ij} ≥ p` or `d_{ji} ≥ q`"): the intended condition is `p ≥ d_{ij}` or `q ≥ d_{ji}`, the
complement of the range `0 ≤ p < d_{ij}`, `0 ≤ q < d_{ji}` on which `s` is defined. We use the
intended reading.

The dual scalars `Q'` (`sec:datum`, p. 5, last display): `r'_i = -r_i`, `t'_{ij} = t_{ji}^{-1}`
(`i ≠ j`; also for `i = j` since `t_{ii} = 1`), `s'_{ij}^{pq} = t_{ij}^{-1} t_{ji}^{-1} s_{ij}^{pq}`
(`CLScalars.dual`). It is an involution (`CLScalars.dual_dual`).

## The KLR polynomials (`sec:KLR`, eq. `eq_r2_ij-gen` and `eq_pq`, p. 7)

For `i ≠ j` the double crossing on `E_i E_j` is `t_{ij}` if `(α_i, α_j) = 0`, and
`t_{ij} x_i^{d_{ij}} + t_{ji} x_j^{d_{ji}} + ∑_{p,q} s_{ij}^{pq} x_i^p x_j^q` otherwise, where the
sum is over the `p, q` with `(α_i, α_i) p + (α_j, α_j) q = -2 (α_i, α_j)` (eq. `eq_pq`), i.e.
over the pairs of the same weighted degree as `x_i^{d_{ij}}`. We record the right-hand side as the
polynomial `qCL S i j ∈ k[u, v]` (`u = x_i`, `v = x_j`), with the sum over `0 ≤ p < d_{ij}`,
`0 ≤ q < d_{ji}` satisfying `eq_pq` (the pairs with `p ≥ d_{ij}` or `q ≥ d_{ji}` satisfying `eq_pq`
are `(d_{ij}, 0)` and `(0, d_{ji})`, where `s = 0` by convention). Then

* `rename_swap_qCL`: `Q_{ij}(u, v) = Q_{ji}(v, u)`, as required of the polynomials of a KLR
  algebra (this uses `s_{ij}^{pq} = s_{ji}^{qp}` and, when `i · j = 0`, `t_{ij} = t_{ji}`);
* `qCL_kl`: for the KL scalars (`t = 1`, `s = 0`, `r = 1`; `CLScalars.kl`) `Q` is the KL II
  polynomial `u^{d_{ij}} + v^{d_{ji}}` (`KLR.klQ2`), as stated in CL §1.1 ("`U(g)` from [KL3]
  corresponds to `t_{ij} = t_{ji} = 1` and `s = 0`");
* `qCL_dual`: `Q'_{ij} = t_{ij}^{-1} t_{ji}^{-1} Q_{ij}`;
* `qCL_isWeightedHomogeneous`, `qbar_qCL_isWeightedHomogeneous`: `Q_{ij}` is weighted
  homogeneous of degree `-2 (i · j)` for the weights `i · i`, `j · j` (this is what `eq_pq`
  achieves), and its divided difference `Q̄_{ij}` (`KLR.qbar`) is weighted homogeneous of degree
  `-2 (i · j) - i · i`.
* `qbar_qCL`: the divided difference `Q̄_{ij}(x₀, x₁, x₂)` is the right-hand side of CL's braid
  relation `eq_r3_hard-gen`: `t_{ij} ∑_{ℓ₁ + ℓ₂ = d_{ij} - 1} x₀^{ℓ₁} x₂^{ℓ₂} +
  ∑_{p,q} s_{ij}^{pq} ∑_{ℓ₁ + ℓ₂ = p - 1} x₀^{ℓ₁} x₁^q x₂^{ℓ₂}`.
-/

noncomputable section

namespace Categorification.KL3.Diagram.CL

open QuantumGroup MvPolynomial

variable {I : Type*} (C : CartanDatum I) (k : Type*) [CommRing k]

/-- **Cautis–Lauda's choice of scalars** (arXiv:1111.1431v3, §2.1.1, p. 5): `t_{ij} ∈ kˣ` with
`t_{ii} = 1` and `t_{ij} = t_{ji}` when `i · j = 0`; `s_{ij}^{pq} ∈ k` with `s_{ij}^{pq} = s_{ji}^{qp}`
(only the values with `p < d_{ij}`, `q < d_{ji}` are used); `r_i ∈ kˣ`. -/
@[ext]
structure CLScalars where
  /-- `t_{ij}`. -/
  t : I → I → kˣ
  /-- `s_{ij}^{pq}`. -/
  s : I → I → ℕ → ℕ → k
  /-- `r_i`. -/
  r : I → kˣ
  t_self : ∀ i, t i i = 1
  t_symm : ∀ i j, C.dot i j = 0 → t i j = t j i
  s_symm : ∀ i j p q, s i j p q = s j i q p

namespace CLScalars

variable {C k}

/-- The scalars of Khovanov–Lauda III: `t = 1`, `s = 0`, `r = 1` (CL §1.1, after
Definition 1.1). -/
def kl : CLScalars C k where
  t _ _ := 1
  s _ _ _ _ := 0
  r _ := 1
  t_self _ := rfl
  t_symm _ _ _ := rfl
  s_symm _ _ _ _ := rfl

@[simp] theorem kl_t (i j : I) : (kl : CLScalars C k).t i j = 1 := rfl
@[simp] theorem kl_s (i j : I) (p q : ℕ) : (kl : CLScalars C k).s i j p q = 0 := rfl
@[simp] theorem kl_r (i : I) : (kl : CLScalars C k).r i = 1 := rfl

/-- **The dual scalars `Q'`** (CL §2.1.1, p. 5, last display): `r'_i = -r_i`,
`t'_{ij} = t_{ji}^{-1}`, `s'_{ij}^{pq} = t_{ij}^{-1} t_{ji}^{-1} s_{ij}^{pq}`. -/
def dual (S : CLScalars C k) : CLScalars C k where
  t i j := (S.t j i)⁻¹
  s i j p q := (((S.t i j)⁻¹ * (S.t j i)⁻¹ : kˣ) : k) * S.s i j p q
  r i := -S.r i
  t_self i := by rw [S.t_self, inv_one]
  t_symm i j h := by rw [S.t_symm i j h]
  s_symm i j p q := by rw [S.s_symm i j p q, mul_comm ((S.t i j)⁻¹)]

@[simp] theorem dual_t (S : CLScalars C k) (i j : I) : S.dual.t i j = (S.t j i)⁻¹ := rfl
@[simp] theorem dual_s (S : CLScalars C k) (i j : I) (p q : ℕ) :
    S.dual.s i j p q = (((S.t i j)⁻¹ * (S.t j i)⁻¹ : kˣ) : k) * S.s i j p q := rfl
@[simp] theorem dual_r (S : CLScalars C k) (i : I) : S.dual.r i = -S.r i := rfl

/-- Taking dual scalars is an involution. -/
theorem dual_dual (S : CLScalars C k) : S.dual.dual = S := by
  refine CLScalars.ext (funext fun i => funext fun j => ?_)
    (funext fun i => funext fun j => funext fun p => funext fun q => ?_)
    (funext fun i => ?_)
  · simp
  · simp only [dual_s, dual_t, inv_inv, ← mul_assoc, ← Units.val_mul]
    rw [show S.t j i * S.t i j * (S.t i j)⁻¹ * (S.t j i)⁻¹ = 1 by
      rw [mul_inv_cancel_right, mul_inv_cancel], Units.val_one, one_mul]
  · simp

/-- The KL scalars are self-dual up to the sign of `r`: `kl.dual` has `r = -1`. -/
theorem dual_kl_r (i : I) : (kl : CLScalars C k).dual.r i = -1 := by simp

end CLScalars

/-! ## The KLR polynomials `Q_ij` -/

/-- **CL's KLR polynomials** (arXiv:1111.1431v3, eq. `eq_r2_ij-gen` with `eq_pq`, p. 7): for
`i ≠ j`, `Q_{ij}(u, v) = t_{ij}` if `i · j = 0` and otherwise
`Q_{ij}(u, v) = t_{ij} u^{d_{ij}} + t_{ji} v^{d_{ji}} + ∑ s_{ij}^{pq} u^p v^q`, the sum over
`0 ≤ p < d_{ij}`, `0 ≤ q < d_{ji}` with `(i·i) p + (j·j) q = -2 (i·j)`. (The value on the diagonal
is never used.) -/
def qCL {C : CartanDatum I} {k : Type*} [CommRing k] (S : CLScalars C k) (i j : I) : MvPolynomial (Fin 2) k :=
  if C.dot i j = 0 then MvPolynomial.C (S.t i j : k)
  else MvPolynomial.C (S.t i j : k) * X 0 ^ C.dij i j + MvPolynomial.C (S.t j i : k) * X 1 ^ C.dij j i +
    ∑ p ∈ Finset.range (C.dij i j), ∑ q ∈ Finset.range (C.dij j i),
      if C.dot i i * p + C.dot j j * q = -2 * C.dot i j then
        MvPolynomial.C (S.s i j p q) * X 0 ^ p * X 1 ^ q else 0

variable {C k}

theorem qCL_of_dot_eq_zero (S : CLScalars C k) {i j : I} (h : C.dot i j = 0) :
    qCL S i j = MvPolynomial.C (S.t i j : k) := if_pos h

theorem qCL_of_dot_ne_zero (S : CLScalars C k) {i j : I} (h : C.dot i j ≠ 0) :
    qCL S i j = MvPolynomial.C (S.t i j : k) * X 0 ^ C.dij i j +
      MvPolynomial.C (S.t j i : k) * X 1 ^ C.dij j i +
      ∑ p ∈ Finset.range (C.dij i j), ∑ q ∈ Finset.range (C.dij j i),
        if C.dot i i * p + C.dot j j * q = -2 * C.dot i j then
          MvPolynomial.C (S.s i j p q) * X 0 ^ p * X 1 ^ q else 0 := if_neg h

/-- **`Q_{ij}(u, v) = Q_{ji}(v, u)`**: the symmetry required of the polynomials of a KLR
algebra. It uses `s_{ij}^{pq} = s_{ji}^{qp}` and, for `i · j = 0`, `t_{ij} = t_{ji}`. -/
theorem rename_swap_qCL (S : CLScalars C k) (i j : I) :
    rename ![(1 : Fin 2), 0] (qCL S j i) = qCL S i j := by
  unfold qCL
  rw [C.symm j i]
  split_ifs with h
  · rw [rename_C, S.t_symm i j h]
  · simp only [map_add, map_mul, map_pow, rename_C, rename_X, map_sum, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons]
    rw [Finset.sum_comm, add_comm (MvPolynomial.C _ * _)]
    congr 1
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => ?_
    rw [apply_ite (rename ![(1 : Fin 2), 0]), map_zero, map_mul, map_mul, map_pow, map_pow,
      rename_C, rename_X, rename_X, add_comm (C.dot j j * (p : ℤ))]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    split_ifs with hpq
    · rw [S.s_symm j i p q]; ring
    · rfl

/-- For the KL scalars, `Q` is the family of KL II polynomials `u^{d_{ij}} + v^{d_{ji}}`
(`1` if `i · j = 0`). -/
theorem qCL_kl : qCL (CLScalars.kl : CLScalars C k) = KLR.klQ2 k C := by
  funext i j
  unfold qCL KLR.klQ2
  split_ifs with h <;> simp

/-- **`Q'_{ij} = t_{ij}^{-1} t_{ji}^{-1} Q_{ij}`**: the polynomials of the dual scalars. -/
theorem qCL_dual (S : CLScalars C k) (i j : I) :
    qCL S.dual i j = MvPolynomial.C ((((S.t i j)⁻¹ * (S.t j i)⁻¹ : kˣ)) : k) * qCL S i j := by
  unfold qCL
  simp only [CLScalars.dual_t, CLScalars.dual_s]
  have h₁ : (((S.t i j)⁻¹ * (S.t j i)⁻¹ : kˣ) : k) * (S.t i j : k) = ((S.t j i)⁻¹ : kˣ) := by
    rw [← Units.val_mul]; congr 1; rw [mul_comm, mul_inv_cancel_left]
  have h₂ : (((S.t i j)⁻¹ * (S.t j i)⁻¹ : kˣ) : k) * (S.t j i : k) = ((S.t i j)⁻¹ : kˣ) := by
    rw [← Units.val_mul]; congr 1; exact inv_mul_cancel_right _ _
  split_ifs with h
  · rw [← map_mul, h₁]
  · rw [mul_add, mul_add, ← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, h₁, h₂, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    split_ifs
    · rw [map_mul]; ring
    · rw [mul_zero]

/-! ## Homogeneity -/

/-- `Q_{ij}` is weighted homogeneous of degree `-2 (i · j)` for the weights `i · i`, `j · j`
(this is the purpose of the condition `eq_pq` on the sum). -/
theorem qCL_isWeightedHomogeneous (S : CLScalars C k) {i j : I} (h : i ≠ j) :
    (qCL S i j).IsWeightedHomogeneous ![C.dot i i, C.dot j j] (-2 * C.dot i j) := by
  unfold qCL
  split_ifs with h0
  · rw [h0, mul_zero]; exact isWeightedHomogeneous_C _ _
  · have h₁ := C.dij_mul h
    have h₂ := C.dij_mul (Ne.symm h)
    refine IsWeightedHomogeneous.add (IsWeightedHomogeneous.add ?_ ?_) ?_
    · convert (isWeightedHomogeneous_C ![C.dot i i, C.dot j j] (S.t i j : k)).mul
        ((isWeightedHomogeneous_X k ![C.dot i i, C.dot j j] 0).pow (C.dij i j)) using 1
      simp [h₁]
    · convert (isWeightedHomogeneous_C ![C.dot i i, C.dot j j] (S.t j i : k)).mul
        ((isWeightedHomogeneous_X k ![C.dot i i, C.dot j j] 1).pow (C.dij j i)) using 1
      simp [h₂, C.symm j i]
    · refine IsWeightedHomogeneous.sum _ _ _ fun p _ =>
        IsWeightedHomogeneous.sum _ _ _ fun q _ => ?_
      split_ifs with hpq
      · convert ((isWeightedHomogeneous_C ![C.dot i i, C.dot j j] (S.s i j p q)).mul
          ((isWeightedHomogeneous_X k ![C.dot i i, C.dot j j] 0).pow p)).mul
          ((isWeightedHomogeneous_X k ![C.dot i i, C.dot j j] 1).pow q) using 1
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, smul_eq_mul,
          nsmul_eq_mul, zero_add]
        linear_combination -hpq
      · exact isWeightedHomogeneous_zero _ _ _

/-- The divided difference `Q̄` (`KLR.qbar`) of a weighted homogeneous polynomial of degree `e`
for the weights `w₀, w₁` is weighted homogeneous of degree `e - w₀` for the weights
`w₀, w₁, w₀`. -/
theorem qbar_isWeightedHomogeneous {Q : MvPolynomial (Fin 2) k} {w₀ w₁ e : ℤ}
    (hQ : Q.IsWeightedHomogeneous ![w₀, w₁] e) :
    (KLR.qbar Q).IsWeightedHomogeneous ![w₀, w₁, w₀] (e - w₀) := by
  unfold KLR.qbar
  rw [Finsupp.sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun s hs => ?_
  have hw : Finsupp.weight ![w₀, w₁] s = e := hQ (MvPolynomial.mem_support_iff.mp hs)
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two] at hw
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, smul_eq_mul] at hw
  rcases Nat.eq_zero_or_pos (s 0) with h0 | hpos
  · rw [h0, Finset.range_zero, Finset.sum_empty, mul_zero]
    exact isWeightedHomogeneous_zero _ _ _
  · have hsum : (∑ t ∈ Finset.range (s 0), X 0 ^ t * X 2 ^ (s 0 - 1 - t) :
        MvPolynomial (Fin 3) k).IsWeightedHomogeneous ![w₀, w₁, w₀] ((s 0 - 1 : ℕ) * w₀) := by
      refine IsWeightedHomogeneous.sum _ _ _ fun t ht => ?_
      have ht' := Finset.mem_range.mp ht
      convert ((isWeightedHomogeneous_X k ![w₀, w₁, w₀] 0).pow t).mul
        ((isWeightedHomogeneous_X k ![w₀, w₁, w₀] 2).pow (s 0 - 1 - t)) using 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
        smul_eq_mul, nsmul_eq_mul]
      push_cast [Nat.cast_sub (show t ≤ s 0 - 1 by omega), Nat.cast_sub (show 1 ≤ s 0 by omega)]
      ring
    convert ((isWeightedHomogeneous_C ![w₀, w₁, w₀] (Q.coeff s)).mul
      ((isWeightedHomogeneous_X k ![w₀, w₁, w₀] 1).pow (s 1))).mul hsum using 1
    simp only [Matrix.cons_val_one, Matrix.head_cons, smul_eq_mul, nsmul_eq_mul, zero_add]
    push_cast [Nat.cast_sub (show 1 ≤ s 0 by omega)]
    linear_combination -hw

/-- `Q̄_{ij}` is weighted homogeneous of degree `-2 (i · j) - i · i` for the weights
`i · i`, `j · j`, `i · i` (the degrees needed for the homogeneity of the braid relation). -/
theorem qbar_qCL_isWeightedHomogeneous (S : CLScalars C k) {i j : I} (h : i ≠ j) :
    (KLR.qbar (qCL S i j)).IsWeightedHomogeneous ![C.dot i i, C.dot j j, C.dot i i]
      (-2 * C.dot i j - C.dot i i) :=
  qbar_isWeightedHomogeneous (qCL_isWeightedHomogeneous S h)

/-! ## The divided difference `Q̄_ij` in CL's form -/

theorem qbar_zero : KLR.qbar (0 : MvPolynomial (Fin 2) k) = 0 := by
  unfold KLR.qbar; exact Finsupp.sum_zero_index

theorem qbar_sum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin 2) k) :
    KLR.qbar (∑ x ∈ s, f x) = ∑ x ∈ s, KLR.qbar (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [qbar_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, KLR.qbar_add, ih]

/-- `Q̄` of `c u^p v^q` is `c v^q ∑_{t < p} x₀^t x₂^{p-1-t}`. -/
theorem qbar_C_mul_X_pow_mul_X_pow (c : k) (p q : ℕ) :
    KLR.qbar (MvPolynomial.C c * X 0 ^ p * X 1 ^ q : MvPolynomial (Fin 2) k) =
      MvPolynomial.C c * X 1 ^ q * ∑ t ∈ Finset.range p, X 0 ^ t * X 2 ^ (p - 1 - t) := by
  have : (MvPolynomial.C c * X 0 ^ p * X 1 ^ q : MvPolynomial (Fin 2) k) =
      monomial (Finsupp.single 0 p + Finsupp.single 1 q) c := by
    rw [X_pow_eq_monomial, X_pow_eq_monomial, mul_assoc, monomial_mul, C_mul_monomial, mul_one,
      mul_one]
  rw [this, KLR.qbar_monomial]
  simp

/-- **CL's braid correction term** (arXiv:1111.1431v3, eq. `eq_r3_hard-gen`, pp. 7–8, right-hand
side): for `i · j ≠ 0`, the divided difference of `Q_{ij}` is
`t_{ij} ∑_{ℓ₁ + ℓ₂ = d_{ij} - 1} x₀^{ℓ₁} x₂^{ℓ₂} + ∑_{p,q} s_{ij}^{pq} x₁^q ∑_{ℓ₁ + ℓ₂ = p - 1}
x₀^{ℓ₁} x₂^{ℓ₂}` (with `x₀`, `x₁`, `x₂` the dots on the strands `i`, `j`, `i` of `E_i E_j E_i`;
the `p, q` summation as in `eq_pq`). The inner sum over `ℓ₁ + ℓ₂ = p - 1` is written with the
truncated subtraction `p - 1`; this is harmless because the terms with `p = 0` never satisfy
`eq_pq` within the range `q < d_{ji}`. -/
theorem qbar_qCL (S : CLScalars C k) {i j : I} (hij : i ≠ j) (h : C.dot i j ≠ 0) :
    KLR.qbar (qCL S i j) =
      MvPolynomial.C (S.t i j : k) *
          ∑ l ∈ Finset.antidiagonal (C.dij i j - 1), X 0 ^ l.1 * X 2 ^ l.2 +
        ∑ p ∈ Finset.range (C.dij i j), ∑ q ∈ Finset.range (C.dij j i),
          if C.dot i i * p + C.dot j j * q = -2 * C.dot i j then
            MvPolynomial.C (S.s i j p q) * X 1 ^ q *
              ∑ l ∈ Finset.antidiagonal (p - 1), X 0 ^ l.1 * X 2 ^ l.2
          else 0 := by
  have hd : 0 < C.dij i j := C.dij_pos hij h
  rw [qCL_of_dot_ne_zero S h, KLR.qbar_add, KLR.qbar_add, qbar_sum]
  have e1 : (MvPolynomial.C (S.t i j : k) * X 0 ^ C.dij i j : MvPolynomial (Fin 2) k) =
      MvPolynomial.C (S.t i j : k) * X 0 ^ C.dij i j * X 1 ^ 0 := by rw [pow_zero, mul_one]
  have e2 : (MvPolynomial.C (S.t j i : k) * X 1 ^ C.dij j i : MvPolynomial (Fin 2) k) =
      MvPolynomial.C (S.t j i : k) * X 0 ^ 0 * X 1 ^ C.dij j i := by rw [pow_zero, mul_one]
  rw [e1, e2, qbar_C_mul_X_pow_mul_X_pow, qbar_C_mul_X_pow_mul_X_pow]
  simp only [Finset.range_zero, Finset.sum_empty, mul_zero, add_zero, pow_zero, mul_one]
  congr 1
  · simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    rw [Nat.succ_eq_add_one, Nat.sub_add_cancel hd]
  · refine Finset.sum_congr rfl fun p _ => ?_
    rw [qbar_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    split_ifs with hpq
    · rw [qbar_C_mul_X_pow_mul_X_pow]
      have hp : 0 < p := by
        rcases Nat.eq_zero_or_pos p with rfl | hp
        · exfalso
          have h₂ := C.dij_mul (Ne.symm hij)
          rw [C.symm j i] at h₂
          have hq' := Finset.mem_range.mp hq
          have hjj := C.dot_self_pos j
          simp only [Nat.cast_zero, mul_zero, zero_add] at hpq
          have := hpq.trans h₂.symm
          rw [mul_comm] at this
          have := mul_right_cancel₀ hjj.ne' this
          omega
        · exact hp
      simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      rw [Nat.succ_eq_add_one, Nat.sub_add_cancel hp]
    · rw [qbar_zero]

end Categorification.KL3.Diagram.CL
