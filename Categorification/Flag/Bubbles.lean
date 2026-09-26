/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.Adjunction

/-!
# Bubbles in the flag 2-category

Khovanov–Lauda III, arXiv:0807.3250v1: the images under `Γ_N` (Definition 6.1) of the dotted
bubbles of `U` (Definition 3.1), and the bubble relations of Definition 3.1 (positivity and
normalization, eq. (3.4); the infinite Grassmannian relation, eq. (3.7), TeX label
`eq_infinite_Grass`) in the flag 2-category.

A dotted bubble in the region of weight `λ = λ(k)` is the composite `cap ∘ (dots) ∘ cup`:

* `bubbleFE α = cap_FE((ξ^α ⊗ 1) · cup_FE(1)) ∈ H_k` (the cup and the cap of Definition 6.1,
  eqs. (6.2), (6.4), through `F_i E_i 1_λ`);
* `bubbleEF α = cap_EF((ξ^α ⊗ 1) · cup_EF(1))` (eqs. (6.3), (6.5), through `E_i F_i 1_λ`; in the
  Borel model the weight is that of `+_i k'`, `k'` the labelling `lab`, and the value lies in
  `BorelRing k (moveLab lab v₀ j')`).

By Lemma 5.4 (iii), (iv) and `capFE_slide`, `capEF_slide` it does not matter on which strand the
dots are placed.

## Main results

* `bubbleFE_eq` : `bubbleFE α = (-1)^n ∑_{a + b = n} x(k)_{i,a} x̄(k)_{i+1,b}` with
  `n = α + λ_i + 1` (in the Borel model `n = α + d + 1 - b`, `d = k_i - k_{i-1}`,
  `b = k_{i+1} - k_i`), and `bubbleFE α = 0` if `α + λ_i + 1 < 0`;
* `bubbleEF_eq` : `bubbleEF α = (-1)^n ∑_{a + b = n} x_{i+1,a} x̄_{i,b}` with `n = α - λ_i + 1`,
  and `0` if `α - λ_i + 1 < 0`;
* `bubbleFEH_eq`, `bubbleEFH_eq` : the same in the presentation (5.2) of `H_k` (`Flag.H`), for a
  composition `d` (`λ_i = d_i - d_{i+1}`);
* `bubbleFE_neg`, `bubbleFE_zero`, `bubbleEF_neg`, `bubbleEF_zero` : bubbles of negative degree
  vanish and bubbles of degree `0` equal `1` (the bubble axioms (3.4) of Definition 3.1);
* `grassmannian`, `grassmannianH` : the two families `Φ_n = (-1)^n ∑_{a+b=n} x_{i,a} x̄_{i+1,b}`
  and `Ψ_n = (-1)^n ∑_{a+b=n} x_{i+1,a} x̄_{i,b}` satisfy `∑_{a+b=n} Φ_a Ψ_b = δ_{n,0}`
  (generating functions `Φ(t) Ψ(t) = x_i(-t) x̄_i(-t) x_{i+1}(-t) x̄_{i+1}(-t) = 1` by eq. (5.7)).
  Since `bubbleFE α = Φ_{α+λ_i+1}` and `bubbleEF α = Ψ_{α-λ_i+1}`, this is the image of the
  infinite Grassmannian relation (3.7) for real bubbles; in `U` the fake bubbles are defined by
  (3.7), so any 2-functor must send them to the `Φ_n`, `Ψ_n` with small `n` (the 2-functor
  itself is not constructed here).

In KL III's grading `deg x_{j,α} = 2α`, `bubbleFE α` has degree `2(α + λ_i + 1)` and
`bubbleEF α` has degree `2(α - λ_i + 1)`, the degrees of the two orientations of dotted bubbles
in Definition 3.1 (gradings are not formalized here).
-/

noncomputable section

namespace Categorification.Flag

open MvPolynomial TensorProduct
open Finset (univ range antidiagonal)

/-! ### A convolution identity -/

section Conv

variable {A : Type*} [CommRing A]

/-- `∑_{f ≤ d} (-1)^{d-f} x_{d-f} τ(α + f)`, with `τ(c) = (-1)^{c+1-b} y_{c+1-b}` (`0` for
`c + 1 < b`) and `x_β = 0` for `β > d`, equals `(-1)^n ∑_{a + b = n} x_a y_b`,
`n = α + d + 1 - b` (and `0` if `α + d + 1 < b`). -/
theorem conv_trace_sum (x y : ℕ → A) (b d α : ℕ) (hx : ∀ β, d < β → x β = 0) :
    ∑ f ∈ range (d + 1), (-1) ^ (d - f) * x (d - f) *
        (if b ≤ α + f + 1 then (-1) ^ (α + f + 1 - b) * y (α + f + 1 - b) else 0) =
      if b ≤ α + d + 1 then
        (-1) ^ (α + d + 1 - b) * ∑ p ∈ antidiagonal (α + d + 1 - b), x p.1 * y p.2
      else 0 := by
  by_cases hb : b ≤ α + d + 1
  · rw [if_pos hb]
    set n := α + d + 1 - b with hn
    rw [← Finset.sum_range_reflect]
    have hterm : ∀ β ∈ range (d + 1), (-1) ^ (d - (d + 1 - 1 - β)) * x (d - (d + 1 - 1 - β)) *
        (if b ≤ α + (d + 1 - 1 - β) + 1 then
          (-1) ^ (α + (d + 1 - 1 - β) + 1 - b) * y (α + (d + 1 - 1 - β) + 1 - b) else 0) =
        (-1) ^ n * (if β ≤ n then x β * y (n - β) else 0) := by
      intro β hβ
      have hβ' : β ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hβ)
      rw [Nat.add_sub_cancel, show d - (d - β) = β by omega]
      by_cases h : β ≤ n
      · rw [if_pos (by omega), if_pos h, show α + (d - β) + 1 - b = n - β by omega]
        have := neg_one_pow_mul_neg_one_pow'' (A := A) h
        linear_combination (x β * y (n - β)) * this
      · rw [if_neg (by omega), if_neg h, mul_zero, mul_zero]
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    congr 1
    set G : ℕ → A := fun β => if β ≤ n then x β * y (n - β) else 0 with hG
    have h1 : ∑ β ∈ range (d + 1), G β = ∑ β ∈ range (n + d + 1), G β :=
      Finset.sum_subset (Finset.range_subset.2 (by omega)) fun β _ hβ => by
        simp only [Finset.mem_range, not_lt] at hβ
        simp only [hG, hx β (by omega), zero_mul, ite_self]
    have h2 : ∑ p ∈ antidiagonal n, x p.1 * y p.2 = ∑ β ∈ range (n + d + 1), G β := by
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        ← Finset.sum_subset (Finset.range_subset.2 (show n + 1 ≤ n + d + 1 by omega))
          fun β _ hβ => by
            simp only [Finset.mem_range, not_lt] at hβ
            simp only [hG, if_neg (show ¬ β ≤ n by omega)]]
      exact Finset.sum_congr rfl fun β hβ => by
        simp only [hG, if_pos (Nat.lt_succ_iff.1 (Finset.mem_range.1 hβ))]
    rw [h1, h2]
  · rw [if_neg hb]
    refine Finset.sum_eq_zero fun f hf => ?_
    have : f ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hf)
    rw [if_neg (by omega), mul_zero]

end Conv

/-! ### The infinite Grassmannian relation -/

section GrassmannianAbstract

variable {A : Type*} [CommRing A]

/-- `Φ_n = (-1)^n ∑_{a + b = n} x_a y_b`. -/
def bubbleSeq (x y : ℕ → A) (n : ℕ) : A := (-1) ^ n * ∑ p ∈ antidiagonal n, x p.1 * y p.2

/-- If `x x̄ = 1` and `x' x̄' = 1` as power series, then `Φ Ψ = 1` for `Φ = (-1)^n (x x̄')_n` and
`Ψ = (-1)^n (x' x̄)_n`. -/
theorem bubbleSeq_mul (x xb x' xb' : ℕ → A)
    (h : ∀ α, ∑ f ∈ range (α + 1), x f * xb (α - f) = if α = 0 then 1 else 0)
    (h' : ∀ α, ∑ f ∈ range (α + 1), x' f * xb' (α - f) = if α = 0 then 1 else 0) (n : ℕ) :
    ∑ p ∈ antidiagonal n, bubbleSeq x xb' p.1 * bubbleSeq x' xb p.2 = if n = 0 then 1 else 0 := by
  have hXX : ∀ (u v : ℕ → A), (∀ α, ∑ f ∈ range (α + 1), u f * v (α - f) =
      if α = 0 then 1 else 0) → PowerSeries.mk u * PowerSeries.mk v = 1 := fun u v huv => by
    ext α
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_one,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [PowerSeries.coeff_mk]
    exact huv α
  have hΦ : ∀ (u v : ℕ → A) a, bubbleSeq u v a =
      PowerSeries.coeff A a (PowerSeries.rescale (-1) (PowerSeries.mk u * PowerSeries.mk v)) :=
    fun u v a => by
      rw [PowerSeries.coeff_rescale, PowerSeries.coeff_mul]
      simp only [PowerSeries.coeff_mk, bubbleSeq]
  simp only [hΦ]
  rw [← PowerSeries.coeff_mul, ← map_mul,
    show PowerSeries.mk x * PowerSeries.mk xb' * (PowerSeries.mk x' * PowerSeries.mk xb) =
      (PowerSeries.mk x * PowerSeries.mk xb) * (PowerSeries.mk x' * PowerSeries.mk xb') by ring,
    hXX x xb h, hXX x' xb' h', mul_one, map_one, PowerSeries.coeff_one]

end GrassmannianAbstract

section Grassmannian

variable {k : Type*} [Field k] {V : Type*} [Fintype V] [DecidableEq V] {J : Type*}
  [DecidableEq J]

variable (k) in
/-- `Φ_n = (-1)^n ∑_{a + b = n} x_{j₁,a} x̄_{j₂,b}` (the image of a bubble with `n` in KL III's
bubble indexing). -/
def bubbleSeries (lab : V → J) (j₁ j₂ : J) (n : ℕ) : BorelRing k lab :=
  (-1) ^ n * ∑ p ∈ antidiagonal n, xB k lab j₁ p.1 * xbarB k lab j₂ p.2

/-- **The infinite Grassmannian relation in the flag 2-category**:
`∑_{a + b = n} Φ_a Ψ_b = δ_{n,0}` for `Φ = bubbleSeries j₁ j₂`, `Ψ = bubbleSeries j₂ j₁`
(generating functions: `Φ(t) = x_{j₁}(-t) x̄_{j₂}(-t)`, `Ψ(t) = x_{j₂}(-t) x̄_{j₁}(-t)`, and
`x_j(t) x̄_j(t) = 1` is KL III eq. (5.7)). -/
theorem grassmannian (lab : V → J) (j₁ j₂ : J) (n : ℕ) :
    ∑ p ∈ antidiagonal n, bubbleSeries k lab j₁ j₂ p.1 * bubbleSeries k lab j₂ j₁ p.2 =
      if n = 0 then 1 else 0 :=
  bubbleSeq_mul _ _ _ _ (sum_xB_mul_xbarB j₁) (sum_xB_mul_xbarB j₂) n

end Grassmannian

/-! ### The dotted bubbles -/

section Bubbles

variable {k : Type*} [Field k] {V : Type*} [Fintype V] [DecidableEq V] {J : Type*}
  [Fintype J] [DecidableEq J]

section FE

attribute [local instance] midAlgebra

variable (k) in
/-- **The bubble through `F_i E_i 1_λ`** with `α` dots: `cap_FE((ξ^α ⊗ 1) · cup_FE(1)) ∈ H_k`. -/
def bubbleFE (lab : V → J) (v₀ : V) (j' : J) (α : ℕ) : BorelRing k lab :=
  capFE k lab v₀ j' (((xi k lab v₀ ^ α) ⊗ₜ 1) * cupEltKL k lab v₀ j')

omit [Fintype J] in
theorem dBlock_eq (lab : V → J) (v₀ : V) (j' : J) (hj : j' ≠ lab v₀) :
    dBlock lab v₀ j' = (labSet lab (· = j')).card := by
  rw [dBlock, card_split_some, if_neg hj, Nat.sub_zero]

/-- **The FE-bubble in closed form**: `bubbleFE α = (-1)^n ∑_{a + b = n} x(k)_{i,a} x̄(k)_{i+1,b}`,
`n = α + d + 1 - b` (`d` the size of block `i` = `j'`, `b` the size of block `i + 1` = the block of
`v₀`), and `0` if `α + d + 1 < b`. -/
theorem bubbleFE_eq (lab : V → J) (v₀ : V) (j' : J) (hj : j' ≠ lab v₀) (α : ℕ) :
    bubbleFE k lab v₀ j' α =
      if blockCard lab v₀ ≤ α + dBlock lab v₀ j' + 1 then
        bubbleSeries k lab j' (lab v₀) (α + dBlock lab v₀ j' + 1 - blockCard lab v₀)
      else 0 := by
  rw [bubbleFE, cupEltKL, Finset.mul_sum, map_sum]
  have hterm : ∀ f ∈ range (dBlock lab v₀ j' + 1),
      capFE k lab v₀ j' (((xi k lab v₀ ^ α) ⊗ₜ 1) * ((-1) ^ (dBlock lab v₀ j' - f) *
        ((xi k lab v₀ ^ f) ⊗ₜ xs (k := k) (lab := lab) (v₀ := v₀) j' (dBlock lab v₀ j' - f)))) =
      (-1) ^ (dBlock lab v₀ j' - f) * xB k lab j' (dBlock lab v₀ j' - f) *
        (if blockCard lab v₀ ≤ α + f + 1 then (-1) ^ (α + f + 1 - blockCard lab v₀) *
          xbarB k lab (lab v₀) (α + f + 1 - blockCard lab v₀) else 0) := by
    intro f _
    have hsign : ((-1 : CupRing k lab v₀ j') ^ (dBlock lab v₀ j' - f)) =
        (pR k lab v₀ ((-1) ^ (dBlock lab v₀ j' - f)) ⊗ₜ 1) := by
      rw [map_pow, map_neg, map_one, neg_one_pow_tmul_one]
    rw [mul_left_comm, hsign, capFE_left, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      capFE_tmul, ← pow_add, xs, ← pR_xB k j' hj, mul_comm (xi k lab v₀ ^ (α + f)), trR_pR_mul,
      trR_xi_pow]
    ring
  rw [Finset.sum_congr rfl hterm, conv_trace_sum (xB k lab j') (xbarB k lab (lab v₀))
    (blockCard lab v₀) (dBlock lab v₀ j') α (fun β hβ => xB_eq_zero (by
      rw [← dBlock_eq lab v₀ j' hj]; exact hβ))]
  rfl

end FE

section EF

attribute [local instance] rightAlgebra

variable (k) in
/-- **The bubble through `E_i F_i 1_λ`** (`λ` the weight of `+_i k'`, `k'` the labelling `lab`)
with `α` dots: `cap_EF((ξ^α ⊗ 1) · cup_EF(1)) ∈ H_{+_i k'}`. -/
def bubbleEF (lab : V → J) (v₀ : V) (j' : J) (α : ℕ) : BorelRing k (moveLab lab v₀ j') :=
  capEF k lab v₀ j' (((xi k lab v₀ ^ α) ⊗ₜ 1) * cupEltRKL k lab v₀)

omit [Fintype J] in
theorem dBlockR_eq (lab : V → J) (v₀ : V) (j' : J) (hj : j' ≠ lab v₀) :
    dBlockR lab v₀ = (labSet (moveLab lab v₀ j') (· = lab v₀)).card := by
  rw [dBlockR, labSet_move_eq, if_neg (Ne.symm hj)]

/-- **The EF-bubble in closed form**: `bubbleEF α = (-1)^n ∑_{a + b = n} x_{i+1,a} x̄_{i,b}` in
`H_{+_i k'}`, `n = α + d + 1 - b'` (`d` the size of block `i + 1` of `+_i k'`, `b'` the size of
block `i` of `+_i k'`), and `0` if `α + d + 1 < b'`. -/
theorem bubbleEF_eq (lab : V → J) (v₀ : V) (j' : J) (hj : j' ≠ lab v₀) (α : ℕ) :
    bubbleEF k lab v₀ j' α =
      if blockCardL lab v₀ j' ≤ α + dBlockR lab v₀ + 1 then
        bubbleSeries k (moveLab lab v₀ j') (lab v₀) j'
          (α + dBlockR lab v₀ + 1 - blockCardL lab v₀ j')
      else 0 := by
  rw [bubbleEF, cupEltRKL, Finset.mul_sum, map_sum]
  have hterm : ∀ f ∈ range (dBlockR lab v₀ + 1),
      capEF k lab v₀ j' (((xi k lab v₀ ^ α) ⊗ₜ 1) * ((-1) ^ (dBlockR lab v₀ - f) *
        ((xi k lab v₀ ^ f) ⊗ₜ xsR (k := k) lab v₀ (dBlockR lab v₀ - f)))) =
      (-1) ^ (dBlockR lab v₀ - f) * xB k (moveLab lab v₀ j') (lab v₀) (dBlockR lab v₀ - f) *
        (if blockCardL lab v₀ j' ≤ α + f + 1 then (-1) ^ (α + f + 1 - blockCardL lab v₀ j') *
          xbarB k (moveLab lab v₀ j') j' (α + f + 1 - blockCardL lab v₀ j') else 0) := by
    intro f _
    have hsign : ((-1 : CupRingR (k := k) lab v₀) ^ (dBlockR lab v₀ - f)) =
        (pL k lab v₀ j' ((-1) ^ (dBlockR lab v₀ - f)) ⊗ₜ 1) := by
      rw [map_pow, map_neg, map_one, neg_one_pow_tmul_one]
    rw [mul_left_comm, hsign, capEF_left, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      capEF_tmul, ← pow_add, xsR, ← pL_xB k (lab v₀) (Ne.symm hj),
      mul_comm (xi k lab v₀ ^ (α + f)), trL_pL_mul, trL_xi_pow]
    ring
  rw [Finset.sum_congr rfl hterm, conv_trace_sum (xB k (moveLab lab v₀ j') (lab v₀))
    (xbarB k (moveLab lab v₀ j') j') (blockCardL lab v₀ j') (dBlockR lab v₀) α
    (fun β hβ => xB_eq_zero (by rw [← dBlockR_eq lab v₀ j' hj]; exact hβ))]
  rfl

end EF

/-! ### Positivity and normalization -/

/-- **Bubbles of negative degree vanish** (FE-bubbles: `α + λ_i + 1 < 0`). -/
theorem bubbleFE_neg (lab : V → J) (v₀ : V) (j' : J) (hj : j' ≠ lab v₀) (α : ℕ)
    (h : α + dBlock lab v₀ j' + 1 < blockCard lab v₀) : bubbleFE k lab v₀ j' α = 0 := by
  rw [bubbleFE_eq lab v₀ j' hj, if_neg (by omega)]

/-- **Bubbles of degree zero are `1`** (FE-bubbles: `α + λ_i + 1 = 0`). -/
theorem bubbleFE_zero (lab : V → J) (v₀ : V) (j' : J) (hj : j' ≠ lab v₀) (α : ℕ)
    (h : α + dBlock lab v₀ j' + 1 = blockCard lab v₀) : bubbleFE k lab v₀ j' α = 1 := by
  rw [bubbleFE_eq lab v₀ j' hj, if_pos h.ge, h, Nat.sub_self, bubbleSeries]
  simp

/-- **Bubbles of negative degree vanish** (EF-bubbles: `α - λ_i + 1 < 0`). -/
theorem bubbleEF_neg (lab : V → J) (v₀ : V) (j' : J) (hj : j' ≠ lab v₀) (α : ℕ)
    (h : α + dBlockR lab v₀ + 1 < blockCardL lab v₀ j') : bubbleEF k lab v₀ j' α = 0 := by
  rw [bubbleEF_eq lab v₀ j' hj, if_neg (by omega)]

/-- **Bubbles of degree zero are `1`** (EF-bubbles: `α - λ_i + 1 = 0`). -/
theorem bubbleEF_zero (lab : V → J) (v₀ : V) (j' : J) (hj : j' ≠ lab v₀) (α : ℕ)
    (h : α + dBlockR lab v₀ + 1 = blockCardL lab v₀ j') : bubbleEF k lab v₀ j' α = 1 := by
  rw [bubbleEF_eq lab v₀ j' hj, if_pos h.ge, h, Nat.sub_self, bubbleSeries]
  simp

end Bubbles

/-! ### The bubbles in the presentation (5.2) of `H_k` -/

section Composition

variable {K : Type*} [Field K] {m : ℕ}

/-- **The infinite Grassmannian relation in `H_k`** (presentation (5.2)): the two bubble series
`Φ_n = (-1)^n ∑_{a+b=n} x(k)_{i,a} x̄(k)_{i+1,b}` and `Ψ_n = (-1)^n ∑_{a+b=n} x(k)_{i+1,a} x̄(k)_{i,b}`
satisfy `∑_{a+b=n} Φ_a Ψ_b = δ_{n,0}`. -/
theorem grassmannianH {n : ℕ} (d : Fin n → ℕ) (j₁ j₂ : Fin n) (N : ℕ) :
    ∑ p ∈ antidiagonal N, bubbleSeq (x K d j₁) (xbar K d j₂) p.1 *
      bubbleSeq (x K d j₂) (xbar K d j₁) p.2 = if N = 0 then 1 else 0 :=
  bubbleSeq_mul _ _ _ _ (sum_x_mul_xbar j₁) (sum_x_mul_xbar j₂) N

theorem borelEquivH'_xbarB {V : Type*} [Fintype V] {n : ℕ} (lab : V → Fin n) (d : Fin n → ℕ)
    (hd : ∀ j, Fintype.card {v // lab v = j} = d j) (j : Fin n) (α : ℕ) :
    borelEquivH' K lab d hd (xbarB K lab j α) = xbar K d j α := by
  rw [borelEquivH', AlgEquiv.trans_apply, borelEquivOfCard_xbarB, AlgEquiv.symm_apply_eq,
    hEquiv_xbar]

theorem map_bubbleSeries {V : Type*} [Fintype V] [DecidableEq V] {J : Type*} [DecidableEq J]
    {lab : V → J} {A : Type*} [CommRing A] (φ : BorelRing K lab →+* A) (xA xbA : J → ℕ → A)
    (hx : ∀ j α, φ (xB K lab j α) = xA j α) (hxb : ∀ j α, φ (xbarB K lab j α) = xbA j α)
    (j₁ j₂ : J) (n : ℕ) :
    φ (bubbleSeries K lab j₁ j₂ n) = bubbleSeq (xA j₁) (xbA j₂) n := by
  simp only [bubbleSeries, bubbleSeq, map_mul, map_pow, map_neg, map_one, map_sum, hx, hxb]

/-- The FE-bubble with `α` dots in the region of weight `λ(k)`, as an element of `H_k`
(presentation (5.2)). -/
def bubbleFEH (i : Fin m) (d : Fin (m + 1) → ℕ) (h : 0 < d i.succ) (α : ℕ) : H K d :=
  (hEquiv K d).symm (bubbleFE K (Sigma.fst : Gen d → Fin (m + 1)) (movedVar i d h) i.castSucc α)

/-- **The FE-bubble in `H_k`**: `bubbleFEH α = (-1)^n ∑_{a+b=n} x(k)_{i,a} x̄(k)_{i+1,b}` with
`n = α + λ_i + 1 = α + d_i + 1 - d_{i+1}`, and `0` if `α + λ_i + 1 < 0`. -/
theorem bubbleFEH_eq (i : Fin m) (d : Fin (m + 1) → ℕ) (h : 0 < d i.succ) (α : ℕ) :
    bubbleFEH (K := K) i d h α = if d i.succ ≤ α + d i.castSucc + 1 then
      bubbleSeq (x K d i.castSucc) (xbar K d i.succ) (α + d i.castSucc + 1 - d i.succ) else 0 := by
  have hj : i.castSucc ≠ (Sigma.fst : Gen d → Fin (m + 1)) (movedVar i d h) :=
    (Fin.castSucc_lt_succ i).ne
  have hdB : dBlock (Sigma.fst : Gen d → Fin (m + 1)) (movedVar i d h) i.castSucc =
      d i.castSucc := by
    rw [dBlock_eq _ _ _ hj, card_labSet_sigma]
  rw [bubbleFEH, bubbleFE_eq _ _ _ hj, hdB, blockCard_movedVar]
  split_ifs
  · exact map_bubbleSeries (hEquiv K d).symm.toRingEquiv.toRingHom (x K d) (xbar K d)
      (fun j α => by
        change (hEquiv K d).symm _ = _
        rw [AlgEquiv.symm_apply_eq, hEquiv_x])
      (fun j α => by
        change (hEquiv K d).symm _ = _
        rw [AlgEquiv.symm_apply_eq, hEquiv_xbar])
      _ _ _
  · exact map_zero _

theorem raise_succ (i : Fin m) (d : Fin (m + 1) → ℕ) : raise i d i.succ = d i.succ - 1 := by
  rw [raise, if_neg (Fin.castSucc_lt_succ i).ne', if_pos rfl]

theorem raise_castSucc (i : Fin m) (d : Fin (m + 1) → ℕ) :
    raise i d i.castSucc = d i.castSucc + 1 := by
  rw [raise, if_pos rfl]

/-- The EF-bubble with `α` dots in the region of weight `λ(+_i k)`, as an element of
`H_{+_i k}` (presentation (5.2)). -/
def bubbleEFH (i : Fin m) (d : Fin (m + 1) → ℕ) (h : 0 < d i.succ) (α : ℕ) : H K (raise i d) :=
  borelEquivH' K _ (raise i d) (card_moveLab i d h)
    (bubbleEF K (Sigma.fst : Gen d → Fin (m + 1)) (movedVar i d h) i.castSucc α)

/-- **The EF-bubble in `H_{k'}`, `k' = +_i k`**:
`bubbleEFH α = (-1)^n ∑_{a+b=n} x(k')_{i+1,a} x̄(k')_{i,b}` with
`n = α - λ_i(k') + 1 = α + d'_{i+1} + 1 - d'_i`, and `0` if `α - λ_i(k') + 1 < 0`. -/
theorem bubbleEFH_eq (i : Fin m) (d : Fin (m + 1) → ℕ) (h : 0 < d i.succ) (α : ℕ) :
    bubbleEFH (K := K) i d h α =
      if raise i d i.castSucc ≤ α + raise i d i.succ + 1 then
        bubbleSeq (x K (raise i d) i.succ) (xbar K (raise i d) i.castSucc)
          (α + raise i d i.succ + 1 - raise i d i.castSucc) else 0 := by
  have hj : i.castSucc ≠ (Sigma.fst : Gen d → Fin (m + 1)) (movedVar i d h) :=
    (Fin.castSucc_lt_succ i).ne
  have hdB : dBlockR (Sigma.fst : Gen d → Fin (m + 1)) (movedVar i d h) = raise i d i.succ := by
    rw [raise_succ, dBlockR, card_split_some, if_pos rfl, card_labSet_sigma]
    rfl
  have hbL : blockCardL (Sigma.fst : Gen d → Fin (m + 1)) (movedVar i d h) i.castSucc =
      raise i d i.castSucc := by
    rw [raise_castSucc, blockCardL_movedVar]
  rw [bubbleEFH, bubbleEF_eq _ _ _ hj, hdB, hbL]
  split_ifs
  · exact map_bubbleSeries (borelEquivH' K _ (raise i d) (card_moveLab i d h)).toRingEquiv.toRingHom
      (x K (raise i d)) (xbar K (raise i d))
      (fun j α => borelEquivH'_xB K _ _ (card_moveLab i d h) j α)
      (fun j α => borelEquivH'_xbarB _ _ (card_moveLab i d h) j α) _ _ _
  · exact map_zero _

end Composition

end Categorification.Flag

end
