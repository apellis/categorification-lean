/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.QuantumGroup.UDotKL3

/-!
# An orthogonalising model of `'U 1_λ` (towards KL III Proposition 2.5)

Khovanov–Lauda III, arXiv:0807.3250v1, §2.1.3, Proposition 2.5 (`prop_nondeg`): the bilinear
form `( , )` of Proposition 2.2 is nondegenerate on `U̇`. KL III only point to Lusztig,
*Introduction to quantum groups*, Ch. 26 (Theorem 26.3.1). This file provides the key
construction of a direct proof (the proof itself is in
`Categorification.QuantumGroup.UDotNondeg`).

## The model

Lusztig (26.1) realises the form on `U̇ 1_λ` as a limit of the contravariant forms on
`ᵚM(λ') ⊗ M(λ'')` (lowest ⊗ highest weight modules) as `λ', λ'' → ∞` with `λ'' - λ' = λ`.
We use the resulting *limit action* directly, without modules or limits. On `M = 'f ⊗ 'f`
(basis the pairs of words `(x, y)`; `x ⊗ y` stands for the pure tensor `E_y ξ ⊗ F_x η`), with
`μ = λ + |y| - |x|` and `n_i = ⟨i, μ⟩` (`UDot.ndWn`), let (`d_i` = Lusztig's twisted derivation
`PreF.d` at `v = q⁻¹`, `g_i = q_i⁻¹ (1 - q_i²)⁻¹`, `UDot.ndG`)

* `E_i (x ⊗ y) = x ⊗ θ_i y + g_i q_i^{-n_i} d_i(x) ⊗ y` (`UDot.ndE`),
* `F_j (x ⊗ y) = θ_j x ⊗ y + g_j q_j^{n_j} x ⊗ d_j(y)` (`UDot.ndF`).

These satisfy the commutation relation `E_i F_j - F_j E_i = δ_{ij} [⟨i, μ⟩]_i` on the weight
space of weight `μ` (`UDot.ndE_ndF_sub`), so the free algebra `'U 1_λ` acts on `M`
(`UDot.ndAct`) killing the commutation relators of KL III eq. (2.4) (`UDot.ndNF_comm`); the
Serre relators are *not* killed. We write `ndNF z = z · (1 ⊗ 1)`.

The point (proved in `Categorification.QuantumGroup.UDotNondeg`) is that for KL III's
normalisation `(θ_i, θ_i) = (1 - q_i²)⁻¹` the form `( , )` becomes the *tensor product* of the
forms on `'f` in this model: `(z, w) = (ndNF z, ndNF w)_{'f ⊗ 'f}`.

## Main results

* `UDot.ndE_ndF_sub` — the commutation relation on weight spaces;
* `UDot.ndNF_mem_Msupp` — `ndNF (E_w)` lies in the weight space of `w`;
* `UDot.ndNF_comm` — `ndNF` kills the commutation relators;
* `UDot.ndNF_posF` — `ndNF (x⁺) = 1 ⊗ x`.
-/

noncomputable section

namespace Categorification.QuantumGroup

open scoped Classical
open PreF

namespace UDot

variable {I : Type*} {K : Type*} [Field K] (C : CartanDatum I) (q : Kˣ)

/-! ### Scalars -/

/-- The weight number `⟨i, μ⟩ = ⟨i, λ + |y| - |x|⟩` of the basis vector `x ⊗ y` (`ℓ = ⟨-, λ⟩`). -/
def ndWn (ℓ : I → ℤ) (i : I) (x y : FreeMonoid I) : ℤ := ℓ i + msA C i (wt y) - msA C i (wt x)

/-- `g_i = q_i⁻¹ (1 - q_i²)⁻¹`. -/
def ndG (i : I) : K := qp q (-di C i) * (1 - qp q (2 * di C i))⁻¹

/-! ### The operators -/

/-- `E_i` on the model: `x ⊗ y ↦ x ⊗ θ_i y + g_i q_i^{-n_i} d_i(x) ⊗ y`. -/
def ndE (ℓ : I → ℤ) (i : I) : Module.End K (M K I) :=
  Finsupp.linearCombination K fun p =>
    tm (word p.1) (θ i * word p.2) +
      (ndG C q i * qp q (-(di C i * ndWn C ℓ i p.1 p.2))) •
        tm (PreF.d C.dot q⁻¹ i (word p.1)) (word p.2)

/-- `F_j` on the model: `x ⊗ y ↦ θ_j x ⊗ y + g_j q_j^{n_j} x ⊗ d_j(y)`. -/
def ndF (ℓ : I → ℤ) (j : I) : Module.End K (M K I) :=
  Finsupp.linearCombination K fun p =>
    tm (θ j * word p.1) (word p.2) +
      (ndG C q j * qp q (di C j * ndWn C ℓ j p.1 p.2)) •
        tm (word p.1) (PreF.d C.dot q⁻¹ j (word p.2))

variable {C q}

theorem ndE_tm_word (ℓ : I → ℤ) (i : I) (u w : FreeMonoid I) :
    ndE C q ℓ i (tm (word u) (word w)) =
      tm (word u) (θ i * word w) +
        (ndG C q i * qp q (-(di C i * ndWn C ℓ i u w))) • tm (PreF.d C.dot q⁻¹ i (word u)) (word w) := by
  rw [tm_word_word, ndE, Finsupp.linearCombination_single, one_smul]

theorem ndF_tm_word (ℓ : I → ℤ) (j : I) (u w : FreeMonoid I) :
    ndF C q ℓ j (tm (word u) (word w)) =
      tm (θ j * word u) (word w) +
        (ndG C q j * qp q (di C j * ndWn C ℓ j u w)) • tm (word u) (PreF.d C.dot q⁻¹ j (word w)) := by
  rw [tm_word_word, ndF, Finsupp.linearCombination_single, one_smul]

/-- `ndE` on `x ⊗ y` with `x`, `y` homogeneous for the functional `msA i`. -/
theorem ndE_tm_of (ℓ : I → ℤ) (i : I) {Sx Sy : Set (FreeMonoid I)} {mx my : ℤ}
    (hSx : ∀ u ∈ Sx, msA C i (wt u) = mx) (hSy : ∀ w ∈ Sy, msA C i (wt w) = my)
    {x y : PreF K I} (hx : x ∈ (supp Sx : Submodule K (PreF K I)))
    (hy : y ∈ (supp Sy : Submodule K (PreF K I))) :
    ndE C q ℓ i (tm x y) =
      tm x (θ i * y) + (ndG C q i * qp q (-(di C i * (ℓ i + my - mx)))) •
        tm (PreF.d C.dot q⁻¹ i x) y := by
  have h1 : ∀ w ∈ Sy, ndE C q ℓ i (tm x (word w)) =
      tm x (θ i * word w) + (ndG C q i * qp q (-(di C i * (ℓ i + my - mx)))) •
        tm (PreF.d C.dot q⁻¹ i x) (word w) := by
    intro w hw
    refine eqOn_supp ((ndE C q ℓ i) ∘ₗ tm.flip (word w))
      (tm.flip (θ i * word w) + (ndG C q i * qp q (-(di C i * (ℓ i + my - mx)))) •
        (tm.flip (word w) ∘ₗ PreF.d C.dot q⁻¹ i)) (fun u hu => ?_) x hx
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.flip_apply, LinearMap.add_apply,
      LinearMap.smul_apply, ndE_tm_word, ndWn, hSx u hu, hSy w hw]
  refine eqOn_supp ((ndE C q ℓ i) ∘ₗ tm x)
    (tm x ∘ₗ LinearMap.mulLeft K (θ i) + (ndG C q i * qp q (-(di C i * (ℓ i + my - mx)))) •
      tm (PreF.d C.dot q⁻¹ i x)) (fun w hw => ?_) y hy
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.mulLeft_apply, h1 w hw]

/-- `ndF` on `x ⊗ y` with `x`, `y` homogeneous for the functional `msA j`. -/
theorem ndF_tm_of (ℓ : I → ℤ) (j : I) {Sx Sy : Set (FreeMonoid I)} {mx my : ℤ}
    (hSx : ∀ u ∈ Sx, msA C j (wt u) = mx) (hSy : ∀ w ∈ Sy, msA C j (wt w) = my)
    {x y : PreF K I} (hx : x ∈ (supp Sx : Submodule K (PreF K I)))
    (hy : y ∈ (supp Sy : Submodule K (PreF K I))) :
    ndF C q ℓ j (tm x y) =
      tm (θ j * x) y + (ndG C q j * qp q (di C j * (ℓ j + my - mx))) •
        tm x (PreF.d C.dot q⁻¹ j y) := by
  have h1 : ∀ w ∈ Sy, ndF C q ℓ j (tm x (word w)) =
      tm (θ j * x) (word w) + (ndG C q j * qp q (di C j * (ℓ j + my - mx))) •
        tm x (PreF.d C.dot q⁻¹ j (word w)) := by
    intro w hw
    refine eqOn_supp ((ndF C q ℓ j) ∘ₗ tm.flip (word w))
      (tm.flip (word w) ∘ₗ LinearMap.mulLeft K (θ j) +
        (ndG C q j * qp q (di C j * (ℓ j + my - mx))) •
          tm.flip (PreF.d C.dot q⁻¹ j (word w))) (fun u hu => ?_) x hx
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.flip_apply, LinearMap.add_apply,
      LinearMap.smul_apply, LinearMap.mulLeft_apply, ndF_tm_word, ndWn, hSx u hu, hSy w hw]
  refine eqOn_supp ((ndF C q ℓ j) ∘ₗ tm x)
    (tm (θ j * x) + (ndG C q j * qp q (di C j * (ℓ j + my - mx))) •
      (tm x ∘ₗ PreF.d C.dot q⁻¹ j)) (fun w hw => ?_) y hy
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
    h1 w hw]

/-! ### The commutation relation -/

theorem qp_inv_zpow (e : ℤ) : ((((q⁻¹ : Kˣ) ^ e : Kˣ)) : K) = qp q (-e) := by
  rw [qp, inv_zpow', zpow_neg]

theorem qp_eq_zpow (e : ℤ) : qp q e = (q : K) ^ e := by
  rw [qp, Units.val_zpow_eq_zpow_val]

/-- The diagonal scalar: `g_i (q_i^{2-n} - q_i^{n+2}) = [n]_i`. -/
theorem ndG_sub (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) (i : I) (n : ℤ) :
    ndG C q i * qp q (-(di C i * (n - 2))) - ndG C q i * qp q (di C i * (n + 2)) =
      qbr (qi C q i) n := by
  have hne := qi_sub_inv_ne_zero C q hq i
  have hq0 : (q : K) ≠ 0 := Units.ne_zero q
  set y : K := (q : K) ^ di C i with hy
  have hy0 : y ≠ 0 := zpow_ne_zero _ hq0
  have ht : ((qi C q i : Kˣ) : K) = y := by rw [qi, Units.val_zpow_eq_zpow_val]
  have hti : (((qi C q i)⁻¹ : Kˣ) : K) = y⁻¹ := by rw [Units.val_inv_eq_inv_val, ht]
  have hne' : y - y⁻¹ ≠ 0 := by rwa [ht, hti] at hne
  have h1y : 1 - y ^ 2 ≠ 0 := by
    intro h
    apply hne'
    have : y ^ 2 = 1 := by linear_combination -h
    field_simp
    linear_combination this
  set Y : K := y ^ n with hY
  have hY0 : Y ≠ 0 := zpow_ne_zero _ hy0
  have e1 : qp q (-(di C i * (n - 2))) = Y⁻¹ * y ^ 2 := by
    rw [qp_eq_zpow, show -(di C i * (n - 2)) = di C i * (-n) + di C i * 2 by ring,
      zpow_add₀ hq0, zpow_mul, zpow_mul, ← hy, zpow_neg, zpow_ofNat]
  have e2 : qp q (di C i * (n + 2)) = Y * y ^ 2 := by
    rw [qp_eq_zpow, show di C i * (n + 2) = di C i * n + di C i * 2 by ring,
      zpow_add₀ hq0, zpow_mul, zpow_mul, ← hy, zpow_ofNat]
  have e3 : qp q (-di C i) = y⁻¹ := by rw [qp_eq_zpow, zpow_neg]
  have e4 : qp q (2 * di C i) = y ^ 2 := by
    rw [qp_eq_zpow, mul_comm, zpow_mul, ← hy, zpow_ofNat]
  have e5 : qbr (qi C q i) n = (Y - Y⁻¹) / (y - y⁻¹) := by
    rw [qbr, ht, hti, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, ht, zpow_neg]
  have key : y - y⁻¹ = -(1 - y ^ 2) * y⁻¹ := by field_simp; ring
  have h : y⁻¹ * y ^ 2 = y := by rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hy0, one_mul]
  rw [ndG, e1, e2, e3, e4, e5, key, div_eq_mul_inv, mul_inv, inv_inv, inv_neg]
  linear_combination (1 - y ^ 2)⁻¹ * (Y⁻¹ - Y) * h

/-- **The commutation relation on the model.** On the weight space of signed weight `P - N`,
`E_i F_j - F_j E_i` acts by `δ_{ij} [⟨i, λ + P - N⟩]_i`. -/
theorem ndE_ndF_sub (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) (ℓ : I → ℤ) (i j : I)
    {P N : Multiset I} {v : M K I} (hv : v ∈ Msupp P N) :
    ndE C q ℓ i (ndF C q ℓ j v) - ndF C q ℓ j (ndE C q ℓ i v) =
      if j = i then qbr (qi C q i) (ℓ i + msA C i P - msA C i N) • v else 0 := by
  refine Msupp_induction (motive := fun v => ndE C q ℓ i (ndF C q ℓ j v) -
      ndF C q ℓ j (ndE C q ℓ i v) =
      if j = i then qbr (qi C q i) (ℓ i + msA C i P - msA C i N) • v else 0) hv (by simp)
    (fun x y hx hy => by
      beta_reduce at hx hy ⊢
      rw [map_add, map_add, map_add, map_add, add_sub_add_comm, hx, hy]
      split_ifs <;> simp [smul_add])
    (fun r x hx => by
      beta_reduce at hx ⊢
      rw [map_smul, map_smul, map_smul, map_smul, ← smul_sub, hx]
      split_ifs <;> simp [smul_comm r])
    fun u w h => ?_
  beta_reduce
  have hwt : msA C i (wt w) - msA C i (wt u) = msA C i P - msA C i N := by
    have := congrArg (msA C i) h
    simp only [msA_add] at this
    linarith
  -- the four expansions
  have hSu : ∀ u' ∈ ({u} : Set (FreeMonoid I)), ∀ k, msA C k (wt u') = msA C k (wt u) := by
    rintro u' rfl k; rfl
  have hSw : ∀ w' ∈ ({w} : Set (FreeMonoid I)), ∀ k, msA C k (wt w') = msA C k (wt w) := by
    rintro w' rfl k; rfl
  have hdw : ∀ k, ∀ w' ∈ {w' : FreeMonoid I | j ::ₘ wt w' = wt w},
      msA C k (wt w') = msA C k (wt w) - A C k j := by
    intro k w' hw'
    simp only [Set.mem_setOf_eq] at hw'
    rw [← hw', msA_cons]; ring
  have hdu : ∀ k, ∀ u' ∈ {u' : FreeMonoid I | i ::ₘ wt u' = wt u},
      msA C k (wt u') = msA C k (wt u) - A C k i := by
    intro k u' hu'
    simp only [Set.mem_setOf_eq] at hu'
    rw [← hu', msA_cons]; ring
  have T1 : ndE C q ℓ i (tm (θ j * word u) (word w)) =
      tm (θ j * word u) (θ i * word w) +
        (ndG C q i * qp q (-(di C i * (ℓ i + msA C i (wt w) - (A C i j + msA C i (wt u)))))) •
          tm (PreF.d C.dot q⁻¹ i (θ j * word u)) (word w) := by
    rw [θ, ← word_mul, ndE_tm_word, ndWn, wt_mul, wt_of, msA_add, msA_singleton]
  have T2 := ndE_tm_of (C := C) (q := q) ℓ i (hSu · · i) (hdw i) (word_mem_supp rfl)
    (d_word_mem_supp (dot := C.dot) (v := q⁻¹) j w)
  have T3 : ndF C q ℓ j (tm (word u) (θ i * word w)) =
      tm (θ j * word u) (θ i * word w) +
        (ndG C q j * qp q (di C j * (ℓ j + (A C j i + msA C j (wt w)) - msA C j (wt u)))) •
          tm (word u) (PreF.d C.dot q⁻¹ j (θ i * word w)) := by
    rw [θ, ← word_mul, ndF_tm_word, ndWn, wt_mul, wt_of, msA_add, msA_singleton]
  have T4 := ndF_tm_of (C := C) (q := q) ℓ j (hdu j) (hSw · · j)
    (d_word_mem_supp (dot := C.dot) (v := q⁻¹) i u) (word_mem_supp rfl)
  rw [ndF_tm_word, ndE_tm_word, map_add, map_smul, map_add, map_smul, T1, T2, T3, T4,
    d_θ_mul, d_θ_mul, qp_inv_zpow, qp_inv_zpow]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, ndWn]
  -- scalar identities
  have hij : di C i * A C i j = di C j * A C j i := di_mul_A_comm C i j
  have hdij : di C i * A C i j = C.dot j i := by rw [di_mul_A, C.symm]
  have hdji : di C j * A C j i = C.dot i j := by rw [di_mul_A, C.symm]
  have s1 : ndG C q i * qp q (-(di C i * (ℓ i + msA C i (wt w) - (A C i j + msA C i (wt u))))) *
      qp q (-C.dot j i) = ndG C q i * qp q (-(di C i * (ℓ i + msA C i (wt w) - msA C i (wt u)))) := by
    rw [mul_assoc, ← qp_add]; congr 2; linear_combination hdij
  have s2 : ndG C q j * qp q (di C j * (ℓ j + (A C j i + msA C j (wt w)) - msA C j (wt u))) *
      qp q (-C.dot i j) = ndG C q j * qp q (di C j * (ℓ j + msA C j (wt w) - msA C j (wt u))) := by
    rw [mul_assoc, ← qp_add]; congr 2; linear_combination hdji
  have s3 : ndG C q j * qp q (di C j * (ℓ j + msA C j (wt w) - msA C j (wt u))) *
      (ndG C q i * qp q (-(di C i * (ℓ i + (msA C i (wt w) - A C i j) - msA C i (wt u))))) =
      ndG C q i * qp q (-(di C i * (ℓ i + msA C i (wt w) - msA C i (wt u)))) *
      (ndG C q j * qp q (di C j * (ℓ j + msA C j (wt w) - (msA C j (wt u) - A C j i)))) := by
    set a := di C j * (ℓ j + msA C j (wt w) - msA C j (wt u))
    set b := -(di C i * (ℓ i + (msA C i (wt w) - A C i j) - msA C i (wt u)))
    set c' := -(di C i * (ℓ i + msA C i (wt w) - msA C i (wt u)))
    set d' := di C j * (ℓ j + msA C j (wt w) - (msA C j (wt u) - A C j i))
    calc ndG C q j * qp q a * (ndG C q i * qp q b)
        = ndG C q i * ndG C q j * qp q (a + b) := by rw [qp_add]; ring
      _ = ndG C q i * ndG C q j * qp q (c' + d') := by
          congr 2; simp only [a, b, c', d']; linear_combination hij
      _ = ndG C q i * qp q c' * (ndG C q j * qp q d') := by rw [qp_add]; ring
  by_cases hji : j = i
  · subst hji
    simp only [if_true, A_self] at s1 s2 s3 ⊢
    have e5 : ℓ j + msA C j P - msA C j N = ℓ j + msA C j (wt w) - msA C j (wt u) := by
      linarith
    have s4 : ndG C q j * qp q (-(di C j * (ℓ j + msA C j (wt w) - (2 + msA C j (wt u))))) -
        ndG C q j * qp q (di C j * (ℓ j + (2 + msA C j (wt w)) - msA C j (wt u))) =
        qbr (qi C q j) (ℓ j + msA C j P - msA C j N) := by
      rw [e5, ← ndG_sub hq j]
      congr 3 <;> ring
    linear_combination (norm := module)
      s1 • tm (θ j * PreF.d C.dot q⁻¹ j (word u)) (word w) -
      s2 • tm (word u) (θ j * PreF.d C.dot q⁻¹ j (word w)) +
      s3 • tm (PreF.d C.dot q⁻¹ j (word u)) (PreF.d C.dot q⁻¹ j (word w)) +
      s4 • tm (word u) (word w)
  · simp only [if_neg hji, if_neg (Ne.symm hji), map_zero, LinearMap.zero_apply, zero_add,
      add_zero, smul_zero]
    linear_combination (norm := module)
      s1 • tm (θ j * PreF.d C.dot q⁻¹ i (word u)) (word w) -
      s2 • tm (word u) (θ i * PreF.d C.dot q⁻¹ j (word w)) +
      s3 • tm (PreF.d C.dot q⁻¹ i (word u)) (PreF.d C.dot q⁻¹ j (word w))

/-! ### The action of `'U 1_λ` -/

variable (C q) in
/-- The generator `E_{εi}` acting on the model. -/
def ndGen (ℓ : I → ℤ) : Bool × I → Module.End K (M K I)
  | (true, i) => ndE C q ℓ i
  | (false, i) => ndF C q ℓ i

variable (C q) in
/-- The action of the free algebra `'U 1_λ` on the model. -/
def ndAct (ℓ : I → ℤ) : Free K I →ₐ[K] Module.End K (M K I) :=
  MonoidAlgebra.lift K (FreeMonoid (Bool × I)) (Module.End K (M K I))
    (FreeMonoid.lift (ndGen C q ℓ))

theorem ndAct_ew (ℓ : I → ℤ) (w : List (Bool × I)) :
    ndAct C q ℓ (ew w) = (w.map (ndGen C q ℓ)).prod := by
  rw [ndAct, ew, word, MonoidAlgebra.lift_single, one_smul, FreeMonoid.lift_apply]
  rfl

theorem ndAct_ew_cons (ℓ : I → ℤ) (l : Bool × I) (w : List (Bool × I)) :
    ndAct C q ℓ (ew (l :: w)) = ndGen C q ℓ l * ndAct C q ℓ (ew w) := by
  rw [ndAct_ew, ndAct_ew, List.map_cons, List.prod_cons]

variable (C q) in
/-- The model normal form `ndNF z = z · (1 ⊗ 1)`. -/
def ndNF (ℓ : I → ℤ) : Free K I →ₗ[K] M K I :=
  LinearMap.applyₗ (vac (K := K) (I := I)) ∘ₗ (ndAct C q ℓ).toLinearMap

theorem ndNF_apply (ℓ : I → ℤ) (x : Free K I) : ndNF C q ℓ x = ndAct C q ℓ x vac := rfl

theorem ndNF_mul (ℓ : I → ℤ) (x y : Free K I) :
    ndNF C q ℓ (x * y) = ndAct C q ℓ x (ndNF C q ℓ y) := by
  simp [ndNF_apply, Module.End.mul_apply]

theorem ndNF_ew_cons (ℓ : I → ℤ) (l : Bool × I) (w : List (Bool × I)) :
    ndNF C q ℓ (ew (l :: w)) = ndGen C q ℓ l (ndNF C q ℓ (ew w)) := by
  rw [ndNF_apply, ndAct_ew_cons, Module.End.mul_apply]; rfl

theorem ndNF_ew_append (ℓ : I → ℤ) (w w' : List (Bool × I)) :
    ndNF C q ℓ (ew (w ++ w')) = ndAct C q ℓ (ew w) (ndNF C q ℓ (ew w')) := by
  rw [ew_append, ndNF_mul]

/-! ### Weight spaces -/

theorem tm_word_mem_Msupp_of {P N : Multiset I} {u : FreeMonoid I} {S : Set (FreeMonoid I)}
    (hS : ∀ w ∈ S, wt w + N = wt u + P) {y : PreF K I}
    (hy : y ∈ (supp S : Submodule K (PreF K I))) : tm (word u) y ∈ Msupp P N := by
  rw [supp_eq_span] at hy
  induction hy using Submodule.span_induction with
  | mem z hz => obtain ⟨w, hw, rfl⟩ := hz; exact tm_mem_Msupp (hS w hw)
  | zero => simp
  | add z z' _ _ hz hz' => rw [map_add]; exact add_mem hz hz'
  | smul r z _ hz => rw [map_smul]; exact Submodule.smul_mem _ _ hz

theorem tm_mem_Msupp_of_word {P N : Multiset I} {w : FreeMonoid I} {S : Set (FreeMonoid I)}
    (hS : ∀ u ∈ S, wt w + N = wt u + P) {x : PreF K I}
    (hx : x ∈ (supp S : Submodule K (PreF K I))) : tm x (word w) ∈ Msupp P N := by
  rw [supp_eq_span] at hx
  induction hx using Submodule.span_induction with
  | mem z hz => obtain ⟨u, hu, rfl⟩ := hz; exact tm_mem_Msupp (hS u hu)
  | zero => simp
  | add z z' _ _ hz hz' => rw [map_add, LinearMap.add_apply]; exact add_mem hz hz'
  | smul r z _ hz => rw [map_smul, LinearMap.smul_apply]; exact Submodule.smul_mem _ _ hz

theorem ndF_mem_Msupp (ℓ : I → ℤ) (j : I) {P N : Multiset I} {v : M K I} (hv : v ∈ Msupp P N) :
    ndF C q ℓ j v ∈ Msupp P (j ::ₘ N) := by
  refine Msupp_induction (motive := fun v => ndF C q ℓ j v ∈ Msupp P (j ::ₘ N)) hv (by simp)
    (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add]; exact add_mem hx hy)
    (fun r x hx => by beta_reduce at hx ⊢; rw [map_smul]; exact Submodule.smul_mem _ _ hx)
    fun u w h => ?_
  beta_reduce
  rw [ndF_tm_word]
  refine add_mem ?_ (Submodule.smul_mem _ _ ?_)
  · rw [θ, ← word_mul]
    refine tm_mem_Msupp ?_
    rw [wt_mul, wt_of, ← Multiset.singleton_add, add_left_comm, h]
    abel
  · refine tm_word_mem_Msupp_of (fun w' hw' => ?_) (d_word_mem_supp (dot := C.dot) (v := q⁻¹) j w)
    simp only [Set.mem_setOf_eq] at hw'
    rw [← h, ← hw', Multiset.cons_add, Multiset.add_cons]

theorem ndE_mem_Msupp (ℓ : I → ℤ) (i : I) {P N : Multiset I} {v : M K I} (hv : v ∈ Msupp P N) :
    ndE C q ℓ i v ∈ Msupp (i ::ₘ P) N := by
  refine Msupp_induction (motive := fun v => ndE C q ℓ i v ∈ Msupp (i ::ₘ P) N) hv (by simp)
    (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add]; exact add_mem hx hy)
    (fun r x hx => by beta_reduce at hx ⊢; rw [map_smul]; exact Submodule.smul_mem _ _ hx)
    fun u w h => ?_
  beta_reduce
  rw [ndE_tm_word]
  refine add_mem ?_ (Submodule.smul_mem _ _ ?_)
  · rw [θ, ← word_mul]
    refine tm_mem_Msupp ?_
    rw [wt_mul, wt_of, ← Multiset.singleton_add, add_assoc, h]
    abel
  · refine tm_mem_Msupp_of_word (fun u' hu' => ?_) (d_word_mem_supp (dot := C.dot) (v := q⁻¹) i u)
    simp only [Set.mem_setOf_eq] at hu'
    rw [h, ← hu', Multiset.cons_add, Multiset.add_cons]

/-- `ndNF (E_w)` lies in the weight space of `w`. -/
theorem ndNF_mem_Msupp (ℓ : I → ℤ) (w : List (Bool × I)) :
    ndNF C q ℓ (ew w) ∈ Msupp (posMS w) (negMS w) := by
  induction w with
  | nil =>
    rw [ew_nil, ndNF_apply, map_one, Module.End.one_apply, vac_eq, ← word_one]
    exact tm_mem_Msupp (by simp)
  | cons l w ih =>
    obtain ⟨b, i⟩ := l
    rw [ndNF_ew_cons]
    cases b
    · simpa using ndF_mem_Msupp ℓ i ih
    · simpa using ndE_mem_Msupp ℓ i ih

/-- **`ndNF` kills the commutation relators** (KL III eq. (2.4)). -/
theorem ndNF_comm (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) (ℓ : I → ℤ) (a b : List (Bool × I))
    (i j : I) :
    ndNF C q ℓ (ew (a ++ (true, i) :: (false, j) :: b)) =
      ndNF C q ℓ (ew (a ++ (false, j) :: (true, i) :: b)) +
        if j = i then qbr (qi C q i) (wl C ℓ b i) • ndNF C q ℓ (ew (a ++ b)) else 0 := by
  rw [ndNF_ew_append, ndNF_ew_append, ndNF_ew_append, ndNF_ew_cons, ndNF_ew_cons, ndNF_ew_cons,
    ndNF_ew_cons]
  change ndAct C q ℓ (ew a) (ndE C q ℓ i (ndF C q ℓ j _)) =
    ndAct C q ℓ (ew a) (ndF C q ℓ j (ndE C q ℓ i _)) + _
  rw [← sub_eq_iff_eq_add', ← map_sub, ndE_ndF_sub hq ℓ i j (ndNF_mem_Msupp ℓ b), wl, aS_eq,
    ← add_sub_assoc]
  split_ifs <;> simp

theorem ndNF_posW (ℓ : I → ℤ) (b : List I) :
    ndNF C q ℓ (ew (posW b)) = tm (1 : PreF K I) (word (FreeMonoid.ofList b)) := by
  induction b with
  | nil => rw [posW_nil, ew_nil, ndNF_apply, map_one, Module.End.one_apply, vac_eq]; rfl
  | cons i b ih =>
    rw [posW_cons, ndNF_ew_cons, ih]
    change ndE C q ℓ i _ = _
    rw [← word_one, ndE_tm_word, word_one, d_one, map_zero, LinearMap.zero_apply, smul_zero,
      add_zero, FreeMonoid.ofList_cons, word_of_mul]

/-- `ndNF (x⁺) = 1 ⊗ x`. -/
theorem ndNF_posF (ℓ : I → ℤ) (x : PreF K I) : ndNF C q ℓ (posF x) = tm (1 : PreF K I) x := by
  induction x using induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
  | smul_word u r =>
    rw [map_smul, map_smul, posF_word, ndNF_posW, FreeMonoid.ofList_toList, map_smul]

/-! ### Triangularity -/

/-- The span of the basis vectors `x ⊗ y` with `x` of length `< k`. -/
def Mlow (k : ℕ) : Submodule K (M K I) :=
  Finsupp.supported K K {p : FreeMonoid I × FreeMonoid I | Multiset.card (wt p.1) < k}

theorem tm_mem_Mlow {k : ℕ} {u : FreeMonoid I} (hu : Multiset.card (wt u) < k) (y : PreF K I) :
    tm (word u) y ∈ (Mlow k : Submodule K (M K I)) := by
  induction y using induction_linear with
  | zero => simp
  | add y y' hy hy' => rw [map_add]; exact add_mem hy hy'
  | smul_word w r =>
    rw [map_smul, tm_word_word]
    exact Submodule.smul_mem _ _ (Finsupp.single_mem_supported K _ hu)

theorem Mlow_induction {k : ℕ} {motive : M K I → Prop} {v : M K I} (hv : v ∈ (Mlow k : Submodule K (M K I)))
    (zero : motive 0) (add : ∀ x y, motive x → motive y → motive (x + y))
    (smul : ∀ (r : K) x, motive x → motive (r • x))
    (basis : ∀ u w : FreeMonoid I, Multiset.card (wt u) < k → motive (tm (word u) (word w))) :
    motive v := by
  rw [Mlow, Finsupp.supported_eq_span_single] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, hp, rfl⟩ := hx
    show motive (Finsupp.single p 1)
    rw [single_eq_tm]
    exact basis p.1 p.2 hp
  | zero => exact zero
  | add x y _ _ hx hy => exact add x y hx hy
  | smul r x _ hx => exact smul r x hx

theorem ndF_mem_Mlow (ℓ : I → ℤ) (j : I) {k : ℕ} {v : M K I}
    (hv : v ∈ (Mlow k : Submodule K (M K I))) : ndF C q ℓ j v ∈ (Mlow (k + 1) : Submodule K (M K I)) := by
  refine Mlow_induction (motive := fun v => ndF C q ℓ j v ∈ (Mlow (k + 1) : Submodule K (M K I)))
    hv (by simp)
    (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add]; exact add_mem hx hy)
    (fun r x hx => by beta_reduce at hx ⊢; rw [map_smul]; exact Submodule.smul_mem _ _ hx)
    fun u w h => ?_
  beta_reduce
  rw [ndF_tm_word, θ, ← word_mul]
  refine add_mem (tm_mem_Mlow ?_ _) (Submodule.smul_mem _ _ (tm_mem_Mlow (by omega) _))
  simp only [wt_mul, wt_of, Multiset.card_add, Multiset.card_singleton]
  omega

/-- `F_c` applied to `x ⊗ y` is `θ_c x ⊗ y` plus terms with a shorter first factor. -/
theorem ndAct_negW_tm (ℓ : I → ℤ) (c : List I) (x w : FreeMonoid I) :
    ndAct C q ℓ (ew (negW c)) (tm (word x) (word w)) -
        tm (word (FreeMonoid.ofList c * x)) (word w) ∈
      (Mlow (c.length + Multiset.card (wt x)) : Submodule K (M K I)) := by
  induction c with
  | nil => simp
  | cons j c ih =>
    rw [negW_cons, ndAct_ew_cons, Module.End.mul_apply]
    change ndF C q ℓ j _ - _ ∈ _
    have h1 := ndF_mem_Mlow (C := C) (q := q) ℓ j ih
    rw [map_sub, ndF_tm_word] at h1
    have h2 : tm (word (FreeMonoid.ofList c * x)) (PreF.d C.dot q⁻¹ j (word w)) ∈
        (Mlow (c.length + Multiset.card (wt x) + 1) : Submodule K (M K I)) :=
      tm_mem_Mlow (by simp [wt]) _
    have e : θ j * word (FreeMonoid.ofList c * x) =
        (word (FreeMonoid.ofList (j :: c) * x) : PreF K I) := by
      rw [θ, ← word_mul, FreeMonoid.ofList_cons, mul_assoc]
    rw [e] at h1
    have := add_mem h1 (Submodule.smul_mem _ (ndG C q j * qp q (di C j *
      ndWn C ℓ j (FreeMonoid.ofList c * x) w)) h2)
    rw [List.length_cons, show c.length + 1 + Multiset.card (wt x) =
      c.length + Multiset.card (wt x) + 1 by omega]
    convert this using 1
    abel

end UDot

end Categorification.QuantumGroup

end
