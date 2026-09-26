/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.CupsMirror

/-!
# Caps and biadjointness in the flag 2-category (KL III Definition 6.1)

Khovanov–Lauda III, arXiv:0807.3250v1, §6.1.1 (TeX `sln-2008-ArXiv.tex`, subsubsection
"Biadjointness", Definition 6.1, eqs. (6.2)–(6.5)) and the biadjointness part of Proposition 6.3.

We keep the Borel model: `lab : V → J`, `v₀`, `j' ≠ lab v₀`; `M = H_{k^{+i}}`, `R = H_k` (acting
through `pR`), `R' = H_{+_i k}` (acting through `pL`).

## The caps

KL III define the caps on the spanning elements `ξ^{α₁} ⊗ ξ^{α₂}`. We define them as
"multiply, then take the Frobenius trace" (`trR`, `trL` of `Categorification.Flag.Free`) and prove
that they take the values of Definition 6.1:

* `capFE : H_{k^{+i}} ⊗_{H_{+_i k}} H_{k^{+i}} → H_k` (eq. (6.4), the image of the cap
  `F_i E_i 1_λ → 1_λ`): `capFE_xi` gives
  `ξ^{α₁} ⊗ ξ^{α₂} ↦ (-1)^{α₁+α₂+1-b} x̄(k)_{i+1,α₁+α₂+1-b}`, `b = k_{i+1} - k_i`;
* `capEF : H_{k^{+i}} ⊗_{H_k} H_{k^{+i}} → H_{+_i k}` (eq. (6.5) at the weight of `+_i k`):
  `ξ^{α₁} ⊗ ξ^{α₂} ↦ (-1)^{α₁+α₂+1-b'} x̄(+_i k)_{i,α₁+α₂+1-b'}`, `b' = (+_i k)_i - (+_i k)_{i-1}`;

(with the convention `x̄_{j,γ} = 0` for `γ < 0`), and that they are bimodule maps
(`capFE_left`, `capFE_right`, `capEF_left`, `capEF_right`). Dots slide across caps
(`capFE_slide`, `capEF_slide`); across cups this is Lemma 5.4 (iii), (iv) (`lemma_5_4_iii`,
`lemma_5_4_iv`): together, the cyclicity relations (3.3) for dots.

## Biadjointness

With the cups of Corollary 5.5 (`cupEltKL`, `cupEltRKL`), the four zigzag identities of KL III
Definition 3.1 (biadjointness of `E_i` and `F_i`, eqs. (3.1), (3.2)) hold in the flag 2-category:

* `snake_E_FE`, `snake_F_FE` : `(cap_EF ∘ 1_E) ∘ (1_E ∘ cup_FE) = 1_E` and
  `(1_F ∘ cap_EF) ∘ (cup_FE ∘ 1_F) = 1_F`;
* `snake_E_EF`, `snake_F_EF` : `(1_E ∘ cap_FE) ∘ (cup_EF ∘ 1_E) = 1_E` and
  `(cap_FE ∘ 1_F) ∘ (1_F ∘ cup_EF) = 1_F`.

They are stated elementwise: for the cup element `∑_f c_f ⊗ c'_f` the composite sends `m` to
`∑_f tr(m c_f) c'_f` (resp. `∑_f c_f tr(c'_f m)`). The first identity of each pair is the
generating-function identity `(-ξ)^a = ∑ x_u x̄_{a-u}` (KL III (5.30)) combined with the trace
formula (`zigzag_of_trace`); the second follows from the first by the symmetry of dual bases for
a symmetric bilinear form (`dual_basis_symm`).

Gradings are not treated.
-/

noncomputable section

namespace Categorification.Flag

open MvPolynomial TensorProduct
open Finset (univ range antidiagonal)

/-! ### Abstract Frobenius algebra lemmas -/

section Abstract

variable {R M : Type*} [CommRing R] [CommRing M] [Algebra R M]

/-- **Dual bases for a symmetric form.** If `∑_i tr(m b_i) v_i = m` for all `m` (so `(v_i)` is a
right dual basis of the basis `(b_i)` for the form `tr(m m')`), then also
`∑_i tr(v_i m) b_i = m` for all `m`. -/
theorem dual_basis_symm {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Basis ι R M)
    (tr : M →ₗ[R] R) (v : ι → M) (hZ : ∀ m, ∑ i, tr (m * B i) • v i = m) (m : M) :
    ∑ i, tr (v i * m) • B i = m := by
  let G : Matrix ι ι R := fun i j => tr (B i * B j)
  let Y : Matrix ι ι R := fun h i => B.repr (v i) h
  have hGY : G * Y.transpose = 1 := by
    ext g h
    have := congrArg (fun m => B.repr m h) (hZ (B g))
    simp only [map_sum, LinearEquiv.map_smul, Finsupp.coe_finset_sum, Finset.sum_apply,
      Finsupp.smul_apply, smul_eq_mul, Basis.repr_self] at this
    rw [Finsupp.single_apply] at this
    rw [Matrix.mul_apply, Matrix.one_apply, ← this]
    rfl
  have hYG : Y.transpose * G = 1 := Matrix.mul_eq_one_comm.1 hGY
  -- the identity on the basis
  have hbasis : ∀ g, ∑ i, tr (v i * B g) • B i = B g := by
    intro g
    have hv : ∀ i, v i = ∑ h, Y h i • B h := fun i => (B.sum_repr (v i)).symm
    have hcoef : ∀ i, tr (v i * B g) = if i = g then 1 else 0 := by
      intro i
      have := congrFun (congrFun hYG i) g
      rw [Matrix.mul_apply, Matrix.one_apply] at this
      rw [← this, hv i, Finset.sum_mul, map_sum]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [smul_mul_assoc, LinearMap.map_smul, smul_eq_mul]
      rfl
    simp only [hcoef, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
  -- extend by linearity
  let F : M →ₗ[R] M := ∑ i, (tr ∘ₗ LinearMap.mulLeft R (v i)).smulRight (B i)
  have hF : ∀ m, F m = ∑ i, tr (v i * m) • B i := fun m => by
    simp [F, LinearMap.sum_apply]
  have : F = LinearMap.id := B.ext fun g => by rw [hF, hbasis, LinearMap.id_apply]
  rw [← hF, this, LinearMap.id_apply]

theorem neg_one_pow_mul_neg_one_pow'' {A : Type*} [CommRing A] {u a : ℕ} (h : u ≤ a) :
    ((-1 : A) ^ u) * (-1) ^ (a - u) = (-1) ^ a := by
  rw [← pow_add, Nat.add_sub_cancel' h]

/-- **The zigzag identity from the trace formula.** Let `M` be free over `R` with basis `ξ^a`,
`a ≤ d`, and let `tr` be the coordinate of `ξ^d`, with `tr(ξ^c) = (-1)^{c-d} ȳ_{c-d}` (`0` for
`c < d`). If `x_u = 0` for `u > d` and `(-ξ)^a = ∑_{u + w = a} x_u ȳ_w` for all `a`, then
`∑_{f ≤ d} (-1)^{d-f} tr(m ξ^f) x_{d-f} = m` for all `m`. -/
theorem zigzag_of_trace {d : ℕ} (B : Basis (Fin (d + 1)) R M) (ξ : M)
    (hB : ∀ a, B a = ξ ^ (a : ℕ)) (tr : M →ₗ[R] R) (y : ℕ → R)
    (htr : ∀ c, tr (ξ ^ c) =
      if d + 1 ≤ c + 1 then (-1) ^ (c + 1 - (d + 1)) * y (c + 1 - (d + 1)) else 0)
    (x : ℕ → M) (hx : ∀ u, d < u → x u = 0)
    (hneg : ∀ a, (-ξ) ^ a = ∑ p ∈ antidiagonal a, x p.1 * algebraMap R M (y p.2)) (m : M) :
    ∑ f ∈ range (d + 1), (-1) ^ (d - f) * algebraMap R M (tr (m * ξ ^ f)) * x (d - f) = m := by
  -- the identity on powers of `ξ`
  have hpow : ∀ a, ∑ f ∈ range (d + 1), (-1) ^ (d - f) * algebraMap R M (tr (ξ ^ a * ξ ^ f)) *
      x (d - f) = ξ ^ a := by
    intro a
    rw [← Finset.sum_range_reflect]
    have hterm : ∀ u ∈ range (d + 1), (-1) ^ (d - (d + 1 - 1 - u)) *
        algebraMap R M (tr (ξ ^ a * ξ ^ (d + 1 - 1 - u))) * x (d - (d + 1 - 1 - u)) =
        (-1) ^ a * (if u ≤ a then x u * algebraMap R M (y (a - u)) else 0) := by
      intro u hu
      have hu' : u ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hu)
      rw [Nat.add_sub_cancel, show d - (d - u) = u by omega, ← pow_add, htr]
      by_cases h : u ≤ a
      · rw [if_pos (by omega), if_pos h, show a + (d - u) + 1 - (d + 1) = a - u by omega,
          map_mul, map_pow, map_neg, map_one]
        have := neg_one_pow_mul_neg_one_pow'' (A := M) h
        linear_combination (x u * algebraMap R M (y (a - u))) * this
      · rw [if_neg (by omega), if_neg h, map_zero, mul_zero, zero_mul, mul_zero]
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    set G : ℕ → M := fun u => if u ≤ a then x u * algebraMap R M (y (a - u)) else 0 with hG
    have h1 : ∑ u ∈ range (d + 1), G u = ∑ u ∈ range (a + d + 1), G u :=
      Finset.sum_subset (Finset.range_subset.2 (by omega)) fun u _ hu => by
        simp only [Finset.mem_range, not_lt] at hu
        simp only [hG, hx u (by omega), zero_mul, ite_self]
    have h2 : ∑ p ∈ antidiagonal a, x p.1 * algebraMap R M (y p.2) =
        ∑ u ∈ range (a + d + 1), G u := by
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        ← Finset.sum_subset (Finset.range_subset.2 (show a + 1 ≤ a + d + 1 by omega))
          fun u _ hu => by
            simp only [Finset.mem_range, not_lt] at hu
            simp only [hG, if_neg (show ¬ u ≤ a by omega)]]
      exact Finset.sum_congr rfl fun u hu => by
        simp only [hG, if_pos (Nat.lt_succ_iff.1 (Finset.mem_range.1 hu))]
    rw [h1, ← h2, ← hneg, ← mul_pow]
    simp
  -- extend by linearity
  let F : M →ₗ[R] M := ∑ f ∈ range (d + 1),
    (tr ∘ₗ LinearMap.mulRight R (ξ ^ f)).smulRight ((-1) ^ (d - f) * x (d - f))
  have hF : ∀ m, F m = ∑ f ∈ range (d + 1), (-1) ^ (d - f) * algebraMap R M (tr (m * ξ ^ f)) *
      x (d - f) := fun m => by
    simp only [F, LinearMap.coeFn_sum, Finset.sum_apply, LinearMap.smulRight_apply,
      LinearMap.comp_apply, LinearMap.mulRight_apply, Algebra.smul_def]
    exact Finset.sum_congr rfl fun f _ => by ring
  have : F = LinearMap.id := B.ext fun a => by rw [hF, hB, hpow, LinearMap.id_apply]
  rw [← hF, this, LinearMap.id_apply]

/-- The second zigzag identity: under the hypotheses of `zigzag_of_trace`,
`∑_{f ≤ d} (-1)^{d-f} ξ^f tr(x_{d-f} m) = m` for all `m`. -/
theorem zigzag_of_trace' {d : ℕ} (B : Basis (Fin (d + 1)) R M) (ξ : M)
    (hB : ∀ a, B a = ξ ^ (a : ℕ)) (tr : M →ₗ[R] R) (y : ℕ → R)
    (htr : ∀ c, tr (ξ ^ c) =
      if d + 1 ≤ c + 1 then (-1) ^ (c + 1 - (d + 1)) * y (c + 1 - (d + 1)) else 0)
    (x : ℕ → M) (hx : ∀ u, d < u → x u = 0)
    (hneg : ∀ a, (-ξ) ^ a = ∑ p ∈ antidiagonal a, x p.1 * algebraMap R M (y p.2)) (m : M) :
    ∑ f ∈ range (d + 1), (-1) ^ (d - f) * ξ ^ f * algebraMap R M (tr (x (d - f) * m)) = m := by
  let v : Fin (d + 1) → M := fun i => (-1) ^ (d - (i : ℕ)) * x (d - i)
  have hsign : ∀ j : ℕ, ((-1 : M) ^ j) = algebraMap R M ((-1) ^ j) := fun j => by
    rw [map_pow, map_neg, map_one]
  have hZ : ∀ m', ∑ i, tr (m' * B i) • v i = m' := by
    intro m'
    conv_rhs => rw [← zigzag_of_trace B ξ hB tr y htr x hx hneg m']
    rw [← Fin.sum_univ_eq_sum_range (fun f => (-1) ^ (d - f) * algebraMap R M (tr (m' * ξ ^ f)) *
      x (d - f)) (d + 1)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hB, Algebra.smul_def]
    ring
  conv_rhs => rw [← dual_basis_symm B tr v hZ m]
  rw [← Fin.sum_univ_eq_sum_range (fun f => (-1) ^ (d - f) * ξ ^ f *
    algebraMap R M (tr (x (d - f) * m))) (d + 1)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hB, Algebra.smul_def]
  have h1 : tr ((-1) ^ (d - (i : ℕ)) * x (d - i) * m) = (-1) ^ (d - (i : ℕ)) * tr (x (d - i) * m) := by
    rw [hsign, mul_assoc, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]
  simp only [v]
  rw [h1, (algebraMap R M).map_mul, ← hsign]
  ring

end Abstract

/-! ### The caps -/

section Caps

variable {k : Type*} [Field k] {V : Type*} [Fintype V] [DecidableEq V] {J : Type*}
  [Fintype J] [DecidableEq J]

section FE

attribute [local instance] midAlgebra

variable (k) in
/-- **The cap `F_i E_i 1_λ → 1_λ`** (KL III Definition 6.1, eq. (6.4)):
`H_{k^{+i}} ⊗_{H_{+_i k}} H_{k^{+i}} → H_k`, `m ⊗ m' ↦ tr(m m')`. -/
def capFE (lab : V → J) (v₀ : V) (j' : J) : CupRing k lab v₀ j' →+ BorelRing k lab :=
  (trR k lab v₀).comp
    (Algebra.TensorProduct.lmul' (BorelRing k (moveLab lab v₀ j'))).toRingHom.toAddMonoidHom

theorem capFE_tmul (lab : V → J) (v₀ : V) (j' : J) (m m' : BorelRing k (splitLab lab v₀)) :
    capFE k lab v₀ j' (m ⊗ₜ m') = trR k lab v₀ (m * m') := by
  simp [capFE, Algebra.TensorProduct.lmul'_apply_tmul]

theorem capFE_mul_tmul (lab : V → J) (v₀ : V) (j' : J) (r : BorelRing k (splitLab lab v₀))
    (t : CupRing k lab v₀ j') :
    capFE k lab v₀ j' ((r ⊗ₜ 1) * t) = trR k lab v₀ (r * Algebra.TensorProduct.lmul'
      (BorelRing k (moveLab lab v₀ j')) t) := by
  simp [capFE, map_mul, Algebra.TensorProduct.lmul'_apply_tmul]

/-- `capFE` is a map of left `H_k`-modules. -/
theorem capFE_left (lab : V → J) (v₀ : V) (j' : J) (r : BorelRing k lab)
    (t : CupRing k lab v₀ j') :
    capFE k lab v₀ j' ((pR k lab v₀ r ⊗ₜ 1) * t) = r * capFE k lab v₀ j' t := by
  rw [capFE_mul_tmul, trR_pR_mul]
  rfl

/-- `capFE` is a map of right `H_k`-modules. -/
theorem capFE_right (lab : V → J) (v₀ : V) (j' : J) (r : BorelRing k lab)
    (t : CupRing k lab v₀ j') :
    capFE k lab v₀ j' ((1 ⊗ₜ pR k lab v₀ r) * t) = r * capFE k lab v₀ j' t := by
  simp only [capFE, AddMonoidHom.comp_apply, AlgHom.toRingHom_eq_coe,
    RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, RingHom.coe_coe, map_mul,
    Algebra.TensorProduct.lmul'_apply_tmul, one_mul]
  exact trR_pR_mul lab v₀ r _

/-- **KL III Definition 6.1, eq. (6.4)**: `ξ^{α₁} ⊗ ξ^{α₂} ↦ (-1)^{α₁+α₂+1-b} x̄(k)_{i+1,α₁+α₂+1-b}`
(zero if `α₁ + α₂ + 1 < b`), `b = k_{i+1} - k_i` the size of the block of `v₀`. -/
theorem capFE_xi (lab : V → J) (v₀ : V) (j' : J) (α₁ α₂ : ℕ) :
    capFE k lab v₀ j' ((xi k lab v₀ ^ α₁) ⊗ₜ (xi k lab v₀ ^ α₂)) =
      if blockCard lab v₀ ≤ α₁ + α₂ + 1 then
        (-1) ^ (α₁ + α₂ + 1 - blockCard lab v₀) *
          xbarB k lab (lab v₀) (α₁ + α₂ + 1 - blockCard lab v₀)
      else 0 := by
  rw [capFE_tmul, ← pow_add, trR_xi_pow]

/-- **Cyclicity of dots on the FE-cap**: a dot slides across the cap,
`cap_FE((m ⊗ 1) t) = cap_FE((1 ⊗ m) t)` for every `m ∈ H_{k^{+i}}` (in particular for `m = ξ`). -/
theorem capFE_slide (lab : V → J) (v₀ : V) (j' : J) (m : BorelRing k (splitLab lab v₀))
    (t : CupRing k lab v₀ j') :
    capFE k lab v₀ j' ((m ⊗ₜ 1) * t) = capFE k lab v₀ j' ((1 ⊗ₜ m) * t) := by
  simp [capFE, map_mul, Algebra.TensorProduct.lmul'_apply_tmul]

end FE

section EF

attribute [local instance] rightAlgebra

variable (k) in
/-- **The cap `E_i F_i 1_μ → 1_μ`** at the weight `μ` of `+_i k` (KL III Definition 6.1,
eq. (6.5)): `H_{k^{+i}} ⊗_{H_k} H_{k^{+i}} → H_{+_i k}`, `m ⊗ m' ↦ tr(m m')`. -/
def capEF (lab : V → J) (v₀ : V) (j' : J) :
    CupRingR (k := k) lab v₀ →+ BorelRing k (moveLab lab v₀ j') :=
  (trL k lab v₀ j').comp
    (Algebra.TensorProduct.lmul' (BorelRing k lab)).toRingHom.toAddMonoidHom

theorem capEF_tmul (lab : V → J) (v₀ : V) (j' : J) (m m' : BorelRing k (splitLab lab v₀)) :
    capEF k lab v₀ j' (m ⊗ₜ m') = trL k lab v₀ j' (m * m') := by
  simp [capEF, Algebra.TensorProduct.lmul'_apply_tmul]

/-- `capEF` is a map of left `H_{+_i k}`-modules. -/
theorem capEF_left (lab : V → J) (v₀ : V) (j' : J) (r : BorelRing k (moveLab lab v₀ j'))
    (t : CupRingR (k := k) lab v₀) :
    capEF k lab v₀ j' ((pL k lab v₀ j' r ⊗ₜ 1) * t) = r * capEF k lab v₀ j' t := by
  simp only [capEF, AddMonoidHom.comp_apply, AlgHom.toRingHom_eq_coe,
    RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, RingHom.coe_coe, map_mul,
    Algebra.TensorProduct.lmul'_apply_tmul, mul_one]
  exact trL_pL_mul lab v₀ j' r _

/-- `capEF` is a map of right `H_{+_i k}`-modules. -/
theorem capEF_right (lab : V → J) (v₀ : V) (j' : J) (r : BorelRing k (moveLab lab v₀ j'))
    (t : CupRingR (k := k) lab v₀) :
    capEF k lab v₀ j' ((1 ⊗ₜ pL k lab v₀ j' r) * t) = r * capEF k lab v₀ j' t := by
  simp only [capEF, AddMonoidHom.comp_apply, AlgHom.toRingHom_eq_coe,
    RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, RingHom.coe_coe, map_mul,
    Algebra.TensorProduct.lmul'_apply_tmul, one_mul]
  exact trL_pL_mul lab v₀ j' r _

/-- **KL III Definition 6.1, eq. (6.5)**: `ξ^{α₁} ⊗ ξ^{α₂} ↦
(-1)^{α₁+α₂+1-b'} x̄(+_i k)_{i,α₁+α₂+1-b'}` (zero if `α₁ + α₂ + 1 < b'`), `b'` the size of block
`i` of `+_i k`. -/
theorem capEF_xi (lab : V → J) (v₀ : V) (j' : J) (α₁ α₂ : ℕ) :
    capEF k lab v₀ j' ((xi k lab v₀ ^ α₁) ⊗ₜ (xi k lab v₀ ^ α₂)) =
      if blockCardL lab v₀ j' ≤ α₁ + α₂ + 1 then
        (-1) ^ (α₁ + α₂ + 1 - blockCardL lab v₀ j') *
          xbarB k (moveLab lab v₀ j') j' (α₁ + α₂ + 1 - blockCardL lab v₀ j')
      else 0 := by
  rw [capEF_tmul, ← pow_add, trL_xi_pow]

/-- **Cyclicity of dots on the EF-cap**: `cap_EF((m ⊗ 1) t) = cap_EF((1 ⊗ m) t)`. -/
theorem capEF_slide (lab : V → J) (v₀ : V) (j' : J) (m : BorelRing k (splitLab lab v₀))
    (t : CupRingR (k := k) lab v₀) :
    capEF k lab v₀ j' ((m ⊗ₜ 1) * t) = capEF k lab v₀ j' ((1 ⊗ₜ m) * t) := by
  simp [capEF, map_mul, Algebra.TensorProduct.lmul'_apply_tmul]

end EF

/-! ### Biadjointness: the zigzag identities -/

section Snakes

attribute [local instance] midAlgebra rightAlgebra

omit [Fintype J] in
theorem blockCardL_eq_dBlock (lab : V → J) (v₀ : V) (j' : J) :
    blockCardL lab v₀ j' = dBlock lab v₀ j' + 1 := by
  rw [blockCardL, labSet_move_eq, if_pos rfl, Finset.card_insert_of_not_mem (v₀_not_mem_split j')]

omit [Fintype J] in
theorem blockCard_eq_dBlockR (lab : V → J) (v₀ : V) :
    blockCard lab v₀ = dBlockR lab v₀ + 1 := by
  have h1 := card_split_some lab v₀ (lab v₀)
  have h2 := blockCard_pos lab v₀
  rw [if_pos rfl] at h1
  simp only [dBlockR, blockCard] at h1 h2 ⊢
  omega

/-- The trace `tr : H_{k^{+i}} → H_{+_i k}` as a linear map, with the basis reindexed by
`Fin (d + 1)`. -/
private theorem snake_data_L (lab : V → J) (v₀ : V) (j' : J) :
    ∃ (B : Basis (Fin (dBlock lab v₀ j' + 1)) (BorelRing k (moveLab lab v₀ j'))
        (BorelRing k (splitLab lab v₀)))
      (tr : BorelRing k (splitLab lab v₀) →ₗ[BorelRing k (moveLab lab v₀ j')]
        BorelRing k (moveLab lab v₀ j')),
      (∀ a, B a = xi k lab v₀ ^ (a : ℕ)) ∧ ∀ y, tr y = trL k lab v₀ j' y :=
  ⟨(basisL k lab v₀ j').reindex (finCongr (blockCardL_eq_dBlock lab v₀ j')),
    (basisL k lab v₀ j').coord ⟨blockCardL lab v₀ j' - 1, by
      rw [blockCardL_eq_dBlock]; omega⟩,
    fun a => by rw [Basis.reindex_apply, basisL_apply]; rfl, fun _ => rfl⟩

private theorem snake_data_R (lab : V → J) (v₀ : V) :
    ∃ (B : Basis (Fin (dBlockR lab v₀ + 1)) (BorelRing k lab) (BorelRing k (splitLab lab v₀)))
      (tr : BorelRing k (splitLab lab v₀) →ₗ[BorelRing k lab] BorelRing k lab),
      (∀ a, B a = xi k lab v₀ ^ (a : ℕ)) ∧ ∀ y, tr y = trR k lab v₀ y :=
  ⟨(basisR k lab v₀).reindex (finCongr (blockCard_eq_dBlockR lab v₀)),
    (basisR k lab v₀).coord ⟨blockCard lab v₀ - 1, by
      rw [blockCard_eq_dBlockR]; omega⟩,
    fun a => by rw [Basis.reindex_apply, basisR_apply]; rfl, fun _ => rfl⟩

/-- **Zigzag identity** `(cap_EF ∘ 1_E) ∘ (1_E ∘ cup_FE) = 1_E` on `E_i 1_λ` (KL III Definition 3.1
via Definition 6.1): for the cup element `∑_f (-1)^{d-f} ξ^f ⊗ x(k)_{i,d-f}` of `F_i E_i 1_λ`,
`∑_f (-1)^{d-f} cap_EF(m ⊗ ξ^f) · x(k)_{i,d-f} = m` for all `m ∈ H_{k^{+i}}`. -/
theorem snake_E_FE (lab : V → J) (v₀ : V) (j' : J) (m : BorelRing k (splitLab lab v₀)) :
    ∑ f ∈ range (dBlock lab v₀ j' + 1), (-1) ^ (dBlock lab v₀ j' - f) *
      pL k lab v₀ j' (capEF k lab v₀ j' (m ⊗ₜ[BorelRing k lab] (xi k lab v₀ ^ f))) *
        xs (k := k) (lab := lab) (v₀ := v₀) j' (dBlock lab v₀ j' - f) = m := by
  obtain ⟨B, tr, hB, htr⟩ := snake_data_L (k := k) lab v₀ j'
  have h := zigzag_of_trace B (xi k lab v₀) hB tr (xbarB k (moveLab lab v₀ j') j')
    (fun c => by rw [htr, trL_xi_pow, blockCardL_eq_dBlock])
    (xs (k := k) (lab := lab) (v₀ := v₀) j') (fun _ hu => xB_eq_zero hu) (neg_xi_pow (j' := j')) m
  simp only [htr, algebraMap_mid] at h
  simpa only [capEF_tmul] using h

/-- **Zigzag identity** `(1_F ∘ cap_EF) ∘ (cup_FE ∘ 1_F) = 1_F` on `F_i 1_{λ+i_X}`:
`∑_f (-1)^{d-f} ξ^f · cap_EF(x(k)_{i,d-f} ⊗ m) = m`. -/
theorem snake_F_FE (lab : V → J) (v₀ : V) (j' : J) (m : BorelRing k (splitLab lab v₀)) :
    ∑ f ∈ range (dBlock lab v₀ j' + 1), (-1) ^ (dBlock lab v₀ j' - f) * xi k lab v₀ ^ f *
      pL k lab v₀ j' (capEF k lab v₀ j'
        (xs (k := k) (lab := lab) (v₀ := v₀) j' (dBlock lab v₀ j' - f) ⊗ₜ[BorelRing k lab] m))
      = m := by
  obtain ⟨B, tr, hB, htr⟩ := snake_data_L (k := k) lab v₀ j'
  have h := zigzag_of_trace' B (xi k lab v₀) hB tr (xbarB k (moveLab lab v₀ j') j')
    (fun c => by rw [htr, trL_xi_pow, blockCardL_eq_dBlock])
    (xs (k := k) (lab := lab) (v₀ := v₀) j') (fun _ hu => xB_eq_zero hu) (neg_xi_pow (j' := j')) m
  simp only [htr, algebraMap_mid] at h
  simpa only [capEF_tmul] using h

/-- **Zigzag identity** `(cap_FE ∘ 1_F) ∘ (1_F ∘ cup_EF) = 1_F` on `F_i 1_μ` (`μ` the weight of
`+_i k`): for the cup element `∑_g (-1)^{d-g} ξ^g ⊗ x(+_i k)_{i+1,d-g}` of `E_i F_i 1_μ`,
`∑_g (-1)^{d-g} cap_FE(m ⊗ ξ^g) · x(+_i k)_{i+1,d-g} = m`. -/
theorem snake_F_EF (lab : V → J) (v₀ : V) (j' : J) (m : BorelRing k (splitLab lab v₀)) :
    ∑ g ∈ range (dBlockR lab v₀ + 1), (-1) ^ (dBlockR lab v₀ - g) *
      pR k lab v₀ (capFE k lab v₀ j' (m ⊗ₜ[BorelRing k (moveLab lab v₀ j')] (xi k lab v₀ ^ g))) *
        xsR (k := k) lab v₀ (dBlockR lab v₀ - g) = m := by
  obtain ⟨B, tr, hB, htr⟩ := snake_data_R (k := k) lab v₀
  have h := zigzag_of_trace B (xi k lab v₀) hB tr (xbarB k lab (lab v₀))
    (fun c => by rw [htr, trR_xi_pow, blockCard_eq_dBlockR])
    (xsR (k := k) lab v₀) (fun _ hu => xB_eq_zero hu) (neg_xi_pow_R lab v₀) m
  simp only [htr, algebraMap_right] at h
  simpa only [capFE_tmul] using h

/-- **Zigzag identity** `(1_E ∘ cap_FE) ∘ (cup_EF ∘ 1_E) = 1_E` on `E_i 1_λ`:
`∑_g (-1)^{d-g} ξ^g · cap_FE(x(+_i k)_{i+1,d-g} ⊗ m) = m`. -/
theorem snake_E_EF (lab : V → J) (v₀ : V) (j' : J) (m : BorelRing k (splitLab lab v₀)) :
    ∑ g ∈ range (dBlockR lab v₀ + 1), (-1) ^ (dBlockR lab v₀ - g) * xi k lab v₀ ^ g *
      pR k lab v₀ (capFE k lab v₀ j'
        (xsR (k := k) lab v₀ (dBlockR lab v₀ - g) ⊗ₜ[BorelRing k (moveLab lab v₀ j')] m)) = m := by
  obtain ⟨B, tr, hB, htr⟩ := snake_data_R (k := k) lab v₀
  have h := zigzag_of_trace' B (xi k lab v₀) hB tr (xbarB k lab (lab v₀))
    (fun c => by rw [htr, trR_xi_pow, blockCard_eq_dBlockR])
    (xsR (k := k) lab v₀) (fun _ hu => xB_eq_zero hu) (neg_xi_pow_R lab v₀) m
  simp only [htr, algebraMap_right] at h
  simpa only [capFE_tmul] using h

end Snakes

end Caps

end Categorification.Flag

end
