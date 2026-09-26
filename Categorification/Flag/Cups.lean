/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.Bimodule

/-!
# Cups in the flag 2-category: KL III Lemma 5.4 and Corollary 5.5

Khovanov–Lauda III, arXiv:0807.3250v1, §5.2.4 (TeX `sln-2008-ArXiv.tex`, "Identities arising from
tensor products"), Lemma 5.4 (i), (iii) and Corollary 5.5 (first map).

We keep the Borel model of `Categorification.Flag.Bimodule`: `lab : V → J`, the variable `v₀`
moves from block `lab v₀` (KL III's `i + 1`) to block `j' ≠ lab v₀` (KL III's `i`);
`M = BorelRing k (splitLab lab v₀)` is `H_{k^{+i}}`, `R = BorelRing k (moveLab lab v₀ j')` is
`H_{+_i k}`, and `M` is an `R`-algebra via `p_2^* = pL` (`midAlgebra`, a local instance). The
ring `M ⊗_R M` is KL III's `H_{k^{+i}} ⊗_{H_{+_i k}} H_{k^{+i}}` (eq. (5.41)), the image of
`F_i E_i 1_k`. We write `x_β = x(k)_{i,β}` for the class of `e_β` of block `j'` without `v₀`
(`xB k (splitLab lab v₀) (some j') β`, the image of `x(k)_{i,β}` under `p_1^*`) and `ξ = ξ_i`.

## Main results

* `neg_xi_pow` : in `H_{k^{+i}}`, `(-ξ)^f = ∑_{a + b = f} x(k)_{i,a} · p_2^* x̄(+_i k)_{i,b}` (the
  algebraic content of KL III eq. (5.31));
* `lemma_5_4_i` : **Lemma 5.4 (i)**, in the sign-free form
  `∑_{a + b = α} (-ξ)^a ⊗ x_b = ∑_{a + b = α} x_a ⊗ (-ξ)^b`, and `lemma_5_4_i_KL` in KL III's form
  `∑_f (-1)^{α-f} ξ^f ⊗ x_{α-f} = ∑_g (-1)^{α-g} x_{α-g} ⊗ ξ^g`;
* `lemma_5_4_iii` : **Lemma 5.4 (iii)**: for `d = k_i - k_{i-1}` (the size of block `i` of `k`),
  `ξ` slides through the cup element: `(ξ ⊗ 1) c = (1 ⊗ ξ) c`, where
  `c = cupElt = ∑_{a + b = d} (-ξ)^a ⊗ x_b` and KL III's cup element is
  `cupEltKL = ∑_f (-1)^{d-f} ξ^f ⊗ x_{d-f} = (-1)^d c` (`cupEltKL_eq`);
* `mem_slideSub` : every element `p_1^* z`, `z ∈ H_k`, slides through `c` (and so does every
  `p_2^* r` and `ξ`);
* `cupEltKL_bimodule` : **Corollary 5.5 (first map)** for a composition: `1 ↦ cupEltKL` defines a
  map of `(H_k, H_k)`-bimodules `H_k → H_{k^{+i}} ⊗_{H_{+_i k}} H_{k^{+i}}`, i.e.
  `(z ⊗ 1) cupEltKL = (1 ⊗ z) cupEltKL` for all `z ∈ H_k`.

**Reading of (5.45).** The printed statement of Lemma 5.4 (iii) has `x(k)_{i+1, k_i-k_{i-1}-f}`;
its proof (from part (i)) and Corollary 5.5 use `x(k)_{i, k_i-k_{i-1}-f}`, and the vanishing
`x(k)_{i, k_i - k_{i-1} + 1} = 0` invoked in the proof is about block `i`. We formalize the version
with `x(k)_{i,·}`. (We have not checked whether the literally printed version also holds.)

Gradings (the degrees `1 + λ_i` of Corollary 5.5) are not treated here.
-/

noncomputable section

namespace Categorification.Flag

open MvPolynomial TensorProduct
open Finset (univ range antidiagonal)

variable (k : Type*) [Field k] {V : Type*} [Fintype V] [DecidableEq V] {J : Type*}
  [DecidableEq J] (lab : V → J) (v₀ : V) (j' : J)

/-- `H_{k^{+i}}` as an `H_{+_i k}`-algebra via `p_2^*`. -/
def midAlgebra : Algebra (BorelRing k (moveLab lab v₀ j')) (BorelRing k (splitLab lab v₀)) :=
  (pL k lab v₀ j').toRingHom.toAlgebra

attribute [local instance] midAlgebra

omit [DecidableEq J] in
theorem algebraMap_mid (r : BorelRing k (moveLab lab v₀ j')) :
    algebraMap (BorelRing k (moveLab lab v₀ j')) (BorelRing k (splitLab lab v₀)) r =
      pL k lab v₀ j' r := rfl

/-- The ring `H_{k^{+i}} ⊗_{H_{+_i k}} H_{k^{+i}}` (KL III eq. (5.41)). -/
abbrev CupRing : Type _ :=
  BorelRing k (splitLab lab v₀) ⊗[BorelRing k (moveLab lab v₀ j')] BorelRing k (splitLab lab v₀)

variable {k lab v₀ j'}

omit [DecidableEq J] in
/-- Elements of `p_2^*(H_{+_i k})` pass through the tensor sign. -/
theorem pL_tmul_one (r : BorelRing k (moveLab lab v₀ j')) :
    (pL k lab v₀ j' r ⊗ₜ[BorelRing k (moveLab lab v₀ j')] (1 : BorelRing k (splitLab lab v₀))) =
      (1 : BorelRing k (splitLab lab v₀)) ⊗ₜ pL k lab v₀ j' r :=
  Algebra.TensorProduct.tmul_one_eq_one_tmul r

/-! ### `(-ξ)^f` in terms of generators of the two outer regions -/

theorem labSet_split_ne_none :
    labSet (splitLab lab v₀) (· ≠ none) = univ.erase v₀ := by
  ext v
  by_cases hv : v = v₀ <;> simp [hv, splitLab_of_ne]

theorem labSet_split_some_union_move_ne :
    labSet (splitLab lab v₀) (· = some j') ∪ labSet (moveLab lab v₀ j') (· ≠ j') =
      labSet (splitLab lab v₀) (· ≠ none) := by
  ext v
  by_cases hv : v = v₀
  · subst hv; simp [moveLab]
  · simp [hv, splitLab_of_ne hv, moveLab, Function.update_of_ne hv, em]

theorem labSet_split_some_disjoint_move_ne :
    Disjoint (labSet (splitLab lab v₀) (· = some j')) (labSet (moveLab lab v₀ j') (· ≠ j')) := by
  rw [Finset.disjoint_left]
  intro v h1 h2
  by_cases hv : v = v₀
  · subst hv; simp at h1
  · simp [hv, splitLab_of_ne hv, moveLab, Function.update_of_ne hv] at h1 h2
    exact h2 h1

omit [DecidableEq V] [DecidableEq J] in
theorem mkB_esymmElt (lab : V → J) (r : ℕ) :
    mkB k lab (esymmElt k lab r) = if r = 0 then 1 else 0 := by
  rcases r with _ | r
  · rw [if_pos rfl, ← map_one (mkB k lab)]
    congr 1
    exact Subtype.ext (esymm_zero _ _)
  · rw [if_neg (Nat.succ_ne_zero r), mkB_eq_zero_iff]
    exact esymmElt_succ_mem lab r

/-- **`(-ξ)^f = ∑_{a + b = f} x(k)_{i,a} · p_2^* x̄(+_i k)_{i,b}`** in `H_{k^{+i}}` (the algebraic
content of KL III eqs. (5.30), (5.31)). -/
theorem neg_xi_pow (f : ℕ) :
    (-xi k lab v₀) ^ f = ∑ p ∈ antidiagonal f, xB k (splitLab lab v₀) (some j') p.1 *
      pL k lab v₀ j' (xbarB k (moveLab lab v₀ j') j' p.2) := by
  set W := labSet (splitLab lab v₀) (· ≠ none)
  have hW : setEsymm (k := k) W f ∈ labelInvariants k (splitLab lab v₀) :=
    setEsymm_labSet_mem _ _ _
  -- `e_f(V ∖ v₀) ≡ (-ξ)^f`
  have hW' : W = univ.erase v₀ := labSet_split_ne_none
  have h1 : mkB k _ ⟨setEsymm W f, hW⟩ = (-xi k lab v₀) ^ f := by
    have hins : insert v₀ W = univ := by
      rw [hW', Finset.insert_erase (Finset.mem_univ _)]
    have hs := setEsymm_eq_sum_insert (k := k) (s := W) (v := v₀)
      (by rw [hW']; simp) f
    rw [hins] at hs
    have : (⟨setEsymm W f, hW⟩ : labelInvariants k (splitLab lab v₀)) =
        ∑ h ∈ range (f + 1), (-(⟨X v₀, X_mem_split k lab v₀⟩ :
          labelInvariants k (splitLab lab v₀))) ^ h * esymmElt k _ (f - h) := by
      apply Subtype.ext
      simp only [AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul, SubmonoidClass.coe_pow,
        NegMemClass.coe_neg, esymmElt]
      rw [hs]
      rfl
    rw [this, map_sum]
    simp only [map_mul, map_pow, map_neg, mkB_esymmElt]
    rw [Finset.sum_eq_single f]
    · simp [xi]
    · intro h hh hne
      have : f - h ≠ 0 := by have := Finset.mem_range.1 hh; omega
      simp [this]
    · intro h; exact absurd (Finset.self_mem_range_succ f) h
  -- `e_f(V ∖ v₀) = ∑ e_a(block j' ∖ v₀) e_b(V ∖ (block j' ∪ v₀))`
  have h2 : mkB k _ ⟨setEsymm W f, hW⟩ = ∑ p ∈ antidiagonal f,
      xB k (splitLab lab v₀) (some j') p.1 *
        pL k lab v₀ j' (xbarB k (moveLab lab v₀ j') j' p.2) := by
    have hD : ∀ b, setEsymm (k := k) (labSet (moveLab lab v₀ j') (· ≠ j')) b ∈
        labelInvariants k (splitLab lab v₀) := fun b =>
      labelInvariants_mono k (refines_splitLab_move lab v₀ j') (setEsymm_labSet_mem _ _ _)
    have hpL : ∀ b, pL k lab v₀ j' (xbarB k (moveLab lab v₀ j') j' b) =
        mkB k _ ⟨_, hD b⟩ := fun b => pL_mk k _ _ rfl
    have : (⟨setEsymm W f, hW⟩ : labelInvariants k (splitLab lab v₀)) =
        ∑ p ∈ antidiagonal f, blockElt k (splitLab lab v₀) (some j') p.1 * ⟨_, hD p.2⟩ := by
      apply Subtype.ext
      simp only [AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul, blockElt]
      change setEsymm (labSet (splitLab lab v₀) (· ≠ none)) f = _
      rw [← labSet_split_some_union_move_ne, setEsymm_union labSet_split_some_disjoint_move_ne]
    rw [this, map_sum]
    simp only [map_mul, hpL]
    rfl
  rw [← h1, h2]

/-! ### Lemma 5.4 (i) -/

/-- The truncated generating polynomial `∑_{β ≤ n} u_β t^β`. -/
def ser {R : Type*} [CommRing R] (n : ℕ) (u : ℕ → R) : Polynomial R :=
  ∑ β ∈ range (n + 1), Polynomial.C (u β) * Polynomial.X ^ β

theorem coeff_ser {R : Type*} [CommRing R] (n : ℕ) (u : ℕ → R) (β : ℕ) :
    (ser n u).coeff β = if β ≤ n then u β else 0 := by
  rw [ser, Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Nat.lt_succ_iff]

theorem coeff_ser_mul {R : Type*} [CommRing R] {n f : ℕ} (hf : f ≤ n) (u w : ℕ → R) :
    (ser n u * ser n w).coeff f = ∑ p ∈ antidiagonal f, u p.1 * w p.2 := by
  rw [Polynomial.coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [coeff_ser, coeff_ser, if_pos ((Finset.antidiagonal.fst_le hp).trans hf),
    if_pos ((Finset.antidiagonal.snd_le hp).trans hf)]

variable (j') in
/-- `x_β = x(k)_{i,β}` in `H_{k^{+i}}`. -/
abbrev xs (β : ℕ) : BorelRing k (splitLab lab v₀) := xB k (splitLab lab v₀) (some j') β

/-- **KL III Lemma 5.4 (i)** (sign-free form): in `H_{k^{+i}} ⊗_{H_{+_i k}} H_{k^{+i}}`,
`∑_{a + b = α} (-ξ)^a ⊗ x_b = ∑_{a + b = α} x_a ⊗ (-ξ)^b`. -/
theorem lemma_5_4_i (α : ℕ) :
    ∑ p ∈ antidiagonal α, (((-xi k lab v₀) ^ p.1) ⊗ₜ[BorelRing k (moveLab lab v₀ j')]
      xs (k := k) (lab := lab) (v₀ := v₀) j' p.2) =
    ∑ p ∈ antidiagonal α, (xs (k := k) (lab := lab) (v₀ := v₀) j' p.1 ⊗ₜ[BorelRing k (moveLab lab v₀ j')]
      ((-xi k lab v₀) ^ p.2)) := by
  set T := CupRing k lab v₀ j'
  let y : ℕ → BorelRing k (splitLab lab v₀) := fun b =>
    pL k lab v₀ j' (xbarB k (moveLab lab v₀ j') j' b)
  let u : ℕ → T := fun a => xs j' a ⊗ₜ 1
  let w : ℕ → T := fun b => y b ⊗ₜ 1
  let u' : ℕ → T := fun c => 1 ⊗ₜ xs j' c
  have hw : ∀ b, w b = 1 ⊗ₜ y b := fun b => pL_tmul_one _
  have hPQ : ∀ f ≤ α, (ser α u * ser α w).coeff f = ((-xi k lab v₀) ^ f) ⊗ₜ 1 := by
    intro f hf
    rw [coeff_ser_mul hf, neg_xi_pow (j' := j') f, sum_tmul]
    refine Finset.sum_congr rfl fun p _ => ?_
    show (xs j' p.1 ⊗ₜ 1) * (y p.2 ⊗ₜ 1) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  have hQP : ∀ q ≤ α, (ser α w * ser α u').coeff q = 1 ⊗ₜ ((-xi k lab v₀) ^ q) := by
    intro q hq
    rw [coeff_ser_mul hq, neg_xi_pow (j' := j') q, tmul_sum,
      ← Finset.Nat.sum_antidiagonal_swap]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hw]
    show ((1 : BorelRing k (splitLab lab v₀)) ⊗ₜ y p.2) * (1 ⊗ₜ xs j' p.1) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm]
  calc ∑ p ∈ antidiagonal α, (((-xi k lab v₀) ^ p.1) ⊗ₜ[BorelRing k (moveLab lab v₀ j')]
        xs (k := k) (lab := lab) (v₀ := v₀) j' p.2)
      = ∑ p ∈ antidiagonal α, (ser α u * ser α w).coeff p.1 * (ser α u').coeff p.2 := by
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [hPQ p.1 (Finset.antidiagonal.fst_le hp), coeff_ser,
          if_pos (Finset.antidiagonal.snd_le hp)]
        show _ = (((-xi k lab v₀) ^ p.1) ⊗ₜ 1) * (1 ⊗ₜ xs j' p.2)
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    _ = (ser α u * ser α w * ser α u').coeff α := (Polynomial.coeff_mul _ _ _).symm
    _ = (ser α u * (ser α w * ser α u')).coeff α := by rw [mul_assoc]
    _ = ∑ p ∈ antidiagonal α, (ser α u).coeff p.1 * (ser α w * ser α u').coeff p.2 :=
        Polynomial.coeff_mul _ _ _
    _ = _ := by
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [hQP p.2 (Finset.antidiagonal.snd_le hp), coeff_ser,
          if_pos (Finset.antidiagonal.fst_le hp)]
        show (xs j' p.1 ⊗ₜ 1) * (1 ⊗ₜ ((-xi k lab v₀) ^ p.2)) = _
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem neg_one_pow_tmul_one {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (f : ℕ) :
    ((-1 : A) ^ f) ⊗ₜ[R] (1 : A) = (-1) ^ f := by
  calc ((-1 : A) ^ f) ⊗ₜ[R] (1 : A) = ((-1 : A) ^ f) ⊗ₜ[R] ((1 : A) ^ f) := by rw [one_pow]
    _ = ((-1 : A) ⊗ₜ[R] (1 : A)) ^ f := (Algebra.TensorProduct.tmul_pow _ _ _).symm
    _ = (-1) ^ f := by rw [neg_tmul, ← Algebra.TensorProduct.one_def]

theorem one_tmul_neg_one_pow {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (f : ℕ) :
    (1 : A) ⊗ₜ[R] ((-1 : A) ^ f) = (-1) ^ f := by
  calc (1 : A) ⊗ₜ[R] ((-1 : A) ^ f) = ((1 : A) ^ f) ⊗ₜ[R] ((-1 : A) ^ f) := by rw [one_pow]
    _ = ((1 : A) ⊗ₜ[R] (-1 : A)) ^ f := (Algebra.TensorProduct.tmul_pow _ _ _).symm
    _ = (-1) ^ f := by rw [tmul_neg, ← Algebra.TensorProduct.one_def]

theorem neg_one_pow_mul_neg_one_pow {A : Type*} [CommRing A] {α f : ℕ} (h : f ≤ α) :
    ((-1 : A) ^ α) * (-1) ^ f = (-1) ^ (α - f) := by
  rw [← pow_add, show α + f = (α - f) + 2 * f by omega, pow_add, pow_mul]
  simp

/-- `(-1)^α ∑_{a + b = α} (-ξ)^a ⊗ y_b = ∑_{f ≤ α} (-1)^{α-f} ξ^f ⊗ y_{α-f}`. -/
theorem neg_one_pow_mul_sum_tmul {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (ξ : A) (y : ℕ → A) (α : ℕ) :
    (-1) ^ α * ∑ p ∈ antidiagonal α, (((-ξ) ^ p.1) ⊗ₜ[R] y p.2) =
      ∑ f ∈ range (α + 1), (-1) ^ (α - f) * ((ξ ^ f) ⊗ₜ[R] y (α - f)) := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.mul_sum]
  refine Finset.sum_congr rfl fun f hf => ?_
  have hf' : f ≤ α := Nat.lt_succ_iff.1 (Finset.mem_range.1 hf)
  have : (((-ξ) ^ f) ⊗ₜ[R] y (α - f)) = (-1) ^ f * ((ξ ^ f) ⊗ₜ[R] y (α - f)) := by
    rw [← neg_one_pow_tmul_one, Algebra.TensorProduct.tmul_mul_tmul, one_mul, neg_pow]
  rw [this, ← mul_assoc, neg_one_pow_mul_neg_one_pow hf']

/-- The mirror image of `neg_one_pow_mul_sum_tmul`. -/
theorem neg_one_pow_mul_sum_tmul' {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (ξ : A) (y : ℕ → A) (α : ℕ) :
    (-1) ^ α * ∑ p ∈ antidiagonal α, (y p.1 ⊗ₜ[R] ((-ξ) ^ p.2)) =
      ∑ g ∈ range (α + 1), (-1) ^ (α - g) * (y (α - g) ⊗ₜ[R] (ξ ^ g)) := by
  rw [← Finset.Nat.sum_antidiagonal_swap, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun g hg => ?_
  have hg' : g ≤ α := Nat.lt_succ_iff.1 (Finset.mem_range.1 hg)
  simp only [Prod.fst_swap, Prod.snd_swap]
  have : (y (α - g) ⊗ₜ[R] ((-ξ) ^ g)) = (-1) ^ g * (y (α - g) ⊗ₜ[R] (ξ ^ g)) := by
    rw [← one_tmul_neg_one_pow, Algebra.TensorProduct.tmul_mul_tmul, one_mul, neg_pow]
  rw [this, ← mul_assoc, neg_one_pow_mul_neg_one_pow hg']

/-- **KL III Lemma 5.4 (i), eq. (5.43)** as printed:
`∑_{f=0}^{α} (-1)^{α-f} ξ^f ⊗ x(k)_{i,α-f} = ∑_{g=0}^{α} (-1)^{α-g} x(k)_{i,α-g} ⊗ ξ^g`. -/
theorem lemma_5_4_i_KL (α : ℕ) :
    ∑ f ∈ range (α + 1), (-1) ^ (α - f) * ((xi k lab v₀ ^ f) ⊗ₜ[BorelRing k (moveLab lab v₀ j')]
      xs (k := k) (lab := lab) (v₀ := v₀) j' (α - f)) =
    ∑ g ∈ range (α + 1), (-1) ^ (α - g) * (xs (k := k) (lab := lab) (v₀ := v₀) j' (α - g)
      ⊗ₜ[BorelRing k (moveLab lab v₀ j')] (xi k lab v₀ ^ g)) := by
  rw [← neg_one_pow_mul_sum_tmul, ← neg_one_pow_mul_sum_tmul', lemma_5_4_i]

/-! ### Lemma 5.4 (iii) -/

variable (lab v₀ j') in
/-- `d = k_i - k_{i-1}`: the size of block `i` of `k` (block `j'` of `lab`, without `v₀`). -/
abbrev dBlock : ℕ := (labSet (splitLab lab v₀) (· = some j')).card

variable (k lab v₀ j') in
/-- The cup element (sign-free): `c = ∑_{a + b = d} (-ξ)^a ⊗ x_b`. -/
def cupElt : CupRing k lab v₀ j' :=
  ∑ p ∈ antidiagonal (dBlock lab v₀ j'), (((-xi k lab v₀) ^ p.1) ⊗ₜ xs j' p.2)

variable (k lab v₀ j') in
/-- **KL III's cup element** (Corollary 5.5): `∑_{f=0}^{d} (-1)^{d-f} ξ^f ⊗ x(k)_{i,d-f}`. -/
def cupEltKL : CupRing k lab v₀ j' :=
  ∑ f ∈ range (dBlock lab v₀ j' + 1),
    (-1) ^ (dBlock lab v₀ j' - f) * ((xi k lab v₀ ^ f) ⊗ₜ xs j' (dBlock lab v₀ j' - f))

theorem cupEltKL_eq : cupEltKL k lab v₀ j' = (-1) ^ dBlock lab v₀ j' * cupElt k lab v₀ j' :=
  (neg_one_pow_mul_sum_tmul _ _ _).symm

theorem xs_dBlock_succ : xs (k := k) (lab := lab) (v₀ := v₀) j' (dBlock lab v₀ j' + 1) = 0 :=
  xB_eq_zero (Nat.lt_succ_self _)

/-- **KL III Lemma 5.4 (iii), eq. (5.45)** (with `x(k)_{i,·}`, see the module docstring): `ξ`
slides through the cup element, `(ξ ⊗ 1) c = (1 ⊗ ξ) c`. -/
theorem lemma_5_4_iii :
    (xi k lab v₀ ⊗ₜ 1) * cupElt k lab v₀ j' = (1 ⊗ₜ xi k lab v₀) * cupElt k lab v₀ j' := by
  set d := dBlock lab v₀ j'
  have hL : (xi k lab v₀ ⊗ₜ 1) * cupElt k lab v₀ j' =
      -∑ p ∈ antidiagonal (d + 1), (((-xi k lab v₀) ^ p.1) ⊗ₜ[BorelRing k (moveLab lab v₀ j')]
        xs (k := k) (lab := lab) (v₀ := v₀) j' p.2) := by
    rw [Finset.Nat.sum_antidiagonal_succ, xs_dBlock_succ, tmul_zero, zero_add, cupElt,
      Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, pow_succ (-xi k lab v₀) p.1, mul_neg,
      neg_tmul, neg_neg, mul_comm (xi k lab v₀)]
  have hR : (1 ⊗ₜ xi k lab v₀) * cupElt k lab v₀ j' =
      -∑ p ∈ antidiagonal (d + 1), (xs (k := k) (lab := lab) (v₀ := v₀) j' p.1
        ⊗ₜ[BorelRing k (moveLab lab v₀ j')] ((-xi k lab v₀) ^ p.2)) := by
    rw [Finset.Nat.sum_antidiagonal_succ', xs_dBlock_succ, zero_tmul, zero_add, cupElt,
      lemma_5_4_i, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, pow_succ (-xi k lab v₀) p.2, mul_neg,
      tmul_neg, neg_neg, mul_comm (xi k lab v₀)]
  rw [hL, hR, lemma_5_4_i]

/-! ### Sliding through the cup -/

variable (k lab v₀ j') in
/-- The elements `m ∈ H_{k^{+i}}` with `(m ⊗ 1) c = (1 ⊗ m) c`. -/
def slideSub : Subalgebra k (BorelRing k (splitLab lab v₀)) where
  carrier := {m | (m ⊗ₜ 1) * cupElt k lab v₀ j' = (1 ⊗ₜ m) * cupElt k lab v₀ j'}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    have h1 : (a * b) ⊗ₜ[BorelRing k (moveLab lab v₀ j')] (1 : BorelRing k (splitLab lab v₀)) =
        (a ⊗ₜ 1) * (b ⊗ₜ 1) := by rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    have h2 : (1 : BorelRing k (splitLab lab v₀)) ⊗ₜ[BorelRing k (moveLab lab v₀ j')] (a * b) =
        (1 ⊗ₜ a) * (1 ⊗ₜ b) := by rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    calc (a * b) ⊗ₜ[BorelRing k (moveLab lab v₀ j')] (1 : BorelRing k (splitLab lab v₀)) *
          cupElt k lab v₀ j'
        = (a ⊗ₜ 1) * ((b ⊗ₜ 1) * cupElt k lab v₀ j') := by rw [h1, mul_assoc]
      _ = (a ⊗ₜ 1) * ((1 ⊗ₜ b) * cupElt k lab v₀ j') := by rw [hb]
      _ = (1 ⊗ₜ b) * ((a ⊗ₜ 1) * cupElt k lab v₀ j') := by ring
      _ = (1 ⊗ₜ b) * ((1 ⊗ₜ a) * cupElt k lab v₀ j') := by rw [ha]
      _ = _ := by rw [h2]; ring
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [add_tmul, tmul_add, add_mul, add_mul, ha, hb]
  algebraMap_mem' r := by
    simp only [Set.mem_setOf_eq]
    rw [← (pL k lab v₀ j').commutes r, pL_tmul_one]

theorem pL_mem_slideSub (r : BorelRing k (moveLab lab v₀ j')) :
    pL k lab v₀ j' r ∈ slideSub k lab v₀ j' := by
  change _ * _ = _ * _
  rw [pL_tmul_one]

theorem xi_mem_slideSub : xi k lab v₀ ∈ slideSub k lab v₀ j' := lemma_5_4_iii

/-- The inverse relation for the block receiving `v₀`:
`x(k^{+i})_{j',β} = ∑_{f ≤ β} (-ξ)^f p_2^* x(+_i k)_{j',β-f}`. -/
theorem xB_split_eq_sum_move (β : ℕ) :
    xB k (splitLab lab v₀) (some j') β =
      ∑ f ∈ range (β + 1), (-xi k lab v₀) ^ f * pL k lab v₀ j' (xB k (moveLab lab v₀ j') j' (β - f)) := by
  have hs := setEsymm_eq_sum_insert (k := k) (v₀_not_mem_split (lab := lab) (v₀ := v₀) j') β
  have hset : insert v₀ (labSet (splitLab lab v₀) (· = some j')) = labSet (moveLab lab v₀ j') (· = j') :=
    ((labSet_move_eq (lab := lab) (v₀ := v₀) (j' := j') j').trans (if_pos rfl)).symm
  rw [hset] at hs
  have : ∀ f, pL k lab v₀ j' (xB k (moveLab lab v₀ j') j' (β - f)) =
      mkB k _ ⟨setEsymm (labSet (moveLab lab v₀ j') (· = j')) (β - f),
        labelInvariants_mono k (refines_splitLab_move lab v₀ j')
          (blockElt k (moveLab lab v₀ j') j' (β - f)).2⟩ :=
    fun f => pL_mk k _ _ rfl
  simp only [this, xi, ← map_neg, ← map_pow, ← map_mul, ← map_sum]
  rw [xB]
  congr 1
  apply Subtype.ext
  simp only [blockElt, AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul,
    SubmonoidClass.coe_pow, NegMemClass.coe_neg]
  exact hs

/-- **Every `p_1^*(x(k)_{j,β})` slides through the cup** (for `j' ≠ lab v₀`). -/
theorem pR_xB_mem_slideSub (hj : j' ≠ lab v₀) (j : J) (β : ℕ) :
    pR k lab v₀ (xB k lab j β) ∈ slideSub k lab v₀ j' := by
  by_cases h1 : j = lab v₀
  · subst h1
    rcases β with _ | β
    · rw [xB_zero, map_one]; exact Subalgebra.one_mem _
    · rw [pR_xB_succ, if_pos rfl, ← pL_xB k _ (Ne.symm hj), ← pL_xB k _ (Ne.symm hj)]
      exact Subalgebra.add_mem _ (pL_mem_slideSub _)
        (Subalgebra.mul_mem _ xi_mem_slideSub (pL_mem_slideSub _))
  · rw [pR_xB k j h1]
    by_cases h2 : j = j'
    · subst h2
      rw [xB_split_eq_sum_move]
      exact Subalgebra.sum_mem _ fun f _ => Subalgebra.mul_mem _
        (Subalgebra.pow_mem _ (Subalgebra.neg_mem _ xi_mem_slideSub) _) (pL_mem_slideSub _)
    · rw [← pL_xB k j h2]
      exact pL_mem_slideSub _

/-! ### Corollary 5.5 for compositions -/

section Composition

variable {K : Type*} [Field K] {m : ℕ}

omit [DecidableEq J] in
/-- `H_k` is generated by the `x(k)_{j,α}`. -/
theorem adjoin_x {n : ℕ} (d : Fin n → ℕ) :
    Algebra.adjoin K (Set.range fun p : Fin n × ℕ => x K d p.1 p.2) = ⊤ := by
  rw [eq_top_iff]
  rintro z -
  obtain ⟨F, rfl⟩ := mkH_surjective K d z
  induction F using MvPolynomial.induction_on with
  | C a => rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]; exact Subalgebra.algebraMap_mem _ a
  | add p q hp hq => rw [map_add]; exact Subalgebra.add_mem _ hp hq
  | mul_X p v hp =>
    rw [map_mul]
    refine Subalgebra.mul_mem _ hp (Algebra.subset_adjoin ⟨(v.1, v.2 + 1), ?_⟩)
    change mkH K d (xgen K d v.1 (v.2 + 1)) = _
    rw [xgen_succ v.2.2]

/-- **KL III Corollary 5.5 (first map)**: for block sizes `d` and a vertex `i` with
`d_{i+1} > 0`, the assignment `1 ↦ ∑_{f=0}^{d_i} (-1)^{d_i - f} ξ^f ⊗ x(k)_{i,d_i - f}` is a map of
`(H_k, H_k)`-bimodules `H_k → H_{k^{+i}} ⊗_{H_{+_i k}} H_{k^{+i}}`: for every `z ∈ H_k`,
`(z ⊗ 1) · cup = (1 ⊗ z) · cup`. -/
theorem cupEltKL_bimodule (i : Fin m) (d : Fin (m + 1) → ℕ) (h : 0 < d i.succ) (z : H K d) :
    (eRight K i d h z ⊗ₜ 1) *
        cupEltKL K (Sigma.fst : Gen d → Fin (m + 1)) (movedVar i d h) i.castSucc =
      (1 ⊗ₜ eRight K i d h z) *
        cupEltKL K (Sigma.fst : Gen d → Fin (m + 1)) (movedVar i d h) i.castSucc := by
  have hj : i.castSucc ≠ (Sigma.fst : Gen d → Fin (m + 1)) (movedVar i d h) :=
    (Fin.castSucc_lt_succ i).ne
  have hz : eRight K i d h z ∈ (slideSub K (Sigma.fst : Gen d → Fin (m + 1)) (movedVar i d h)
      i.castSucc : Subalgebra K (ERing K i d h)) := by
    have hle : Algebra.adjoin K (Set.range fun p : Fin (m + 1) × ℕ => x K d p.1 p.2) ≤
        (slideSub K (Sigma.fst : Gen d → Fin (m + 1)) (movedVar i d h) i.castSucc).comap
          (eRight K i d h) := by
      rw [Algebra.adjoin_le_iff]
      rintro _ ⟨p, rfl⟩
      rw [SetLike.mem_coe, Subalgebra.mem_comap, eRight, AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe, hEquiv_x]
      exact pR_xB_mem_slideSub hj p.1 p.2
    rw [adjoin_x] at hle
    exact hle Algebra.mem_top
  rw [cupEltKL_eq, mul_left_comm, hz, mul_left_comm]

end Composition

end Categorification.Flag

end
