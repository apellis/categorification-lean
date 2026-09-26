/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.Free

/-!
# Erratum: KL III Lemma 5.4 (iii) as printed

Khovanov–Lauda III, arXiv:0807.3250v1, Lemma 5.4 (iii), eq. (5.45) (TeX `sln-2008-ArXiv.tex`,
`\begin{lem}\label{lem_relations}`), is printed as: in `H_{k^{+i}} ⊗_{H_{+_i k}} H_{k^{+i}}`,

  `∑_{f=0}^{d} (-1)^{d-f} ξ_i^{f+1} ⊗ x(k)_{i+1,d-f} = ∑_{g=0}^{d} (-1)^{d-g} ξ_i^g ⊗ x(k)_{i+1,d-g} ξ_i`,
  `d = k_i - k_{i-1}`.

Its proof (from part (i)) and its use in Corollary 5.5 concern `x(k)_{i,·}` instead of
`x(k)_{i+1,·}`; the corrected statement is `Categorification.Flag.lemma_5_4_iii`. Here we show
that the printed statement is false, under either reading of the symbol `x(k)_{i+1,β}` in
`H_{k^{+i}}`:

* `lemma_5_4_iii_printed_false` : reading `x(k)_{i+1,β}` as the image `p_1^* x(k)_{i+1,β}` of the
  generator of `H_k` (the right `H_k`-action, KL III's convention in eqs. (5.26)–(5.27));
* `lemma_5_4_iii_printed_false'` : reading it as the canonical generator `x(k^{+i})_{i+1,β}` of
  `H_{k^{+i}}` (`e_β` of block `i + 1` without `ξ_i`).

The counterexample is `N = 2`, `k = (0, 1, 2)` (`n = 2`, `i = 1`, so `d = 1`) over any field of
characteristic `≠ 2`. In the Borel model the variables are `Fin 2`, `k` is the labelling `id`
(blocks `{0}`, `{1}`), `v₀ = 1` moves into block `0`. The two sides are separated by the
`H_{+_i k}`-bilinear form `m ⊗ m' ↦ tr(m) tr(m')` (`tr` the Frobenius trace `trL`), on which they
take the values `-1` and `1`.
-/

noncomputable section

namespace Categorification.Flag

open MvPolynomial TensorProduct
open Finset (univ range)

namespace Erratum545

variable (k : Type*) [Field k]

/-- The labelling of `k = (0, 1, 2)`: two blocks of size one. -/
abbrev lab0 : Fin 2 → Fin 2 := id

/-- `H_{+_i k}` (all variables in block `0`). -/
abbrev R' : Type _ := BorelRing k (moveLab lab0 1 0)

/-- `H_{k^{+i}}`. -/
abbrev M : Type _ := BorelRing k (splitLab lab0 1)

attribute [local instance] midAlgebra

/-- The bilinear form `m ⊗ m' ↦ tr(m) tr(m')` on `H_{k^{+i}} ⊗_{H_{+_i k}} H_{k^{+i}}`. -/
def trForm : M k ⊗[R' k] M k →ₗ[R' k] R' k :=
  TensorProduct.lift ((LinearMap.mul (R' k) (R' k)).compl₁₂
    ((basisL k lab0 1 0).coord ⟨blockCardL lab0 1 0 - 1, by
      have : 0 < blockCardL (lab0 : Fin 2 → Fin 2) 1 0 := by
        rw [blockCardL_eq]; exact blockCard_pos _ _
      omega⟩)
    ((basisL k lab0 1 0).coord ⟨blockCardL lab0 1 0 - 1, by
      have : 0 < blockCardL (lab0 : Fin 2 → Fin 2) 1 0 := by
        rw [blockCardL_eq]; exact blockCard_pos _ _
      omega⟩))

variable {k}

theorem trForm_tmul (m m' : M k) :
    trForm k (m ⊗ₜ m') = trL k lab0 1 0 m * trL k lab0 1 0 m' := rfl

theorem blockCardL_eq_two : blockCardL (lab0 : Fin 2 → Fin 2) 1 0 = 2 := by decide

theorem trL_xi_pow_zero : trL k lab0 1 0 (xi k lab0 1 ^ 0) = 0 := by
  rw [trL_xi_pow, blockCardL_eq_two, if_neg (by omega)]

theorem trL_xi_pow_one : trL k lab0 1 0 (xi k lab0 1 ^ 1) = 1 := by
  rw [trL_xi_pow, blockCardL_eq_two, if_pos (by omega), xbarB_zero]
  simp

theorem xbarB_move_one : xbarB k (moveLab lab0 1 0) 0 1 = 0 := by
  have h : setEsymm (k := k) (labSet (moveLab (lab0 : Fin 2 → Fin 2) 1 0) (· ≠ 0)) 1 = 0 :=
    setEsymm_eq_zero (by decide)
  rw [xbarB, ← map_zero (mkB k _)]
  exact congrArg _ (Subtype.ext h)

theorem trL_xi_pow_two : trL k lab0 1 0 (xi k lab0 1 ^ 2) = 0 := by
  rw [trL_xi_pow, blockCardL_eq_two, if_pos (by omega), show 2 + 1 - 2 = 1 by rfl,
    xbarB_move_one, mul_zero]

theorem xB_split_one_one : xB k (splitLab lab0 1) (some 1) 1 = 0 :=
  xB_eq_zero (by decide)

/-- `p_1^* x(k)_{i+1,1} = ξ`. -/
theorem pR_xB_one : pR k lab0 1 (xB k lab0 1 1) = xi k lab0 1 := by
  have := pR_xB_succ (k := k) (lab := lab0) (v₀ := (1 : Fin 2)) 1 0
  simp only [zero_add] at this
  rw [if_pos (show (1 : Fin 2) = lab0 1 from rfl), xB_split_one_one, xB_zero, zero_add,
    mul_one] at this
  exact this

theorem trL_one : trL k lab0 1 0 (1 : M k) = 0 := by
  rw [← pow_zero (xi k lab0 1)]; exact trL_xi_pow_zero

theorem trL_xi : trL k lab0 1 0 (xi k lab0 1) = 1 := by
  rw [← pow_one (xi k lab0 1)]; exact trL_xi_pow_one

theorem trL_xi_sq : trL k lab0 1 0 (xi k lab0 1 * xi k lab0 1) = 0 := by
  rw [← pow_two]; exact trL_xi_pow_two

theorem two_ne_zero_R' (h2 : (2 : k) ≠ 0) : (2 : R' k) ≠ 0 := by
  haveI : Nontrivial (R' k) := by
    apply Module.nontrivial_of_finrank_pos (R := k)
    have := finrank_borelRing k (moveLab (lab0 : Fin 2 → Fin 2) 1 0)
    rcases Nat.eq_zero_or_pos (Module.finrank k (R' k)) with h | h
    · rw [h, zero_mul] at this
      exact absurd this.symm (Nat.factorial_ne_zero _)
    · exact h
  intro h
  apply h2
  apply (algebraMap k (R' k)).injective
  rw [map_ofNat, h, map_zero]

/-- **KL III Lemma 5.4 (iii), eq. (5.45), as printed, is false** (reading `x(k)_{i+1,β}` as
`p_1^* x(k)_{i+1,β}`): for `N = 2`, `k = (0, 1, 2)`, `d = k_i - k_{i-1} = 1`, over any field of
characteristic `≠ 2`,
`∑_{f=0}^{1} (-1)^{1-f} ξ^{f+1} ⊗ x(k)_{i+1,1-f} ≠ ∑_{g=0}^{1} (-1)^{1-g} ξ^g ⊗ x(k)_{i+1,1-g} ξ`. -/
theorem lemma_5_4_iii_printed_false (h2 : (2 : k) ≠ 0) :
    ∑ f ∈ range (dBlock (lab0 : Fin 2 → Fin 2) 1 0 + 1), (-1 : CupRing k lab0 1 0) ^ (1 - f) *
      ((xi k lab0 1 ^ (f + 1)) ⊗ₜ[R' k] pR k lab0 1 (xB k lab0 1 (1 - f))) ≠
    ∑ g ∈ range (dBlock (lab0 : Fin 2 → Fin 2) 1 0 + 1), (-1 : CupRing k lab0 1 0) ^ (1 - g) *
      ((xi k lab0 1 ^ g) ⊗ₜ[R' k] (pR k lab0 1 (xB k lab0 1 (1 - g)) * xi k lab0 1)) := by
  have hd : dBlock (lab0 : Fin 2 → Fin 2) 1 0 = 1 := by decide
  intro h
  have h' := congrArg (trForm k) h
  rw [hd] at h'
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.sub_self,
    pow_zero, one_mul, pow_one, Nat.sub_zero, map_add] at h'
  rw [xB_zero, map_one, one_mul, pR_xB_one] at h'
  simp only [neg_mul, one_mul, map_neg, trForm_tmul, pow_one, mul_one, pow_two,
    show 1 + 1 = 2 from rfl, trL_one, trL_xi, trL_xi_sq, mul_zero, zero_mul] at h'
  apply two_ne_zero_R' h2
  linear_combination -h'

/-- **KL III Lemma 5.4 (iii), eq. (5.45), as printed, is false** (reading `x(k)_{i+1,β}` as the
canonical generator `x(k^{+i})_{i+1,β}` of `H_{k^{+i}}`), for `N = 2`, `k = (0, 1, 2)`. -/
theorem lemma_5_4_iii_printed_false' (h2 : (2 : k) ≠ 0) :
    ∑ f ∈ range (dBlock (lab0 : Fin 2 → Fin 2) 1 0 + 1), (-1 : CupRing k lab0 1 0) ^ (1 - f) *
      ((xi k lab0 1 ^ (f + 1)) ⊗ₜ[R' k] xB k (splitLab lab0 1) (some 1) (1 - f)) ≠
    ∑ g ∈ range (dBlock (lab0 : Fin 2 → Fin 2) 1 0 + 1), (-1 : CupRing k lab0 1 0) ^ (1 - g) *
      ((xi k lab0 1 ^ g) ⊗ₜ[R' k] (xB k (splitLab lab0 1) (some 1) (1 - g) * xi k lab0 1)) := by
  have hd : dBlock (lab0 : Fin 2 → Fin 2) 1 0 = 1 := by decide
  intro h
  have h' := congrArg (trForm k) h
  rw [hd] at h'
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.sub_self,
    pow_zero, one_mul, pow_one, Nat.sub_zero, map_add] at h'
  rw [xB_zero, xB_split_one_one] at h'
  simp only [neg_mul, one_mul, map_neg, trForm_tmul, tmul_zero, zero_mul, mul_zero, map_zero,
    neg_zero, zero_add, pow_one, mul_one, pow_two, show 1 + 1 = 2 from rfl, trL_one, trL_xi,
    trL_xi_sq] at h'
  apply two_ne_zero_R' h2
  linear_combination -2 * h'

end Erratum545

end Categorification.Flag

end
