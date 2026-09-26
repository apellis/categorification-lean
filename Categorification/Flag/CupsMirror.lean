/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.Free

/-!
# The other cup: KL III Lemma 5.4 (ii), (iv) and Corollary 5.5 (second map)

Khovanov–Lauda III, arXiv:0807.3250v1, §5.2.4 (TeX `sln-2008-ArXiv.tex`, "Identities arising from
tensor products"), Lemma 5.4 (ii), (iv) (eqs. (5.44), (5.46)) and Corollary 5.5.

`Categorification.Flag.Cups` treats the ring `H_{k^{+i}} ⊗_{H_{+_i k}} H_{k^{+i}}` (the image of
`F_i E_i 1_k`), with `H_{+_i k}` acting through `p_2^* = pL`. Here we treat the ring
`H_{k^{+i}} ⊗_{H_k} H_{k^{+i}}` with `H_k` acting through `p_1^* = pR` (`rightAlgebra`), the image
of `E_i F_i 1_{+_i k}`: in KL III's notation this is `H_{-_i k'^{+i}} ⊗_{H_{k'-i}} H_{-_i k'^{+i}}`
for `k' = +_i k`, and `x(k')_{i+1,β}` is the class of `e_β` of the block of `v₀` without `v₀`
(`xB k (splitLab lab v₀) (some (lab v₀)) β`).

All statements are obtained from those of `Categorification.Flag.Cups` by the relabelling
`lab ↦ moveLab lab v₀ (lab v₀) = lab` (`j' = lab v₀`): the generic versions (`*_gen`) are stated
for an arbitrary labelling `S` equal to `splitLab A v₀` and `L` equal to `moveLab A v₀ j'`, and
proved by substitution.

## Main results

* `neg_xi_pow_R` : `(-ξ)^f = ∑_{a + b = f} x(k')_{i+1,a} · p_1^* x̄(k)_{i+1,b}` (the mirror of
  KL III eq. (5.30));
* `lemma_5_4_ii` : **Lemma 5.4 (ii), eq. (5.44)**:
  `∑_f (-1)^{α-f} ξ^f ⊗ x(k')_{i+1,α-f} = ∑_g (-1)^{α-g} x(k')_{i+1,α-g} ⊗ ξ^g`;
* `lemma_5_4_iv` : **Lemma 5.4 (iv), eq. (5.46)**, as printed: `ξ` slides through the cup element
  `∑_{f ≤ d} (-1)^{d-f} ξ^f ⊗ x(k')_{i+1,d-f}`, `d = k'_{i+1} - k'_i`;
* `cupR_bimodule` : **Corollary 5.5 (second map)**: `1 ↦ ∑_g (-1)^{d-g} ξ^g ⊗ x(k')_{i+1,d-g}` is a
  map of `(H_{k'}, H_{k'})`-bimodules `H_{k'} → H_{k'^{-i}} ⊗_{H_{k'-i}} H_{k'^{-i}}` (every element of
  `H_{k'} = H_{+_i k}`, acting through `p_2^*`, slides through the cup element);
* `cupL_bimodule` : Corollary 5.5 (first map) for an arbitrary labelling (finitely many labels),
  generalizing `cupEltKL_bimodule`.

Gradings (the degrees `1 ± λ_i` of Corollary 5.5) are not treated.
-/

noncomputable section

namespace Categorification.Flag

open MvPolynomial TensorProduct
open Finset (univ range antidiagonal)

/-! ### Elements sliding through a tensor -/

section Slide

variable {R M : Type*} [CommRing R] [CommRing M] [Algebra R M]

/-- For `c ∈ M ⊗_R M`, the elements `m` with `(m ⊗ 1) c = (1 ⊗ m) c` (those sliding through `c`). -/
def slideSubring (c : M ⊗[R] M) : Subring M where
  carrier := {m | (m ⊗ₜ[R] (1 : M)) * c = ((1 : M) ⊗ₜ[R] m) * c}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    have h1 : (a * b) ⊗ₜ[R] (1 : M) = (a ⊗ₜ 1) * (b ⊗ₜ 1) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    have h2 : (1 : M) ⊗ₜ[R] (a * b) = (1 ⊗ₜ a) * (1 ⊗ₜ b) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    calc (a * b) ⊗ₜ[R] (1 : M) * c = (a ⊗ₜ 1) * ((b ⊗ₜ 1) * c) := by rw [h1, mul_assoc]
      _ = (a ⊗ₜ 1) * ((1 ⊗ₜ b) * c) := by rw [hb]
      _ = (1 ⊗ₜ b) * ((a ⊗ₜ 1) * c) := by ring
      _ = (1 ⊗ₜ b) * ((1 ⊗ₜ a) * c) := by rw [ha]
      _ = _ := by rw [h2]; ring
  one_mem' := rfl
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [add_tmul, tmul_add, add_mul, add_mul, ha, hb]
  zero_mem' := by
    simp only [Set.mem_setOf_eq, zero_tmul, tmul_zero]
  neg_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [neg_tmul, tmul_neg, neg_mul, neg_mul, ha]

theorem mem_slideSubring {c : M ⊗[R] M} {m : M} :
    m ∈ slideSubring c ↔ (m ⊗ₜ[R] (1 : M)) * c = ((1 : M) ⊗ₜ[R] m) * c := Iff.rfl

theorem algebraMap_mem_slideSubring (c : M ⊗[R] M) (r : R) :
    algebraMap R M r ∈ slideSubring c := by
  rw [mem_slideSubring, Algebra.TensorProduct.tmul_one_eq_one_tmul]

end Slide

section Generic

variable (k : Type*) [Field k] {V : Type*} [Fintype V] [DecidableEq V] {J : Type*}
  [DecidableEq J]

omit [Fintype V] [DecidableEq J] in
theorem lab_eq_moveLab_self (lab : V → J) (v₀ : V) : lab = moveLab lab v₀ (lab v₀) :=
  (Function.update_eq_self v₀ lab).symm

omit [Fintype V] [DecidableEq J] in
theorem lab_eq_moveLab_moveLab (lab : V → J) (v₀ : V) (j' : J) :
    lab = moveLab (moveLab lab v₀ j') v₀ (lab v₀) := by
  rw [moveLab, moveLab, Function.update_idem, Function.update_eq_self]

variable {k}

/-- Generic form of `neg_xi_pow`. -/
theorem neg_xi_pow_gen (A : V → J) (v₀ : V) (j' : J) (S : V → Option J) (L : V → J)
    (hS : S = splitLab A v₀) (hL : L = moveLab A v₀ j') (h : Refines S L)
    (hv : ∀ w, S w = S v₀ → w = v₀) (f : ℕ) :
    (-xiS k S v₀ hv) ^ f = ∑ p ∈ antidiagonal f, xB k S (some j') p.1 *
      refineHom k h (xbarB k L j' p.2) := by
  subst hS hL
  exact neg_xi_pow f

/-- Generic form of `lemma_5_4_i_KL`. -/
theorem lemma_5_4_i_gen (A : V → J) (v₀ : V) (j' : J) (S : V → Option J) (L : V → J)
    (hS : S = splitLab A v₀) (hL : L = moveLab A v₀ j') (h : Refines S L)
    (hv : ∀ w, S w = S v₀ → w = v₀) (α : ℕ) :
    letI := (refineHom k h).toRingHom.toAlgebra
    ∑ f ∈ range (α + 1), (-1 : BorelRing k S ⊗[BorelRing k L] BorelRing k S) ^ (α - f) *
      ((xiS k S v₀ hv ^ f) ⊗ₜ[BorelRing k L] xB k S (some j') (α - f)) =
    ∑ g ∈ range (α + 1), (-1 : BorelRing k S ⊗[BorelRing k L] BorelRing k S) ^ (α - g) *
      (xB k S (some j') (α - g) ⊗ₜ[BorelRing k L] (xiS k S v₀ hv ^ g)) := by
  subst hS hL
  exact lemma_5_4_i_KL α

/-- Generic form of `lemma_5_4_iii`. -/
theorem lemma_5_4_iii_gen (A : V → J) (v₀ : V) (j' : J) (S : V → Option J) (L : V → J)
    (hS : S = splitLab A v₀) (hL : L = moveLab A v₀ j') (h : Refines S L)
    (hv : ∀ w, S w = S v₀ → w = v₀) :
    letI := (refineHom k h).toRingHom.toAlgebra
    (xiS k S v₀ hv ⊗ₜ[BorelRing k L] (1 : BorelRing k S)) *
      ∑ p ∈ antidiagonal (labSet S (· = some j')).card,
        (((-xiS k S v₀ hv) ^ p.1) ⊗ₜ[BorelRing k L] xB k S (some j') p.2) =
    ((1 : BorelRing k S) ⊗ₜ[BorelRing k L] xiS k S v₀ hv) *
      ∑ p ∈ antidiagonal (labSet S (· = some j')).card,
        (((-xiS k S v₀ hv) ^ p.1) ⊗ₜ[BorelRing k L] xB k S (some j') p.2) := by
  subst hS hL
  exact lemma_5_4_iii

/-- Generic form of `pR_xB_mem_slideSub`. -/
theorem slide_gen (A : V → J) (v₀ : V) (j' : J) (S : V → Option J) (L : V → J)
    (hS : S = splitLab A v₀) (hL : L = moveLab A v₀ j') (h : Refines S L) (hA : Refines S A)
    (hv : ∀ w, S w = S v₀ → w = v₀) (hj : j' ≠ A v₀) (j : J) (β : ℕ) :
    letI := (refineHom k h).toRingHom.toAlgebra
    (refineHom k hA (xB k A j β) ⊗ₜ[BorelRing k L] (1 : BorelRing k S)) *
      ∑ p ∈ antidiagonal (labSet S (· = some j')).card,
        (((-xiS k S v₀ hv) ^ p.1) ⊗ₜ[BorelRing k L] xB k S (some j') p.2) =
    ((1 : BorelRing k S) ⊗ₜ[BorelRing k L] refineHom k hA (xB k A j β)) *
      ∑ p ∈ antidiagonal (labSet S (· = some j')).card,
        (((-xiS k S v₀ hv) ^ p.1) ⊗ₜ[BorelRing k L] xB k S (some j') p.2) := by
  subst hS hL
  exact pR_xB_mem_slideSub hj j β

end Generic

/-! ### The mirrored identities -/

section Mirror

variable {k : Type*} [Field k] {V : Type*} [Fintype V] [DecidableEq V] {J : Type*}
  [DecidableEq J]

/-- **The mirror of KL III eq. (5.30)**: in `H_{k^{+i}}`,
`(-ξ)^f = ∑_{a + b = f} x(k^{+i})_{j,a} · p_1^* x̄(k)_{j,b}`, `j` the block of `v₀`. -/
theorem neg_xi_pow_R (lab : V → J) (v₀ : V) (f : ℕ) :
    (-xi k lab v₀) ^ f = ∑ p ∈ antidiagonal f, xB k (splitLab lab v₀) (some (lab v₀)) p.1 *
      pR k lab v₀ (xbarB k lab (lab v₀) p.2) :=
  neg_xi_pow_gen lab v₀ (lab v₀) (splitLab lab v₀) lab rfl (lab_eq_moveLab_self lab v₀)
    (refines_splitLab lab v₀) (splitLab_singleton lab v₀) f

attribute [local instance] rightAlgebra

/-- The ring `H_{k^{+i}} ⊗_{H_k} H_{k^{+i}}` (`H_k` acting through `p_1^*`), the image of
`E_i F_i 1_{+_i k}`. -/
abbrev CupRingR (lab : V → J) (v₀ : V) : Type _ :=
  BorelRing k (splitLab lab v₀) ⊗[BorelRing k lab] BorelRing k (splitLab lab v₀)

/-- `x(k')_{i+1,β}`: `e_β` of the block of `v₀` without `v₀`. -/
abbrev xsR (lab : V → J) (v₀ : V) (β : ℕ) : BorelRing k (splitLab lab v₀) :=
  xB k (splitLab lab v₀) (some (lab v₀)) β

/-- **KL III Lemma 5.4 (ii), eq. (5.44)**: in `H_{k^{+i}} ⊗_{H_k} H_{k^{+i}}`,
`∑_{f=0}^{α} (-1)^{α-f} ξ^f ⊗ x(k')_{i+1,α-f} = ∑_{g=0}^{α} (-1)^{α-g} x(k')_{i+1,α-g} ⊗ ξ^g`. -/
theorem lemma_5_4_ii (lab : V → J) (v₀ : V) (α : ℕ) :
    ∑ f ∈ range (α + 1), (-1) ^ (α - f) * ((xi k lab v₀ ^ f) ⊗ₜ[BorelRing k lab]
      xsR (k := k) lab v₀ (α - f)) =
    ∑ g ∈ range (α + 1), (-1) ^ (α - g) * (xsR (k := k) lab v₀ (α - g)
      ⊗ₜ[BorelRing k lab] (xi k lab v₀ ^ g)) :=
  lemma_5_4_i_gen lab v₀ (lab v₀) (splitLab lab v₀) lab rfl (lab_eq_moveLab_self lab v₀)
    (refines_splitLab lab v₀) (splitLab_singleton lab v₀) α

/-- `d = k'_{i+1} - k'_i`: the size of the block of `v₀` without `v₀`. -/
abbrev dBlockR (lab : V → J) (v₀ : V) : ℕ := (labSet (splitLab lab v₀) (· = some (lab v₀))).card

variable (k) in
/-- The cup element (sign-free): `c = ∑_{a + b = d} (-ξ)^a ⊗ x(k')_{i+1,b}`. -/
def cupEltR (lab : V → J) (v₀ : V) : CupRingR (k := k) lab v₀ :=
  ∑ p ∈ antidiagonal (dBlockR lab v₀), (((-xi k lab v₀) ^ p.1) ⊗ₜ xsR lab v₀ p.2)

variable (k) in
/-- **KL III's second cup element** (Corollary 5.5, Definition 6.1 eq. (6.3)):
`∑_{g=0}^{d} (-1)^{d-g} ξ^g ⊗ x(k')_{i+1,d-g}`. -/
def cupEltRKL (lab : V → J) (v₀ : V) : CupRingR (k := k) lab v₀ :=
  ∑ g ∈ range (dBlockR lab v₀ + 1),
    (-1) ^ (dBlockR lab v₀ - g) * ((xi k lab v₀ ^ g) ⊗ₜ xsR lab v₀ (dBlockR lab v₀ - g))

theorem cupEltRKL_eq (lab : V → J) (v₀ : V) :
    cupEltRKL k lab v₀ = (-1) ^ dBlockR lab v₀ * cupEltR k lab v₀ :=
  (neg_one_pow_mul_sum_tmul _ _ _).symm

/-- **KL III Lemma 5.4 (ii) ⇒ (iv), eq. (5.46)**: `ξ` slides through the cup element,
`(ξ ⊗ 1) c = (1 ⊗ ξ) c`. -/
theorem lemma_5_4_iv (lab : V → J) (v₀ : V) :
    (xi k lab v₀ ⊗ₜ 1) * cupEltR k lab v₀ = (1 ⊗ₜ xi k lab v₀) * cupEltR k lab v₀ :=
  lemma_5_4_iii_gen lab v₀ (lab v₀) (splitLab lab v₀) lab rfl (lab_eq_moveLab_self lab v₀)
    (refines_splitLab lab v₀) (splitLab_singleton lab v₀)

/-- **KL III Lemma 5.4 (iv), eq. (5.46)** in KL III's form:
`∑_{f=0}^{d} (-1)^{d-f} ξ^{f+1} ⊗ x(k')_{i+1,d-f} = ∑_{g=0}^{d} (-1)^{d-g} ξ^g ⊗ x(k')_{i+1,d-g} ξ`. -/
theorem lemma_5_4_iv_KL (lab : V → J) (v₀ : V) :
    ∑ f ∈ range (dBlockR lab v₀ + 1), (-1 : CupRingR (k := k) lab v₀) ^ (dBlockR lab v₀ - f) *
      ((xi k lab v₀ ^ (f + 1)) ⊗ₜ[BorelRing k lab] xsR lab v₀ (dBlockR lab v₀ - f)) =
    ∑ g ∈ range (dBlockR lab v₀ + 1), (-1 : CupRingR (k := k) lab v₀) ^ (dBlockR lab v₀ - g) *
      ((xi k lab v₀ ^ g) ⊗ₜ[BorelRing k lab] (xsR lab v₀ (dBlockR lab v₀ - g) * xi k lab v₀)) := by
  have h : (xi k lab v₀ ⊗ₜ 1) * cupEltRKL k lab v₀ = (1 ⊗ₜ xi k lab v₀) * cupEltRKL k lab v₀ := by
    rw [cupEltRKL_eq, mul_left_comm, lemma_5_4_iv, mul_left_comm]
  simp only [cupEltRKL, Finset.mul_sum] at h
  convert h using 2 with f _ g _
  · rw [mul_left_comm, Algebra.TensorProduct.tmul_mul_tmul, one_mul, pow_succ']
  · rw [mul_left_comm, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm (xi k lab v₀)]

/-! ### Corollary 5.5 for an arbitrary labelling -/

variable [Fintype J]

/-- **KL III Corollary 5.5 (second map)**: every element of `H_{k'} = H_{+_i k}` (acting on
`H_{k^{+i}}` through `p_2^*`) slides through the cup element of `H_{k^{+i}} ⊗_{H_k} H_{k^{+i}}`;
hence `1 ↦ ∑_g (-1)^{d-g} ξ^g ⊗ x(k')_{i+1,d-g}` is a bimodule map. -/
theorem cupR_bimodule (lab : V → J) (v₀ : V) (j' : J) (hj : j' ≠ lab v₀)
    (z : BorelRing k (moveLab lab v₀ j')) :
    (pL k lab v₀ j' z ⊗ₜ 1) * cupEltRKL k lab v₀ = (1 ⊗ₜ pL k lab v₀ j' z) * cupEltRKL k lab v₀ := by
  rw [cupEltRKL_eq, mul_left_comm, mul_left_comm (1 ⊗ₜ _)]
  congr 1
  let T : Subalgebra k (BorelRing k (splitLab lab v₀)) :=
    { slideSubring (cupEltR k lab v₀) with
      algebraMap_mem' := fun c => by
        rw [← (pR k lab v₀).commutes c]
        exact algebraMap_mem_slideSubring _ _ }
  have hle : Algebra.adjoin k (Set.range fun p : J × ℕ => xB k (moveLab lab v₀ j') p.1 p.2) ≤
      T.comap (pL k lab v₀ j') := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨⟨j, β⟩, rfl⟩
    exact slide_gen (moveLab lab v₀ j') v₀ (lab v₀) (splitLab lab v₀) lab
      (splitLab_moveLab lab v₀ j') (lab_eq_moveLab_moveLab lab v₀ j') (refines_splitLab lab v₀)
      (refines_splitLab_move lab v₀ j') (splitLab_singleton lab v₀)
      (by rw [moveLab_self]; exact Ne.symm hj) j β
  exact hle (by rw [adjoin_xB]; exact Algebra.mem_top)

omit [Fintype J] in
theorem lemma_5_4_iv' (lab : V → J) (v₀ : V) :
    xi k lab v₀ ∈ slideSubring (cupEltR k lab v₀) := lemma_5_4_iv lab v₀

end Mirror

section MirrorL

variable {k : Type*} [Field k] {V : Type*} [Fintype V] [DecidableEq V] {J : Type*}
  [Fintype J] [DecidableEq J]

attribute [local instance] midAlgebra

/-- **KL III Corollary 5.5 (first map)** for an arbitrary labelling (finitely many labels): every
element of `H_k` (acting through `p_1^*`) slides through the cup element of
`H_{k^{+i}} ⊗_{H_{+_i k}} H_{k^{+i}}`. -/
theorem cupL_bimodule (lab : V → J) (v₀ : V) (j' : J) (hj : j' ≠ lab v₀)
    (z : BorelRing k lab) :
    (pR k lab v₀ z ⊗ₜ 1) * cupEltKL k lab v₀ j' = (1 ⊗ₜ pR k lab v₀ z) * cupEltKL k lab v₀ j' := by
  rw [cupEltKL_eq, mul_left_comm, mul_left_comm (1 ⊗ₜ _)]
  congr 1
  have hle : Algebra.adjoin k (Set.range fun p : J × ℕ => xB k lab p.1 p.2) ≤
      (slideSub k lab v₀ j').comap (pR k lab v₀) := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨⟨j, β⟩, rfl⟩
    exact pR_xB_mem_slideSub hj j β
  exact hle (by rw [adjoin_xB]; exact Algebra.mem_top)

end MirrorL

end Categorification.Flag

end
