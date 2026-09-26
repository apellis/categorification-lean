/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.Crossing

/-!
# Crossings of adjacent colours in the flag 2-category (KL III Definition 6.2)

Khovanov–Lauda III, arXiv:0807.3250v1, §6.1.2 (TeX `sln-2008-ArXiv.tex`, subsubsection
"`R(ν)` generators", Definition 6.2, eqs. (6.8), (6.9); TeX labels `eq_gamma_dcross`,
`eq_gamma_dcross_down`) and the two-strand relations of §6.2 (Proposition 6.7, eq. (6.18), and
Proposition 6.8, eq. (6.19), for `i · j = -1`).

## The two iterated flag varieties

For adjacent colours one of the two orders of `E_i E_{i+1} 1_k` / `E_{i+1} E_i 1_k` (and of
`F_{i+1} F_i 1_k` / `F_i F_{i+1} 1_k`) is a partial flag variety and the other is not. We use the
Borel model of `Categorification.Flag.Crossing` with one set of variables `V` and a labelling
`lab : V → J`, and two variables `v`, `w` with `lab v`, `lab w`, `α` pairwise distinct:

* the **non-flag** tensor product `T_N = EERing lab v w (lab v)`: first `w` moves into the block
  `β = lab v` of `v`, then `v` moves from `β` to `α`;
  `T_N = H(split (move w β) v) ⊗_{H(move w β)} H(split w)`;
* the **flag** tensor product `T_F = EERing lab w v α`: first `v` moves to `α`, then `w` moves to
  `β`; by `tensorEquiv` it is the Borel ring of the labelling in which `v` and `w` are singletons.

For upward strands (`α = i`, `β = i + 1`, `lab w = i + 2`) `T_N` is `Γ(E_i E_{i+1} 1_k)` and
`T_F` is `Γ(E_{i+1} E_i 1_k)`; for downward strands (`α = i + 2`, `β = i + 1`, `lab w = i`)
`T_N` is `Γ(F_{i+1} F_i 1_k)` and `T_F` is `Γ(F_i F_{i+1} 1_k)`.

## Restriction and push-forward

The multiplication map `restrN = jointMap : T_N → H(joint)` (restriction to the divisor on
which the iterated variety is a flag variety) is a surjective ring homomorphism which is not
injective. We construct the push-forward `pushN : H(joint) → T_N` (`H(split w)`-linear, defined
on the basis `x_v^a`, `a < k_β`, of `H(joint)` over `H(split w)`), and prove

* `pushN_restrN` : `pushN (restrN t) = δ t` with `δ = x_v ⊗ 1 - 1 ⊗ x_w`;
* `restrN_pushN` : `restrN (pushN b) = (x_v - x_w) b`;
* `pushN_restrN_mul` : `pushN` is `T_N`-linear, `pushN (restrN s * b) = s * pushN b`.

The key identity is `δ · F(x_v ⊗ 1) = 0` (`deltaN_mul_charN`), where `F` is the characteristic
polynomial of `v` over `H(split w)` (degree `k_β`); it follows from the characteristic polynomial
of `v` over the middle ring (degree `k_β + 1`), which vanishes in `T_N`, and
`e_c(β ∪ w) = e_c(β) + x_w e_{c-1}(β)` (KL III (5.16)).

## The crossings (Definition 6.2)

* `crossNF : T_N → T_F` (a ring homomorphism): `x_v^a ⊗ x_w^b ↦ x_w^b ⊗ x_v^a` (`crossNF_xi`);
  this is `Γ` of the upward crossing `E_i E_{i+1} → E_{i+1} E_i` ((6.8), case `i → j`) and of the
  downward crossing `F_{i+1} F_i → F_i F_{i+1}` ((6.9), case `j → i`).
* `crossFN : T_F → T_N`: `x_w^a ⊗ x_v^b ↦ x_v^{b+1} ⊗ x_w^a - x_v^b ⊗ x_w^{a+1}` (`crossFN_xi`);
  `Γ` of the downward crossing `F_i F_{i+1} → F_{i+1} F_i` is `crossFN` ((6.9), case `i → j`)
  and `Γ` of the upward crossing `E_{i+1} E_i → E_i E_{i+1}` is `-crossFN` ((6.8), case `j → i`).

## Relations

* `crossFN_crossNF` : `crossFN ∘ crossNF = δ ·` on `T_N`, i.e. `x_left - x_right`;
* `crossNF_crossFN` : `crossNF ∘ crossFN = (1 ⊗ x_v - x_w ⊗ 1) ·` on `T_F`, i.e.
  `x_right - x_left`.

With the signs above these are exactly the signed relations (4.11)/(6.19) for `i · j = -1`:
`ψ_{ji} ψ_{ij} = (i - j)(x_left - x_right)` on `E_i E_j` (`up_sq_NF`, `up_sq_FN`).
* `crossNF_*_mul`, `crossFN_*_mul` : dots slide through both crossings (KL III (4.12)/(6.18)).
* `crossNF_left`, `crossNF_right`, `crossFN_left`, `crossFN_right` : both crossings are maps of
  bimodules over the outer rings `H_{+_i +_j k}` and `H_k`.
* `degenerate_xi` : if the block `β` is empty (so `T_F = 0`), the non-flag tensor product is
  built by moving `w` twice and there `x_w ⊗ 1 = 1 ⊗ x_w`; the relation `ψψ = ±(x_left -
  x_right)` then holds trivially.

Gradings (the shifts `{±1}` in (6.8), (6.9)) are not treated.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Categorification.Flag

open MvPolynomial TensorProduct
open Finset (univ range antidiagonal)

/-! ### A polynomial identity -/

section Poly

variable {T : Type*} [CommRing T]

/-- If `E_{b+1} = 0`, then
`∑_{f ≤ b+1} (-t)^f (E_{b+1-f} + [b+1-f ≠ 0] y E_{b-f}) = (y - t) ∑_{f ≤ b} (-t)^f E_{b-f}`:
the characteristic polynomial of a block with one more variable `y`. -/
theorem charPoly_insert (t y : T) (E : ℕ → T) (b : ℕ) (hE : E (b + 1) = 0) :
    ∑ f ∈ range (b + 2), (-t) ^ f * (E (b + 1 - f) + if b + 1 - f = 0 then 0 else y * E (b + 1 - f - 1)) =
      (y - t) * ∑ f ∈ range (b + 1), (-t) ^ f * E (b - f) := by
  simp only [mul_add, Finset.sum_add_distrib]
  have h1 : ∑ f ∈ range (b + 2), (-t) ^ f * E (b + 1 - f) =
      -t * ∑ f ∈ range (b + 1), (-t) ^ f * E (b - f) := by
    rw [Finset.sum_range_succ', Nat.sub_zero, hE, mul_zero, add_zero, Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [show b + 1 - (f + 1) = b - f by omega, pow_succ]
    ring
  have h2 : ∑ f ∈ range (b + 2), (-t) ^ f * (if b + 1 - f = 0 then 0 else y * E (b + 1 - f - 1)) =
      y * ∑ f ∈ range (b + 1), (-t) ^ f * E (b - f) := by
    rw [Finset.sum_range_succ, show b + 1 - (b + 1) = 0 by omega, if_pos rfl, mul_zero, add_zero,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun f hf => ?_
    have : f < b + 1 := Finset.mem_range.1 hf
    rw [if_neg (by omega), show b + 1 - f - 1 = b - f by omega]
    ring
  rw [h1, h2]
  ring

end Poly

/-! ### The non-flag tensor product -/

section NonFlag

variable {k : Type*} [Field k] {V : Type*} [Fintype V] [DecidableEq V] {J : Type*}
  [Fintype J] [DecidableEq J] (lab : V → J) (v w : V)

attribute [local instance] rightAlgebra midAlgebra jointAlgebra

/-- The non-flag tensor product `T_N = H(split (move w β) v) ⊗_{H(move w β)} H(split w)`,
`β = lab v`: first `w` moves into the block of `v`, then `v` moves out of it. -/
abbrev NRing : Type _ := EERing (k := k) lab v w (lab v)

variable (k) in
/-- `ξ₁ = x_v ⊗ 1` (the dot on the left strand of `T_N`). -/
abbrev xiN₁ : NRing (k := k) lab v w := xi k (moveLab lab w (lab v)) v ⊗ₜ 1

variable (k) in
/-- `ξ₂ = 1 ⊗ x_w` (the dot on the right strand of `T_N`). -/
abbrev xiN₂ : NRing (k := k) lab v w := 1 ⊗ₜ xi k lab w

variable (k) in
/-- `δ = x_v ⊗ 1 - 1 ⊗ x_w`. -/
def deltaN : NRing (k := k) lab v w := xiN₁ k lab v w - xiN₂ k lab v w

variable (k) in
/-- The restriction `T_N → H(joint)`, `m₁ ⊗ m₂ ↦ m₁ m₂` (`jointMap`). -/
abbrev restrN : NRing (k := k) lab v w →ₐ[BorelRing k (moveLab lab w (lab v))]
    BorelRing k (jointLab lab v w) :=
  jointMap k lab v w (lab v)

/-- The size `k_β` of the block of `v` in `lab` (after moving `w` out of the way). -/
abbrev bN : ℕ := blockCard (splitLab lab w) v

variable {lab v w}

theorem ne_of_lab_ne (hw : lab w ≠ lab v) : v ≠ w := fun h => hw (by rw [h])

theorem splitLab_w_v (hw : lab w ≠ lab v) : splitLab lab w v = some (lab v) :=
  splitLab_of_ne (ne_of_lab_ne hw)

theorem moveLab_w_v (hw : lab w ≠ lab v) : moveLab lab w (lab v) v = lab v := by
  rw [moveLab, Function.update_of_ne (ne_of_lab_ne hw)]

theorem bN_eq (hw : lab w ≠ lab v) :
    bN lab v w = (labSet (splitLab lab w) (· = some (lab v))).card := by
  rw [bN, blockCard, splitLab_w_v hw]

theorem blockCard_move_eq (hw : lab w ≠ lab v) :
    blockCard (moveLab lab w (lab v)) v = bN lab v w + 1 := by
  rw [blockCard, moveLab_w_v hw, labSet_move_eq, if_pos rfl,
    Finset.card_insert_of_not_mem (by simp), bN_eq hw]

theorem restrN_tmul (m₁ : BorelRing k (splitLab (moveLab lab w (lab v)) v))
    (m₂ : BorelRing k (splitLab lab w)) :
    restrN k lab v w (m₁ ⊗ₜ m₂) =
      refineHom k (refines_joint_left lab v w (lab v)) m₁ * pR k (splitLab lab w) v m₂ :=
  jointMap_tmul lab v w (lab v) m₁ m₂

/-- `x_w` in the joint Borel ring. -/
theorem pR_xi_w (hw : lab w ≠ lab v) :
    pR k (splitLab lab w) v (xi k lab w) =
      xiS k (jointLab lab v w) w (joint_singleton_right lab v w (ne_of_lab_ne hw)) :=
  pR_mk k _ _ rfl

theorem restrN_xiN₁ : restrN k lab v w (xiN₁ k lab v w) = xi k (splitLab lab w) v := by
  rw [restrN_tmul, map_one, mul_one, jointLeft_xi]

theorem restrN_xiN₂ (hw : lab w ≠ lab v) :
    restrN k lab v w (xiN₂ k lab v w) =
      xiS k (jointLab lab v w) w (joint_singleton_right lab v w (ne_of_lab_ne hw)) := by
  rw [restrN_tmul, map_one, one_mul, pR_xi_w hw]

theorem restrN_one_tmul (m : BorelRing k (splitLab lab w)) :
    restrN k lab v w (1 ⊗ₜ m) = pR k (splitLab lab w) v m := by
  rw [restrN_tmul, map_one, one_mul]

/-- `restrN` is onto. -/
theorem restrN_surjective (b : BorelRing k (jointLab lab v w)) :
    ∃ c : Fin (bN lab v w) → BorelRing k (splitLab lab w),
      restrN k lab v w (∑ a : Fin (bN lab v w), xiN₁ k lab v w ^ (a : ℕ) * (1 ⊗ₜ c a)) = b := by
  obtain ⟨c, hc⟩ := split_span (splitLab lab w) v b
  refine ⟨c, ?_⟩
  rw [← hc, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, map_pow, restrN_xiN₁, restrN_one_tmul, mul_comm]

/-! #### The key identity `δ · F(ξ₁) = 0` -/

variable (k lab v w) in
/-- `e_c(β)` (the block `β = lab v` of `lab`, containing `v`), in `H(split w)`. -/
abbrev eN (c : ℕ) : BorelRing k (splitLab lab w) := xB k (splitLab lab w) (some (lab v)) c

variable (k lab v w) in
/-- The characteristic polynomial `F(ξ₁) = ∑_{f ≤ k_β} (-ξ₁)^f e_{k_β - f}(β)` of `v` over
`H(split w)`, evaluated at `ξ₁ = x_v ⊗ 1` in `T_N`. -/
def charN : NRing (k := k) lab v w :=
  ∑ f ∈ range (bN lab v w + 1), (-xiN₁ k lab v w) ^ f * (1 ⊗ₜ eN k lab v w (bN lab v w - f))

/-- In `T_N`, `1 ⊗ r = r ⊗ 1` for `r` in the middle ring. -/
theorem one_tmul_pL_eq (r : BorelRing k (moveLab lab w (lab v))) :
    (1 : BorelRing k (splitLab (moveLab lab w (lab v)) v)) ⊗ₜ[BorelRing k (moveLab lab w (lab v))]
        pL k lab w (lab v) r = pR k (moveLab lab w (lab v)) v r ⊗ₜ 1 := by
  rw [← algebraMap_mid, ← algebraMap_right]
  exact (Algebra.TensorProduct.tmul_one_eq_one_tmul r).symm

/-- **The key identity** `δ · F(ξ₁) = 0` in `T_N`. -/
theorem deltaN_mul_charN (hw : lab w ≠ lab v) : deltaN k lab v w * charN k lab v w = 0 := by
  -- the characteristic polynomial of `v` over the middle ring vanishes
  have hm := split_monic (k := k) (moveLab lab w (lab v)) v
  rw [blockCard_move_eq hw] at hm
  have hRv := moveLab_w_v (lab := lab) hw
  simp only [hRv] at hm
  have hg : ∑ f ∈ range (bN lab v w + 2), (-xiN₁ k lab v w) ^ f *
      (1 ⊗ₜ pL k lab w (lab v) (xB k (moveLab lab w (lab v)) (lab v) (bN lab v w + 1 - f))) = 0 := by
    have := congrArg (fun z => z ⊗ₜ[BorelRing k (moveLab lab w (lab v))]
      (1 : BorelRing k (splitLab lab w))) hm
    simp only [zero_tmul] at this
    rw [← this, sum_tmul]
    refine Finset.sum_congr rfl fun f _ => ?_
    have e : ∀ z : BorelRing k (splitLab (moveLab lab w (lab v)) v),
        z ⊗ₜ[BorelRing k (moveLab lab w (lab v))] (1 : BorelRing k (splitLab lab w)) =
          Algebra.TensorProduct.includeLeftRingHom z := fun z => rfl
    simp only [xiN₁]
    rw [one_tmul_pL_eq, e, e, e, ← map_neg, ← map_pow, ← map_mul]
  -- expand `e_c(β ∪ w) = e_c(β) + x_w e_{c-1}(β)`
  have hexp : ∀ c : ℕ, (1 : BorelRing k (splitLab (moveLab lab w (lab v)) v)) ⊗ₜ[BorelRing k
      (moveLab lab w (lab v))] pL k lab w (lab v) (xB k (moveLab lab w (lab v)) (lab v) c) =
      (1 ⊗ₜ eN k lab v w c) + if c = 0 then 0 else xiN₂ k lab v w * (1 ⊗ₜ eN k lab v w (c - 1)) := by
    intro c
    rcases c with _ | c
    · simp [eN]
    · rw [pL_xB_succ, if_pos rfl, if_neg (Nat.succ_ne_zero c), Nat.add_sub_cancel, tmul_add,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  simp only [hexp] at hg
  have hE : eN k lab v w (bN lab v w + 1) = 0 := xB_eq_zero (by rw [← bN_eq hw]; omega)
  have hE' : (1 : BorelRing k (splitLab (moveLab lab w (lab v)) v)) ⊗ₜ[BorelRing k
      (moveLab lab w (lab v))] eN k lab v w (bN lab v w + 1) = 0 := by rw [hE, tmul_zero]
  rw [charPoly_insert _ _ (fun c => (1 : BorelRing k (splitLab (moveLab lab w (lab v)) v)) ⊗ₜ[
    BorelRing k (moveLab lab w (lab v))] eN k lab v w c) (bN lab v w) hE'] at hg
  rw [deltaN, charN, ← neg_sub, neg_mul, hg, neg_zero]

/-! #### The push-forward -/

variable (k lab v w) in
/-- **The push-forward** `H(joint) → T_N`: on the basis `x_v^a` (`a < k_β`) of `H(joint)` over
`H(split w)`, `∑_a r_a x_v^a ↦ ∑_a (1 ⊗ r_a) δ ξ₁^a`. -/
def pushN : BorelRing k (jointLab lab v w) →+ NRing (k := k) lab v w where
  toFun b := ∑ a, ((1 : BorelRing k (splitLab (moveLab lab w (lab v)) v)) ⊗ₜ[BorelRing k
    (moveLab lab w (lab v))] ((basisR k (splitLab lab w) v).repr b a)) *
      (deltaN k lab v w * xiN₁ k lab v w ^ (a : ℕ))
  map_zero' := by simp
  map_add' b c := by simp [tmul_add, add_mul, Finset.sum_add_distrib]

theorem pushN_apply (b : BorelRing k (jointLab lab v w)) :
    pushN k lab v w b = ∑ a, ((1 : BorelRing k (splitLab (moveLab lab w (lab v)) v)) ⊗ₜ[BorelRing k
      (moveLab lab w (lab v))] ((basisR k (splitLab lab w) v).repr b a)) *
        (deltaN k lab v w * xiN₁ k lab v w ^ (a : ℕ)) := rfl

theorem one_tmul_mul (c c' : BorelRing k (splitLab lab w)) :
    ((1 : BorelRing k (splitLab (moveLab lab w (lab v)) v)) ⊗ₜ[BorelRing k (moveLab lab w (lab v))]
      (c * c')) = (1 ⊗ₜ c) * (1 ⊗ₜ c') := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

/-- `pushN` is `H(split w)`-linear. -/
theorem pushN_pR_mul (c : BorelRing k (splitLab lab w)) (b : BorelRing k (jointLab lab v w)) :
    pushN k lab v w (pR k (splitLab lab w) v c * b) = (1 ⊗ₜ c) * pushN k lab v w b := by
  rw [pushN_apply, pushN_apply, ← smul_right, LinearEquiv.map_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finsupp.smul_apply, smul_eq_mul, one_tmul_mul]
  ring

theorem pushN_basis (a : Fin (bN lab v w)) :
    pushN k lab v w (xi k (splitLab lab w) v ^ (a : ℕ)) =
      deltaN k lab v w * xiN₁ k lab v w ^ (a : ℕ) := by
  rw [pushN_apply, ← basisR_apply, Basis.repr_self, Finset.sum_eq_single a]
  · rw [Finsupp.single_eq_same, ← Algebra.TensorProduct.one_def, one_mul]
  · intro b _ hb
    rw [Finsupp.single_eq_of_ne hb.symm, tmul_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ a) h

theorem one_tmul_neg_one_pow' (f : ℕ) :
    ((1 : BorelRing k (splitLab (moveLab lab w (lab v)) v)) ⊗ₜ[BorelRing k (moveLab lab w (lab v))]
      ((-1 : BorelRing k (splitLab lab w)) ^ f)) = (-1) ^ f := by
  have : ∀ z : BorelRing k (splitLab lab w),
      ((1 : BorelRing k (splitLab (moveLab lab w (lab v)) v)) ⊗ₜ[BorelRing k
        (moveLab lab w (lab v))] z) = Algebra.TensorProduct.includeRight z := fun z => rfl
  rw [this, map_pow, map_neg, map_one]

theorem pushN_neg_pow_mul {f : ℕ} (hf : f < bN lab v w) (c : BorelRing k (splitLab lab w)) :
    pushN k lab v w ((-xi k (splitLab lab w) v) ^ f * pR k (splitLab lab w) v c) =
      deltaN k lab v w * ((-xiN₁ k lab v w) ^ f * (1 ⊗ₜ c)) := by
  have e : (-xi k (splitLab lab w) v) ^ f * pR k (splitLab lab w) v c =
      pR k (splitLab lab w) v ((-1) ^ f * c) * xi k (splitLab lab w) v ^ f := by
    rw [map_mul, map_pow, map_neg, map_one, neg_pow]; ring
  rw [e, pushN_pR_mul, pushN_basis ⟨f, hf⟩, one_tmul_mul, one_tmul_neg_one_pow', neg_pow]
  ring

theorem pushN_top (hw : lab w ≠ lab v) :
    pushN k lab v w (xi k (splitLab lab w) v ^ bN lab v w) =
      deltaN k lab v w * xiN₁ k lab v w ^ bN lab v w := by
  have hm := split_monic (k := k) (splitLab lab w) v
  simp only [splitLab_w_v hw] at hm
  rw [Finset.sum_range_succ, Nat.sub_self, xB_zero, map_one, mul_one] at hm
  have hS : (-xi k (splitLab lab w) v) ^ bN lab v w = -∑ f ∈ range (bN lab v w),
      (-xi k (splitLab lab w) v) ^ f * pR k (splitLab lab w) v (eN k lab v w (bN lab v w - f)) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact hm
  have hc := deltaN_mul_charN (k := k) hw
  rw [charN, Finset.sum_range_succ, Nat.sub_self, eN, xB_zero, ← Algebra.TensorProduct.one_def,
    mul_one, mul_add] at hc
  have e1 : xi k (splitLab lab w) v ^ bN lab v w =
      pR k (splitLab lab w) v ((-1) ^ bN lab v w) * (-xi k (splitLab lab w) v) ^ bN lab v w := by
    rw [map_pow, map_neg, map_one, ← mul_pow]; simp
  rw [e1, pushN_pR_mul, hS, map_neg, map_sum, Finset.sum_congr rfl fun f hf =>
    pushN_neg_pow_mul (Finset.mem_range.1 hf) _, ← Finset.mul_sum, one_tmul_neg_one_pow']
  rw [neg_pow (xiN₁ k lab v w) (bN lab v w)] at hc
  have h1 : ((-1 : NRing (k := k) lab v w) ^ bN lab v w) * (-1) ^ bN lab v w = 1 := by
    rw [← mul_pow]; simp
  rw [eq_neg_of_add_eq_zero_left hc, neg_neg, mul_left_comm, ← mul_assoc ((-1) ^ bN lab v w), h1,
    one_mul]

theorem pushN_xi_pow (hw : lab w ≠ lab v) {a : ℕ} (ha : a ≤ bN lab v w) :
    pushN k lab v w (xi k (splitLab lab w) v ^ a) = deltaN k lab v w * xiN₁ k lab v w ^ a := by
  rcases ha.lt_or_eq with h | rfl
  · exact pushN_basis ⟨a, h⟩
  · exact pushN_top hw

/-- **`pushN ∘ restrN = δ ·`** on `T_N`. -/
theorem pushN_restrN (hw : lab w ≠ lab v) (t : NRing (k := k) lab v w) :
    pushN k lab v w (restrN k lab v w t) = deltaN k lab v w * t := by
  obtain ⟨c, rfl⟩ := tensor_span lab v w (lab v) t
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have ha : (a : ℕ) ≤ bN lab v w := by
    have := a.2; have h2 := blockCard_move_eq hw; omega
  rw [restrN_tmul, map_pow, jointLeft_xi, mul_comm, pushN_pR_mul, pushN_xi_pow hw ha]
  have : (xi k (moveLab lab w (lab v)) v ^ (a : ℕ)) ⊗ₜ[BorelRing k (moveLab lab w (lab v))] c a =
      xiN₁ k lab v w ^ (a : ℕ) * (1 ⊗ₜ c a) := by
    rw [xiN₁, Algebra.TensorProduct.tmul_pow, one_pow, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, mul_one]
  rw [this]; ring

theorem restrN_deltaN (hw : lab w ≠ lab v) :
    restrN k lab v w (deltaN k lab v w) = xi k (splitLab lab w) v -
      xiS k (jointLab lab v w) w (joint_singleton_right lab v w (ne_of_lab_ne hw)) := by
  rw [deltaN, map_sub, restrN_xiN₁, restrN_xiN₂ hw]

/-- **`restrN ∘ pushN = (x_v - x_w) ·`** on `H(joint)`. -/
theorem restrN_pushN (hw : lab w ≠ lab v) (b : BorelRing k (jointLab lab v w)) :
    restrN k lab v w (pushN k lab v w b) = (xi k (splitLab lab w) v -
      xiS k (jointLab lab v w) w (joint_singleton_right lab v w (ne_of_lab_ne hw))) * b := by
  obtain ⟨c, rfl⟩ := restrN_surjective (k := k) b
  rw [pushN_restrN hw, map_mul, restrN_deltaN hw]

/-- **`pushN` is `T_N`-linear**. -/
theorem pushN_restrN_mul (hw : lab w ≠ lab v) (s : NRing (k := k) lab v w)
    (b : BorelRing k (jointLab lab v w)) :
    pushN k lab v w (restrN k lab v w s * b) = s * pushN k lab v w b := by
  obtain ⟨c, rfl⟩ := restrN_surjective (k := k) b
  rw [← map_mul, pushN_restrN hw, pushN_restrN hw]; ring

/-! ### The flag tensor product and the two crossings -/

/-- A labelling refines itself; `refineHom` along it is the identity. -/
theorem refineHom_self {l : V → J} (h : Refines l l) (z : BorelRing k l) : refineHom k h z = z := by
  obtain ⟨a, rfl⟩ := mkB_surjective l z
  exact refineHom_mk _ a a rfl

theorem refines_of_eq {J₁ : Type*} {l₁ l₂ : V → J₁} (h : l₁ = l₂) : Refines l₁ l₂ := by
  subst h; exact fun _ _ h => h

/-- The two ways of moving `w` to `β` and `v` to `α` give the same labelling. -/
theorem moveLab_comm (hvw : v ≠ w) (α β : J) :
    moveLab (moveLab lab w β) v α = moveLab (moveLab lab v α) w β := by
  unfold moveLab; exact Function.update_comm hvw.symm _ _ _

variable (α : J) (hw : lab w ≠ lab v) (hα : lab w ≠ α)

variable (k lab v w) in
/-- The flag tensor product `T_F = H(split (move v α) w) ⊗_{H(move v α)} H(split v)`: first `v`
moves to `α`, then `w` moves into the block `β = lab v`. -/
abbrev FRing : Type _ := EERing (k := k) lab w v α

/-- **`Γ` of the crossing `T_N → T_F`** (KL III (6.8) for `i → j`, (6.9) for `j → i`):
the restriction to the flag variety, a ring homomorphism. -/
def crossNF (t : NRing (k := k) lab v w) : FRing k lab v w α :=
  (tensorEquiv k lab w v α (ne_of_lab_ne hw).symm hα).symm
    (refineHom k (refines_joint_swap (lab := lab) (ne_of_lab_ne hw)) (restrN k lab v w t))

/-- **`Γ` of the crossing `T_F → T_N`** up to sign (KL III (6.9) for `i → j`; minus `Γ` of (6.8)
for `j → i`): the push-forward. -/
def crossFN (s : FRing k lab v w α) : NRing (k := k) lab v w :=
  pushN k lab v w (refineHom k (refines_joint_swap (lab := lab) (ne_of_lab_ne hw).symm)
    (tensorEquiv k lab w v α (ne_of_lab_ne hw).symm hα s))

theorem crossNF_apply (t : NRing (k := k) lab v w) :
    crossNF α hw hα t = (tensorEquiv k lab w v α (ne_of_lab_ne hw).symm hα).symm (refineHom k (refines_joint_swap (lab := lab) (ne_of_lab_ne hw)) (restrN k lab v w t)) := rfl

theorem crossFN_apply (s : FRing k lab v w α) :
    crossFN α hw hα s = pushN k lab v w (refineHom k (refines_joint_swap (lab := lab) (ne_of_lab_ne hw).symm) (tensorEquiv k lab w v α (ne_of_lab_ne hw).symm hα s)) := rfl

theorem crossNF_mul (t t' : NRing (k := k) lab v w) :
    crossNF α hw hα (t * t') = crossNF α hw hα t * crossNF α hw hα t' := by
  simp only [crossNF_apply, map_mul]

theorem crossNF_add (t t' : NRing (k := k) lab v w) :
    crossNF α hw hα (t + t') = crossNF α hw hα t + crossNF α hw hα t' := by
  simp only [crossNF_apply, map_add]

theorem crossFN_add (s s' : FRing k lab v w α) :
    crossFN α hw hα (s + s') = crossFN α hw hα s + crossFN α hw hα s' := by
  simp only [crossFN_apply, map_add]

theorem tensorEquivF_crossNF (t : NRing (k := k) lab v w) :
    tensorEquiv k lab w v α (ne_of_lab_ne hw).symm hα (crossNF α hw hα t) = refineHom k (refines_joint_swap (lab := lab) (ne_of_lab_ne hw)) (restrN k lab v w t) := by
  rw [crossNF_apply, AlgEquiv.apply_symm_apply]

theorem swap_swap (hw : lab w ≠ lab v) (z : BorelRing k (jointLab lab v w)) : refineHom k (refines_joint_swap (lab := lab) (ne_of_lab_ne hw).symm) (refineHom k (refines_joint_swap (lab := lab) (ne_of_lab_ne hw)) z) = z := by
  rw [refineHom_comp_apply, refineHom_self]

theorem swap_swap' (hw : lab w ≠ lab v) (z : BorelRing k (jointLab lab w v)) : refineHom k (refines_joint_swap (lab := lab) (ne_of_lab_ne hw)) (refineHom k (refines_joint_swap (lab := lab) (ne_of_lab_ne hw).symm) z) = z := by
  rw [refineHom_comp_apply, refineHom_self]

/-- **`crossFN ∘ crossNF = δ ·`** on `T_N`: the double crossing is `x_left - x_right`. -/
theorem crossFN_crossNF (t : NRing (k := k) lab v w) :
    crossFN α hw hα (crossNF α hw hα t) = deltaN k lab v w * t := by
  rw [crossFN_apply, tensorEquivF_crossNF, swap_swap hw, pushN_restrN hw]

theorem tensorEquivF_xw :
    tensorEquiv k lab w v α (ne_of_lab_ne hw).symm hα (xi k (moveLab lab v α) w ⊗ₜ 1) =
      xiS k (jointLab lab w v) w (splitLab_singleton _ w) :=
  tensorEquiv_xi_tmul_one lab w v α (ne_of_lab_ne hw).symm hα

theorem tensorEquivF_xv :
    tensorEquiv k lab w v α (ne_of_lab_ne hw).symm hα (1 ⊗ₜ xi k lab v) =
      xiS k (jointLab lab w v) v (joint_singleton_right lab w v (ne_of_lab_ne hw).symm) :=
  tensorEquiv_one_tmul_xi lab w v α (ne_of_lab_ne hw).symm hα

theorem swap_xv :
    refineHom k (refines_joint_swap (lab := lab) (ne_of_lab_ne hw)) (xi k (splitLab lab w) v) =
      xiS k (jointLab lab w v) v (joint_singleton_right lab w v (ne_of_lab_ne hw).symm) :=
  refineHom_mk _ _ _ rfl

theorem swap_xw :
    refineHom k (refines_joint_swap (lab := lab) (ne_of_lab_ne hw)) (xiS k (jointLab lab v w) w (joint_singleton_right lab v w (ne_of_lab_ne hw))) =
      xiS k (jointLab lab w v) w (splitLab_singleton _ w) :=
  refineHom_mk _ _ _ rfl

/-- **`crossNF ∘ crossFN = (1 ⊗ x_v - x_w ⊗ 1) ·`** on `T_F`: the double crossing is
`x_right - x_left`. -/
theorem crossNF_crossFN (s : FRing k lab v w α) :
    crossNF α hw hα (crossFN α hw hα s) =
      ((1 ⊗ₜ xi k lab v) - (xi k (moveLab lab v α) w ⊗ₜ 1)) * s := by
  apply (tensorEquiv k lab w v α (ne_of_lab_ne hw).symm hα).injective
  rw [tensorEquivF_crossNF, crossFN_apply, restrN_pushN hw, map_mul, swap_swap' hw, map_mul, map_sub,
    map_sub, swap_xv hw, swap_xw hw, tensorEquivF_xw α hw hα, tensorEquivF_xv α hw hα]

/-! #### Dots slide through the crossings -/

theorem crossNF_xiN₁ : crossNF α hw hα (xiN₁ k lab v w) = 1 ⊗ₜ xi k lab v := by
  apply (tensorEquiv k lab w v α (ne_of_lab_ne hw).symm hα).injective
  rw [tensorEquivF_crossNF, restrN_xiN₁, swap_xv hw, tensorEquivF_xv α hw hα]

theorem crossNF_xiN₂ : crossNF α hw hα (xiN₂ k lab v w) = xi k (moveLab lab v α) w ⊗ₜ 1 := by
  apply (tensorEquiv k lab w v α (ne_of_lab_ne hw).symm hα).injective
  rw [tensorEquivF_crossNF, restrN_xiN₂ hw, swap_xw hw, tensorEquivF_xw α hw hα]

/-- **Dot slide** (KL III (4.12)): a dot on the left strand before the crossing is a dot on the
right strand after it. -/
theorem crossNF_xiN₁_mul (t : NRing (k := k) lab v w) :
    crossNF α hw hα (xiN₁ k lab v w * t) = (1 ⊗ₜ xi k lab v) * crossNF α hw hα t := by
  rw [crossNF_mul, crossNF_xiN₁]

/-- **Dot slide** (KL III (4.12)): a dot on the right strand before the crossing is a dot on the
left strand after it. -/
theorem crossNF_xiN₂_mul (t : NRing (k := k) lab v w) :
    crossNF α hw hα (xiN₂ k lab v w * t) = (xi k (moveLab lab v α) w ⊗ₜ 1) * crossNF α hw hα t := by
  rw [crossNF_mul, crossNF_xiN₂]

theorem crossFN_mul (s : FRing k lab v w α) (s' : NRing (k := k) lab v w)
    (h : tensorEquiv k lab w v α (ne_of_lab_ne hw).symm hα s = refineHom k (refines_joint_swap (lab := lab) (ne_of_lab_ne hw)) (restrN k lab v w s')) (t : FRing k lab v w α) :
    crossFN α hw hα (s * t) = s' * crossFN α hw hα t := by
  rw [crossFN_apply, crossFN_apply, map_mul, map_mul, h, swap_swap hw, pushN_restrN_mul hw]

/-- **Dot slide** (KL III (4.12)) for `crossFN`, left strand. -/
theorem crossFN_xw_mul (t : FRing k lab v w α) :
    crossFN α hw hα ((xi k (moveLab lab v α) w ⊗ₜ 1) * t) =
      xiN₂ k lab v w * crossFN α hw hα t :=
  crossFN_mul α hw hα _ _ (by rw [tensorEquivF_xw α hw hα, restrN_xiN₂ hw, swap_xw hw]) t

/-- **Dot slide** (KL III (4.12)) for `crossFN`, right strand. -/
theorem crossFN_xv_mul (t : FRing k lab v w α) :
    crossFN α hw hα ((1 ⊗ₜ xi k lab v) * t) = xiN₁ k lab v w * crossFN α hw hα t :=
  crossFN_mul α hw hα _ _ (by rw [tensorEquivF_xv α hw hα, restrN_xiN₁, swap_xv hw]) t

/-! #### KL III's formulas (6.8), (6.9) -/

/-- **KL III (6.8), case `i → j`, and (6.9), case `j → i`**:
`ξ_i^{a} ⊗ ξ_j^{b} ↦ ξ_j^{b} ⊗ ξ_i^{a}` (here `ξ_i = x_v`, `ξ_j = x_w`). -/
theorem crossNF_xi (a b : ℕ) :
    crossNF α hw hα ((xi k (moveLab lab w (lab v)) v ^ a) ⊗ₜ[BorelRing k (moveLab lab w (lab v))]
        (xi k lab w ^ b)) =
      (xi k (moveLab lab v α) w ^ b) ⊗ₜ[BorelRing k (moveLab lab v α)] (xi k lab v ^ a) := by
  apply (tensorEquiv k lab w v α (ne_of_lab_ne hw).symm hα).injective
  rw [tensorEquivF_crossNF, restrN_tmul, map_pow, map_pow, jointLeft_xi, pR_xi_w hw, map_mul,
    map_pow, map_pow, swap_xv hw, swap_xw hw, tensorEquiv_xi, mul_comm]

theorem swap'_xw :
    refineHom k (refines_joint_swap (lab := lab) (ne_of_lab_ne hw).symm)
        (xiS k (jointLab lab w v) w (splitLab_singleton _ w)) =
      xiS k (jointLab lab v w) w (joint_singleton_right lab v w (ne_of_lab_ne hw)) :=
  refineHom_mk _ _ _ rfl

theorem swap'_xv :
    refineHom k (refines_joint_swap (lab := lab) (ne_of_lab_ne hw).symm)
        (xiS k (jointLab lab w v) v (joint_singleton_right lab w v (ne_of_lab_ne hw).symm)) =
      xi k (splitLab lab w) v :=
  refineHom_mk _ _ _ rfl

/-- **KL III (6.9), case `i → j`** (and minus (6.8), case `j → i`):
`ξ_i^{a} ⊗ ξ_j^{b} ↦ ξ_j^{b+1} ⊗ ξ_i^{a} - ξ_j^{b} ⊗ ξ_i^{a+1}` (here `ξ_i = x_w`, `ξ_j = x_v`). -/
theorem crossFN_xi (a b : ℕ) :
    crossFN α hw hα ((xi k (moveLab lab v α) w ^ a) ⊗ₜ[BorelRing k (moveLab lab v α)]
        (xi k lab v ^ b)) =
      (xi k (moveLab lab w (lab v)) v ^ (b + 1)) ⊗ₜ[BorelRing k (moveLab lab w (lab v))]
          (xi k lab w ^ a) -
        (xi k (moveLab lab w (lab v)) v ^ b) ⊗ₜ[BorelRing k (moveLab lab w (lab v))]
          (xi k lab w ^ (a + 1)) := by
  have e : refineHom k (refines_joint_swap (lab := lab) (ne_of_lab_ne hw).symm)
      (tensorEquiv k lab w v α (ne_of_lab_ne hw).symm hα
        ((xi k (moveLab lab v α) w ^ a) ⊗ₜ[BorelRing k (moveLab lab v α)] (xi k lab v ^ b))) =
      restrN k lab v w ((xi k (moveLab lab w (lab v)) v ^ b) ⊗ₜ[BorelRing k (moveLab lab w (lab v))]
        (xi k lab w ^ a)) := by
    rw [tensorEquiv_xi, map_mul, map_pow, map_pow, swap'_xw hw, swap'_xv hw, restrN_tmul, map_pow,
      map_pow, jointLeft_xi, pR_xi_w hw, mul_comm]
  rw [crossFN_apply, e, pushN_restrN hw, deltaN, sub_mul, xiN₁, xiN₂,
    Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul,
    ← pow_succ', ← pow_succ']

/-! #### The signed KLR relation (4.11) for adjacent colours -/

/-- **KL III (4.11)/(6.19), `i · j = -1`, on `T_N`**: with `Γ(ψ_{T_N → T_F}) = crossNF` and
`Γ(ψ_{T_F → T_N}) = -crossFN` (upward strands, `T_N = E_i E_{i+1}`), the double crossing is
`(i - (i+1)) (x_left - x_right) = x_right - x_left`. -/
theorem up_sq_NF (t : NRing (k := k) lab v w) :
    -crossFN α hw hα (crossNF α hw hα t) = (xiN₂ k lab v w - xiN₁ k lab v w) * t := by
  rw [crossFN_crossNF, deltaN, ← neg_mul, neg_sub]

/-- **KL III (4.11)/(6.19), `i · j = -1`, on `T_F`**: with the same signs (upward strands,
`T_F = E_{i+1} E_i`), the double crossing is `((i+1) - i)(x_left - x_right) = x_left - x_right`. -/
theorem up_sq_FN (s : FRing k lab v w α) :
    crossNF α hw hα (-crossFN α hw hα s) =
      ((xi k (moveLab lab v α) w ⊗ₜ 1) - (1 ⊗ₜ xi k lab v)) * s := by
  have : crossNF α hw hα (-crossFN α hw hα s) = -crossNF α hw hα (crossFN α hw hα s) := by
    rw [eq_neg_iff_add_eq_zero, ← crossNF_add, neg_add_cancel, crossNF_apply, map_zero, map_zero,
      map_zero]
  rw [this, crossNF_crossFN, ← neg_mul, neg_sub]

/-! #### Bimodule maps -/

/-- `crossNF` is a map of right `H_k`-modules. -/
theorem crossNF_right (r : BorelRing k lab) (t : NRing (k := k) lab v w) :
    crossNF α hw hα ((1 ⊗ₜ pR k lab w r) * t) = (1 ⊗ₜ pR k lab v r) * crossNF α hw hα t := by
  rw [crossNF_mul]
  congr 1
  apply (tensorEquiv k lab w v α (ne_of_lab_ne hw).symm hα).injective
  rw [tensorEquivF_crossNF, restrN_one_tmul]
  simp only [tensorEquiv, AlgEquiv.coe_ofBijective]
  rw [jointMap_tmul, map_one, one_mul]
  simp only [pR, refineHom_comp_apply]

/-- `crossFN` is a map of right `H_k`-modules. -/
theorem crossFN_right (r : BorelRing k lab) (s : FRing k lab v w α) :
    crossFN α hw hα ((1 ⊗ₜ pR k lab v r) * s) = (1 ⊗ₜ pR k lab w r) * crossFN α hw hα s := by
  refine crossFN_mul α hw hα _ _ ?_ s
  rw [restrN_one_tmul]
  simp only [tensorEquiv, AlgEquiv.coe_ofBijective]
  rw [jointMap_tmul, map_one, one_mul]
  simp only [pR, refineHom_comp_apply]

/-- The left outer ring of `T_N`: `v` moved to `α`, `w` to `β`. -/
theorem refines_outer (hvw : v ≠ w) :
    Refines (moveLab (moveLab lab v α) w (lab v)) (moveLab (moveLab lab w (lab v)) v α) :=
  refines_of_eq (moveLab_comm hvw α (lab v)).symm

/-- `crossNF` is a map of left `H_{+_i +_j k}`-modules. -/
theorem crossNF_left (q : BorelRing k (moveLab (moveLab lab w (lab v)) v α))
    (t : NRing (k := k) lab v w) :
    crossNF α hw hα ((pL k (moveLab lab w (lab v)) v α q ⊗ₜ 1) * t) =
      (pL k (moveLab lab v α) w (lab v) (refineHom k (refines_outer α (ne_of_lab_ne hw)) q) ⊗ₜ 1) *
        crossNF α hw hα t := by
  rw [crossNF_mul]
  congr 1
  apply (tensorEquiv k lab w v α (ne_of_lab_ne hw).symm hα).injective
  rw [tensorEquivF_crossNF, restrN_tmul, map_one, mul_one]
  simp only [tensorEquiv, AlgEquiv.coe_ofBijective]
  rw [jointMap_tmul, map_one, mul_one]
  simp only [pL, refineHom_comp_apply]

/-- `crossFN` is a map of left `H_{+_i +_j k}`-modules. -/
theorem crossFN_left (q : BorelRing k (moveLab (moveLab lab w (lab v)) v α))
    (s : FRing k lab v w α) :
    crossFN α hw hα ((pL k (moveLab lab v α) w (lab v)
        (refineHom k (refines_outer α (ne_of_lab_ne hw)) q) ⊗ₜ 1) * s) =
      (pL k (moveLab lab w (lab v)) v α q ⊗ₜ 1) * crossFN α hw hα s := by
  refine crossFN_mul α hw hα _ _ ?_ s
  rw [restrN_tmul, map_one, mul_one]
  simp only [tensorEquiv, AlgEquiv.coe_ofBijective]
  rw [jointMap_tmul, map_one, mul_one]
  simp only [pL, refineHom_comp_apply]

end NonFlag

/-! ### The degenerate case: the block `β` is empty -/

section Degenerate

variable {k : Type*} [Field k] {V : Type*} [Fintype V] [DecidableEq V] {J : Type*}
  [Fintype J] [DecidableEq J]

attribute [local instance] rightAlgebra midAlgebra

theorem labSet_split_eq_empty {S : V → J} (w : V) {β : J} (h : ∀ u, u ≠ w → S u ≠ β) :
    labSet (splitLab S w) (· = some β) = ∅ := by
  rw [labSet_split_some, Finset.eq_empty_iff_forall_not_mem]
  intro u hu
  rw [Finset.mem_erase, mem_labSet] at hu
  exact h u hu.1 hu.2

/-- **The degenerate non-flag tensor product.** If no variable of `lab` lies in the block `β`
(KL III: `k_{i+1} = k_i`, so that `E_{i+1} E_i 1_k = 0`, resp. `F_i F_{i+1} 1_k = 0`), the
non-flag product `E_i E_{i+1} 1_k` (resp. `F_{i+1} F_i 1_k`) moves the same variable `w` twice,
and in `H(split (move w β) w) ⊗_{H(move w β)} H(split w)` the two dots agree:
`x_w ⊗ 1 = 1 ⊗ x_w`. Hence the double crossing `± (x_left - x_right)` vanishes, matching the
zero map through `0`. -/
theorem degenerate_xi (lab : V → J) (w : V) (β : J) (hβ : ∀ u, lab u ≠ β) :
    (xi k (moveLab lab w β) w ⊗ₜ[BorelRing k (moveLab lab w β)] (1 : BorelRing k (splitLab lab w))) =
      1 ⊗ₜ xi k lab w := by
  have hR : ∀ u, u ≠ w → moveLab lab w β u ≠ β := fun u hu => by
    rw [moveLab, Function.update_of_ne hu]; exact hβ u
  have h1 : pR k (moveLab lab w β) w (xB k (moveLab lab w β) β 1) = xi k (moveLab lab w β) w := by
    rw [pR_xB_succ, if_pos (moveLab_self lab w β).symm, xB_zero, mul_one,
      xB_eq_zero (by rw [labSet_split_eq_empty w hR, Finset.card_empty]; omega), zero_add]
  have h2 : pL k lab w β (xB k (moveLab lab w β) β 1) = xi k lab w := by
    rw [pL_xB_succ, if_pos rfl, xB_zero, mul_one,
      xB_eq_zero (by rw [labSet_split_eq_empty w (fun u _ => hβ u), Finset.card_empty]; omega),
      zero_add]
  rw [← h1, ← h2, ← algebraMap_mid, ← algebraMap_right]
  exact Algebra.TensorProduct.tmul_one_eq_one_tmul _

end Degenerate

end Categorification.Flag

end
