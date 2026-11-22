/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.Sl2Categorification.Strings

/-!
# Positive bases of locally finite `𝔰𝔩₂`-modules

Chuang and Rouquier (*Derived equivalences for symmetric groups and `sl₂`-categorification*,
arXiv:math/0407205v2, §4.2, **Lemma 4.3**) consider a locally finite `𝔰𝔩₂(ℚ)`-module `V` with a
basis `B` of weight vectors such that the cone `⊕_{b ∈ B} ℚ_{≥0} b` is stable under `e` and `f`.
With `h₊(v) = max {i | eⁱ v ≠ 0}`, `h₋(v) = max {i | fⁱ v ≠ 0}`, `d(v) = h₊(v) + h₋(v) + 1`,
`L₊ = {b ∈ B | f b = 0}` and `L₋ = {b ∈ B | e b = 0}`, they prove:

1. if `c ∈ B` occurs in `e b` or in `f b`, then `d(c) ≤ d(b)`; hence the span `V^{≤ r}` of the
   `b ∈ B` with `d(b) ≤ r` is a submodule;
2. `e^{h₊(b)} b ∈ ⊕_{c ∈ L₋} ℚ_{≥0} c`, and dually for `f`;
3. for `b ∈ L₊` there are `α_b > 0` and `c ∈ L₋` with `e^{h₊(b)} b = α_b c`, and `b ↦ c` is a
   bijection `L₊ ≃ L₋`.

This file proves these statements, for a basis indexed by any type.

## Main results

* `Sl2.IsPos`: an operator mapping basis vectors into the cone.
* `Sl2.IsPos.apply_basis_eq_zero`: a positive operator killing a vector of the cone kills each
  basis vector in its support.
* `Sl2.hPlus`: `h₊(v)` (as `sInf {k | e^{k+1} v = 0}`).
* `Sl2.PosBasis.hPlus_lt_of_e` (Lemma 4.3 (1)) and `Sl2.PosBasis.dOf_le_of_e`,
  `Sl2.PosBasis.dOf_le_of_f`.
* `Sl2.PosBasis.e_basis_eq_zero_of_top` (Lemma 4.3 (2)).
* `Sl2.PosBasis.exists_top_eq_smul` and `Sl2.PosBasis.existsUnique_top` (Lemma 4.3 (3)).
-/

namespace Categorification.Sl2

open Module.End

attribute [local instance 100] LieRing.ofAssociativeRing

section Swap

variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W] {e f : Module.End K W}

lemma hOp_swap : hOp f e = -hOp e f := by simp [hOp]

/-- Exchanging `e` and `f` (and negating `h`) gives again an `𝔰𝔩₂`-action. -/
lemma IsSl2Pair.swap (t : IsSl2Pair e f) : IsSl2Pair f e where
  h_e := by rw [hOp_swap, neg_mul, mul_neg, sub_neg_eq_add, neg_add_eq_sub, ← neg_sub, t.h_f,
    neg_neg]
  h_f := by rw [hOp_swap, neg_mul, mul_neg, sub_neg_eq_add, neg_add_eq_sub, ← neg_sub, t.h_e]

lemma casimir_swap : casimir f e = casimir e f := by
  ext x
  have := casimir_eq_symm (e := e) (f := f) x
  simp only [IsSl2Triple.casimir, toEnd_eq] at this
  rw [← this, casimir_apply, hOp_swap]
  simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.smul_apply,
    LinearMap.neg_apply, map_neg, neg_neg, smul_neg]

lemma block_swap (m : ℕ) : block f e m = block e f m := by
  simp [block, casimir_swap]

end Swap

section HPlus

variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W]

/-- `h₊(v) = max {i | eⁱ v ≠ 0}`, written as the least `k` with `e^{k+1} v = 0`. -/
noncomputable def hPlus (e : Module.End K W) (v : W) : ℕ := sInf {k | (e ^ (k + 1)) v = 0}

lemma hPlus_le {e : Module.End K W} {v : W} {k : ℕ} (h : (e ^ (k + 1)) v = 0) : hPlus e v ≤ k :=
  Nat.sInf_le h

lemma hPlus_eq {e : Module.End K W} {v : W} {a : ℕ} (h1 : (e ^ a) v ≠ 0)
    (h2 : (e ^ (a + 1)) v = 0) : hPlus e v = a := by
  refine le_antisymm (hPlus_le h2) (le_csInf ⟨a, h2⟩ fun k hk ↦ ?_)
  by_contra hlt
  apply h1
  rw [show a = (a - (k + 1)) + (k + 1) by omega, pow_add, Module.End.mul_apply,
    hk, map_zero]

lemma pow_hPlus_succ {e : Module.End K W} {v : W} {a : ℕ} (h2 : (e ^ (a + 1)) v = 0) :
    (e ^ (hPlus e v + 1)) v = 0 :=
  Nat.sInf_mem (s := {k | (e ^ (k + 1)) v = 0}) ⟨a, h2⟩

end HPlus

section Cone

variable {ι V : Type*} [AddCommGroup V] [Module ℚ V] (B : Module.Basis ι ℚ V)

/-- The cone of vectors with nonnegative coordinates in the basis `B`. -/
def cone : Set V := {v | ∀ j, 0 ≤ B.repr v j}

/-- An operator mapping every basis vector into the cone. -/
def IsPos (T : Module.End ℚ V) : Prop := ∀ i, T (B i) ∈ cone B

variable {B}

lemma basis_mem_cone (i : ι) : B i ∈ cone B := fun j ↦ by
  classical
  rw [Module.Basis.repr_self, Finsupp.single_apply]
  split_ifs <;> norm_num

lemma repr_apply_eq_sum (T : Module.End ℚ V) (v : V) (j : ι) :
    B.repr (T v) j = ∑ i ∈ (B.repr v).support, B.repr v i * B.repr (T (B i)) j := by
  conv_lhs => rw [← B.linearCombination_repr v]
  rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_sum, Finsupp.finsetSum_apply]
  simp [map_smul]

lemma IsPos.mem_cone {T : Module.End ℚ V} (hT : IsPos B T) {v : V} (hv : v ∈ cone B) :
    T v ∈ cone B := fun j ↦ by
  rw [repr_apply_eq_sum]
  exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (hv i) (hT i j)

lemma isPos_one : IsPos B 1 := fun i ↦ basis_mem_cone i

lemma IsPos.mul {S T : Module.End ℚ V} (hS : IsPos B S) (hT : IsPos B T) : IsPos B (S * T) :=
  fun i ↦ hS.mem_cone (hT i)

lemma IsPos.pow {T : Module.End ℚ V} (hT : IsPos B T) (k : ℕ) : IsPos B (T ^ k) := by
  induction k with
  | zero => exact isPos_one
  | succ k ih => rw [pow_succ]; exact ih.mul hT

/-- A positive operator killing a vector of the cone kills every basis vector in its
support. -/
lemma IsPos.apply_basis_eq_zero {T : Module.End ℚ V} (hT : IsPos B T) {v : V}
    (hv : v ∈ cone B) (h : T v = 0) {c : ι} (hc : B.repr v c ≠ 0) : T (B c) = 0 := by
  apply B.repr.injective
  rw [map_zero]
  ext j
  have h0 : B.repr (T v) j = 0 := by rw [h]; simp
  rw [repr_apply_eq_sum] at h0
  have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ mul_nonneg (hv i) (hT i j)).mp h0 c
    (Finsupp.mem_support_iff.mpr hc)
  simpa [hc] using this

/-- The projection killing the basis vector `B b`. -/
noncomputable def killBasis (b : ι) : Module.End ℚ V :=
  LinearMap.id - (B.coord b).smulRight (B b)

lemma killBasis_apply (b : ι) (v : V) : killBasis (B := B) b v = v - B.repr v b • B b := rfl

lemma isPos_killBasis (b : ι) : IsPos B (killBasis (B := B) b) := fun i j ↦ by
  classical
  rw [killBasis_apply, Module.Basis.repr_self, Finsupp.single_apply]
  split_ifs with h
  · subst h; simp
  · rw [zero_smul, sub_zero]; exact basis_mem_cone i j

lemma eq_smul_of_killBasis_eq_zero {b : ι} {v : V} (h : killBasis (B := B) b v = 0) :
    v = B.repr v b • B b := by
  rwa [killBasis_apply, sub_eq_zero] at h

lemma eq_of_basis_eq_smul {c c' : ι} {s : ℚ} (h : B c = s • B c') (_hs : s ≠ 0) : c = c' := by
  classical
  by_contra hne
  have := congrArg (fun v ↦ B.repr v c) h
  simp [Ne.symm hne] at this

lemma exists_repr_ne_zero {v : V} (hv : v ≠ 0) : ∃ c, B.repr v c ≠ 0 := by
  by_contra h
  push Not at h
  exact hv (B.repr.injective (by ext c; simp [h c]))

end Cone

section Lowest

variable {W : Type*} [AddCommGroup W] [Module ℚ W] {e f : Module.End ℚ W}

/-- On a vector `y` of weight `-a` killed by `f`, `f^j e^j y = (a!/(a-j)!) j! y` for `j ≤ a`. -/
lemma pow_f_pow_e_eq (t : IsSl2Pair e f) {a : ℕ} {y : W} (hy : f y = 0)
    (hν : hOp e f y = ((-(a : ℤ) : ℤ) : ℚ) • y) {j : ℕ} (hj : j ≤ a) :
    (f ^ j) ((e ^ j) y) = ((a.descFactorial j * j.factorial : ℕ) : ℚ) • y := by
  have hb : y ∈ block e f a := by
    rw [mem_block_iff, casimir_apply, hν, map_smul, hν]
    have hfe : f (e y) = -hOp e f y := by rw [hOp_apply, hy, map_zero, zero_sub, neg_neg]
    rw [hfe, hν]
    push_cast
    simp only [smul_neg, neg_neg, neg_smul]
    module
  have step : ∀ k < a, f ((e ^ (k + 1)) y) = ((((a : ℤ) - k) * (k + 1) : ℤ) : ℚ) • (e ^ k) y := by
    intro k hk
    have h4 := four_f_e (pow_e_mem_block t hb k) (hOp_pow_e t hν k)
    rw [pow_succ', Module.End.mul_apply]
    have h4' : (4 : ℚ) • f (e ((e ^ k) y)) =
        (4 : ℚ) • ((((a : ℤ) - k) * (k + 1) : ℤ) : ℚ) • (e ^ k) y := by
      rw [h4, smul_smul]; push_cast; ring_nf
    exact smul_right_injective W (by norm_num : (4 : ℚ) ≠ 0) h4'
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ f, Module.End.mul_apply, step j (by omega), map_smul, ih (by omega), smul_smul,
      Nat.descFactorial_succ, Nat.factorial_succ]
    congr 1
    push_cast [Nat.cast_sub (show j ≤ a by omega)]
    ring

/-- On a vector `y` of weight `-a` killed by `f`, `f^j e^j y` is a positive multiple of `y` for
`j ≤ a` (in fact `(j!)² binom(a, j)² ...`; only positivity is used). -/
lemma exists_pow_f_pow_e (t : IsSl2Pair e f) {a : ℕ} {y : W} (hy : f y = 0)
    (hν : hOp e f y = ((-(a : ℤ) : ℤ) : ℚ) • y) {j : ℕ} (hj : j ≤ a) :
    ∃ β : ℚ, 0 < β ∧ (f ^ j) ((e ^ j) y) = β • y := by
  have hb : y ∈ block e f a := by
    rw [mem_block_iff, casimir_apply, hν, map_smul, hν]
    have hfe : f (e y) = -hOp e f y := by rw [hOp_apply, hy, map_zero, zero_sub, neg_neg]
    rw [hfe, hν]
    push_cast
    simp only [smul_neg, neg_neg, neg_smul]
    module
  have step : ∀ k < a, f ((e ^ (k + 1)) y) = ((((a : ℤ) - k) * (k + 1) : ℤ) : ℚ) • (e ^ k) y := by
    intro k hk
    have h4 := four_f_e (pow_e_mem_block t hb k) (hOp_pow_e t hν k)
    rw [pow_succ', Module.End.mul_apply]
    have h4' : (4 : ℚ) • f (e ((e ^ k) y)) =
        (4 : ℚ) • ((((a : ℤ) - k) * (k + 1) : ℤ) : ℚ) • (e ^ k) y := by
      rw [h4, smul_smul]; push_cast; ring_nf
    exact smul_right_injective W (by norm_num : (4 : ℚ) ≠ 0) h4'
  induction j with
  | zero => exact ⟨1, one_pos, by simp⟩
  | succ j ih =>
    obtain ⟨β, hβ, h⟩ := ih (by omega)
    refine ⟨((((a : ℤ) - j) * (j + 1) : ℤ) : ℚ) * β, mul_pos ?_ hβ, ?_⟩
    · have : (0 : ℤ) < ((a : ℤ) - j) * (j + 1) := mul_pos (by omega) (by omega)
      exact_mod_cast this
    · rw [pow_succ f, Module.End.mul_apply, step j (by omega), map_smul, h, smul_smul]

end Lowest

/-- `d(v) = h₊(v) + h₋(v) + 1`. -/
noncomputable def dOf {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    (e f : Module.End K W) (v : W) : ℕ :=
  hPlus e v + hPlus f v + 1

variable {ι V : Type*} [AddCommGroup V] [Module ℚ V]

/-- The hypotheses of Chuang–Rouquier, Lemma 4.3: `B` is a basis of weight vectors (of weights
`wt`) of a locally finite `𝔰𝔩₂`-module whose cone is stable under `e` and `f`. -/
structure PosBasis (B : Module.Basis ι ℚ V) (e f : Module.End ℚ V) (wt : ι → ℤ) : Prop where
  sl2 : IsSl2Pair e f
  wt_eq : ∀ i, hOp e f (B i) = (wt i : ℚ) • B i
  pos_e : IsPos B e
  pos_f : IsPos B f
  locFin : ∀ w : V, ∃ U : Submodule ℚ V, FiniteDimensional ℚ U ∧ w ∈ U ∧
    (∀ u ∈ U, e u ∈ U) ∧ (∀ u ∈ U, f u ∈ U)

/-- The span `V^{≤ r}` of the basis vectors `b` with `d(b) ≤ r`. -/
noncomputable def lowSpan (B : Module.Basis ι ℚ V) (e f : Module.End ℚ V) (r : ℕ) :
    Submodule ℚ V :=
  Submodule.span ℚ (B '' {i | dOf e f (B i) ≤ r})

namespace PosBasis

variable {B : Module.Basis ι ℚ V} {e f : Module.End ℚ V} {wt : ι → ℤ} (P : PosBasis B e f wt)
include P

/-- Exchanging `e` and `f` and negating the weights. -/
lemma swap : PosBasis B f e (fun i ↦ -wt i) where
  sl2 := P.sl2.swap
  wt_eq i := by rw [hOp_swap, LinearMap.neg_apply, P.wt_eq]; push_cast; rw [neg_smul]
  pos_e := P.pos_f
  pos_f := P.pos_e
  locFin w := by
    obtain ⟨U, h1, h2, h3, h4⟩ := P.locFin w
    exact ⟨U, h1, h2, h4, h3⟩

/-- `h₋(b) - h₊(b) = wt b`, with the strings `e^{h₊} b ≠ 0 = e^{h₊ + 1} b` and
`f^{h₋} b ≠ 0 = f^{h₋ + 1} b`. -/
lemma strings (i : ι) : (hPlus f (B i) : ℤ) = hPlus e (B i) + wt i ∧
    (e ^ hPlus e (B i)) (B i) ≠ 0 ∧ (e ^ (hPlus e (B i) + 1)) (B i) = 0 ∧
    (f ^ hPlus f (B i)) (B i) ≠ 0 ∧ (f ^ (hPlus f (B i) + 1)) (B i) = 0 := by
  obtain ⟨a, b, hab, h1, h2, h3, h4⟩ :=
    exists_strings_of_locFin P.sl2 P.locFin (P.wt_eq i) (B.ne_zero i)
  rw [hPlus_eq h1 h2, hPlus_eq h3 h4]
  exact ⟨hab, h1, h2, h3, h4⟩

/-- A vector of weight `ν` only involves basis vectors of weight `ν`. -/
lemma wt_eq_of_repr_ne_zero {v : V} {ν : ℤ} (hv : hOp e f v = (ν : ℚ) • v) {c : ι}
    (hc : B.repr v c ≠ 0) : wt c = ν := by
  classical
  have h1 : B.repr (hOp e f v) c = (ν : ℚ) * B.repr v c := by rw [hv]; simp
  rw [repr_apply_eq_sum, Finset.sum_eq_single c] at h1
  · simp only [P.wt_eq, map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
      Finsupp.single_eq_same, smul_eq_mul, mul_one] at h1
    have : (wt c : ℚ) = ν := mul_left_cancel₀ hc (h1.trans (mul_comm _ _))
    exact_mod_cast this
  · intro i _ hi
    simp [P.wt_eq, hi]
  · intro h
    exact absurd (Finsupp.mem_support_iff.mpr hc) h

lemma hOp_e_basis (i : ι) : hOp e f (e (B i)) = ((wt i + 2 : ℤ) : ℚ) • e (B i) := by
  rw [hOp_e_apply P.sl2, P.wt_eq, map_smul]; push_cast; module

lemma hOp_pow_e_basis (i : ι) (k : ℕ) :
    hOp e f ((e ^ k) (B i)) = ((wt i + 2 * k : ℤ) : ℚ) • (e ^ k) (B i) :=
  hOp_pow_e P.sl2 (P.wt_eq i) k

/-- **Chuang–Rouquier, Lemma 4.3 (1)**, first step: if `c` occurs in `e b`, then
`h₊(c) < h₊(b)`. -/
theorem hPlus_lt_of_e {i c : ι} (hc : B.repr (e (B i)) c ≠ 0) :
    hPlus e (B c) + 1 ≤ hPlus e (B i) := by
  obtain ⟨-, -, h2, -, -⟩ := P.strings i
  have h0 : (e ^ hPlus e (B i)) (e (B i)) = 0 := by
    rw [← Module.End.mul_apply, ← pow_succ]; exact h2
  have := (P.pos_e.pow (hPlus e (B i))).apply_basis_eq_zero (P.pos_e i) h0 hc
  rcases hh : hPlus e (B i) with _ | k
  · rw [hh, pow_zero, Module.End.one_apply] at this
    exact absurd this (B.ne_zero c)
  · rw [hh] at this
    have := hPlus_le this
    omega

/-- **Chuang–Rouquier, Lemma 4.3 (1)**: if `c` occurs in `e b`, then `d(c) ≤ d(b)`. -/
theorem dOf_le_of_e {i c : ι} (hc : B.repr (e (B i)) c ≠ 0) :
    dOf e f (B c) ≤ dOf e f (B i) := by
  have h1 := P.hPlus_lt_of_e hc
  have hwc := P.wt_eq_of_repr_ne_zero (P.hOp_e_basis i) hc
  have hsi := (P.strings i).1
  have hsc := (P.strings c).1
  simp only [dOf]
  omega

/-- **Chuang–Rouquier, Lemma 4.3 (1)**: if `c` occurs in `f b`, then `d(c) ≤ d(b)`. -/
theorem dOf_le_of_f {i c : ι} (hc : B.repr (f (B i)) c ≠ 0) :
    dOf e f (B c) ≤ dOf e f (B i) := by
  have := P.swap.dOf_le_of_e hc
  simp only [dOf] at this ⊢
  omega

/-- **Chuang–Rouquier, Lemma 4.3 (2)**: every basis vector occurring in `e^{h₊(b)} b` is killed
by `e` (and the coefficients are nonnegative). -/
theorem e_basis_eq_zero_of_top {i c : ι} (hc : B.repr ((e ^ hPlus e (B i)) (B i)) c ≠ 0) :
    e (B c) = 0 := by
  refine P.pos_e.apply_basis_eq_zero ((P.pos_e.pow _) i) ?_ hc
  rw [← Module.End.mul_apply, ← pow_succ']
  exact (P.strings i).2.2.1

/-- **Chuang–Rouquier, Lemma 4.3 (1)**: `V^{≤ r}` is stable under `e`. -/
theorem e_mem_lowSpan {r : ℕ} {v : V} (hv : v ∈ lowSpan B e f r) : e v ∈ lowSpan B e f r := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    rw [← B.linearCombination_repr (e (B i)), Finsupp.linearCombination_apply]
    refine Submodule.sum_mem _ fun c hc ↦ Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact ⟨c, le_trans (P.dOf_le_of_e (Finsupp.mem_support_iff.mp hc)) hi, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

/-- **Chuang–Rouquier, Lemma 4.3 (1)**: `V^{≤ r}` is stable under `f`. -/
theorem f_mem_lowSpan {r : ℕ} {v : V} (hv : v ∈ lowSpan B e f r) : f v ∈ lowSpan B e f r := by
  have h : lowSpan B e f r = lowSpan B f e r := by
    simp only [lowSpan, dOf, add_comm (hPlus e _)]
  rw [h] at hv ⊢
  exact P.swap.e_mem_lowSpan hv

/-- A basis vector killed by `f` has weight `-h₊(b)`. -/
lemma wt_of_f_eq_zero {b : ι} (hb : f (B b) = 0) : wt b = -(hPlus e (B b) : ℤ) := by
  have h := (P.strings b).1
  have : hPlus f (B b) = 0 := Nat.le_zero.mp (hPlus_le (by rw [zero_add, pow_one]; exact hb))
  omega

lemma hOp_of_f_eq_zero {b : ι} (hb : f (B b) = 0) :
    hOp e f (B b) = ((-(hPlus e (B b) : ℤ) : ℤ) : ℚ) • B b := by
  rw [P.wt_eq, P.wt_of_f_eq_zero hb]

/-- **Chuang–Rouquier, Lemma 4.3 (3)**, first part: for `b ∈ L₊` there are `c ∈ L₋` and
`α > 0` with `e^{h₊(b)} b = α c`. -/
theorem exists_top_eq_smul {b : ι} (hb : f (B b) = 0) :
    ∃ c, e (B c) = 0 ∧ ∃ α : ℚ, 0 < α ∧ (e ^ hPlus e (B b)) (B b) = α • B c := by
  obtain ⟨β, -, hfe⟩ := exists_pow_f_pow_e P.sl2 hb (P.hOp_of_f_eq_zero hb) le_rfl
  have hv0 : (e ^ hPlus e (B b)) (B b) ≠ 0 := (P.strings b).2.1
  obtain ⟨c, hc⟩ := exists_repr_ne_zero (B := B) hv0
  have hec : e (B c) = 0 := P.e_basis_eq_zero_of_top hc
  have hvcone : (e ^ hPlus e (B b)) (B b) ∈ cone B := (P.pos_e.pow _) b
  have hT : (killBasis (B := B) b * f ^ hPlus e (B b)) ((e ^ hPlus e (B b)) (B b)) = 0 := by
    rw [Module.End.mul_apply, hfe, map_smul, killBasis_apply]; simp
  have h1 := ((isPos_killBasis b).mul (P.pos_f.pow _)).apply_basis_eq_zero hvcone hT hc
  rw [Module.End.mul_apply] at h1
  have hγ := eq_smul_of_killBasis_eq_zero h1
  have hwb := P.hOp_pow_e_basis b (hPlus e (B b))
  rw [P.wt_of_f_eq_zero hb] at hwb
  have hwc : wt c = hPlus e (B b) := P.wt_eq_of_repr_ne_zero (ν := (hPlus e (B b) : ℤ))
    (by rw [hwb]; congr 1; push_cast; ring) hc
  have hνc : hOp f e (B c) = ((-(hPlus e (B b) : ℤ) : ℤ) : ℚ) • B c := by
    rw [hOp_swap, LinearMap.neg_apply, P.wt_eq, hwc]; push_cast; rw [neg_smul]
  obtain ⟨β', hβ', hef⟩ := exists_pow_f_pow_e P.sl2.swap hec hνc le_rfl
  rw [hγ, map_smul] at hef
  have hγ0 : B.repr ((f ^ hPlus e (B b)) (B c)) b ≠ 0 := by
    intro h
    rw [h, zero_smul, eq_comm, smul_eq_zero] at hef
    exact hef.elim hβ'.ne' (B.ne_zero c)
  have hvB : (e ^ hPlus e (B b)) (B b) =
      (β' / B.repr ((f ^ hPlus e (B b)) (B c)) b) • B c := by
    rw [div_eq_inv_mul, ← smul_smul, ← hef, smul_smul, inv_mul_cancel₀ hγ0, one_smul]
  refine ⟨c, hec, _, ?_, hvB⟩
  have hr : B.repr ((e ^ hPlus e (B b)) (B b)) c =
      β' / B.repr ((f ^ hPlus e (B b)) (B c)) b := by
    rw [hvB]; simp
  exact lt_of_le_of_ne (hr ▸ hvcone c) fun h ↦ hc (hr.trans h.symm)

/-- **Chuang–Rouquier, Lemma 4.3 (3)**: `b ↦ c` with `e^{h₊(b)} b ∈ ℚ_{>0} c` is a bijection
from `L₊ = {b | f b = 0}` to `L₋ = {c | e c = 0}`: every `c ∈ L₋` arises from exactly one
`b ∈ L₊`. -/
theorem existsUnique_top {c : ι} (hc : e (B c) = 0) :
    ∃! b, f (B b) = 0 ∧ ∃ α : ℚ, 0 < α ∧ (e ^ hPlus e (B b)) (B b) = α • B c := by
  -- the weight of the target of `b` is `h₊(b)`
  have key : ∀ b, f (B b) = 0 → ∀ α : ℚ, 0 < α →
      (e ^ hPlus e (B b)) (B b) = α • B c → wt c = hPlus e (B b) := by
    intro b hb α hα h
    have hwb := P.hOp_pow_e_basis b (hPlus e (B b))
    rw [P.wt_of_f_eq_zero hb] at hwb
    refine P.wt_eq_of_repr_ne_zero (v := (e ^ hPlus e (B b)) (B b))
      (ν := (hPlus e (B b) : ℤ)) (by rw [hwb]; congr 1; push_cast; ring) ?_
    rw [h]; simp [hα.ne']
  obtain ⟨b, hb, α', hα', h'⟩ := P.swap.exists_top_eq_smul (b := c) hc
  obtain ⟨c', hc', α, hα, hbc⟩ := P.exists_top_eq_smul hb
  have hwc : -wt c = -(hPlus f (B c) : ℤ) := P.swap.wt_of_f_eq_zero hc
  have hwb : -wt b = hPlus f (B c) := by
    have := P.swap.wt_eq_of_repr_ne_zero (v := (f ^ hPlus f (B c)) (B c))
      (ν := (hPlus f (B c) : ℤ)) (c := b) ?_ (by rw [h']; simp [hα'.ne'])
    · exact this
    · have h2 := P.swap.hOp_pow_e_basis c (hPlus f (B c))
      rw [hwc] at h2; rw [h2]; congr 1; push_cast; ring
  have hab : hPlus e (B b) = hPlus f (B c) := by
    have := P.wt_of_f_eq_zero hb; omega
  have hνc : hOp f e (B c) = ((-(hPlus f (B c) : ℤ) : ℤ) : ℚ) • B c := by
    rw [hOp_swap, LinearMap.neg_apply, P.wt_eq, show wt c = (hPlus f (B c) : ℤ) by omega]
    push_cast; rw [neg_smul]
  obtain ⟨β, hβ, hef⟩ := exists_pow_f_pow_e P.sl2.swap hc hνc le_rfl
  rw [h', map_smul, ← hab, hbc, smul_smul] at hef
  have hcc : c' = c := by
    refine eq_of_basis_eq_smul (B := B) (s := (α' * α)⁻¹ * β) ?_ (by positivity)
    rw [← smul_smul, ← hef, smul_smul, inv_mul_cancel₀ (mul_pos hα' hα).ne', one_smul]
  rw [hcc] at hbc
  refine ⟨b, ⟨hb, α, hα, hbc⟩, fun b₂ ⟨hb₂, α₂, hα₂, h₂⟩ ↦ ?_⟩
  have k₂ := key b₂ hb₂ α₂ hα₂ h₂
  have k₁ := key b hb α hα hbc
  obtain ⟨γ, hγ, hfe⟩ := exists_pow_f_pow_e P.sl2 hb₂ (P.hOp_of_f_eq_zero hb₂) le_rfl
  obtain ⟨γ₁, hγ₁, hfe₁⟩ := exists_pow_f_pow_e P.sl2 hb (P.hOp_of_f_eq_zero hb) le_rfl
  have he : hPlus e (B b₂) = hPlus e (B b) := by omega
  rw [h₂, map_smul, he] at hfe
  rw [hbc, map_smul] at hfe₁
  -- `γ b₂ = α₂ f^a c` and `γ₁ b = α f^a c`
  refine eq_of_basis_eq_smul (B := B) (s := (α₂ * γ₁) / (γ * α)) ?_
    (div_pos (mul_pos hα₂ hγ₁) (mul_pos hγ hα)).ne'
  have e1 : B b₂ = (γ⁻¹ * α₂) • (f ^ hPlus e (B b)) (B c) := by
    rw [← smul_smul, hfe, smul_smul, inv_mul_cancel₀ hγ.ne', one_smul]
  have e2 : (f ^ hPlus e (B b)) (B c) = (γ₁ / α) • B b := by
    rw [div_eq_inv_mul, ← smul_smul, ← hfe₁, smul_smul, inv_mul_cancel₀ hα.ne', one_smul]
  rw [e1, e2, smul_smul]; congr 1; field_simp

end PosBasis

end Categorification.Sl2
