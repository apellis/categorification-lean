/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.Sl2
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Weight strings in locally finite `𝔰𝔩₂`-modules

Chuang and Rouquier (*Derived equivalences for symmetric groups and `sl₂`-categorification*,
arXiv:math/0407205v2, §4.2) attach to a vector `v` of a locally finite `𝔰𝔩₂(ℚ)`-module the
numbers `h₊(v) = max {i | eⁱ v ≠ 0}`, `h₋(v) = max {i | fⁱ v ≠ 0}` and `d(v) = h₊(v) + h₋(v) + 1`.
Their Lemmas 4.1 and 4.3 use that for a nonzero vector `v` of weight `λ`,
`h₋(v) - h₊(v) = λ`, so that `d(v) = 1 + 2 h₊(v) + λ`. This file proves this.

We work with two operators `e`, `f` on a vector space over a field of characteristic zero,
with `h = ef - fe`, `[h, e] = 2e` and `[h, f] = -2f` (`IsSl2Pair`).

## Main results

* `Sl2.iSup_block_eq_top`: a finite-dimensional module is the sum of the eigenspaces of the
  Casimir operator `Ω = h² + 2h + 4fe` for the eigenvalues `m(m + 2)`, `m ∈ ℕ`.
* `Sl2.exists_strings_of_mem_block`: in the `m(m + 2)`-eigenspace of `Ω`, a nonzero vector of
  weight `λ` has `h₊ = (m - λ)/2` and `h₋ = (m + λ)/2`.
* `Sl2.exists_strings`: a nonzero vector `v` of weight `λ` of a finite-dimensional module has
  `e^a v ≠ 0 = e^(a+1) v` and `f^b v ≠ 0 = f^(b+1) v` with `b = a + λ`.
* `Sl2.exists_strings_of_locFin`: the same for modules on which every vector lies in a
  finite-dimensional subspace stable under `e` and `f` (locally finite modules).

The proofs go through the Casimir operator and the primitive decomposition of lie-lean
(`IsSl2Triple.mem_primitiveSpan`) rather than through complete reducibility.
-/

namespace Categorification.Sl2

open Polynomial Module.End

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W]

/-- The operator `h = ef - fe`. -/
def hOp (e f : Module.End K W) : Module.End K W := e * f - f * e

/-- Operators `e`, `f` with `[h, e] = 2e` and `[h, f] = -2f` for `h = ef - fe`: an action of
`𝔰𝔩₂`. -/
structure IsSl2Pair (e f : Module.End K W) : Prop where
  h_e : hOp e f * e - e * hOp e f = (2 : K) • e
  h_f : hOp e f * f - f * hOp e f = -((2 : K) • f)

/-- The Casimir operator `h² + 2h + 4fe`. -/
def casimir (e f : Module.End K W) : Module.End K W :=
  hOp e f * hOp e f + (2 : K) • hOp e f + (4 : K) • (f * e)

/-- The eigenspace of the Casimir operator for the eigenvalue `m(m + 2)`. -/
def block (e f : Module.End K W) (m : ℕ) : Submodule K W :=
  (casimir e f).eigenspace ((m : K) * (m + 2))

section Basic

variable {e f : Module.End K W}

lemma mem_block_iff {m : ℕ} {x : W} :
    x ∈ block e f m ↔ casimir e f x = ((m : K) * (m + 2)) • x := by
  rw [block, mem_eigenspace_iff]

lemma toEnd_eq (x : Module.End K W) : LieModule.toEnd K (Module.End K W) W x = x := by
  simp

/-- `h e = e h + 2 e`, applied to a vector. -/
lemma hOp_e_apply (t : IsSl2Pair e f) (x : W) :
    hOp e f (e x) = e (hOp e f x) + (2 : K) • e x := by
  have := congrArg (fun T : Module.End K W ↦ T x) t.h_e
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at this
  rw [← this]; abel

/-- `h f = f h - 2 f`, applied to a vector. -/
lemma hOp_f_apply (t : IsSl2Pair e f) (x : W) :
    hOp e f (f x) = f (hOp e f x) - (2 : K) • f x := by
  have := congrArg (fun T : Module.End K W ↦ T x) t.h_f
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.neg_apply,
    LinearMap.smul_apply] at this
  rw [sub_eq_iff_eq_add] at this
  rw [this]; abel

lemma hOp_apply (x : W) : hOp e f x = e (f x) - f (e x) := rfl

lemma casimir_apply (x : W) :
    casimir e f x = hOp e f (hOp e f x) + (2 : K) • hOp e f x + (4 : K) • f (e x) := rfl

/-- If `h = 0` then `e = 0` and `f = 0`; otherwise `(h, e, f)` is an `𝔰𝔩₂`-triple. -/
lemma eq_zero_or_isSl2Triple [CharZero K] (t : IsSl2Pair e f) :
    (e = 0 ∧ f = 0) ∨ IsSl2Triple (hOp e f) e f := by
  by_cases h0 : hOp e f = 0
  · left
    have he := t.h_e
    have hf := t.h_f
    rw [h0, zero_mul, mul_zero, sub_zero] at he hf
    exact ⟨(smul_eq_zero.mp he.symm).resolve_left two_ne_zero,
      (smul_eq_zero.mp (neg_eq_zero.mp hf.symm)).resolve_left two_ne_zero⟩
  · right
    refine ⟨h0, ?_, ?_, ?_⟩
    · rw [LieRing.of_associative_ring_bracket]; rfl
    · rw [LieRing.of_associative_ring_bracket, t.h_e, two_smul, two_nsmul]
    · rw [LieRing.of_associative_ring_bracket, t.h_f, two_smul, two_nsmul]

lemma casimir_eq_triple (x : W) :
    IsSl2Triple.casimir K W (hOp e f) e f x = casimir e f x := by
  simp [IsSl2Triple.casimir, casimir, hOp]

/-- The Casimir operator commutes with `e`. -/
lemma casimir_e_apply [CharZero K] (t : IsSl2Pair e f) (x : W) :
    casimir e f (e x) = e (casimir e f x) := by
  rcases eq_zero_or_isSl2Triple t with ⟨rfl, rfl⟩ | t'
  · simp
  · have := congrArg (fun T : Module.End K W ↦ T x) (t'.commute_casimir_e (K := K) (M := W)).eq
    simpa only [Module.End.mul_apply, toEnd_eq, casimir_eq_triple] using this

/-- `Ω = h² - 2h + 4ef`, the Casimir operator of the triple `(-h, f, e)`. -/
lemma casimir_eq_symm (x : W) :
    IsSl2Triple.casimir K W (-hOp e f) f e x = casimir e f x := by
  simp only [IsSl2Triple.casimir, toEnd_eq, casimir, LinearMap.add_apply, Module.End.mul_apply,
    LinearMap.smul_apply, LinearMap.neg_apply, map_neg, neg_neg, smul_neg]
  rw [show e (f x) = f (e x) + hOp e f x by rw [hOp_apply]; abel]
  module

/-- The Casimir operator commutes with `f`. -/
lemma casimir_f_apply [CharZero K] (t : IsSl2Pair e f) (x : W) :
    casimir e f (f x) = f (casimir e f x) := by
  rcases eq_zero_or_isSl2Triple t with ⟨rfl, rfl⟩ | t'
  · simp
  · have := congrArg (fun T : Module.End K W ↦ T x)
      (t'.symm.commute_casimir_e (K := K) (M := W)).eq
    simpa only [Module.End.mul_apply, toEnd_eq, casimir_eq_symm] using this

lemma e_mem_block [CharZero K] (t : IsSl2Pair e f) {m : ℕ} {x : W} (hx : x ∈ block e f m) :
    e x ∈ block e f m := by
  rw [mem_block_iff] at hx ⊢
  rw [casimir_e_apply t, hx, map_smul]

lemma f_mem_block [CharZero K] (t : IsSl2Pair e f) {m : ℕ} {x : W} (hx : x ∈ block e f m) :
    f x ∈ block e f m := by
  rw [mem_block_iff] at hx ⊢
  rw [casimir_f_apply t, hx, map_smul]

lemma pow_e_mem_block [CharZero K] (t : IsSl2Pair e f) {m : ℕ} {x : W}
    (hx : x ∈ block e f m) (k : ℕ) : (e ^ k) x ∈ block e f m := by
  induction k with
  | zero => simpa using hx
  | succ k ih => rw [pow_succ', Module.End.mul_apply]; exact e_mem_block t ih

lemma pow_f_mem_block [CharZero K] (t : IsSl2Pair e f) {m : ℕ} {x : W}
    (hx : x ∈ block e f m) (k : ℕ) : (f ^ k) x ∈ block e f m := by
  induction k with
  | zero => simpa using hx
  | succ k ih => rw [pow_succ', Module.End.mul_apply]; exact f_mem_block t ih

lemma hOp_mem_block [CharZero K] (t : IsSl2Pair e f) {m : ℕ} {x : W}
    (hx : x ∈ block e f m) : hOp e f x ∈ block e f m :=
  sub_mem (e_mem_block t (f_mem_block t hx)) (f_mem_block t (e_mem_block t hx))

/-- The blocks are independent: they are eigenspaces of `Ω` for distinct eigenvalues. -/
lemma iSupIndep_block [CharZero K] : iSupIndep (block e f) := by
  refine (eigenspaces_iSupIndep (casimir e f)).comp fun i j hij ↦ ?_
  have : ((i * (i + 2) : ℕ) : K) = ((j * (j + 2) : ℕ) : K) := by push_cast; exact hij
  have hij' := Nat.cast_injective this
  rcases lt_trichotomy i j with h | h | h
  · exact absurd hij' (Nat.mul_lt_mul'' h (by omega)).ne
  · exact h
  · exact absurd hij' (Nat.mul_lt_mul'' h (by omega)).ne'

end Basic

section FiniteDimensional

variable [CharZero K] [FiniteDimensional K W] {e f : Module.End K W}

lemma isNilpotent_e (t : IsSl2Pair e f) : IsNilpotent e := by
  rcases eq_zero_or_isSl2Triple t with ⟨rfl, rfl⟩ | t'
  · exact IsNilpotent.zero
  · simpa only [toEnd_eq] using t'.isNilpotent_toEnd_e (K := K) (M := W)

lemma isNilpotent_f (t : IsSl2Pair e f) : IsNilpotent f := by
  rcases eq_zero_or_isSl2Triple t with ⟨rfl, rfl⟩ | t'
  · exact IsNilpotent.zero
  · simpa only [toEnd_eq] using t'.isNilpotent_toEnd_f (K := K) (M := W)

omit [FiniteDimensional K W] in
/-- The `f`-strings through primitive vectors of weight `m` lie in the `m`-th block. -/
lemma primitiveSpan_le_block (t : IsSl2Pair e f) (m : ℕ) :
    IsSl2Triple.primitiveSpan K W (hOp e f) e f (m : K) ≤ block e f m := by
  refine iSup_le fun j ↦ ?_
  rintro _ ⟨w, ⟨hwe, hwh⟩, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, toEnd_eq] at hwe
  rw [SetLike.mem_coe, mem_eigenspace_iff, toEnd_eq] at hwh
  rw [toEnd_eq]
  refine pow_f_mem_block t ?_ j
  rw [mem_block_iff, casimir_apply, hwe, map_zero, smul_zero, add_zero, hwh, map_smul, hwh,
    smul_smul]
  module

/-- A finite-dimensional module is the sum of the blocks. -/
theorem iSup_block_eq_top (t : IsSl2Pair e f) : ⨆ m : ℕ, block e f m = ⊤ := by
  rcases eq_zero_or_isSl2Triple t with ⟨rfl, rfl⟩ | t'
  · refine eq_top_iff.mpr fun x _ ↦ Submodule.mem_iSup_of_mem 0 ?_
    rw [mem_block_iff]
    simp [casimir, hOp]
  obtain ⟨n, hn⟩ := isNilpotent_e t
  obtain ⟨N, hN'⟩ := isNilpotent_f t
  have hN : LieModule.toEnd K (Module.End K W) W f ^ (N + 1) = 0 := by
    rw [toEnd_eq, pow_succ, hN', zero_mul]
  set c : ℕ → K := fun m ↦ (m : K) * (m + 2)
  have hcop : ∀ i ∈ Finset.range (N + 1), ∀ j ∈ Finset.range (N + 1), i ≠ j →
      IsCoprime ((X - C (c i)) ^ n) ((X - C (c j)) ^ n) := by
    intro i _ j _ hij
    refine (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr fun hc ↦ hij ?_).isUnit).pow
    have : ((i * (i + 2) : ℕ) : K) = ((j * (j + 2) : ℕ) : K) := by push_cast; exact hc
    have hij' := Nat.cast_injective this
    rcases lt_trichotomy i j with h | h | h
    · exact absurd hij' (Nat.mul_lt_mul'' h (by omega)).ne
    · exact h
    · exact absurd hij' (Nat.mul_lt_mul'' h (by omega)).ne'
  refine eq_top_iff.mpr fun v _ ↦ ?_
  have hv : v ∈ LinearMap.ker (aeval (IsSl2Triple.casimir K W (hOp e f) e f)
      (∏ m ∈ Finset.range (N + 1), (X - C (c m)) ^ n)) := by
    rw [LinearMap.mem_ker, Finset.prod_pow, map_pow]
    exact t'.aeval_casimir_pow_apply_eq_zero hN n (by rw [toEnd_eq, hn, LinearMap.zero_apply])
  refine (iSup₂_le fun m _ ↦ ?_ : _ ≤ ⨆ m : ℕ, block e f m)
    (Module.End.ker_aeval_prod_le_iSup _ _ _ hcop hv)
  intro x hx
  exact Submodule.mem_iSup_of_mem m (primitiveSpan_le_block t m
    (t'.mem_primitiveSpan hN m n n (by rw [toEnd_eq, hn, LinearMap.zero_apply]) hx))

section Strings

omit [FiniteDimensional K W]

variable {m : ℕ} {y : W}

omit [CharZero K] in
/-- On a vector of weight `ν` in the `m`-th block, `4fe = (m - ν)(m + ν + 2)`. -/
lemma four_f_e (hy : y ∈ block e f m) {ν : ℤ} (hν : hOp e f y = (ν : K) • y) :
    (4 : K) • f (e y) = (((m - ν) * (m + ν + 2) : ℤ) : K) • y := by
  rw [mem_block_iff, casimir_apply, hν, map_smul, hν, smul_smul] at hy
  push_cast
  linear_combination (norm := module) hy

omit [CharZero K] in
/-- On a vector of weight `ν` in the `m`-th block, `4ef = (m - ν + 2)(m + ν)`. -/
lemma four_e_f (hy : y ∈ block e f m) {ν : ℤ} (hν : hOp e f y = (ν : K) • y) :
    (4 : K) • e (f y) = (((m - ν + 2) * (m + ν) : ℤ) : K) • y := by
  have h1 := four_f_e hy hν
  have h2 : e (f y) = f (e y) + hOp e f y := by rw [hOp_apply]; abel
  rw [h2, smul_add, h1, hν]
  push_cast
  module

omit [CharZero K] in
lemma hOp_pow_e (t : IsSl2Pair e f) {ν : ℤ} (hν : hOp e f y = (ν : K) • y) (k : ℕ) :
    hOp e f ((e ^ k) y) = ((ν + 2 * k : ℤ) : K) • (e ^ k) y := by
  induction k with
  | zero => simpa using hν
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, hOp_e_apply t, ih, map_smul]
    push_cast
    module

omit [CharZero K] in
lemma hOp_pow_f (t : IsSl2Pair e f) {ν : ℤ} (hν : hOp e f y = (ν : K) • y) (k : ℕ) :
    hOp e f ((f ^ k) y) = ((ν - 2 * k : ℤ) : K) • (f ^ k) y := by
  induction k with
  | zero => simpa using hν
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, hOp_f_apply t, ih, map_smul]
    push_cast
    module

/-- Along the `e`-string of a nonzero vector, `eᵏ y ≠ 0` as long as the coefficients of `4fe`
at the weights passed are nonzero. -/
lemma pow_e_ne_zero (t : IsSl2Pair e f) (hy : y ∈ block e f m) {ν : ℤ}
    (hν : hOp e f y = (ν : K) • y) (hy0 : y ≠ 0) (k : ℕ)
    (hc : ∀ i < k, ((m : ℤ) - (ν + 2 * i)) * (m + (ν + 2 * i) + 2) ≠ 0) : (e ^ k) y ≠ 0 := by
  induction k with
  | zero => simpa using hy0
  | succ k ih =>
    have hk := ih fun i hi ↦ hc i (by omega)
    intro h0
    rw [pow_succ', Module.End.mul_apply] at h0
    have h4 := four_f_e (pow_e_mem_block t hy k) (hOp_pow_e t hν k)
    rw [h0, map_zero, smul_zero, eq_comm, smul_eq_zero] at h4
    exact h4.elim (Int.cast_ne_zero.mpr (hc k (by omega))) hk

/-- Along the `f`-string of a nonzero vector, `fᵏ y ≠ 0` as long as the coefficients of `4ef`
at the weights passed are nonzero. -/
lemma pow_f_ne_zero (t : IsSl2Pair e f) (hy : y ∈ block e f m) {ν : ℤ}
    (hν : hOp e f y = (ν : K) • y) (hy0 : y ≠ 0) (k : ℕ)
    (hc : ∀ i < k, ((m : ℤ) - (ν - 2 * i) + 2) * (m + (ν - 2 * i)) ≠ 0) : (f ^ k) y ≠ 0 := by
  induction k with
  | zero => simpa using hy0
  | succ k ih =>
    have hk := ih fun i hi ↦ hc i (by omega)
    intro h0
    rw [pow_succ', Module.End.mul_apply] at h0
    have h4 := four_e_f (pow_f_mem_block t hy k) (hOp_pow_f t hν k)
    rw [h0, map_zero, smul_zero, eq_comm, smul_eq_zero] at h4
    exact h4.elim (Int.cast_ne_zero.mpr (hc k (by omega))) hk

end Strings

section Vanishing

variable {m : ℕ} {y : W}

lemma eq_zero_of_e (t : IsSl2Pair e f) (hy : y ∈ block e f m) {ν : ℤ}
    (hν : hOp e f y = (ν : K) • y)
    (hc : ∀ i : ℕ, ((m : ℤ) - (ν + 2 * i)) * (m + (ν + 2 * i) + 2) ≠ 0) : y = 0 := by
  by_contra hy0
  obtain ⟨n, hn⟩ := isNilpotent_e t
  exact pow_e_ne_zero t hy hν hy0 n (fun i _ ↦ hc i) (by rw [hn, LinearMap.zero_apply])

lemma eq_zero_of_f (t : IsSl2Pair e f) (hy : y ∈ block e f m) {ν : ℤ}
    (hν : hOp e f y = (ν : K) • y)
    (hc : ∀ i : ℕ, ((m : ℤ) - (ν - 2 * i) + 2) * (m + (ν - 2 * i)) ≠ 0) : y = 0 := by
  by_contra hy0
  obtain ⟨n, hn⟩ := isNilpotent_f t
  exact pow_f_ne_zero t hy hν hy0 n (fun i _ ↦ hc i) (by rw [hn, LinearMap.zero_apply])

/-- In the `m`-th block, a nonzero vector `y` of weight `ν` has `h₊(y) = a`, `h₋(y) = b` with
`m = ν + 2a = -ν + 2b`. -/
theorem exists_strings_of_mem_block (t : IsSl2Pair e f) (hy : y ∈ block e f m) {ν : ℤ}
    (hν : hOp e f y = (ν : K) • y) (hy0 : y ≠ 0) :
    ∃ a b : ℕ, (m : ℤ) = ν + 2 * a ∧ (m : ℤ) = -ν + 2 * b ∧ (e ^ a) y ≠ 0 ∧
      (e ^ (a + 1)) y = 0 ∧ (f ^ b) y ≠ 0 ∧ (f ^ (b + 1)) y = 0 := by
  have hlow : -(m : ℤ) ≤ ν := by
    by_contra hlt
    exact hy0 (eq_zero_of_f t hy hν fun i ↦ mul_ne_zero (by omega) (by omega))
  obtain ⟨a, ha⟩ : ∃ a : ℕ, (m : ℤ) = ν + 2 * a := by
    by_contra hna
    exact hy0 (eq_zero_of_e t hy hν fun i ↦
      mul_ne_zero (fun h ↦ hna ⟨i, by omega⟩) (by omega))
  obtain ⟨b, hb⟩ : ∃ b : ℕ, (b : ℤ) = ν + a := ⟨(ν + a).toNat, Int.toNat_of_nonneg (by omega)⟩
  refine ⟨a, b, ha, by omega, ?_, ?_, ?_, ?_⟩
  · exact pow_e_ne_zero t hy hν hy0 a fun i hi ↦ mul_ne_zero (by omega) (by omega)
  · exact eq_zero_of_e t (pow_e_mem_block t hy _) (hOp_pow_e t hν _)
      fun i ↦ mul_ne_zero (by push_cast; omega) (by push_cast; omega)
  · exact pow_f_ne_zero t hy hν hy0 b fun i hi ↦ mul_ne_zero (by omega) (by omega)
  · exact eq_zero_of_f t (pow_f_mem_block t hy _) (hOp_pow_f t hν _)
      fun i ↦ mul_ne_zero (by push_cast; omega) (by push_cast; omega)

end Vanishing

section Global

variable {e f : Module.End K W}

omit [FiniteDimensional K W] in
/-- An operator preserving the blocks kills a sum of block components only if it kills each
component. -/
lemma map_eq_zero_of_sum (T : Module.End K W) (hT : ∀ m, ∀ w ∈ block e f m, T w ∈ block e f m)
    {s : Finset ℕ} {x : ℕ → W} (hx : ∀ m ∈ s, x m ∈ block e f m)
    (h : T (∑ m ∈ s, x m) = 0) : ∀ m ∈ s, T (x m) = 0 := by
  rw [map_sum] at h
  exact (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mp iSupIndep_block s (fun m ↦ T (x m))
    (fun m hm ↦ hT m _ (hx m hm)) h

/-- **Chuang–Rouquier, §4.2.** A nonzero vector `v` of weight `l` of a finite-dimensional
`𝔰𝔩₂`-module has `h₊(v) = a` and `h₋(v) = b` with `b = a + l`. -/
theorem exists_strings (t : IsSl2Pair e f) {v : W} {l : ℤ} (hv : hOp e f v = (l : K) • v)
    (hv0 : v ≠ 0) :
    ∃ a b : ℕ, (b : ℤ) = a + l ∧ (e ^ a) v ≠ 0 ∧ (e ^ (a + 1)) v = 0 ∧
      (f ^ b) v ≠ 0 ∧ (f ^ (b + 1)) v = 0 := by
  have hmem : v ∈ ⨆ m : ℕ, block e f m := by rw [iSup_block_eq_top t]; trivial
  obtain ⟨x, hx, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).mp hmem
  simp only [Finsupp.sum] at hv hv0 ⊢
  set s := x.support with hs_def
  have hx' : ∀ m ∈ s, x m ∈ block e f m := fun m _ ↦ hx m
  have hs : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    exact hv0 (by rw [h, Finset.sum_empty])
  have hw : ∀ m ∈ s, hOp e f (x m) = (l : K) • x m := by
    intro m hm
    have := map_eq_zero_of_sum (hOp e f - (l : K) • 1)
      (fun m w hw ↦ sub_mem (hOp_mem_block t hw) (Submodule.smul_mem _ _ (by simpa using hw)))
      hx' (by rw [LinearMap.sub_apply, hv]; simp [Finset.smul_sum]) m hm
    simpa [sub_eq_zero] using this
  have hne : ∀ m ∈ s, x m ≠ 0 := fun m hm ↦ Finsupp.mem_support_iff.mp hm
  set M := s.max' hs
  have hM : M ∈ s := s.max'_mem hs
  have hle : ∀ m ∈ s, m ≤ M := fun m hm ↦ s.le_max' m hm
  obtain ⟨a, b, ha, hb, hea, hea', hfb, hfb'⟩ :=
    exists_strings_of_mem_block t (hx M) (hw M hM) (hne M hM)
  refine ⟨a, b, by omega, fun h ↦ hea ?_, ?_, fun h ↦ hfb ?_, ?_⟩
  · exact map_eq_zero_of_sum (e ^ a) (fun m w hw ↦ pow_e_mem_block t hw a) hx' h M hM
  · rw [map_sum]
    refine Finset.sum_eq_zero fun m hm ↦ ?_
    obtain ⟨a', b', ha', -, -, he', -, -⟩ :=
      exists_strings_of_mem_block t (hx m) (hw m hm) (hne m hm)
    have := hle m hm
    rw [show a + 1 = (a - a') + (a' + 1) by omega, pow_add, Module.End.mul_apply, he',
      map_zero]
  · exact map_eq_zero_of_sum (f ^ b) (fun m w hw ↦ pow_f_mem_block t hw b) hx' h M hM
  · rw [map_sum]
    refine Finset.sum_eq_zero fun m hm ↦ ?_
    obtain ⟨a', b', -, hb', -, -, -, hf'⟩ :=
      exists_strings_of_mem_block t (hx m) (hw m hm) (hne m hm)
    have := hle m hm
    rw [show b + 1 = (b - b') + (b' + 1) by omega, pow_add, Module.End.mul_apply, hf',
      map_zero]

end Global

end FiniteDimensional

section LocallyFinite

variable [CharZero K] {e f : Module.End K W}

omit [CharZero K] in
lemma coe_pow_restrict {U : Submodule K W} (g : Module.End K W) (hg : ∀ u ∈ U, g u ∈ U)
    (k : ℕ) (u : U) : (((g.restrict hg) ^ k) u : W) = (g ^ k) u := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', Module.End.mul_apply, LinearMap.coe_restrict_apply, ih,
      pow_succ', Module.End.mul_apply]

omit [CharZero K] in
lemma isSl2Pair_restrict (t : IsSl2Pair e f) {U : Submodule K W} (he : ∀ u ∈ U, e u ∈ U)
    (hf : ∀ u ∈ U, f u ∈ U) : IsSl2Pair (e.restrict he) (f.restrict hf) := by
  constructor
  · ext u
    have := congr($(t.h_e) (u : W))
    simpa [hOp, LinearMap.coe_restrict_apply] using this
  · ext u
    have := congr($(t.h_f) (u : W))
    simpa [hOp, LinearMap.coe_restrict_apply] using this

/-- **Chuang–Rouquier, §4.2**, for locally finite modules: if every vector lies in a
finite-dimensional subspace stable under `e` and `f`, a nonzero vector `v` of weight `l` has
`h₊(v) = a` and `h₋(v) = b` with `b = a + l`. -/
theorem exists_strings_of_locFin (t : IsSl2Pair e f)
    (hfin : ∀ w : W, ∃ U : Submodule K W, FiniteDimensional K U ∧ w ∈ U ∧
      (∀ u ∈ U, e u ∈ U) ∧ (∀ u ∈ U, f u ∈ U))
    {v : W} {l : ℤ} (hv : hOp e f v = (l : K) • v) (hv0 : v ≠ 0) :
    ∃ a b : ℕ, (b : ℤ) = a + l ∧ (e ^ a) v ≠ 0 ∧ (e ^ (a + 1)) v = 0 ∧
      (f ^ b) v ≠ 0 ∧ (f ^ (b + 1)) v = 0 := by
  obtain ⟨U, hU, hvU, he, hf⟩ := hfin v
  have hv' : hOp (e.restrict he) (f.restrict hf) ⟨v, hvU⟩ = (l : K) • ⟨v, hvU⟩ := by
    ext
    simpa [hOp, LinearMap.coe_restrict_apply] using hv
  obtain ⟨a, b, hab, h1, h2, h3, h4⟩ :=
    exists_strings (isSl2Pair_restrict t he hf) hv' (by simpa using hv0)
  refine ⟨a, b, hab, ?_, ?_, ?_, ?_⟩
  · rwa [ne_eq, ← Submodule.coe_eq_zero, coe_pow_restrict] at h1
  · rwa [← Submodule.coe_eq_zero, coe_pow_restrict] at h2
  · rwa [ne_eq, ← Submodule.coe_eq_zero, coe_pow_restrict] at h3
  · rwa [← Submodule.coe_eq_zero, coe_pow_restrict] at h4

end LocallyFinite

end Categorification.Sl2
