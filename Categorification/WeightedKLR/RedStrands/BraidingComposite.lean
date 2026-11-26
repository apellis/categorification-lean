/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.AdjacentBraidingForm

/-!
# Composites of adjacent braidings at `v = 1`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §6.1, proof
of Lemma 6.11. The braid functor `𝔅_w` of a reduced word categorifies the composite of the
braidings of adjacent factors along the word, and at `q = 1` this composite is the permutation
of tensor factors by `w`. This file proves the lattice form of that statement.

* `VOneCongr f f'`: two maps between ordered tensor products preserve the integral lattices and
  agree modulo `(v - 1)` times the lattice. This is stable under composition
  (`VOneCongr.comp`).
* `tensorPermute σ`: the permutation of the tensor factors, `x_1 ⊗ ⋯ ⊗ x_ℓ ↦ x_{σ 1} ⊗ ⋯`.
* `vOneCongr_braidingAt`: the braiding of the factors `n, n + 1` of an ordered tensor product
  with `ℓ = n + 2 + m` factors (`braidingAt`) is `VOneCongr` to the permutation by the
  transposition `swapAt` of those factors. So is every composite of such braidings with the
  permutation by the product of the transpositions (`VOneCongr.comp`, `tensorPermute_trans`).
* `orderedForm_evalOne_of_vOneCongr`: if `f ≡ f'`, then `B(f a, b)` and `B(f' a, b)` are Laurent
  polynomials with the same value at `v = 1`.
-/

noncomputable section

namespace Categorification.Stendhal.FirstWeight

open KLR KLRAlgebra KLGamma Categorification.Graded QuantumGroup QuantumGroup.UDot
open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF
open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

local notation "𝕍" => (RatFunc.X : RatFunc ℚ)
local notation "𝕂" => RatFunc ℚ
local notation "LP" => LaurentPolynomial ℤ
local notation "ev" => integralLaurentEval

section Lattice

variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y}

private abbrev Fac (w : Dom R) := IrreducibleModule R 𝕍 w.1

/-! ### Congruence modulo `v - 1` -/

/-- Two `ℚ(v)`-linear maps between ordered tensor products preserve the integral lattices and
agree modulo `(v - 1)` times the lattice: they have the same limit at `v = 1`. -/
structure VOneCongr {n n' : ℕ} {wt : Fin n → Dom R} {wt' : Fin n' → Dom R}
    (f f' : TensorSpace wt →ₗ[𝕂] TensorSpace wt') : Prop where
  left : ∀ x ∈ integralTensor wt, f x ∈ integralTensor wt'
  right : ∀ x ∈ integralTensor wt, f' x ∈ integralTensor wt'
  sub : ∀ x ∈ integralTensor wt, f x - f' x ∈ vOneTensor wt'

variable {n n' n'' : ℕ} {wt : Fin n → Dom R} {wt' : Fin n' → Dom R} {wt'' : Fin n'' → Dom R}

theorem sub_one_smul_mem_vOneTensor {x : TensorSpace wt} (hx : x ∈ integralTensor wt) :
    (𝕍 - 1) • x ∈ vOneTensor wt :=
  mem_vOneTensor_iff.2 ⟨x, hx, rfl⟩

theorem map_mem_vOneTensor (f : TensorSpace wt →ₗ[𝕂] TensorSpace wt')
    (hf : ∀ x ∈ integralTensor wt, f x ∈ integralTensor wt') {x : TensorSpace wt}
    (hx : x ∈ vOneTensor wt) : f x ∈ vOneTensor wt' := by
  obtain ⟨y, hy, rfl⟩ := mem_vOneTensor_iff.1 hx
  rw [map_smul]
  exact sub_one_smul_mem_vOneTensor (hf y hy)

theorem vOneTensor_le_integralTensor : vOneTensor wt ≤ integralTensor wt := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := mem_vOneTensor_iff.1 hx
  have h := (integralTensor wt).smul_mem (LaurentPolynomial.T 1 - 1 : LP) hy
  rwa [tensor_laurent_smul, map_sub, integralLaurentEval_T, map_one, zpow_one] at h

theorem VOneCongr.refl (f : TensorSpace wt →ₗ[𝕂] TensorSpace wt')
    (hf : ∀ x ∈ integralTensor wt, f x ∈ integralTensor wt') : VOneCongr f f where
  left := hf
  right := hf
  sub x _ := by rw [sub_self]; exact zero_mem _

/-- `VOneCongr` is stable under composition. -/
theorem VOneCongr.comp {g g' : TensorSpace wt' →ₗ[𝕂] TensorSpace wt''}
    {f f' : TensorSpace wt →ₗ[𝕂] TensorSpace wt'} (hg : VOneCongr g g') (hf : VOneCongr f f') :
    VOneCongr (g ∘ₗ f) (g' ∘ₗ f') where
  left x hx := hg.left _ (hf.left x hx)
  right x hx := hg.right _ (hf.right x hx)
  sub x hx := by
    rw [LinearMap.comp_apply, LinearMap.comp_apply,
      show g (f x) - g' (f' x) = g (f x - f' x) + (g (f' x) - g' (f' x)) by rw [map_sub]; abel]
    exact add_mem (map_mem_vOneTensor g hg.left (hf.sub x hx)) (hg.sub _ (hf.right x hx))

/-! ### Permutations of the tensor factors -/

/-- The permutation of the tensor factors by `σ`: `⨂_j x_j ↦ ⨂_j x_{σ j}`, onto the ordered
tensor product with weights `wt ∘ σ`. -/
def tensorPermute (wt : Fin n → Dom R) (σ : Equiv.Perm (Fin n)) :
    TensorSpace wt ≃ₗ[𝕂] TensorSpace (wt ∘ σ) :=
  PiTensorProduct.reindex 𝕂 (fun j => Fac (wt j)) σ.symm

omit [Finite I] in
theorem tensorPermute_tprod (σ : Equiv.Perm (Fin n)) (z : ∀ j, Fac (wt j)) :
    tensorPermute wt σ (PiTensorProduct.tprod 𝕂 z) = PiTensorProduct.tprod 𝕂 fun j => z (σ j) :=
  PiTensorProduct.reindex_tprod _ _

theorem tensorPermute_mem (σ : Equiv.Perm (Fin n)) {x : TensorSpace wt}
    (hx : x ∈ integralTensor wt) : tensorPermute wt σ x ∈ integralTensor (wt ∘ σ) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    rw [tensorPermute_tprod]
    exact Submodule.subset_span ⟨_, fun j => hz (σ j), rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx =>
    rw [tensor_laurent_smul, map_smul, ← tensor_laurent_smul]
    exact Submodule.smul_mem _ c hx

omit [Finite I] in
/-- Permuting by `σ` and then by `τ` is permuting by `σ * τ`. -/
theorem tensorPermute_trans (σ τ : Equiv.Perm (Fin n)) (x : TensorSpace wt) :
    tensorPermute (wt ∘ σ) τ (tensorPermute wt σ x) = tensorPermute wt (σ * τ) x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c z => rw [map_smul, map_smul, map_smul, tensorPermute_tprod, tensorPermute_tprod,
      tensorPermute_tprod]; rfl
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]; rfl

/-! ### The braiding of two adjacent factors -/

section Adjacent

variable (hR : R.IsXRegular) {k m : ℕ} (u : Fin (k + 2 + m) → Dom R)

omit [Finite I] [DecidableEq I] in
private theorem swap_castAdd (j : Fin k) :
    Equiv.swap (Fin.castAdd m (Fin.natAdd k 0)) (Fin.castAdd m (Fin.natAdd k 1))
      (Fin.castAdd m (Fin.castAdd 2 j)) = Fin.castAdd m (Fin.castAdd 2 j) :=
  Equiv.swap_apply_of_ne_of_ne (by simp [Fin.ext_iff]; omega) (by simp [Fin.ext_iff]; omega)

omit [Finite I] [DecidableEq I] in
private theorem swap_natAdd (j : Fin m) :
    Equiv.swap (Fin.castAdd m (Fin.natAdd k 0)) (Fin.castAdd m (Fin.natAdd k 1))
      (Fin.natAdd (k + 2) j) = Fin.natAdd (k + 2) j :=
  Equiv.swap_apply_of_ne_of_ne (by simp [Fin.ext_iff]; omega) (by simp [Fin.ext_iff]; omega)

local notation "π" => Equiv.swap (Fin.castAdd m (Fin.natAdd k 0)) (Fin.castAdd m (Fin.natAdd k 1))

omit [Finite I] in
/-- The flip of two adjacent factors is the permutation of the factors by the transposition. -/
theorem adjacentFlip_eq_tensorPermute (x : TensorSpace u) :
    adjacentFlip u (u ∘ π) (fun j => by simp only [Function.comp_apply, swap_castAdd])
      (by simp only [Function.comp_apply, Equiv.swap_apply_left])
      (by simp only [Function.comp_apply, Equiv.swap_apply_right])
      (fun j => by simp only [Function.comp_apply, swap_natAdd]) x = tensorPermute u π x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c z =>
    rw [map_smul, map_smul, adjacentFlip_tprod, tensorPermute_tprod]
    congr 1
    change (adjacentDecomp (u ∘ π)).symm _ = _
    rw [LinearEquiv.symm_apply_eq, adjacentDecomp_tprod]
    congr 2
    · congr 1
      exact funext fun j => facCongr_apply _ _ _ (congr_arg_heq z (swap_castAdd j).symm)
    · rw [tensorFlip_mk]
      erw [TensorProduct.congr_tmul]
      exact congrArg₂ _ (facCongr_apply _ _ _ (congr_arg_heq z (Equiv.swap_apply_left _ _).symm))
        (facCongr_apply _ _ _ (congr_arg_heq z (Equiv.swap_apply_right _ _).symm))
    · exact funext fun j => facCongr_apply _ _ _ (congr_arg_heq z (swap_natAdd j).symm)
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- **At `v = 1` the adjacent braiding is the permutation of the two factors** (Webster,
arXiv:1309.3796v2, proof of Lemma 6.11). -/
theorem vOneCongr_adjacentBraiding :
    VOneCongr (adjacentBraiding hR u (u ∘ π) (fun j => by simp only [Function.comp_apply,
        swap_castAdd]) (by simp only [Function.comp_apply, Equiv.swap_apply_left])
        (by simp only [Function.comp_apply, Equiv.swap_apply_right])
        (fun j => by simp only [Function.comp_apply, swap_natAdd])).toLinearMap
      (tensorPermute u π).toLinearMap where
  left x hx := adjacentBraiding_mem_integralTensor hR u _ _ _ _ _ hx
  right x hx := tensorPermute_mem π hx
  sub x hx := by
    obtain ⟨y, hy, he⟩ := adjacentBraiding_sub_adjacentFlip_mem hR u _ _ _ _ _ hx
    rw [LinearEquiv.coe_coe, LinearEquiv.coe_coe, ← adjacentFlip_eq_tensorPermute, he]
    exact sub_one_smul_mem_vOneTensor hy

end Adjacent

/-! ### Braidings at a fixed number of factors -/

section Fixed

variable (hR : R.IsXRegular) {ℓ : ℕ}

/-- The transposition of the factors `n, n + 1` of `ℓ = n + 2 + m` factors. -/
def swapAt (n m : ℕ) (h : n + 2 + m = ℓ) : Equiv.Perm (Fin ℓ) :=
  Equiv.swap (Fin.cast h (Fin.castAdd m (Fin.natAdd n 0)))
    (Fin.cast h (Fin.castAdd m (Fin.natAdd n 1)))

/-- The braiding of the factors `n, n + 1` of the ordered tensor product of `ℓ = n + 2 + m`
factors, onto the ordered tensor product with those two weights exchanged (Webster,
arXiv:1309.3796v3, (1.1)). -/
def braidingAt (n m : ℕ) (h : n + 2 + m = ℓ) (u : Fin ℓ → Dom R) :
    TensorSpace u ≃ₗ[𝕂] TensorSpace (u ∘ swapAt n m h) := by
  subst h
  exact adjacentBraiding hR u _ (fun j => by simp only [Function.comp_apply, swapAt,
      Fin.cast_eq_self, swap_castAdd]) (by simp only [Function.comp_apply, swapAt,
      Fin.cast_eq_self, Equiv.swap_apply_left])
    (by simp only [Function.comp_apply, swapAt, Fin.cast_eq_self, Equiv.swap_apply_right])
    (fun j => by simp only [Function.comp_apply, swapAt, Fin.cast_eq_self, swap_natAdd])

/-- **At `v = 1` the braiding of two adjacent factors is their transposition** (Webster,
arXiv:1309.3796v2, proof of Lemma 6.11). -/
theorem vOneCongr_braidingAt (n m : ℕ) (h : n + 2 + m = ℓ) (u : Fin ℓ → Dom R) :
    VOneCongr (braidingAt hR n m h u).toLinearMap (tensorPermute u (swapAt n m h)).toLinearMap := by
  subst h
  exact vOneCongr_adjacentBraiding hR u

end Fixed

end Lattice

/-! ### The form at `v = 1` -/

variable {I : Type} {k Y : Type*} [DecidableEq I] [Field k] [AddCommGroup Y] [Finite I]
    {Q : I → I → MvPolynomial (Fin 2) k} (C : CartanDatum I) (hQ : IsRouquierQ C Q)
    {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular) {ℓ ℓ' : ℕ} {wt : Fin ℓ → Dom R}
    (Λ' : Fin ℓ' → I →₀ ℕ) (wt' : Fin ℓ' → Dom R)
    (hwt' : ∀ r i, (Λ' r i : ℤ) = (wt' r).1 (R.coroot i))

include C hQ Λ' hwt' in
/-- **Maps congruent at `v = 1` have the same form values at `v = 1`** (Webster,
arXiv:1309.3796v2, proof of Lemma 6.11): if `f ≡ f'` and `a`, `b` are lattice vectors, then
`B(f a, b)` and `B(f' a, b)` are Laurent polynomials with the same value at `v = 1`. -/
theorem orderedForm_evalOne_of_vOneCongr
    [∀ ν : Multiset I, Module.Finite k (TensorProductAlgebra k Q Λ' ν)ᵐᵒᵖ]
    {f f' : TensorSpace wt →ₗ[𝕂] TensorSpace wt'}
    (hf : VOneCongr f f') {a : TensorSpace wt} (ha : a ∈ integralTensor wt)
    {b : TensorSpace wt'} (hb : b ∈ integralTensor wt') :
    ∃ p q : LP, TensorPairing.orderedForm hR wt' (f a) b = ev p ∧
      TensorPairing.orderedForm hR wt' (f' a) b = ev q ∧ evalOne p = evalOne q := by
  obtain ⟨y, hy, hyeq⟩ := mem_vOneTensor_iff.1 (hf.sub a ha)
  obtain ⟨q, hq⟩ := orderedForm_integralTensor C hQ hR Λ' wt' hwt' (hf.right a ha) hb
  obtain ⟨r, hr⟩ := orderedForm_integralTensor C hQ hR Λ' wt' hwt' hy hb
  refine ⟨q + (LaurentPolynomial.T (-1) - 1) * r, q, ?_, hq, ?_⟩
  · rw [show f a = f' a + (𝕍 - 1) • y by rw [← hyeq, add_sub_cancel], map_add, map_smulₛₗ,
      LinearMap.add_apply, LinearMap.smul_apply, hq, hr, smul_eq_mul, map_add, map_mul]
    congr 2
    rw [map_sub ev, map_one, integralLaurentEval_T, map_sub, map_one]
    change RatFunc.bar (RatFunc.X : 𝕂) - 1 = _
    rw [← zpow_one (RatFunc.X : 𝕂), bar_zpow_X, zpow_one]
  · simp

end Categorification.Stendhal.FirstWeight
