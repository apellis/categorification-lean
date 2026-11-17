/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.GradedK0.Induction
import Categorification.KLR.ExtTensorK0Equiv

/-!
# Graded `K₀` of `W_{ν'} ⊗ W_{ν''}`

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, Theorem 2.19. The
product of Theorem 2.19 is a map `K₀(W_{ν'}) ⊗_{ℤ[q,q⁻¹]} K₀(W_{ν''}) → K₀(W_{ν'+ν''})`, and the
proof of Theorem 2.19 identifies `K₀(W_{ν'} ⊗ W_{ν''})` with `K₀(W_{ν'}) ⊗ K₀(W_{ν''})` without
comment.

* `GradingDatum.indK0Tensor`: the product `[P] ⊗ [P'] ↦ [Ind (P ⊠ P')]` on
  `K₀(W_{ν'}) ⊗_{ℤ[q,q⁻¹]} K₀(W_{ν''})`. No hypothesis.
* `GradingDatum.k0TensorEquiv`: over a field, `K₀(W_{ν'}) ⊗_{ℤ[q,q⁻¹]} K₀(W_{ν''}) ≅
  K₀(W_{ν'} ⊗ W_{ν''})`, `x ⊗ y ↦ x ⊠ y`, **under the explicit hypothesis**
  `TensorK0Hyp (G.klrGrade ν') (G.klrGrade ν'')`, with the graded dimensions of `W_{ν'}` and
  `W_{ν''}` as instances (supplied for the grading of the standing hypothesis by
  `GalleryAlgebra.hasGdim_klrGrade`).

## The hypothesis `TensorK0Hyp`

`TensorK0Hyp 𝒜 ℬ` asks:
1. `fdA`, `fdB`: the graded simple tops of the indecomposable graded projective modules of
   `W_{ν'}` and `W_{ν''}` are finite-dimensional over `k`;
2. `endA`, `endB`: they are absolutely irreducible (every endomorphism is a scalar);
3. `fdC`: the graded simple tops of the indecomposable graded projective
   `W_{ν'} ⊗ W_{ν''}`-modules are finite-dimensional.

Webster's paper does not supply any of these for weighted KLR algebras: the proof of
Theorem 2.19 uses `K⁰(W_{ν'} ⊗ W_{ν''}) = K⁰(W_{ν'}) ⊗ K⁰(W_{ν''})` without justification. For
unweighted KLR algebras they follow from Khovanov–Lauda I, Proposition 2.12 and Corollary 3.19
(`Categorification.GradingDatum.tensorK0Hyp`); the argument there uses a central polynomial
subalgebra of positive degree over which the algebra is finite, which is not established here for
`W_ν`.
-/

noncomputable section

namespace Categorification.WeightedKLR

open scoped TensorProduct
open Categorification.Graded

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜]

namespace GradingDatum

section Ring

variable {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} (G : GradingDatum Γ)
  (ν' ν'' : I →₀ ℕ)

/-- **The product of Webster's Theorem 2.19 on `K₀(W_{ν'}) ⊗_{ℤ[q,q⁻¹]} K₀(W_{ν''})`**
(arXiv:1209.2463v4): `[P] ⊗ [P'] ↦ [Ind (P ⊠ P')]`. -/
def indK0Tensor : K0 (G.klrGrade ν') ⊗[LaurentPolynomial ℤ] K0 (G.klrGrade ν'') →ₗ[
    LaurentPolynomial ℤ] K0 (G.klrGrade (ν' + ν'')) :=
  TensorProduct.lift (G.indK0 ν' ν'')

@[simp] theorem indK0Tensor_tmul (x : K0 (G.klrGrade ν')) (y : K0 (G.klrGrade ν'')) :
    G.indK0Tensor ν' ν'' (x ⊗ₜ y) = G.indK0 ν' ν'' x y :=
  TensorProduct.lift.tmul _ _

theorem indK0Tensor_of (P : GProj (G.klrGrade ν')) (P' : GProj (G.klrGrade ν'')) :
    G.indK0Tensor ν' ν'' (K0.of P ⊗ₜ K0.of P') = K0.of (G.indProj P P') := by
  rw [indK0Tensor_tmul, indK0_of]

end Ring

section Field

variable {k : Type*} [Field k] {Γ : WeightedGraph I 𝕜 k} (G : GradingDatum Γ)
  (ν' ν'' : I →₀ ℕ) [HasGdim (G.klrGrade ν')] [HasGdim (G.klrGrade ν'')]

/-- **`K₀(W_{ν'}) ⊗_{ℤ[q,q⁻¹]} K₀(W_{ν''}) ≅ K₀(W_{ν'} ⊗ W_{ν''})`** over a field, under the
explicit hypothesis `TensorK0Hyp` (not supplied by Webster, arXiv:1209.2463v4; see the module
docstring): `x ⊗ y ↦ x ⊠ y`. -/
def k0TensorEquiv (H : TensorK0Hyp (G.klrGrade ν') (G.klrGrade ν'')) :
    K0 (G.klrGrade ν') ⊗[LaurentPolynomial ℤ] K0 (G.klrGrade ν'') ≃ₗ[LaurentPolynomial ℤ]
      K0 (tensorGrading (G.klrGrade ν') (G.klrGrade ν'')) :=
  H.extTensorEquiv

variable {G ν' ν''}

@[simp] theorem k0TensorEquiv_tmul (H : TensorK0Hyp (G.klrGrade ν') (G.klrGrade ν''))
    (x : K0 (G.klrGrade ν')) (y : K0 (G.klrGrade ν'')) :
    G.k0TensorEquiv ν' ν'' H (x ⊗ₜ y) = K0.extTensor (G.klrGrade ν') (G.klrGrade ν'') x y :=
  H.extTensorEquiv_tmul x y

theorem k0TensorEquiv_symm_extTensor (H : TensorK0Hyp (G.klrGrade ν') (G.klrGrade ν''))
    (x : K0 (G.klrGrade ν')) (y : K0 (G.klrGrade ν'')) :
    (G.k0TensorEquiv ν' ν'' H).symm (K0.extTensor (G.klrGrade ν') (G.klrGrade ν'') x y) =
      x ⊗ₜ y := by
  rw [LinearEquiv.symm_apply_eq, k0TensorEquiv_tmul]

end Field

end GradingDatum

end Categorification.WeightedKLR
