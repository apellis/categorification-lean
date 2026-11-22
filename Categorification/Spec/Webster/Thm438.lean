/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.RightTensorHomForm

/-!
# Specification: Webster, arXiv:1309.3796v2, Theorem 4.38

Source: B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
§4.7, Theorem 4.38 (with Lemma 4.36 for the Hom form and Lemma 4.37 for uniqueness).

Paraphrase of the source. For a sequence `λ = (λ₁, …, λ_ℓ)` of dominant weights, there is a
canonical isomorphism from the graded Grothendieck group of finitely generated graded projective
right `T^λ`-modules to the integral form `V^λ_ℤ` of `V_{λ₁} ⊗ ⋯ ⊗ V_{λ_ℓ}`, sending the class
of the projective attached to a loading to the corresponding vector built from highest weight
vectors and the action of the `F_i`; it intertwines the Euler form `gdim HOM(P, Q)` with the
bilinear form on `V^λ_ℤ` introduced before Proposition 4.33.

This file is a specification: nothing in the library imports it. Its only content beyond the
statements is the binding of each statement to the library proof. Any change to this file needs
the maintainer's approval.

## Trusted base (the objects a reader must check against the source)

Each item has a definition card in `docs/Faithfulness/cards/`.
* `Categorification.Stendhal.stendhalGradingDatum`, `TensorProductAlgebra` (via
  `tensorProductGrade`): the graded tensor product algebra `T^λ`
  (card `tensor-product-algebra.md`).
* `Categorification.Graded.K0`, `oppositeGrade`: `K₀` of graded projective modules; right modules
  are modules over the opposite graded algebra (card `graded-k0.md`).
* `rightTensorProjectiveGroup`, `rightTensorWordProjectiveClass`: the classes of the right
  projectives attached to (divided-power) loadings (card `word-projectives.md`).
* `integralTensor`, `integralWordVector`: the integral form `V^λ_ℤ` and the vectors `p^κ_i`
  (card `integral-tensor.md`).
* `TensorPairing.orderedForm`: the bilinear form on the tensor product (card `ordered-form.md`).
* `rightTensorProjectiveHomForm`, `lsCast`: the Euler form `gdim HOM(P, Q)` as a Laurent series.

Conventions (see the cards and `docs/Faithfulness/DEVIATIONS.md`): the identification is
semilinear along `q ↦ q⁻¹`, because the library's grading shift is opposite to the source's
`A(i)_n = A_{i+n}`; in the Hom form the target of the Hom sits in the first slot of the form.
-/

namespace Categorification.Spec.Webster.Thm438

open Categorification.Stendhal Categorification.Stendhal.FirstWeight
open KLR KLRAlgebra KLGamma Categorification.Graded QuantumGroup QuantumGroup.UDot
open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF
open scoped RatFunc

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

/-- The ring involution `q ↦ q⁻¹` of `ℤ[q, q⁻¹]`. -/
abbrev inversion := (LaurentPolynomial.invert (R := ℤ)).toRingEquiv

instance : RingHomInvPair inversion.toRingHom inversion.toRingHom :=
  RingHomInvPair.of_ringEquiv inversion

local instance : NeZero (RatFunc.X : RatFunc ℚ) := ⟨RatFunc.X_ne_zero⟩

/- Hypotheses, in the order of the source's setup (§2.1, §4).
* `C`, `Y`, `R`, `hR`: the Cartan datum and weight lattice (§2.1); `hR` is the regularity
  of the root datum used by the library's construction of `V_λ` (X-regular).
* `Q`, `hQ`: the polynomials `Q_ij` of the KLR algebra over the field `k` (§2.1, the
  conditions stated with the definition of `Q_ij`).
* `Λ`, `wt`, `hwt`: the sequence `λ = (λ₁, …, λ_ℓ)` of dominant weights, given both as
  `I →₀ ℕ` (pairings with simple coroots, used by `T^λ`) and as dominant weights of the root
  datum (used by `V_{λ_j}`), with `hwt` saying they agree. -/
variable {I : Type} {k Y : Type*} [DecidableEq I] [Field k] [AddCommGroup Y] [Finite I]
    {Q : I → I → MvPolynomial (Fin 2) k} (C : CartanDatum I) (hQ : IsRouquierQ C Q)
    {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular) {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ)
    (wt : Fin ℓ → Dom R) (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i))

include hwt in
/-- **Webster, arXiv:1309.3796v2, Theorem 4.38.** There is a `q ↦ q⁻¹`-semilinear isomorphism
`η` from `K₀` of graded right projective `T^λ`-modules (all black contents together) onto the
integral form `V^λ_ℤ`, sending the class of the right projective of every divided-power loading
`w` to the vector `p_w`, and intertwining the Euler form with the bilinear form of `V^λ`:
`gdim HOM(x, y) = ⟨η y, η x⟩`. -/
theorem existence :
    ∃ η : DirectSum (Multiset I) (rightTensorProjectiveGroup C hQ Λ)
        ≃ₛₗ[inversion.toRingHom] integralTensor wt,
      (∀ w : TensorWord I ℓ,
        η (rightTensorWordProjectiveClass C hQ Λ w) = integralWordVector (C := C) wt w) ∧
      ∀ x y : DirectSum (Multiset I) (rightTensorProjectiveGroup C hQ Λ),
        lsCast (rightTensorProjectiveHomForm C hQ Λ x y) =
          algebraMap (RatFunc ℚ) (LaurentSeries ℚ)
            (TensorPairing.orderedForm hR wt (η y).val (η x).val) :=
  ⟨rightTensorModuleEquiv C hQ hR Λ wt hwt, rightTensorModuleEquiv_word C hQ hR Λ wt hwt,
    rightTensorModuleEquiv_homForm C hQ hR Λ wt hwt⟩

include hR hwt in
/-- **Webster, arXiv:1309.3796v2, Theorem 4.38 (canonicity; cf. Lemma 4.37).** A
`q ↦ q⁻¹`-semilinear map with the prescribed values on the loading projectives is the map of
`existence`. -/
theorem uniqueness
    (g h : DirectSum (Multiset I) (rightTensorProjectiveGroup C hQ Λ)
        →ₛₗ[inversion.toRingHom] integralTensor wt)
    (hg : ∀ w, g (rightTensorWordProjectiveClass C hQ Λ w) = integralWordVector (C := C) wt w)
    (hh : ∀ w, h (rightTensorWordProjectiveClass C hQ Λ w) = integralWordVector (C := C) wt w) :
    g = h :=
  (rightTensorModuleEquiv_unique C hQ hR Λ wt hwt g hg).trans
    (rightTensorModuleEquiv_unique C hQ hR Λ wt hwt h hh).symm

end Categorification.Spec.Webster.Thm438
