/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.GradedBraidingBimodule

/-!
# The braiding functor on finite-dimensional graded right modules

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §6.1,
Definition 6.6. For a permutation `σ` of the red labels, the braiding functor
`𝔅_σ = - ⊗_{T^λ} B` sends finite-dimensional graded right `T^λ`-modules to finite-dimensional
graded right `T^{λ ∘ σ}`-modules, where `B` is the braiding bimodule (`braidBimod`) with its
auxiliary grading. Right modules are left modules over the opposite algebras, so `𝔅_σ` is
`GFin.induce` for `B` read as a `((T^{λ ∘ σ})ᵐᵒᵖ, (T^λ)ᵐᵒᵖ)`-bimodule.

## Main definitions

* `braidFunctor σ N` : the graded right `T^{λ ∘ σ}`-module `N ⊗_{T^λ} B`.
* `braidFunctorCongr` : `N ≅ N'` gives `𝔅_σ N ≅ 𝔅_σ N'`.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR TypeA Equiv Categorification.Graded MulOpposite

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
  {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  (hρ : IsReducedChoice ρ) (hQ : KLRSymm Q) (σ : Perm (Fin ℓ))
  {𝔠 : QuantumGroup.CartanDatum I} (hR : IsRouquierQ 𝔠 Q)
  [Module.Finite k (TensorProductAlgebra k Q (Λ ∘ σ) ν)]

local notation "𝒜" Ω => oppositeGrade (tensorProductGrade (rouquierGrading Q hR Ω) ν)

include hρ hQ in
/-- **The braiding functor** `N ↦ N ⊗_{T^λ} B` (Webster, arXiv:1309.3796v2, §6.1, Definition
6.6) on finite-dimensional graded right `T^λ`-modules, with the auxiliary grading of `B`. -/
def braidFunctor (N : GFin (𝒜 Λ)) : GFin (𝒜 (Λ ∘ σ)) :=
  letI := braidBimodDecomposition (Λ := Λ) (ν := ν) hρ hQ σ hR
  letI := braidBimod_gradedSMul_left (Λ := Λ) (ν := ν) hρ hQ σ hR
  letI := braidBimod_gradedSMul_right (Λ := Λ) (ν := ν) hρ hQ σ hR
  letI := finite_braidBimod (Λ := Λ) (ν := ν) hρ hQ σ
  GFin.induce (𝒜 Λ) (𝒜 (Λ ∘ σ)) (braidBimodGrading Q Λ ν hρ hQ σ hR) N

include hρ hQ in
/-- An isomorphism `N ≅ N'` gives `𝔅_σ N ≅ 𝔅_σ N'`. -/
def braidFunctorCongr {N N' : GFin (𝒜 Λ)} (e : N.Iso N') :
    (braidFunctor (Λ := Λ) (ν := ν) hρ hQ σ hR N).Iso (braidFunctor (Λ := Λ) (ν := ν) hρ hQ σ hR N') :=
  letI := braidBimodDecomposition (Λ := Λ) (ν := ν) hρ hQ σ hR
  letI := braidBimod_gradedSMul_left (Λ := Λ) (ν := ν) hρ hQ σ hR
  letI := braidBimod_gradedSMul_right (Λ := Λ) (ν := ν) hρ hQ σ hR
  letI := finite_braidBimod (Λ := Λ) (ν := ν) hρ hQ σ
  GFin.induceCongr e

end Categorification.Stendhal.BraidedStendhalAlgebra
