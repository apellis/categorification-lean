/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.GradedBraidingBimodule
import Categorification.WeightedKLR.RedStrands.RightBoundaryProjectives
import Categorification.Algebra.Graded.IdealTensor
import Categorification.Algebra.Graded.ProjectiveCharacter

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
* `projectiveHomPolynomial_braidFunctor_rightSequence` : `gdim HOM(e(s) T^{λ ∘ σ}, 𝔅_σ (e(t) T^λ))`
  is the graded dimension of `e(t) B e(s)`.
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

variable [Module.Finite k (TensorProductAlgebra k Q Λ ν)]

include hρ hQ in
/-- **The braid of a right sequence projective, tested against right sequence projectives**:
`gdim HOM(e(s) T^{λ ∘ σ}, 𝔅_σ (e(t) T^λ)) = gdim e(t) B e(s)`, with the auxiliary grading of
`B` (Webster, arXiv:1309.3796v2, §6.1, Definition 6.6). -/
theorem projectiveHomPolynomial_braidFunctor_rightSequence
    (t : Seq (stendhalWeight ℓ ν)) (ht : IsRedOrdered t)
    (s : Seq (stendhalWeight ℓ ν)) (hs : IsRedOrdered s) :
    projectiveHomPolynomial (𝒜 (Λ ∘ σ))
        (braidFunctor (Λ := Λ) (ν := ν) hρ hQ σ hR
          (rightSequenceProj (rouquierGrading Q hR Λ) t ht).toGFin)
        (K0.of (rightSequenceProj (rouquierGrading Q hR (Λ ∘ σ)) s hs)) =
      gdimPoly (idem (idem (braidBimodGrading Q Λ ν hρ hQ σ hR)
          (op (TensorProductAlgebra.mk Q (Λ ∘ σ) ν (StendhalAlgebra.e s hs))))
        (op (op (TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e t ht))))) := by
  let := braidBimodDecomposition (Λ := Λ) (ν := ν) hρ hQ σ hR
  let := braidBimod_gradedSMul_left (Λ := Λ) (ν := ν) hρ hQ σ hR
  let := braidBimod_gradedSMul_right (Λ := Λ) (ν := ν) hρ hQ σ hR
  refine (projectiveHomPolynomial_ofIdempotent (𝒜 (Λ ∘ σ)) _ (e := op (TensorProductAlgebra.mk Q (Λ ∘ σ) ν (StendhalAlgebra.e s hs)))
    (congrArg op (isIdempotentElem_mk_e s hs))
    (show _ ∈ (𝒜 (Λ ∘ σ)) 0 from
      mk_e_mem_tensorProductGrade (rouquierGrading Q hR (Λ ∘ σ)) ν s hs)).trans ?_
  refine (gdimPoly_idem_balancedGrading (𝒜 Λ) (braidBimodGrading Q Λ ν hρ hQ σ hR)
    (rightSequenceProj (rouquierGrading Q hR Λ) t ht).grading (e := op (TensorProductAlgebra.mk Q (Λ ∘ σ) ν (StendhalAlgebra.e s hs)))
    (congrArg op (isIdempotentElem_mk_e s hs))
    (show _ ∈ (𝒜 (Λ ∘ σ)) 0 from
      mk_e_mem_tensorProductGrade (rouquierGrading Q hR (Λ ∘ σ)) ν s hs)).trans ?_
  let := idemDecomposition (braidBimodGrading Q Λ ν hρ hQ σ hR)
    (show op (TensorProductAlgebra.mk Q (Λ ∘ σ) ν (StendhalAlgebra.e s hs)) ∈
      oppositeGrade (tensorProductGrade (rouquierGrading Q hR (Λ ∘ σ)) ν) 0 from
      mk_e_mem_tensorProductGrade (rouquierGrading Q hR (Λ ∘ σ)) ν s hs)
  exact gdimPoly_balancedGrading_leftIdeal (𝒜 Λ) (idem (braidBimodGrading Q Λ ν hρ hQ σ hR) _) (e := op (TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e t ht)))
    (congrArg op (isIdempotentElem_mk_e t ht))
    (show _ ∈ (𝒜 Λ) 0 from mk_e_mem_tensorProductGrade (rouquierGrading Q hR Λ) ν t ht)

end Categorification.Stendhal.BraidedStendhalAlgebra
