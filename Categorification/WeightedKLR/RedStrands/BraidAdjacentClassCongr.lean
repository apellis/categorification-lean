/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.GradedBraidAdjacent
import Categorification.WeightedKLR.RedStrands.BraidingDimension

set_option backward.isDefEq.respectTransparency false

/-!
# The class map of an adjacent braid functor at `v = 1`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §6.1,
Corollary 6.10 and proof of Lemma 6.11. For `ℓ = n + 2 + m` red strands and the transposition
`s` of the strands `n + 1, n + 2`, the class map of `𝔅_s` is `x ↦ B(v² R x, -)` with `R` the
braiding of those factors (`braidClass_swapAt`), and `v² R` is congruent at `v = 1` to the
permutation of the tensor factors by `s` (`exists_braidClass_swapAt`).

Route hypotheses, as in `braidClass_pairSwap`: `AllFiniteDeltaInjective` (Corollary 5.22) and
`RowFigureFiveHypotheses` (Proposition 6.9).
-/

noncomputable section

namespace Categorification.Stendhal.FirstWeight

open KLR KLRAlgebra KLGamma Categorification.Graded QuantumGroup QuantumGroup.UDot
open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF
open scoped RatFunc
open DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 1200] Ring.toIntAlgebra
local notation "𝕂" => RatFunc ℚ
local notation "v" => (RatFunc.X : 𝕂)

universe w

variable {I : Type} {k : Type} {Y : Type*} [DecidableEq I] [Field k] [AddCommGroup Y] [Finite I]
    {Q : I → I → MvPolynomial (Fin 2) k} (C : CartanDatum I) (hQ : IsRouquierQ C Q)
    {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular)

/-- **Corollary 6.10 at `ℓ = n + 2 + m` strands** (Webster, arXiv:1309.3796v2): the class map
of `𝔅_s`, for the transposition `s = swapAt n m h` of the strands `n + 1, n + 2`, is
`x ↦ B(v² R x, -)` with `R = braidingAt n m h`. Route hypotheses: `AllFiniteDeltaInjective` and
`RowFigureFiveHypotheses`. -/
theorem braidClass_swapAt {ℓ : ℕ} (n m : ℕ) (h : n + 2 + m = ℓ) (Λ : Fin ℓ → I →₀ ℕ)
    (wt : Fin ℓ → Dom R) (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i))
    [∀ (Ω : Fin ℓ → I →₀ ℕ) (ν : Multiset I), Module.Finite k (TensorProductAlgebra k Q Ω ν)]
    (hall : ∀ (n : ℕ) (Λ' : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective Q Λ' hQ.klrSymm)
    (H : ∀ (Ω : Fin (n + 2 + m) → I →₀ ℕ) (u : Fin (n + 2 + m) → List I)
      (hu : u (rightPos n m) = []), RowFigureFiveHypotheses C hQ Ω u hu)
    [∀ (Ω : Fin ℓ → I →₀ ℕ) (ν : Multiset I) (κ : List (Fin ℓ)),
      DG.HasDerivedCategory.{w, 0} (IsIdempotentElem.Corner
        (BraidedStendhalAlgebra.isIdempotentElem_violMk_redProj k Q Ω ν κ))ᵐᵒᵖ] :
    braidClass C hQ hR Λ wt hwt (swapAt n m h) =
      (formDual hR (wt ∘ swapAt n m h)).comp
        ((v ^ (2 : ℤ) : 𝕂) • (braidingAt hR n m h wt).toLinearMap) := by
  subst h
  exact braidClass_pairSwap.{w} C hQ hR Λ wt hwt hall (H Λ)

/-- **The class map of an adjacent braid functor is congruent to the transposition** (Webster,
arXiv:1309.3796v2, Corollary 6.10 and proof of Lemma 6.11): the class map of `𝔅_s` is
`x ↦ B(f x, -)` with `f ≡` the permutation of the factors by `s` modulo `(v - 1)`. -/
theorem exists_braidClass_swapAt {ℓ : ℕ} (n m : ℕ) (h : n + 2 + m = ℓ) (Λ : Fin ℓ → I →₀ ℕ)
    (wt : Fin ℓ → Dom R) (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i))
    [∀ (Ω : Fin ℓ → I →₀ ℕ) (ν : Multiset I), Module.Finite k (TensorProductAlgebra k Q Ω ν)]
    (hall : ∀ (n : ℕ) (Λ' : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective Q Λ' hQ.klrSymm)
    (H : ∀ (Ω : Fin (n + 2 + m) → I →₀ ℕ) (u : Fin (n + 2 + m) → List I)
      (hu : u (rightPos n m) = []), RowFigureFiveHypotheses C hQ Ω u hu)
    [∀ (Ω : Fin ℓ → I →₀ ℕ) (ν : Multiset I) (κ : List (Fin ℓ)),
      DG.HasDerivedCategory.{w, 0} (IsIdempotentElem.Corner
        (BraidedStendhalAlgebra.isIdempotentElem_violMk_redProj k Q Ω ν κ))ᵐᵒᵖ] :
    ∃ f : TensorSpace wt →ₗ[𝕂] TensorSpace (wt ∘ swapAt n m h),
      VOneCongr f (tensorPermute wt (swapAt n m h)).toLinearMap ∧
        braidClass C hQ hR Λ wt hwt (swapAt n m h) = (formDual hR (wt ∘ swapAt n m h)).comp f :=
  ⟨_, (vOneCongr_braidingAt hR n m h wt).zpow_smul 2,
    braidClass_swapAt.{w} C hQ hR n m h Λ wt hwt hall H⟩

end Categorification.Stendhal.FirstWeight
