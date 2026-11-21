/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicStandardLastIndSurj
import Categorification.Algebra.ExactDimension

/-!
# The `Fᵢ`-part of Proposition 5.5 at the last red strand, given injectivity of `δ₁`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
Proposition 5.5, `F`-part, at the last red strand: for a module `N` over
`T^{λ'} ⊗ R^{λ_ℓ}_β`, the sequence

`0 → S(₁Fᵢ N) → Fᵢ S(N) → S(₂Fᵢ N) → 0`

is exact. Exactness at `Fᵢ S(N)` and at `S(₂Fᵢ N)` is proved (`firstIndDeltaT_exact`,
`lastIndQuotientMap_surjective`). Injectivity of `δ₁ : S(₁Fᵢ N) → Fᵢ S(N)` comes, in
Webster's proof, from a dimension count; it is taken here as the explicit hypothesis
`FirstIndDeltaInjective`. This hypothesis is a route hypothesis, not part of the source
statement; the roadmap (`docs/WeightedKLR/tensor-product-roadmap.md`, §5) tracks its removal
by that dimension count.

## Main definitions and results

* `FirstIndDeltaInjective`: injectivity of `δ₁` (route hypothesis).
* `firstIndDeltaT_shortExact`: the short exact sequence, given `FirstIndDeltaInjective`.
* `firstIndDeltaInjective_iff_finrank`: the hypothesis holds exactly when
  `dim Fᵢ S(N) = dim S(₁Fᵢ N) + dim S(₂Fᵢ N)`, the equality of Webster's dimension count.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra InductionAlong MulOpposite
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} {k : Type*} [DecidableEq I] [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I) (θ β : Multiset I)
  (N : Type*) [AddCommGroup N] [Module k N] [Module (parabolicFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N] (hQ : KLRSymm Q)

/-- **Injectivity of `δ₁ : S(₁Fᵢ N) → Fᵢ S(N)`** (Webster, arXiv:1309.3796v3, proof of
Proposition 5.5, `F`-part). Webster obtains it from a dimension count. Here it is a route
hypothesis of `firstIndDeltaT_shortExact`, tracked for removal in the roadmap. -/
def FirstIndDeltaInjective : Prop :=
  Function.Injective (firstIndDeltaT Q Λ i θ β N hQ)

/-- **The `Fᵢ`-part of Proposition 5.5 at the last red strand** (Webster,
arXiv:1309.3796v3, Proposition 5.5): given injectivity of `δ₁` (`FirstIndDeltaInjective`, a
route hypothesis), `0 → S(₁Fᵢ N) → Fᵢ S(N) → S(₂Fᵢ N) → 0` is exact. -/
theorem firstIndDeltaT_shortExact (hinj : FirstIndDeltaInjective Q Λ i θ β N hQ) :
    Function.Injective (firstIndDeltaT Q Λ i θ β N hQ) ∧
      Function.Exact (firstIndDeltaT Q Λ i θ β N hQ) (lastIndQuotientMap Q Λ i θ β N hQ) ∧
      Function.Surjective (lastIndQuotientMap Q Λ i θ β N hQ) :=
  ⟨hinj, firstIndDeltaT_exact Q Λ i θ β N hQ, lastIndQuotientMap_surjective Q Λ i θ β N hQ⟩

local notation "T′" => TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + (θ + β))

/-- **Injectivity of `δ₁` as a dimension equality** (Webster, arXiv:1309.3796v3, proof of
Proposition 5.5): when `S(₁Fᵢ N)` and `Fᵢ S(N)` are finite-dimensional, `δ₁` is injective
exactly when `dim Fᵢ S(N) = dim S(₁Fᵢ N) + dim S(₂Fᵢ N)`. -/
theorem firstIndDeltaInjective_iff_finrank
    [FiniteDimensional k (RestrictScalars k T′ (FirstIndStandardT Q Λ i θ β N hQ))]
    [FiniteDimensional k (RestrictScalars k T′ (FirstIndF Q Λ i θ β N hQ))] :
    FirstIndDeltaInjective Q Λ i θ β N hQ ↔
      Module.finrank k (RestrictScalars k T′ (FirstIndF Q Λ i θ β N hQ)) =
        Module.finrank k (RestrictScalars k T′ (FirstIndStandardT Q Λ i θ β N hQ)) +
          Module.finrank k (RestrictScalars k T′ (LastIndStandardT Q Λ i θ β N hQ)) :=
  injective_iff_finrank_restrictScalars k (firstIndDeltaT Q Λ i θ β N hQ)
    (lastIndQuotientMap Q Λ i θ β N hQ) (firstIndDeltaT_exact Q Λ i θ β N hQ)
    (lastIndQuotientMap_surjective Q Λ i θ β N hQ)

end Categorification.Stendhal
