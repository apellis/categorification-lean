/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.RigidityExtResolutionWords
import Categorification.WeightedKLR.RedStrands.Prop55DimensionCountQ

/-!
# Proposition 7.6 for Rouquier parameters

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.1,
Proposition 7.6, ungraded, with no route hypothesis: for Rouquier parameters
the injectivity of `δ₁` in (7.25) is `allFiniteDeltaInjective_of_rouquier`.
-/

namespace Categorification.Stendhal

open CategoryTheory KLR KL3.Diagram
open scoped Classical

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} {ℓ : ℕ} {k : Type} [Field k] (Λ : Fin (ℓ + 1) → I →₀ ℕ)
  {C : QuantumGroup.CartanDatum I}

/-- **Proposition 7.6** (Webster, arXiv:1309.3796v3, §7.1), ungraded, for Rouquier parameters, with no route hypothesis: the injectivity of `δ₁` is
`allFiniteDeltaInjective_of_rouquier`. -/
theorem exists_projectiveResolution_websterWords_of_rouquier
    {Q : I → I → MvPolynomial (Fin 2) k} (hR : IsRouquierQ C Q)
    (hQs : KLRSymm Q) {θ : Multiset I}
    (t : Seq (stendhalWeight ℓ θ)) (ht : IsRedOrdered t) (w : List I) {ν : Multiset I}
    (h : θ + wordWt w 0 = ν) :
    ∃ P : ProjectiveResolution (tensorStd Q Λ hQs h
        (oldProj _ Λ θ t ht) (cycWord _ Λ w)),
      ∀ n, LoadingSum (P.complex.X n) (websterWords (t.word.map (addRedColor ℓ)) w.reverse n) :=
  exists_projectiveResolution_websterWords _ Λ hQs hR (allFiniteDeltaInjective_of_rouquier hR hQs) t ht w h

end Categorification.Stendhal
