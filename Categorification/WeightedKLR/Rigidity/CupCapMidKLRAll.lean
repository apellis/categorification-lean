/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapMidKLR
import Categorification.WeightedKLR.Rigidity.CupCapMidRelBraidLoop

/-!
# All KLR relations on the model of a cap after `λ_j`

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.17. With the braid relation on the model
(`CupCap.midRel_braid`), every defining relation of the KLR algebra of `λ` holds on the model
with the maximum before `λ_{j+1}`, so the model is a `T̃^λ`–`T̃^{λ⁺}` bimodule
(`CupCap.midEnvAlg`).

## Main results

* `CupCap.midKLRRel`: the KLR relations of `λ` hold on the model, under the route hypotheses
  `PullOff L`, `PullOffLeft L` (Lemma 7.16 and its mirror) and invertible cup scalars.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

variable {L : Type*} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}

/-- **The KLR relations of `λ` on the model of a cap after `λ_j`.** The quadratic and braid
relations use the loops (max2), hence the route hypotheses `PullOff L` and `PullOffLeft L`
(Lemma 7.16 and its mirror, tracked for removal) and invertible cup scalars. -/
theorem midKLRRel (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i)) (hP : PullOff k Q Λc ν₀ L)
    (hPL : PullOffLeft k Q Λc ν₀ L) : MidKLRRel j hj Q Λ Λc ν ν₀ L hL :=
  midKLRRel_of_braid hκ hP hPL fun p h i => midRel_braid hκ hP hPL p h i

end Categorification.Stendhal.CupCap
