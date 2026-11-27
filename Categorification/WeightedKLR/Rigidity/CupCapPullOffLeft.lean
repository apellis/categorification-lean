/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapPullOff
import Categorification.WeightedKLR.RedStrands.PrependBlack

/-!
# The mirrored pull-off identity for the coefficient module of a cap

Webster, arXiv:1309.3796v3, §7.3, mirror of Lemma 7.16. Let `L` be a right `T̃^{(μ, μ*)}`-module
and `i` a colour. Induce `L` along the map adjoining a black strand of colour `i` on the left
(`CupCap.prependBlackTildeOp`). The *left pull-off identity* (`CupCap.PullOffLeft`) says that
pulling the new strand under all the strands of `L` to the far right and back
(`CupCap.pullOffLeftLoop`) multiplies by the scalar `κ_i` of the relation (max1)
(`CupCap.cupScalar`).

In `K̃^{λ⁺}_λ` (Definition 7.15) it is the coherence of (max2) followed by (max1) for a black
strand left of the maximum, as Lemma 7.16 is the coherence of (max1) followed by (max2) for a
black strand right of it. A model of `K̃` with the maximum at the right end of the strands needs
it; it enters the proof of Lemma 7.17 as an explicit hypothesis on `L`.

## Main definitions

* `CupCap.prependBlackTildeOp`: the black-prepending map on `T̃^{(μ,μ*)}`, in the opposite rings.
* `CupCap.pullOffLeftLoop`: the new strand pulled under all others to the far right and back.
* `CupCap.PullOffLeft`: the left pull-off identity for `L` at every colour.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type*} [DecidableEq I] (k : Type*) [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k)
  (Λc : Fin 2 → I →₀ ℕ) (ν₀ : Multiset I) (i : I)

local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν₀)

/-- Adjoining a black strand of colour `i` on the left of `T̃^{(μ, μ*)}`, as a nonunital map of
the opposite rings. -/
def prependBlackTildeOp :
    (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ →ₙ+* (StendhalAlgebra k Q Λc νᵢ)ᵐᵒᵖ :=
  NonUnitalRingHom.op (NonUnitalRingHomClass.toNonUnitalRingHom (prependBlackStendhal Q Λc i ν₀))

/-- The new strand (at the first position `0`) pulled under the `N` strands to its right to the
far right and back: `underRight N 0 · underLeft N 0`, whose top and bottom have the new strand
first. -/
def pullOffLeftLoop : StendhalAlgebra k Q Λc νᵢ :=
  cupMap k Q Λc νᵢ (underRight N 0 * underLeft N 0)

/-- The element `e' · loop` of the corner `e' T̃^{(μ,μ*)}_{i+ν₀}`. -/
def pullOffLeftCorner : Corner (prependBlackTildeOp k Q Λc ν₀ i) :=
  ⟨op (prependBlackStendhal Q Λc i ν₀ 1 * pullOffLeftLoop k Q Λc ν₀ i), by
    change op (prependBlackStendhal Q Λc i ν₀ 1 * pullOffLeftLoop k Q Λc ν₀ i) *
      op (prependBlackStendhal Q Λc i ν₀ 1) = _
    rw [← op_mul, ← mul_assoc, ← map_mul, one_mul]⟩

variable (L : Type*) [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

/-- **The left pull-off identity**, the mirror of Webster, arXiv:1309.3796v3, Lemma 7.16, for a
right `T̃^{(μ, μ*)}`-module `L`: after adjoining a black strand of colour `i` on the left, pulling
it under all strands of `L` to the far right and back is multiplication by the scalar `κ_i` of
(max1). -/
def PullOffLeft : Prop :=
  ∀ (i : I) (v : L),
    (Ind.tmul (pullOffLeftCorner k Q Λc ν₀ i) v : Ind L (prependBlackTildeOp k Q Λc ν₀ i)) =
      Ind.tmul (unitGen _) (op (algebraMap k (StendhalAlgebra k Q Λc ν₀) (cupScalar Q ν₀ i)) • v)

end Categorification.Stendhal.CupCap
