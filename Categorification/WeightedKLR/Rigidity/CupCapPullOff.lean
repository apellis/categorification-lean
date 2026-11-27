/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapCoevaluation
import Categorification.WeightedKLR.RedStrands.BlackInduction
import Categorification.Algebra.InductionAlong

/-!
# The pull-off identity for the coefficient module of a cap

Webster, arXiv:1309.3796v3, §7.3, Lemma 7.16. Let `L` be a right `T̃^{(μ, μ*)}`-module (with black
strands of weight `ν₀`) and `i` a colour. Induce `L` along the map adjoining a black strand of
colour `i` on the right (`CupCap.appendBlackTildeOp`): `Fᵢ L = L ⊗_{T̃^{(μ,μ*)}_{ν₀}} e' T̃^{(μ,μ*)}_{ν₀+i}`.
The *pull-off identity* (`CupCap.PullOff`) says that pulling the new strand under all the
strands of `L` to the far left and back (`CupCap.pullOffLoop`) multiplies by the scalar
`(-1)^{g_i} ∏_{i' ≠ i} t_{i'i}^{g_{i'}}` of the relation (max1) (`CupCap.cupScalar`):

`v ⊗ (loop) = κ_i (v ⊗ 1)`.

This is the coherence of the relations (max1) and (max2) of Definition 7.15: pulling a black
strand right of the maximum under the cap to the left by (max2) and back by (max1) must give the
scalar of (max1). Webster's Lemma 7.16 asserts the identity for `L = L_μ`, modulo diagrams which
act by zero on the cap; since `L_μ` is supported on loadings with `μ*` last
(`CupCap.smul_e_eq_zero_of_not_isCapGood`), those diagrams are already zero in `Fᵢ L`.

## Main definitions

* `CupCap.appendBlackTildeOp`: the black-appending map on `T̃^{(μ,μ*)}`, in the opposite rings.
* `CupCap.pullOffLoop`: the new strand pulled under all others to the far left and back.
* `CupCap.PullOff`: the pull-off identity for `L` at every colour.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type*} [DecidableEq I] (k : Type*) [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k)
  (Λc : Fin 2 → I →₀ ℕ) (ν₀ : Multiset I) (i : I)

local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν₀)

/-- Adjoining a black strand of colour `i` on the right of `T̃^{(μ, μ*)}`, as a nonunital map of
the opposite rings: induction along it is `Fᵢ` on right modules. -/
def appendBlackTildeOp :
    (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ →ₙ+* (StendhalAlgebra k Q Λc νᵢ)ᵐᵒᵖ :=
  NonUnitalRingHom.op (NonUnitalRingHomClass.toNonUnitalRingHom (appendBlackStendhal Q Λc i ν₀))

/-- The new strand (at the last position `N`) pulled under the `N` strands to its left to the far
left and back: `underLeft N 0 · underRight N 0`, whose top and bottom have the new strand last. -/
def pullOffLoop : StendhalAlgebra k Q Λc νᵢ :=
  cupMap k Q Λc νᵢ (underLeft N 0 * underRight N 0)

/-- The element `e' · loop` of the corner `e' T̃^{(μ,μ*)}_{ν₀+i}`. -/
def pullOffCorner : Corner (appendBlackTildeOp k Q Λc ν₀ i) :=
  ⟨op (appendBlackStendhal Q Λc i ν₀ 1 * pullOffLoop k Q Λc ν₀ i), by
    change op (appendBlackStendhal Q Λc i ν₀ 1 * pullOffLoop k Q Λc ν₀ i) *
      op (appendBlackStendhal Q Λc i ν₀ 1) = _
    rw [← op_mul, ← mul_assoc, ← map_mul, one_mul]⟩

variable (L : Type*) [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

/-- **The pull-off identity** of Webster, arXiv:1309.3796v3, Lemma 7.16, for a right
`T̃^{(μ, μ*)}`-module `L`: in `Fᵢ L`, pulling the new strand of colour `i` under all strands of `L`
to the far left and back is multiplication by the scalar `κ_i` of (max1). -/
def PullOff : Prop :=
  ∀ (i : I) (v : L),
    (Ind.tmul (pullOffCorner k Q Λc ν₀ i) v : Ind L (appendBlackTildeOp k Q Λc ν₀ i)) =
      Ind.tmul (unitGen _) (op (algebraMap k (StendhalAlgebra k Q Λc ν₀) (cupScalar Q ν₀ i)) • v)

end Categorification.Stendhal.CupCap
