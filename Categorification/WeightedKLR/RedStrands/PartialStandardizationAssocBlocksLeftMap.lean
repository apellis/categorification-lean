/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PartialStandardizationAssocBlocksLeft
import Categorification.WeightedKLR.RedStrands.PartialStandardizationBlocksExact

/-!
# Maps of partial standardizations with three blocks, first cut first

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1, the
partial standardization functors after Definition 5.4. A map of modules over
`(T^A(θ) ⊗ T^M(β)) ⊗ T^R(γ)` induces a map of the iterated partial standardizations
`BlocksStandardL` (first cut first), linear over `T^λ((θ + β) + γ)`, as for the other nesting
(`blocksStandardMap`).

## Main definitions

* `Stendhal.blocksMidHomL`: the map of standardizations at the first cut, linear over
  `T^{AM}(θ + β) ⊗ T^R(γ)`.
* `Stendhal.blocksStandardMapL`: the map of iterated partial standardizations.

## Main results

* `Stendhal.blocksStandardMapL_action`: it is linear over `T^λ((θ + β) + γ)`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA
open scoped TensorProduct

variable {I k : Type*} [DecidableEq I] [CommRing k] {a m r : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ((a + m) + r) → I →₀ ℕ) (θ β γ : Multiset I)

/-- The semiring structure of the algebra of three blocks, through its ring structure (so that
linear maps over it elaborate). -/
private abbrev blocksNonAssocSemiringL : NonAssocSemiring (blocksFactorAlgebraL Q Λ θ β γ) :=
  Semiring.toNonAssocSemiring

attribute [local instance high] blocksNonAssocSemiringL

local notation "A₀" => blocksLastAlgebra Q Λ γ
local notation "Dᵢ" => cutFactorAlgebra Q (blocksLeftLabels Λ) θ β
local notation "Dₒ" => cutFactorAlgebra Q Λ (θ + β) γ

variable {N N' : Type*}
  [AddCommGroup N] [Module k N] [Module (blocksFactorAlgebraL Q Λ θ β γ) N]
  [IsScalarTower k (blocksFactorAlgebraL Q Λ θ β γ) N]
  [AddCommGroup N'] [Module k N'] [Module (blocksFactorAlgebraL Q Λ θ β γ) N']
  [IsScalarTower k (blocksFactorAlgebraL Q Λ θ β γ) N']

/-- A map of modules over the three blocks, as a map of modules over the first two. -/
def blocksInnerHomL (g : N →ₗ[blocksFactorAlgebraL Q Λ θ β γ] N') :
    BlocksInnerL Q Λ θ β γ N →ₗ[Dᵢ] BlocksInnerL Q Λ θ β γ N' where
  toFun n := (g n : N')
  map_add' := g.map_add
  map_smul' d n := g.map_smul (d ⊗ₜ[k] (1 : A₀)) n

omit [Module k N] [IsScalarTower k (blocksFactorAlgebraL Q Λ θ β γ) N] [Module k N']
  [IsScalarTower k (blocksFactorAlgebraL Q Λ θ β γ) N'] in
theorem blocksInnerHomL_last (g : N →ₗ[blocksFactorAlgebraL Q Λ θ β γ] N') (t : A₀)
    (n : BlocksInnerL Q Λ θ β γ N) :
    blocksInnerHomL Q Λ θ β γ g (blocksLastEnd Q Λ θ β γ N t n) =
      blocksLastEnd Q Λ θ β γ N' t (blocksInnerHomL Q Λ θ β γ g n) :=
  g.map_smul ((1 : Dᵢ) ⊗ₜ[k] t) n

variable (hQ : KLRSymm Q)

include hQ in
/-- The standardization at the first cut of a map intertwines the actions of
`T^{AM}(θ + β) ⊗ T^R(γ)`. -/
theorem blocksMidActionL_map (g : N →ₗ[blocksFactorAlgebraL Q Λ θ β γ] N') (d : Dₒ)
    (z : CutStandard Q (blocksLeftLabels Λ) θ β (BlocksInnerL Q Λ θ β γ N)) :
    cutStandardMap Q (blocksLeftLabels Λ) θ β (blocksInnerHomL Q Λ θ β γ g)
        (blocksMidActionL Q Λ θ β γ N hQ d z) =
      blocksMidActionL Q Λ θ β γ N' hQ d
        (cutStandardMap Q (blocksLeftLabels Λ) θ β (blocksInnerHomL Q Λ θ β γ g) z) := by
  induction d using TensorProduct.inductionOn generalizing z with
  | tmul u t =>
    simp only [blocksMidActionL, Algebra.TensorProduct.lift_tmul, Module.End.mul_apply]
    rw [blocksLastAction_apply, blocksLastAction_apply]
    exact (cutStandardMap_action Q (blocksLeftLabels Λ) θ β hQ _ u _).trans
      (congrArg _ (cutStandardMap_comm Q (blocksLeftLabels Λ) θ β _ _ _
        (blocksInnerHomL_last Q Λ θ β γ g t) z))
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

/-- **The map of standardizations at the first cut** induced by a map of modules over the
three blocks, linear over `T^{AM}(θ + β) ⊗ T^R(γ)`. -/
def blocksMidHomL (g : N →ₗ[blocksFactorAlgebraL Q Λ θ β γ] N') :
    BlocksMidL Q Λ θ β γ N hQ →ₗ[Dₒ] BlocksMidL Q Λ θ β γ N' hQ where
  toFun := cutStandardMap Q (blocksLeftLabels Λ) θ β (blocksInnerHomL Q Λ θ β γ g)
  map_add' := map_add _
  map_smul' d z := blocksMidActionL_map Q Λ θ β γ hQ g d z

/-- **The map of iterated partial standardizations with three blocks, first cut first**,
induced by a map of modules over `(T^A(θ) ⊗ T^M(β)) ⊗ T^R(γ)`. -/
def blocksStandardMapL (g : N →ₗ[blocksFactorAlgebraL Q Λ θ β γ] N') :
    BlocksStandardL Q Λ θ β γ N hQ →ₗ[k] BlocksStandardL Q Λ θ β γ N' hQ :=
  cutStandardMap Q Λ (θ + β) γ (blocksMidHomL Q Λ θ β γ hQ g)

/-- The map of iterated partial standardizations, first cut first, is linear over
`T^λ((θ + β) + γ)`. -/
theorem blocksStandardMapL_action (g : N →ₗ[blocksFactorAlgebraL Q Λ θ β γ] N')
    (t : TensorProductAlgebra k Q Λ ((θ + β) + γ)) (z : BlocksStandardL Q Λ θ β γ N hQ) :
    blocksStandardMapL Q Λ θ β γ hQ g (blocksStandardActionL Q Λ θ β γ N hQ t z) =
      blocksStandardActionL Q Λ θ β γ N' hQ t (blocksStandardMapL Q Λ θ β γ hQ g z) :=
  cutStandardMap_action Q Λ (θ + β) γ hQ _ t z

end Categorification.Stendhal
