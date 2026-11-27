/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PartialStandardizationBlocks

/-!
# Exactness of partial standardization with three blocks

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5,
Proposition 5.7, for the partial standardization with three consecutive blocks
(`Stendhal.BlocksStandard`): a map of modules over `T^A(θ) ⊗ (T^M(β) ⊗ T^R(γ))` induces a map
of partial standardizations, linear over `T^λ(θ + (β + γ))`, and partial standardization is
exact. Webster states Proposition 5.7 for the functor of Definition 5.4; here it follows from
its form at a cut (`cutStandardMap_exact`), applied at both cuts.

## Main definitions

* `Stendhal.blocksMidHom`: the map of inner standardizations, linear over
  `T^A(θ) ⊗ T^{MR}(β + γ)`.
* `Stendhal.blocksStandardMap`: the map of partial standardizations with three blocks.

## Main results

* `Stendhal.blocksStandardMap_action`: it is linear over `T^λ(θ + (β + γ))`.
* `Stendhal.blocksStandardMap_exact`, `blocksStandardMap_injective`,
  `blocksStandardMap_surjective`: partial standardization with three blocks is exact.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA
open scoped TensorProduct

variable {I k : Type*} [DecidableEq I] [CommRing k] {a m r : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (a + (m + r)) → I →₀ ℕ) (θ β γ : Multiset I)

/-- The semiring structure of the algebra of three blocks, through its ring structure (so that
linear maps over it elaborate). -/
private abbrev blocksNonAssocSemiring : NonAssocSemiring (blocksFactorAlgebra Q Λ θ β γ) :=
  Semiring.toNonAssocSemiring

attribute [local instance high] blocksNonAssocSemiring

local notation "A₀" => blocksHeadAlgebra Q Λ θ
local notation "Dᵢ" => cutFactorAlgebra Q (blocksTailLabels Λ) β γ
local notation "Dₒ" => cutFactorAlgebra Q Λ θ (β + γ)

variable {N N' N'' : Type*}
  [AddCommGroup N] [Module k N] [Module (blocksFactorAlgebra Q Λ θ β γ) N]
  [IsScalarTower k (blocksFactorAlgebra Q Λ θ β γ) N]
  [AddCommGroup N'] [Module k N'] [Module (blocksFactorAlgebra Q Λ θ β γ) N']
  [IsScalarTower k (blocksFactorAlgebra Q Λ θ β γ) N']
  [AddCommGroup N''] [Module k N''] [Module (blocksFactorAlgebra Q Λ θ β γ) N'']
  [IsScalarTower k (blocksFactorAlgebra Q Λ θ β γ) N'']

/-- A map of modules over the three blocks, as a map of modules over the last two. -/
def blocksInnerHom (g : N →ₗ[blocksFactorAlgebra Q Λ θ β γ] N') :
    BlocksInner Q Λ θ β γ N →ₗ[Dᵢ] BlocksInner Q Λ θ β γ N' where
  toFun n := (g n : N')
  map_add' := g.map_add
  map_smul' d n := g.map_smul ((1 : A₀) ⊗ₜ[k] d) n

omit [Module k N] [IsScalarTower k (blocksFactorAlgebra Q Λ θ β γ) N] [Module k N']
  [IsScalarTower k (blocksFactorAlgebra Q Λ θ β γ) N'] in
theorem blocksInnerHom_head (g : N →ₗ[blocksFactorAlgebra Q Λ θ β γ] N') (t : A₀)
    (n : BlocksInner Q Λ θ β γ N) :
    blocksInnerHom Q Λ θ β γ g (blocksHeadEnd Q Λ θ β γ N t n) =
      blocksHeadEnd Q Λ θ β γ N' t (blocksInnerHom Q Λ θ β γ g n) :=
  g.map_smul (t ⊗ₜ[k] (1 : Dᵢ)) n

variable (hQ : KLRSymm Q)

include hQ in
/-- The inner standardization of a map intertwines the actions of `T^A(θ) ⊗ T^{MR}(β + γ)`. -/
theorem blocksMidAction_map (g : N →ₗ[blocksFactorAlgebra Q Λ θ β γ] N') (d : Dₒ)
    (z : CutStandard Q (blocksTailLabels Λ) β γ (BlocksInner Q Λ θ β γ N)) :
    cutStandardMap Q (blocksTailLabels Λ) β γ (blocksInnerHom Q Λ θ β γ g)
        (blocksMidAction Q Λ θ β γ N hQ d z) =
      blocksMidAction Q Λ θ β γ N' hQ d
        (cutStandardMap Q (blocksTailLabels Λ) β γ (blocksInnerHom Q Λ θ β γ g) z) := by
  induction d using TensorProduct.inductionOn generalizing z with
  | tmul t u =>
    simp only [blocksMidAction, Algebra.TensorProduct.lift_tmul, Module.End.mul_apply]
    rw [blocksHeadAction_apply, blocksHeadAction_apply]
    exact (cutStandardMap_comm Q (blocksTailLabels Λ) β γ _ _ _
      (blocksInnerHom_head Q Λ θ β γ g t) _).trans
      (congrArg _ (cutStandardMap_action Q (blocksTailLabels Λ) β γ hQ _ u z))
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

/-- **The map of inner standardizations** induced by a map of modules over the three blocks,
linear over `T^A(θ) ⊗ T^{MR}(β + γ)`. -/
def blocksMidHom (g : N →ₗ[blocksFactorAlgebra Q Λ θ β γ] N') :
    BlocksMid Q Λ θ β γ N hQ →ₗ[Dₒ] BlocksMid Q Λ θ β γ N' hQ where
  toFun := cutStandardMap Q (blocksTailLabels Λ) β γ (blocksInnerHom Q Λ θ β γ g)
  map_add' := map_add _
  map_smul' d z := blocksMidAction_map Q Λ θ β γ hQ g d z

/-- **The map of partial standardizations with three blocks** induced by a map of modules
over `T^A(θ) ⊗ (T^M(β) ⊗ T^R(γ))`. -/
def blocksStandardMap (g : N →ₗ[blocksFactorAlgebra Q Λ θ β γ] N') :
    BlocksStandard Q Λ θ β γ N hQ →ₗ[k] BlocksStandard Q Λ θ β γ N' hQ :=
  cutStandardMap Q Λ θ (β + γ) (blocksMidHom Q Λ θ β γ hQ g)

/-- The map of partial standardizations with three blocks is linear over
`T^λ(θ + (β + γ))`. -/
theorem blocksStandardMap_action (g : N →ₗ[blocksFactorAlgebra Q Λ θ β γ] N')
    (t : TensorProductAlgebra k Q Λ (θ + (β + γ)))
    (z : BlocksStandard Q Λ θ β γ N hQ) :
    blocksStandardMap Q Λ θ β γ hQ g (blocksStandardAction Q Λ θ β γ N hQ t z) =
      blocksStandardAction Q Λ θ β γ N' hQ t (blocksStandardMap Q Λ θ β γ hQ g z) :=
  cutStandardMap_action Q Λ θ (β + γ) hQ _ t z

/-- **Partial standardization with three blocks is exact** (Webster, arXiv:1309.3796v3,
Proposition 5.7, for the partial standardization): a sequence `N → N' → N''` of modules over
the three blocks exact at `N'` gives a sequence of partial standardizations exact at the
middle. -/
theorem blocksStandardMap_exact (f : N →ₗ[blocksFactorAlgebra Q Λ θ β γ] N')
    (g : N' →ₗ[blocksFactorAlgebra Q Λ θ β γ] N'') (h : Function.Exact f g) :
    Function.Exact (blocksStandardMap Q Λ θ β γ hQ f) (blocksStandardMap Q Λ θ β γ hQ g) :=
  cutStandardMap_exact Q Λ θ (β + γ) hQ _ _
    (cutStandardMap_exact Q (blocksTailLabels Λ) β γ hQ (blocksInnerHom Q Λ θ β γ f)
      (blocksInnerHom Q Λ θ β γ g) h)

/-- Partial standardization with three blocks preserves injections. -/
theorem blocksStandardMap_injective (f : N →ₗ[blocksFactorAlgebra Q Λ θ β γ] N')
    (hf : Function.Injective f) :
    Function.Injective (blocksStandardMap Q Λ θ β γ hQ f) :=
  cutStandardMap_injective Q Λ θ (β + γ) hQ _
    (cutStandardMap_injective Q (blocksTailLabels Λ) β γ hQ (blocksInnerHom Q Λ θ β γ f) hf)

/-- Partial standardization with three blocks preserves surjections. -/
theorem blocksStandardMap_surjective (f : N →ₗ[blocksFactorAlgebra Q Λ θ β γ] N')
    (hf : Function.Surjective f) :
    Function.Surjective (blocksStandardMap Q Λ θ β γ hQ f) :=
  cutStandardMap_surjective Q Λ θ (β + γ) hQ _
    (cutStandardMap_surjective Q (blocksTailLabels Λ) β γ hQ (blocksInnerHom Q Λ θ β γ f) hf)

end Categorification.Stendhal
