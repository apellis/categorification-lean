/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PartialStandardizationAssocOrdersAction
import Categorification.WeightedKLR.RedStrands.PartialStandardizationAssocBlocksLeftMap

/-!
# The two orders of the cuts are natural in the module

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1, the
partial standardization functors after Definition 5.4. The identification
`blocksStandardAssocEquiv` of the two iterations of partial standardization with three blocks
is natural: for a map `g : N → N'` of modules over `T^A(θ) ⊗ (T^M(β) ⊗ T^R(γ))`, it takes the
map induced by `g` on the iteration with the first cut first (`blocksStandardMapL`) to the map
induced on the other iteration (`blocksStandardMap`) (`blocksStandardAssocEquiv_map`). Both
iterations are quotients of the outer induction of the inner induction of `N`, on whose
generators `m ⊗ (m' ⊗ n)` all the maps involved act on `n` alone.

## Main definitions

* `Stendhal.blocksAssocInputHom`: a map of modules over the three blocks, for the other
  nesting.
* `Stendhal.blocksOneStepInputHom`: the same map, on the one-step inputs.

## Main results

* `Stendhal.blocksStandardAssocEquiv_map`: naturality of `blocksStandardAssocEquiv`.
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
private abbrev blocksNonAssocSemiringN : NonAssocSemiring (blocksFactorAlgebra Q Λ θ β γ) :=
  Semiring.toNonAssocSemiring

/-- The same for the other nesting. -/
private abbrev blocksNonAssocSemiringNL :
    NonAssocSemiring (blocksFactorAlgebraL Q (Λ ∘ Fin.cast (Nat.add_assoc a m r)) θ β γ) :=
  Semiring.toNonAssocSemiring

attribute [local instance high] blocksNonAssocSemiringN blocksNonAssocSemiringNL

local notation "ΛL" => Λ ∘ Fin.cast (Nat.add_assoc a m r)
local notation "S" => stendhalQ Q Λ
local notation "αᵣ" =>
  Multiset.map (Sum.map (id : I → I) (Fin.castAdd (m + r))) (stendhalWeight a θ)
local notation "β̂ᵣ" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd a))
  (Multiset.map (Sum.map (id : I → I) (Fin.castAdd r)) (stendhalWeight m β))
local notation "γ̂ᵣ" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd a))
  (Multiset.map (Sum.map (id : I → I) (Fin.natAdd m)) (stendhalWeight r γ))

variable {N N' : Type*}
  [AddCommGroup N] [Module k N] [Module (blocksFactorAlgebra Q Λ θ β γ) N]
  [IsScalarTower k (blocksFactorAlgebra Q Λ θ β γ) N]
  [AddCommGroup N'] [Module k N'] [Module (blocksFactorAlgebra Q Λ θ β γ) N']
  [IsScalarTower k (blocksFactorAlgebra Q Λ θ β γ) N']

/-- A map of modules over the three blocks, for the other nesting. -/
def blocksAssocInputHom (g : N →ₗ[blocksFactorAlgebra Q Λ θ β γ] N') :
    BlocksAssocInput Q Λ θ β γ N →ₗ[blocksFactorAlgebraL Q ΛL θ β γ]
      BlocksAssocInput Q Λ θ β γ N' where
  toFun n := (g n : N')
  map_add' := g.map_add
  map_smul' t n := g.map_smul (blocksAssocFactorEquiv Q Λ θ β γ t) n

/-- A map of modules over the three blocks, on the one-step inputs. -/
def blocksOneStepInputHom (g : N →ₗ[blocksFactorAlgebra Q Λ θ β γ] N') :
    BlocksOneStepInput Q Λ θ β γ N →ₗ[TensorKLR3 S αᵣ β̂ᵣ γ̂ᵣ] BlocksOneStepInput Q Λ θ β γ N' where
  toFun n := (g n : N')
  map_add' := g.map_add
  map_smul' t n := g.map_smul (blocksOneStepMap Q Λ θ β γ t) n

variable (hQ : KLRSymm Q)


/-- The maps induced by `g` on the outer inductions and the one-step inductions agree, on the
partial standardization with the cut between the last two blocks first. -/
theorem blocksStandardOfShuffle_symm_map (g : N →ₗ[blocksFactorAlgebra Q Λ θ β γ] N')
    (y : Ind3 S αᵣ β̂ᵣ γ̂ᵣ (BlocksOneStepInput Q Λ θ β γ N)) :
    blocksStandardOfShuffle Q Λ θ β γ N' hQ ((blocksShuffleIndEquiv Q Λ θ β γ N').symm
        (BalancedTensor.mapRight (blocksOneStepInputHom Q Λ θ β γ g) y)) =
      blocksStandardMap Q Λ θ β γ hQ g (blocksStandardOfShuffle Q Λ θ β γ N hQ
        ((blocksShuffleIndEquiv Q Λ θ β γ N).symm y)) := by
  obtain ⟨u, rfl⟩ := (blocksShuffleIndEquiv Q Λ θ β γ N).surjective y
  rw [LinearEquiv.symm_apply_apply]
  induction u using BalancedTensor.induction_on with
  | zero => simp only [map_zero]
  | add u u' hu hu' => simp only [map_add, hu, hu']
  | tmul m₁ y =>
    induction y using BalancedTensor.induction_on with
    | zero => simp only [BalancedTensor.tmul_zero, map_zero]
    | add y y' hy hy' => simp only [BalancedTensor.tmul_add, map_add, hy, hy']
    | tmul m₂ n =>
      have h : BalancedTensor.mapRight (blocksOneStepInputHom Q Λ θ β γ g)
          (blocksShuffleIndEquiv Q Λ θ β γ N (BalancedTensor.tmul m₁ (BalancedTensor.tmul m₂ n))) =
          blocksShuffleIndEquiv Q Λ θ β γ N' (BalancedTensor.tmul m₁ (BalancedTensor.tmul m₂
            (show BlocksInner Q Λ θ β γ N' from g n))) := rfl
      rw [h, LinearEquiv.symm_apply_apply]
      rfl

/-- **The identification of the two iterations of partial standardization with three blocks is
natural in the module**: it intertwines the maps induced by a map `g : N → N'` of modules over
the three blocks. -/
theorem blocksStandardAssocEquiv_map (g : N →ₗ[blocksFactorAlgebra Q Λ θ β γ] N')
    (x : BlocksStandardL Q ΛL θ β γ (BlocksAssocInput Q Λ θ β γ N) hQ) :
    blocksStandardAssocEquiv Q Λ θ β γ N' hQ
        (blocksStandardMapL Q ΛL θ β γ hQ (blocksAssocInputHom Q Λ θ β γ g) x) =
      blocksStandardMap Q Λ θ β γ hQ g (blocksStandardAssocEquiv Q Λ θ β γ N hQ x) := by
  obtain ⟨w, rfl⟩ := blocksStandardOfShuffleL_surjective Q ΛL θ β γ _ hQ x
  induction w using BalancedTensor.induction_on with
  | zero => simp only [map_zero]
  | add w w' hw hw' => simp only [map_add, hw, hw']
  | tmul m₁ y =>
    induction y using BalancedTensor.induction_on with
    | zero => simp only [BalancedTensor.tmul_zero, map_zero]
    | add y y' hy hy' => simp only [BalancedTensor.tmul_add, map_add, hy, hy']
    | tmul m₂ n =>
      have h1 : blocksStandardMapL Q ΛL θ β γ hQ (blocksAssocInputHom Q Λ θ β γ g)
          (blocksStandardOfShuffleL Q ΛL θ β γ (BlocksAssocInput Q Λ θ β γ N) hQ
            (BalancedTensor.tmul m₁ (BalancedTensor.tmul m₂ n))) =
          blocksStandardOfShuffleL Q ΛL θ β γ (BlocksAssocInput Q Λ θ β γ N') hQ
            (BalancedTensor.tmul m₁ (BalancedTensor.tmul m₂
              (show BlocksAssocInput Q Λ θ β γ N' from g n))) := rfl
      rw [h1, blocksStandardAssocEquiv_ofShuffleL, blocksStandardAssocEquiv_ofShuffleL]
      have h2 : blocksAssocInd3Equiv Q Λ θ β γ N' (blocksShuffleInd3EquivL Q ΛL θ β γ
          (BlocksAssocInput Q Λ θ β γ N') (BalancedTensor.tmul m₁ (BalancedTensor.tmul m₂
            (show BlocksAssocInput Q Λ θ β γ N' from g n)))) =
          BalancedTensor.mapRight (blocksOneStepInputHom Q Λ θ β γ g)
            (blocksAssocInd3Equiv Q Λ θ β γ N (blocksShuffleInd3EquivL Q ΛL θ β γ
              (BlocksAssocInput Q Λ θ β γ N)
                (BalancedTensor.tmul m₁ (BalancedTensor.tmul m₂ n)))) :=
        rfl
      rw [h2]
      exact blocksStandardOfShuffle_symm_map Q Λ θ β γ hQ g _

end Categorification.Stendhal
