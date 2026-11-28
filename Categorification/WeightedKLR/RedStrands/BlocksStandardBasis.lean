/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.CutStandardBasis
import Categorification.WeightedKLR.RedStrands.ParabolicStandardExact
import Categorification.WeightedKLR.RedStrands.PartialStandardizationBlocks

/-!
# Shuffle coordinates of an iterated partial standardization

Webster, arXiv:1309.3796v3, §5.1, the partial standardizations after Definition 5.4, in the
induced model (`CutStandard`, iterated in `BlocksStandard`); used in §7.3, proof of Lemma 7.19,
for the standard basis of `S_+`. Webster states no basis of a partial standardization; the
two-block form `𝕊(N) ≅ ⊕_u ε_u N` is `cutStandardShuffleEquiv`. This file prepares its
iteration to several blocks:

* the shuffle coordinates are natural (`cutStandardShuffleEquiv_map`): the map of partial
  standardizations induced by `g` acts on each coordinate by `g`;
* an affine element `z` of the KLR algebra of all strands acts on `𝕊(N)` through `T^λ` as on the
  induced module (`cutStandardShuffleEquiv_action`), so a loading idempotent `e(s)` acts on the
  coordinate `u` by `1_{u s}` (`cutStandardShuffleEquiv_action_e`);
* for three blocks, `𝕊^{A;M;R}(N) ≅ ⊕_{u_out} ε_{u_out} 𝕊^{M;R}(N)` composed with the inner
  coordinates gives `𝕊^{A;M;R}(N)` as a submodule of `Sh_out → Sh_in → N`
  (`blocksStandardShuffleEquiv`), on which the first block acts coordinatewise
  (`blocksMidShuffleEquiv_head`) and the inner affine algebra by `1_{u_in s}`
  (`blocksMidShuffleEquiv_tail_e`).

Any commutative ring `k`, symmetric `Q`.

## Main definitions

* `Stendhal.affineToTensor`: the map from the affine KLR algebra of all strands to `T^λ`.
* `Stendhal.blocksShuffleCoords`, `Stendhal.blocksStandardShuffleEquiv`.

## Main results

* `Stendhal.cutStandardShuffleEquiv_map`, `Stendhal.cutStandardShuffleEquiv_action_e`.
* `Stendhal.blocksMidShuffleEquiv_head`, `Stendhal.blocksMidShuffleEquiv_tail_e`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA TensorProduct
open scoped TensorProduct

section Cut

variable {I k : Type*} [DecidableEq I] [CommRing k] {a r : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (a + r) → I →₀ ℕ) (θ β : Multiset I)

local notation "α" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd r)) (stendhalWeight a θ)
local notation "δ" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd a)) (stendhalWeight r β)
local notation "S" => stendhalQ Q Λ
local notation "Sh" => Shuffle (Seq.card_add' α δ)
local notation "D" => cutFactorAlgebra Q Λ θ β

variable {N N' : Type*} [AddCommGroup N] [Module k N] [Module (cutFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N]
  [AddCommGroup N'] [Module k N'] [Module (cutFactorAlgebra Q Λ θ β) N']
  [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N']
  (hQ : KLRSymm Q)

/-- **The shuffle coordinates are natural**: the map of partial standardizations induced by `g`
acts on each coordinate by `g`. -/
theorem cutStandardShuffleEquiv_map (g : N →ₗ[D] N') (z : CutStandard Q Λ θ β N) (u : Sh) :
    (cutStandardShuffleEquiv Q Λ θ β N' hQ (cutStandardMap Q Λ θ β g z) :
        Sh → CutInput Q Λ θ β N') u =
      g ((cutStandardShuffleEquiv Q Λ θ β N hQ z : Sh → CutInput Q Λ θ β N) u) := by
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ z
  change (cutStandardShuffleEquiv Q Λ θ β N' hQ
    (Submodule.mkQ _ (cutShuffleMap Q Λ θ β g y)) : Sh → CutInput Q Λ θ β N') u = _
  rw [cutStandardShuffleEquiv_mkQ, cutStandardShuffleEquiv_mkQ, cutShuffleMap,
    indDecomp_mapRight_apply]
  exact ((cutInputHom Q Λ θ β g).map_smul _ _).symm

/-- The map from the affine KLR algebra of all strands to `T^λ(θ + β)`. -/
def affineToTensor :
    KLRAlgebra k S (α + δ) →ₐ[k] TensorProductAlgebra k Q Λ (θ + β) :=
  ((TensorProductAlgebra.mk Q Λ (θ + β)).comp (orderProjection Q Λ (θ + β))).comp
    ((StendhalAlgebraAllOrders.ofKLR k Q Λ (θ + β)).comp
      (castKLR S (cutInputWeights_add (a := a) (r := r) θ β)).toAlgHom)

/-- An affine element acts on `𝕊(N)` through `T^λ` as on the induced module. -/
theorem cutStandardAction_affineToTensor (z : KLRAlgebra k S (α + δ))
    (y : CutShuffle Q Λ θ β N) :
    cutStandardAction Q Λ θ β N hQ (affineToTensor Q Λ θ β z) (Submodule.mkQ _ y) =
      Submodule.mkQ _ (z • y) :=
  (LinearMap.congr_fun (cutStandardAction_affine Q Λ θ β N hQ z) _).trans
    (orderedShuffleAction_mkQ _ _ _ z y)

/-- **A loading idempotent acts on the shuffle coordinates**: `e(s)` acts on the coordinate `u`
of `𝕊(N)` by `1_{u s}`. -/
theorem cutStandardShuffleEquiv_action_e (s : Seq (α + δ)) (w : CutStandard Q Λ θ β N)
    (u : Sh) :
    (cutStandardShuffleEquiv Q Λ θ β N hQ
        (cutStandardAction Q Λ θ β N hQ (affineToTensor Q Λ θ β (e s)) w) :
          Sh → CutInput Q Λ θ β N) u =
      concatIdem (Q := S) (u.1 • s) •
        (cutStandardShuffleEquiv Q Λ θ β N hQ w : Sh → CutInput Q Λ θ β N) u := by
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ w
  rw [cutStandardAction_affineToTensor, cutStandardShuffleEquiv_e_smul]

end Cut

/-! ### Three blocks -/

section Blocks

variable {I k : Type*} [DecidableEq I] [CommRing k] {a m r : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (a + (m + r)) → I →₀ ℕ) (θ β γ : Multiset I)
  (N : Type*) [AddCommGroup N] [Module k N] [Module (blocksFactorAlgebra Q Λ θ β γ) N]
  [IsScalarTower k (blocksFactorAlgebra Q Λ θ β γ) N] (hQ : KLRSymm Q)

local notation "αo" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd (m + r)))
  (stendhalWeight a θ)
local notation "δo" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd a))
  (stendhalWeight (m + r) (β + γ))
local notation "αi" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd r)) (stendhalWeight m β)
local notation "δi" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd m)) (stendhalWeight r γ)
local notation "ShO" => Shuffle (Seq.card_add' αo δo)
local notation "ShI" => Shuffle (Seq.card_add' αi δi)
local notation "Inner" => CutInput Q (blocksTailLabels Λ) β γ (BlocksInner Q Λ θ β γ N)

/-- The inner shuffle coordinates of the middle stage `𝕊^{M;R}(N)`. -/
abbrev blocksMidShuffleEquiv :
    BlocksMid Q Λ θ β γ N hQ ≃ₗ[k]
      cutShuffleCoords Q (blocksTailLabels Λ) β γ (BlocksInner Q Λ θ β γ N) :=
  cutStandardShuffleEquiv Q (blocksTailLabels Λ) β γ (BlocksInner Q Λ θ β γ N) hQ

/-- **The first block acts on the inner coordinates coordinatewise.** -/
theorem blocksMidShuffleEquiv_head (t : TensorProductAlgebra k Q (Λ ∘ Fin.castAdd (m + r)) θ)
    (z : BlocksMid Q Λ θ β γ N hQ) (v : ShI) :
    (blocksMidShuffleEquiv Q Λ θ β γ N hQ (blocksHeadAction Q Λ θ β γ N t z) : ShI → Inner) v =
      blocksHeadEnd Q Λ θ β γ N t
        ((blocksMidShuffleEquiv Q Λ θ β γ N hQ z : ShI → Inner) v) :=
  cutStandardShuffleEquiv_map Q (blocksTailLabels Λ) β γ hQ _ z v

/-- **A loading idempotent of the inner blocks acts on the inner coordinates** by `1_{u_in s}`. -/
theorem blocksMidShuffleEquiv_tail_e (s : Seq (αi + δi)) (z : BlocksMid Q Λ θ β γ N hQ)
    (v : ShI) :
    (blocksMidShuffleEquiv Q Λ θ β γ N hQ
        (cutStandardAction Q (blocksTailLabels Λ) β γ (BlocksInner Q Λ θ β γ N) hQ
          (affineToTensor Q (blocksTailLabels Λ) β γ (e s)) z) : ShI → Inner) v =
      concatIdem (Q := stendhalQ Q (blocksTailLabels Λ)) (v.1 • s) •
        (blocksMidShuffleEquiv Q Λ θ β γ N hQ z : ShI → Inner) v :=
  cutStandardShuffleEquiv_action_e Q (blocksTailLabels Λ) β γ hQ s z v

/-- The inner coordinates, applied to each outer coordinate. -/
def blocksInnerCoordMap : (ShO → BlocksMid Q Λ θ β γ N hQ) →ₗ[k] (ShO → ShI → Inner) :=
  LinearMap.pi fun u => (cutShuffleCoords Q (blocksTailLabels Λ) β γ
    (BlocksInner Q Λ θ β γ N)).subtype ∘ₗ (blocksMidShuffleEquiv Q Λ θ β γ N hQ).toLinearMap ∘ₗ
      LinearMap.proj u

theorem blocksInnerCoordMap_injective :
    Function.Injective (blocksInnerCoordMap Q Λ θ β γ N hQ) := fun _ _ h => funext fun u =>
  (blocksMidShuffleEquiv Q Λ θ β γ N hQ).injective (Subtype.ext (congrFun h u))

/-- The coordinates of the partial standardization with three blocks: the families
`G : Sh_out → Sh_in → N` whose rows `G u_out` are the inner coordinates of elements of
`ε_{u_out} 𝕊^{M;R}(N)`. -/
def blocksShuffleCoords : Submodule k (ShO → ShI → Inner) :=
  (cutShuffleCoords Q Λ θ (β + γ) (BlocksMid Q Λ θ β γ N hQ)).map
    (blocksInnerCoordMap Q Λ θ β γ N hQ)

/-- **The partial standardization with three blocks in shuffle coordinates**:
`𝕊^{A;M;R}(N) ≅ ⊕_{u_out} ε_{u_out} ⊕_{u_in} ε_{u_in} N`, as `k`-modules. -/
def blocksStandardShuffleEquiv :
    BlocksStandard Q Λ θ β γ N hQ ≃ₗ[k] blocksShuffleCoords Q Λ θ β γ N hQ :=
  (cutStandardShuffleEquiv Q Λ θ (β + γ) (BlocksMid Q Λ θ β γ N hQ) hQ).trans
    (Submodule.equivMapOfInjective _ (blocksInnerCoordMap_injective Q Λ θ β γ N hQ) _)

/-- The coordinates of `z` are the inner coordinates of its outer coordinates. -/
theorem blocksStandardShuffleEquiv_apply (z : BlocksStandard Q Λ θ β γ N hQ) (u : ShO)
    (v : ShI) :
    (blocksStandardShuffleEquiv Q Λ θ β γ N hQ z : ShO → ShI → Inner) u v =
      (blocksMidShuffleEquiv Q Λ θ β γ N hQ
        ((cutStandardShuffleEquiv Q Λ θ (β + γ) (BlocksMid Q Λ θ β γ N hQ) hQ z :
          ShO → CutInput Q Λ θ (β + γ) (BlocksMid Q Λ θ β γ N hQ)) u) : ShI → Inner) v :=
  rfl

end Blocks

end Categorification.Stendhal
