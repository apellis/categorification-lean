/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PartialStandardizationAssocCutInner
import Categorification.WeightedKLR.RedStrands.PartialStandardizationAssocCutRelabel
import Categorification.WeightedKLR.RedStrands.PartialStandardizationAssocInd

/-!
# The iterated partial standardization with three blocks in one step

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1, the
partial standardization functors `𝕊^{λ_1…λ_a; λ_{a+1}…λ_{a+m}; λ_{a+m+1}…λ_{a+m+r}}` defined
after Definition 5.4. Webster defines the partial standardization with several blocks in one
step: the module over `T^A(θ) ⊗ T^M(β) ⊗ T^R(γ)` is induced to the affine KLR algebra of all
strands along the inclusion `ι₃` of the three blocks, and the part supported on loadings whose
red strands are out of order is removed. Here the iterated partial standardization
`BlocksStandard` (inner cut first) is identified with this one-step model
(`blocksStandardOneStepEquiv`), compatibly with the affine action of all strands
(`blocksStandardOneStepEquiv_smul`).

The three affine input quotients of the one-step model are `cutPrefixProjection` on the first
block and, on the last two blocks, the affine input quotients of the inner cut composed with
the relabelling of their red strands into the alphabet of all red strands
(`blocksOneStepMap`).

## Main definitions

* `Stendhal.blocksOneStepMap`: the quotient of the affine KLR algebras of the three blocks onto
  `T^A(θ) ⊗ (T^M(β) ⊗ T^R(γ))`.
* `Stendhal.BlocksOneStepInput`: a module over the three blocks, restricted along it.
* `Stendhal.BlocksOneStepQuot`: the one-step partial standardization, `Ind₃ N` modulo the
  part supported on unordered loadings.

## Main results

* `Stendhal.blocksShuffleIndEquiv`: the outer induction of the inner affine induced module is
  the one-step induction `Ind₃ N`, semilinearly along the identification of weights.
* `Stendhal.blocksStandardOneStepEquiv`: `BlocksStandard ≃ BlocksOneStepQuot`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA
open scoped TensorProduct

/-- The ordered sums of two equal weights correspond. -/
theorem castKLR_eSum_redOrdered {I k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ}
    {S : I ⊕ Fin ℓ → I ⊕ Fin ℓ → MvPolynomial (Fin 2) k} {μ μ' : Multiset (I ⊕ Fin ℓ)}
    (h : μ = μ') :
    (open Classical in castKLR S h (eSum S (Finset.univ.filter fun s : Seq μ => IsRedOrdered s)))
      = open Classical in eSum S (Finset.univ.filter fun s : Seq μ' => IsRedOrdered s) := by
  subst h; rfl

variable {I k : Type*} [DecidableEq I] [CommRing k] {a m r : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (a + (m + r)) → I →₀ ℕ) (θ β γ : Multiset I)
  (N : Type*) [AddCommGroup N] [Module k N] [Module (blocksFactorAlgebra Q Λ θ β γ) N]
  [IsScalarTower k (blocksFactorAlgebra Q Λ θ β γ) N]

local notation "D₃" => blocksFactorAlgebra Q Λ θ β γ
local notation "Y" => CutShuffle Q (blocksTailLabels Λ) β γ (BlocksInner Q Λ θ β γ N)
local notation "Yₒ" => BlocksShuffleInput Q Λ θ β γ N
local notation "α" =>
  Multiset.map (Sum.map (id : I → I) (Fin.castAdd (m + r))) (stendhalWeight a θ)
local notation "δ" =>
  Multiset.map (Sum.map (id : I → I) (Fin.natAdd a)) (stendhalWeight (m + r) (β + γ))
local notation "β'" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd r)) (stendhalWeight m β)
local notation "γ'" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd m)) (stendhalWeight r γ)
local notation "β̂" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd a))
  (Multiset.map (Sum.map (id : I → I) (Fin.castAdd r)) (stendhalWeight m β))
local notation "γ̂" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd a))
  (Multiset.map (Sum.map (id : I → I) (Fin.natAdd m)) (stendhalWeight r γ))
local notation "S" => stendhalQ Q Λ
local notation "Sᵢ" => stendhalQ Q (blocksTailLabels Λ)

/-- The relabelling of the affine algebras of the last two blocks into the alphabet of all
red strands. -/
abbrev blocksTailTensor : TensorKLR Sᵢ β' γ' ≃ₐ[k] TensorKLR S β̂ γ̂ :=
  stendhalRelabelTensor Q Λ (Fin.natAdd a) (Fin.natAdd_injective (m + r) a) β' γ'

/-- **The affine input quotients of the one-step model**:
`R(α) ⊗ (R(β̂) ⊗ R(γ̂)) → T^A(θ) ⊗ (T^M(β) ⊗ T^R(γ))`. -/
def blocksOneStepMap : TensorKLR3 S α β̂ γ̂ →ₐ[k] D₃ :=
  Algebra.TensorProduct.map (cutPrefixProjection Q Λ θ)
    ((cutInputMap Q (blocksTailLabels Λ) β γ).comp (blocksTailTensor Q Λ β γ).symm.toAlgHom)

theorem blocksOneStepMap_tmul (t : KLRAlgebra k S α) (u : TensorKLR S β̂ γ̂) :
    blocksOneStepMap Q Λ θ β γ (t ⊗ₜ u) = cutPrefixProjection Q Λ θ t ⊗ₜ
      cutInputMap Q (blocksTailLabels Λ) β γ ((blocksTailTensor Q Λ β γ).symm u) := rfl

/-- A module over the three blocks, restricted to the affine algebras of the three blocks. -/
@[nolint unusedArguments]
def BlocksOneStepInput (_Q : I → I → MvPolynomial (Fin 2) k)
    (_Λ : Fin (a + (m + r)) → I →₀ ℕ) (_θ _β _γ : Multiset I) (N : Type*) : Type _ := N

local notation "N₃" => BlocksOneStepInput Q Λ θ β γ N

instance : AddCommGroup N₃ := inferInstanceAs (AddCommGroup N)
instance : Module k N₃ := inferInstanceAs (Module k N)
instance : Module (TensorKLR3 S α β̂ γ̂) N₃ :=
  Module.compHom N (blocksOneStepMap Q Λ θ β γ).toRingHom

omit [Module k N] [IsScalarTower k (blocksFactorAlgebra Q Λ θ β γ) N] in
theorem blocksOneStepInput_smul (t : TensorKLR3 S α β̂ γ̂) (n : N₃) :
    t • n = blocksOneStepMap Q Λ θ β γ t • (show N from n) := rfl

instance : IsScalarTower k (TensorKLR3 S α β̂ γ̂) N₃ where
  smul_assoc c t n := by
    rw [blocksOneStepInput_smul, blocksOneStepInput_smul, map_smul]
    exact smul_assoc c (blocksOneStepMap Q Λ θ β γ t) (show N from n)

/-! ### The inner affine induced module as the inner induction of the one-step model -/

/-- The input of the inner induction, identified. -/
def blocksInnerInputEquiv :
    CutInput Q (blocksTailLabels Λ) β γ (BlocksInner Q Λ θ β γ N) ≃ₗ[k]
      IndInnerInput S α β̂ γ̂ N₃ := LinearEquiv.refl k N

omit [IsScalarTower k (blocksFactorAlgebra Q Λ θ β γ) N] in
theorem blocksInnerInputEquiv_smul (t : TensorKLR Sᵢ β' γ')
    (n : CutInput Q (blocksTailLabels Λ) β γ (BlocksInner Q Λ θ β γ N)) :
    blocksInnerInputEquiv Q Λ θ β γ N (t • n) =
      blocksTailTensor Q Λ β γ t • blocksInnerInputEquiv Q Λ θ β γ N n := by
  change ((1 : blocksHeadAlgebra Q Λ θ) ⊗ₜ[k] cutInputMap Q (blocksTailLabels Λ) β γ t : D₃) •
      (show N from n) =
    blocksOneStepMap Q Λ θ β γ ((1 : KLRAlgebra k S α) ⊗ₜ blocksTailTensor Q Λ β γ t) •
      (show N from n)
  rw [blocksOneStepMap_tmul, map_one, AlgEquiv.symm_apply_apply]

/-- **The inner affine induced module is the inner induction of the one-step model**, after
relabelling the red strands of the last two blocks. -/
def blocksInnerEquiv : Y ≃ₗ[k] IndMid S α β̂ γ̂ N₃ :=
  indTransport (stendhalRelabelAdd Q Λ (Fin.natAdd a) (Fin.natAdd_injective (m + r) a) β' γ')
    (blocksTailTensor Q Λ β γ)
    (stendhalRelabelAdd_concat Q Λ (Fin.natAdd a) (Fin.natAdd_injective (m + r) a))
    (blocksInnerInputEquiv Q Λ θ β γ N) (blocksInnerInputEquiv_smul Q Λ θ β γ N)

omit [DecidableEq I] in
theorem blocksWeight_eq : δ = β̂ + γ̂ := by
  rw [← Multiset.map_add, cutInputWeights_add]

private theorem castKLR_trans' {μ₁ μ₂ μ₃ : Multiset (I ⊕ Fin (a + (m + r)))}
    (h₁ : μ₁ = μ₂) (h₂ : μ₂ = μ₃) (z : KLRAlgebra k S μ₁) :
    castKLR S h₂ (castKLR S h₁ z) = castKLR S (h₁.trans h₂) z := by
  subst h₁ h₂; rfl

/-- The relabelled outer tail action is the identification of weights. -/
theorem stendhalRelabelAdd_blocksTailMap (z : KLRAlgebra k S δ) :
    stendhalRelabelAdd Q Λ (Fin.natAdd a) (Fin.natAdd_injective (m + r) a) β' γ'
      (blocksTailMap Q Λ β γ z) = castKLR S (blocksWeight_eq β γ) z := by
  change castKLR S _ (relabelEquiv (stendhalRelabel Q Λ (Fin.natAdd a)
    (Fin.natAdd_injective (m + r) a) (β' + γ'))
      (castKLR Sᵢ (cutInputWeights_add (a := m) (r := r) β γ).symm
        ((relabelEquiv (blocksTailRelabel Q Λ β γ)).symm z))) = _
  rw [stendhalRelabel_castKLR]
  change castKLR S _ (castKLR S _ ((relabelEquiv (blocksTailRelabel Q Λ β γ))
    ((relabelEquiv (blocksTailRelabel Q Λ β γ)).symm z))) = _
  rw [AlgEquiv.apply_symm_apply, castKLR_trans']

theorem blocksInnerEquiv_head (t : KLRAlgebra k S α) (y : Y) :
    blocksInnerEquiv Q Λ θ β γ N
      (blocksShuffleHead Q Λ θ β γ N (cutPrefixProjection Q Λ θ t) y) =
      indHeadAction N₃ t (blocksInnerEquiv Q Λ θ β γ N y) := by
  induction y using BalancedTensor.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | add y y' hy hy' =>
    rw [map_add, map_add, hy, hy', map_add (blocksInnerEquiv Q Λ θ β γ N), map_add]
  | tmul m' n =>
    change BalancedTensor.tmul (N := IndInnerInput S α β̂ γ̂ N₃) _
        ((cutPrefixProjection Q Λ θ t ⊗ₜ[k]
          (1 : cutFactorAlgebra Q (blocksTailLabels Λ) β γ) : D₃) • (show N from n) : N) =
      BalancedTensor.tmul (N := IndInnerInput S α β̂ γ̂ N₃) _
        (blocksOneStepMap Q Λ θ β γ (t ⊗ₜ (1 : TensorKLR S β̂ γ̂)) • (show N from n) : N)
    rw [blocksOneStepMap_tmul, map_one, map_one]

/-- The identification of the inner modules, on `Y` as a module over the outer affine
algebras. -/
def blocksInputEquiv : Yₒ ≃ₗ[k] IndMid S α β̂ γ̂ N₃ := blocksInnerEquiv Q Λ θ β γ N

/-- The identification of the inner modules is semilinear along the identification of
weights. -/
theorem blocksInputEquiv_smul (s : TensorKLR S α δ) (y : Yₒ) :
    blocksInputEquiv Q Λ θ β γ N (s • y) =
      castTensor S rfl (blocksWeight_eq β γ) s • blocksInputEquiv Q Λ θ β γ N y := by
  induction s using TensorProduct.inductionOn with
  | add s s' hs hs' => rw [add_smul, map_add, hs, hs', map_add, add_smul]
  | tmul t z =>
    rw [castTensor_tmul, castKLR_rfl, indMid_smul, indMidAction_tmul]
    change blocksInnerEquiv Q Λ θ β γ N (blocksShuffleHead Q Λ θ β γ N
      (cutPrefixProjection Q Λ θ t) (blocksTailMap Q Λ β γ z • (show Y from y))) =
        indHeadAction N₃ t (castKLR S (blocksWeight_eq β γ) z •
          blocksInnerEquiv Q Λ θ β γ N (show Y from y))
    rw [blocksInnerEquiv_head]
    congr 1
    change indTransport _ _ _ _ _ (blocksTailMap Q Λ β γ z • (show Y from y)) = _
    rw [indTransport_smul, stendhalRelabelAdd_blocksTailMap]
    rfl

/-! ### The outer induction of `Y` as the one-step induction -/

local notation "W" => Ind S α δ Yₒ

/-- **The outer induction of the inner affine induced module is the one-step induction**
`Ind₃ N` of the three blocks. -/
def blocksShuffleIndEquiv : W ≃ₗ[k] Ind3 S α β̂ γ̂ N₃ :=
  (indCast rfl (blocksWeight_eq β γ) (blocksInputEquiv Q Λ θ β γ N)
    (blocksInputEquiv_smul Q Λ θ β γ N)).trans
    ((indIterEquiv N₃).restrictScalars k)

/-- It is semilinear along the identification of weights. -/
theorem blocksShuffleIndEquiv_smul (z : KLRAlgebra k S (α + δ)) (w : W) :
    blocksShuffleIndEquiv Q Λ θ β γ N (z • w) =
      castKLR S (add_eq_add_of_eq rfl (blocksWeight_eq β γ)) z •
        blocksShuffleIndEquiv Q Λ θ β γ N w := by
  change (indIterEquiv N₃).restrictScalars k ((indCast rfl (blocksWeight_eq β γ)
    (blocksInputEquiv Q Λ θ β γ N) (blocksInputEquiv_smul Q Λ θ β γ N)) (z • w)) = _
  rw [indCast_smul]
  exact (indIterEquiv N₃).map_smul _ _

/-! ### The one-step partial standardization -/

open Classical in
/-- The loadings of all strands with the red strands in order. -/
abbrev blocksOneStepOrdered : Finset (Seq (α + (β̂ + γ̂))) :=
  Finset.univ.filter fun s => IsRedOrdered s

/-- **The one-step partial standardization with three blocks**: the one-step induction modulo
the part supported on loadings whose red strands are out of order. -/
abbrev BlocksOneStepQuot : Type _ :=
  Ind3 S α β̂ γ̂ N₃ ⧸ excludedSpace
    (Algebra.lsmul k k (Ind3 S α β̂ γ̂ N₃) :
      KLRAlgebra k S (α + (β̂ + γ̂)) →ₐ[k] Module.End k (Ind3 S α β̂ γ̂ N₃))
    (blocksOneStepOrdered (a := a) (m := m) (r := r) θ β γ)

theorem blocksShuffleIndEquiv_eSum (w : W) :
    (eSum S (blocksOneStepOrdered (a := a) (m := m) (r := r) θ β γ) :
      KLRAlgebra k S (α + (β̂ + γ̂))) •
        blocksShuffleIndEquiv Q Λ θ β γ N w = 0 ↔
      (eSum S (cutOrderedLoadings (a := a) (r := m + r) θ (β + γ)) :
        KLRAlgebra k S (α + δ)) • w = 0 := by
  rw [← (blocksShuffleIndEquiv Q Λ θ β γ N).map_eq_zero_iff, blocksShuffleIndEquiv_smul,
    cutOrderedLoadings, castKLR_eSum_redOrdered]

theorem map_excludedSpace_blocksShuffleIndEquiv :
    (excludedSpace (Algebra.lsmul k k W : KLRAlgebra k S (α + δ) →ₐ[k] Module.End k W)
      (cutOrderedLoadings (a := a) (r := m + r) θ (β + γ))).map
        (blocksShuffleIndEquiv Q Λ θ β γ N : W →ₗ[k] Ind3 S α β̂ γ̂ N₃) =
      excludedSpace (Algebra.lsmul k k (Ind3 S α β̂ γ̂ N₃) :
        KLRAlgebra k S (α + (β̂ + γ̂)) →ₐ[k] Module.End k (Ind3 S α β̂ γ̂ N₃))
        (blocksOneStepOrdered (a := a) (m := m) (r := r) θ β γ) := by
  ext v
  obtain ⟨w, rfl⟩ := (blocksShuffleIndEquiv Q Λ θ β γ N).surjective v
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]
  exact (blocksShuffleIndEquiv_eSum Q Λ θ β γ N w).symm

variable (hQ : KLRSymm Q)

/-- **The iterated partial standardization with three blocks is the one-step partial
standardization**: `BlocksStandard N ≃ Ind₃ N / (unordered part)`. -/
def blocksStandardOneStepEquiv :
    BlocksStandard Q Λ θ β γ N hQ ≃ₗ[k] BlocksOneStepQuot Q Λ θ β γ N :=
  (blocksStandardEquiv Q Λ θ β γ N hQ).symm.trans
    (Submodule.Quotient.equiv _ _ (blocksShuffleIndEquiv Q Λ θ β γ N)
      (map_excludedSpace_blocksShuffleIndEquiv Q Λ θ β γ N))

theorem blocksStandardOneStepEquiv_apply (w : W) :
    blocksStandardOneStepEquiv Q Λ θ β γ N hQ (blocksStandardOfShuffle Q Λ θ β γ N hQ w) =
      Submodule.Quotient.mk (blocksShuffleIndEquiv Q Λ θ β γ N w) := by
  rw [blocksStandardOneStepEquiv, LinearEquiv.trans_apply, ← blocksStandardEquiv_mk,
    LinearEquiv.symm_apply_apply]
  rfl

/-- The identification is compatible with the affine action of all strands, which acts on
the iterated standardization through `T^λ(θ + (β + γ))`. -/
theorem blocksStandardOneStepEquiv_smul (z : KLRAlgebra k S (α + δ)) (w : W) :
    blocksStandardOneStepEquiv Q Λ θ β γ N hQ
      (blocksStandardAction Q Λ θ β γ N hQ (TensorProductAlgebra.mk Q Λ (θ + (β + γ))
        (orderProjection Q Λ (θ + (β + γ)) (StendhalAlgebraAllOrders.ofKLR k Q Λ (θ + (β + γ))
          (castKLR S (cutInputWeights_add (a := a) (r := m + r) θ (β + γ)) z))))
        (blocksStandardOfShuffle Q Λ θ β γ N hQ w)) =
      Submodule.Quotient.mk (castKLR S (add_eq_add_of_eq rfl (blocksWeight_eq β γ)) z •
        blocksShuffleIndEquiv Q Λ θ β γ N w) := by
  rw [← blocksStandardEquiv_mk, ← blocksStandardEquiv_smul, blocksStandardEquiv_mk,
    blocksStandardOneStepEquiv_apply, blocksShuffleIndEquiv_smul]

end Categorification.Stendhal
