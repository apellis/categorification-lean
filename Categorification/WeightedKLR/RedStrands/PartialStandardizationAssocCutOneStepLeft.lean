/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PartialStandardizationAssocCutInnerLeft
import Categorification.WeightedKLR.RedStrands.PartialStandardizationAssocCutOneStep
import Categorification.WeightedKLR.RedStrands.PartialStandardizationAssocIndLeft

/-!
# The iterated partial standardization, first cut first, in one step

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1, the
partial standardization functors `𝕊^{λ_1…λ_a; λ_{a+1}…λ_{a+m}; λ_{a+m+1}…λ_{a+m+r}}` defined
after Definition 5.4, in one step: the module over the three blocks is induced to the affine
KLR algebra of all strands along the inclusion `ι₃` of the three blocks, and the part supported
on loadings whose red strands are out of order is removed. Here the iterated partial
standardization `BlocksStandardL` (first cut first) is identified with this one-step model
(`blocksStandardOneStepEquivL`), compatibly with the affine action of all strands
(`blocksStandardOneStepEquivL_smul`). `PartialStandardizationAssocCutOneStep` does the same
for the other order of the cuts.

The three affine input quotients are, on the first two blocks, the affine input quotients of
the first cut composed with the relabelling of their red strands into the alphabet of all red
strands, and `cutSuffixProjection` on the last block (`blocksOneStepMapL`).

## Main definitions

* `Stendhal.blocksOneStepMapL`: the quotient of the affine KLR algebras of the three blocks
  onto `(T^A(θ) ⊗ T^M(β)) ⊗ T^R(γ)`.
* `Stendhal.BlocksOneStepInputL`: a module over the three blocks, restricted along it.
* `Stendhal.BlocksOneStepQuotL`: the one-step partial standardization, `Ind₃ N` modulo the
  part supported on unordered loadings.

## Main results

* `Stendhal.blocksShuffleIndEquivL`: the outer induction of the affine induced module of the
  first two blocks is the one-step induction `Ind₃ N`, semilinearly along the identification of
  weights.
* `Stendhal.blocksStandardOneStepEquivL`: `BlocksStandardL ≃ BlocksOneStepQuotL`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA
open scoped TensorProduct

variable {I k : Type*} [DecidableEq I] [CommRing k] {a m r : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ((a + m) + r) → I →₀ ℕ) (θ β γ : Multiset I)
  (N : Type*) [AddCommGroup N] [Module k N] [Module (blocksFactorAlgebraL Q Λ θ β γ) N]
  [IsScalarTower k (blocksFactorAlgebraL Q Λ θ β γ) N]

local notation "D₃" => blocksFactorAlgebraL Q Λ θ β γ
local notation "Dᵢ" => cutFactorAlgebra Q (blocksLeftLabels Λ) θ β
local notation "A₀" => blocksLastAlgebra Q Λ γ
local notation "Y" => CutShuffle Q (blocksLeftLabels Λ) θ β (BlocksInnerL Q Λ θ β γ N)
local notation "Yₒ" => BlocksShuffleInputL Q Λ θ β γ N
local notation "α" =>
  Multiset.map (Sum.map (id : I → I) (Fin.castAdd r)) (stendhalWeight (a + m) (θ + β))
local notation "δ" =>
  Multiset.map (Sum.map (id : I → I) (Fin.natAdd (a + m))) (stendhalWeight r γ)
local notation "α'" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd m)) (stendhalWeight a θ)
local notation "β'" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd a)) (stendhalWeight m β)
local notation "α̂" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd r))
  (Multiset.map (Sum.map (id : I → I) (Fin.castAdd m)) (stendhalWeight a θ))
local notation "β̂" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd r))
  (Multiset.map (Sum.map (id : I → I) (Fin.natAdd a)) (stendhalWeight m β))
local notation "S" => stendhalQ Q Λ
local notation "Sᵢ" => stendhalQ Q (blocksLeftLabels Λ)

/-- The relabelling of the affine algebras of the first two blocks into the alphabet of all
red strands. -/
abbrev blocksHeadTensorL : TensorKLR Sᵢ α' β' ≃ₐ[k] TensorKLR S α̂ β̂ :=
  stendhalRelabelTensor Q Λ (Fin.castAdd r) (Fin.castAdd_injective (a + m) r) α' β'

/-- **The affine input quotients of the one-step model**:
`(R(α̂) ⊗ R(β̂)) ⊗ R(δ) → (T^A(θ) ⊗ T^M(β)) ⊗ T^R(γ)`. -/
def blocksOneStepMapL : TensorKLR3L S α̂ β̂ δ →ₐ[k] D₃ :=
  Algebra.TensorProduct.map
    ((cutInputMap Q (blocksLeftLabels Λ) θ β).comp (blocksHeadTensorL Q Λ θ β).symm.toAlgHom)
    (cutSuffixProjection (a := a + m) (r := r) Q Λ γ)

theorem blocksOneStepMapL_tmul (u : TensorKLR S α̂ β̂) (t : KLRAlgebra k S δ) :
    blocksOneStepMapL Q Λ θ β γ (u ⊗ₜ t) =
      cutInputMap Q (blocksLeftLabels Λ) θ β ((blocksHeadTensorL Q Λ θ β).symm u) ⊗ₜ
        cutSuffixProjection (a := a + m) (r := r) Q Λ γ t := rfl

/-- The affine input quotients of the one-step model, on `R(α̂) ⊗ (R(β̂) ⊗ R(δ))`. -/
def blocksOneStepMap3L : TensorKLR3 S α̂ β̂ δ →ₐ[k] D₃ :=
  (blocksOneStepMapL Q Λ θ β γ).comp
    (Algebra.TensorProduct.assoc k k k (KLRAlgebra k S α̂) (KLRAlgebra k S β̂)
      (KLRAlgebra k S δ)).symm.toAlgHom

/-- A module over the three blocks, restricted to the affine algebras of the three blocks. -/
@[nolint unusedArguments]
def BlocksOneStepInputL (_Q : I → I → MvPolynomial (Fin 2) k)
    (_Λ : Fin ((a + m) + r) → I →₀ ℕ) (_θ _β _γ : Multiset I) (N : Type*) : Type _ := N

local notation "N₃'" => BlocksOneStepInputL Q Λ θ β γ N
local notation "N₃" => ReassocInput S α̂ β̂ δ (BlocksOneStepInputL Q Λ θ β γ N)

instance : AddCommGroup N₃' := inferInstanceAs (AddCommGroup N)
instance : Module k N₃' := inferInstanceAs (Module k N)
instance : Module (TensorKLR3 S α̂ β̂ δ) N₃' :=
  Module.compHom N (blocksOneStepMap3L Q Λ θ β γ).toRingHom

omit [Module k N] [IsScalarTower k (blocksFactorAlgebraL Q Λ θ β γ) N] in
theorem blocksOneStepInputL_smul (t : TensorKLR3 S α̂ β̂ δ) (n : N₃') :
    t • n = blocksOneStepMap3L Q Λ θ β γ t • (show N from n) := rfl

instance : IsScalarTower k (TensorKLR3 S α̂ β̂ δ) N₃' where
  smul_assoc c t n := by
    rw [blocksOneStepInputL_smul, blocksOneStepInputL_smul, map_smul]
    exact smul_assoc c (blocksOneStepMap3L Q Λ θ β γ t) (show N from n)

omit [Module k N] [IsScalarTower k (blocksFactorAlgebraL Q Λ θ β γ) N] in
theorem blocksReassocInput_smul (t : TensorKLR3L S α̂ β̂ δ) (n : N₃) :
    t • n = blocksOneStepMapL Q Λ θ β γ t • (show N from n) := by
  rw [reassocInput_smul]
  change blocksOneStepMapL Q Λ θ β γ ((Algebra.TensorProduct.assoc k k k _ _ _).symm
    (Algebra.TensorProduct.assoc k k k _ _ _ t)) • (show N from n) = _
  rw [AlgEquiv.symm_apply_apply]

/-! ### The affine induced module of the first two blocks as the inner induction -/

omit [IsScalarTower k (blocksFactorAlgebraL Q Λ θ β γ) N] in
private theorem innerInputL_smul (u : TensorKLR S α̂ β̂) (n : IndInnerInputL S α̂ β̂ δ N₃) :
    u • n = (cutInputMap Q (blocksLeftLabels Λ) θ β ((blocksHeadTensorL Q Λ θ β).symm u) ⊗ₜ[k]
      (1 : A₀) : D₃) • (show N from n) := by
  rw [indInnerInputL_smul]
  exact (blocksReassocInput_smul Q Λ θ β γ N _ _).trans (by rw [blocksOneStepMapL_tmul, map_one])

/-- The input of the inner induction, identified. -/
def blocksInnerInputEquivL :
    CutInput Q (blocksLeftLabels Λ) θ β (BlocksInnerL Q Λ θ β γ N) ≃ₗ[k]
      IndInnerInputL S α̂ β̂ δ N₃ := LinearEquiv.refl k N

omit [IsScalarTower k (blocksFactorAlgebraL Q Λ θ β γ) N] in
theorem blocksInnerInputEquivL_smul (t : TensorKLR Sᵢ α' β')
    (n : CutInput Q (blocksLeftLabels Λ) θ β (BlocksInnerL Q Λ θ β γ N)) :
    blocksInnerInputEquivL Q Λ θ β γ N (t • n) =
      blocksHeadTensorL Q Λ θ β t • blocksInnerInputEquivL Q Λ θ β γ N n := by
  change (cutInputMap Q (blocksLeftLabels Λ) θ β t ⊗ₜ[k] (1 : A₀) : D₃) • (show N from n) =
    blocksHeadTensorL Q Λ θ β t • (show IndInnerInputL S α̂ β̂ δ N₃ from n)
  rw [innerInputL_smul, AlgEquiv.symm_apply_apply]

/-- **The affine induced module of the first two blocks is the inner induction of the one-step
model**, after relabelling the red strands of the first two blocks. -/
def blocksInnerEquivL : Y ≃ₗ[k] IndMidL S α̂ β̂ δ N₃ :=
  indTransport (stendhalRelabelAdd Q Λ (Fin.castAdd r) (Fin.castAdd_injective (a + m) r) α' β')
    (blocksHeadTensorL Q Λ θ β)
    (stendhalRelabelAdd_concat Q Λ (Fin.castAdd r) (Fin.castAdd_injective (a + m) r))
    (blocksInnerInputEquivL Q Λ θ β γ N) (blocksInnerInputEquivL_smul Q Λ θ β γ N)

omit [DecidableEq I] in
theorem blocksWeightL_eq : α = α̂ + β̂ := by
  rw [← Multiset.map_add, cutInputWeights_add]

private theorem castKLR_trans' {μ₁ μ₂ μ₃ : Multiset (I ⊕ Fin ((a + m) + r))}
    (h₁ : μ₁ = μ₂) (h₂ : μ₂ = μ₃) (z : KLRAlgebra k S μ₁) :
    castKLR S h₂ (castKLR S h₁ z) = castKLR S (h₁.trans h₂) z := by
  subst h₁ h₂; rfl

/-- The relabelled outer head action is the identification of weights. -/
theorem stendhalRelabelAdd_blocksHeadMapL (z : KLRAlgebra k S α) :
    stendhalRelabelAdd Q Λ (Fin.castAdd r) (Fin.castAdd_injective (a + m) r) α' β'
      (blocksHeadMapL Q Λ θ β z) = castKLR S (blocksWeightL_eq θ β) z := by
  change castKLR S _ (relabelEquiv (stendhalRelabel Q Λ (Fin.castAdd r)
    (Fin.castAdd_injective (a + m) r) (α' + β'))
      (castKLR Sᵢ (cutInputWeights_add (a := a) (r := m) θ β).symm
        ((relabelEquiv (blocksHeadRelabelL Q Λ θ β)).symm z))) = _
  rw [stendhalRelabel_castKLR]
  change castKLR S _ (castKLR S _ ((relabelEquiv (blocksHeadRelabelL Q Λ θ β))
    ((relabelEquiv (blocksHeadRelabelL Q Λ θ β)).symm z))) = _
  rw [AlgEquiv.apply_symm_apply, castKLR_trans']

theorem blocksInnerEquivL_last (t : KLRAlgebra k S δ) (y : Y) :
    blocksInnerEquivL Q Λ θ β γ N
      (blocksShuffleLast Q Λ θ β γ N (cutSuffixProjection (a := a + m) (r := r) Q Λ γ t) y) =
      indTailAction N₃ t (blocksInnerEquivL Q Λ θ β γ N y) := by
  induction y using BalancedTensor.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | add y y' hy hy' =>
    rw [map_add, map_add, hy, hy', map_add (blocksInnerEquivL Q Λ θ β γ N), map_add]
  | tmul m' n =>
    change BalancedTensor.tmul (N := IndInnerInputL S α̂ β̂ δ N₃) _
        (((1 : Dᵢ) ⊗ₜ[k] cutSuffixProjection (a := a + m) (r := r) Q Λ γ t : D₃) •
          (show N from n) : N) =
      BalancedTensor.tmul (N := IndInnerInputL S α̂ β̂ δ N₃) _
        ((((1 : TensorKLR S α̂ β̂) ⊗ₜ t : TensorKLR3L S α̂ β̂ δ) • (show N₃ from n)) : N₃)
    rw [blocksReassocInput_smul, blocksOneStepMapL_tmul, map_one, map_one]

/-- The identification of the inner modules, on `Y` as a module over the outer affine
algebras. -/
def blocksInputEquivL : Yₒ ≃ₗ[k] IndMidL S α̂ β̂ δ N₃ := blocksInnerEquivL Q Λ θ β γ N

/-- The identification of the inner modules is semilinear along the identification of
weights. -/
theorem blocksInputEquivL_smul (s : TensorKLR S α δ) (y : Yₒ) :
    blocksInputEquivL Q Λ θ β γ N (s • y) =
      castTensor S (blocksWeightL_eq θ β) rfl s • blocksInputEquivL Q Λ θ β γ N y := by
  induction s using TensorProduct.inductionOn with
  | add s s' hs hs' => rw [add_smul, map_add, hs, hs', map_add, add_smul]
  | tmul t z =>
    rw [castTensor_tmul, castKLR_rfl, indMidL_smul, indMidActionL_tmul]
    change indTransport _ _ _ _ _ (blocksHeadMapL Q Λ θ β t • blocksShuffleLast Q Λ θ β γ N
      (cutSuffixProjection (a := a + m) (r := r) Q Λ γ z) (show Y from y)) =
        castKLR S (blocksWeightL_eq θ β) t •
          indTailAction N₃ z (blocksInnerEquivL Q Λ θ β γ N (show Y from y))
    rw [indTransport_smul, stendhalRelabelAdd_blocksHeadMapL]
    congr 1
    exact blocksInnerEquivL_last Q Λ θ β γ N z _

/-! ### The outer induction of `Y` as the one-step induction -/

local notation "W" => Ind S α δ Yₒ

/-- **The outer induction of the affine induced module of the first two blocks is the one-step
induction** along `ι₃ᴸ`. -/
def blocksShuffleIndEquivL : W ≃ₗ[k] Ind3L S α̂ β̂ δ N₃ :=
  (indCast (blocksWeightL_eq θ β) rfl (blocksInputEquivL Q Λ θ β γ N)
    (blocksInputEquivL_smul Q Λ θ β γ N)).trans
    ((indIterEquivL N₃).restrictScalars k)

/-- It is semilinear along the identification of weights. -/
theorem blocksShuffleIndEquivL_smul (z : KLRAlgebra k S (α + δ)) (w : W) :
    blocksShuffleIndEquivL Q Λ θ β γ N (z • w) =
      castKLR S (add_eq_add_of_eq (blocksWeightL_eq θ β) rfl) z •
        blocksShuffleIndEquivL Q Λ θ β γ N w := by
  change (indIterEquivL N₃).restrictScalars k ((indCast (blocksWeightL_eq θ β) rfl
    (blocksInputEquivL Q Λ θ β γ N) (blocksInputEquivL_smul Q Λ θ β γ N)) (z • w)) = _
  rw [indCast_smul]
  exact (indIterEquivL N₃).map_smul _ _

omit [DecidableEq I] in
theorem blocksWeightL_add_eq : α + δ = α̂ + (β̂ + δ) :=
  (congrArg (· + δ) (blocksWeightL_eq θ β)).trans (add_assoc _ _ _)

/-- **The outer induction of `Y` is the one-step induction** `Ind₃ N` along `ι₃`. -/
def blocksShuffleInd3EquivL : W ≃ₗ[k] Ind3 S α̂ β̂ δ N₃' :=
  (blocksShuffleIndEquivL Q Λ θ β γ N).trans (ind3LEquiv N₃')

/-- It is semilinear along the identification of weights. -/
theorem blocksShuffleInd3EquivL_smul (z : KLRAlgebra k S (α + δ)) (w : W) :
    blocksShuffleInd3EquivL Q Λ θ β γ N (z • w) =
      castKLR S (blocksWeightL_add_eq θ β γ) z • blocksShuffleInd3EquivL Q Λ θ β γ N w := by
  change ind3LEquiv N₃' (blocksShuffleIndEquivL Q Λ θ β γ N (z • w)) = _
  rw [blocksShuffleIndEquivL_smul, ind3LEquiv_smul, castKLR_trans']
  rfl

/-! ### The one-step partial standardization -/

open Classical in
/-- The loadings of all strands with the red strands in order. -/
abbrev blocksOneStepOrderedL : Finset (Seq (α̂ + (β̂ + δ))) :=
  Finset.univ.filter fun s => IsRedOrdered s

/-- **The one-step partial standardization with three blocks**, for the first-cut-first
nesting: the one-step induction modulo the part supported on loadings whose red strands are
out of order. -/
abbrev BlocksOneStepQuotL : Type _ :=
  Ind3 S α̂ β̂ δ N₃' ⧸ excludedSpace
    (Algebra.lsmul k k (Ind3 S α̂ β̂ δ N₃') :
      KLRAlgebra k S (α̂ + (β̂ + δ)) →ₐ[k] Module.End k (Ind3 S α̂ β̂ δ N₃'))
    (blocksOneStepOrderedL (a := a) (m := m) (r := r) θ β γ)

theorem blocksShuffleInd3EquivL_eSum (w : W) :
    (eSum S (blocksOneStepOrderedL (a := a) (m := m) (r := r) θ β γ) :
      KLRAlgebra k S (α̂ + (β̂ + δ))) •
        blocksShuffleInd3EquivL Q Λ θ β γ N w = 0 ↔
      (eSum S (cutOrderedLoadings (a := a + m) (r := r) (θ + β) γ) :
        KLRAlgebra k S (α + δ)) • w = 0 := by
  rw [← (blocksShuffleInd3EquivL Q Λ θ β γ N).map_eq_zero_iff, blocksShuffleInd3EquivL_smul,
    cutOrderedLoadings, castKLR_eSum_redOrdered]

theorem map_excludedSpace_blocksShuffleInd3EquivL :
    (excludedSpace (Algebra.lsmul k k W : KLRAlgebra k S (α + δ) →ₐ[k] Module.End k W)
      (cutOrderedLoadings (a := a + m) (r := r) (θ + β) γ)).map
        (blocksShuffleInd3EquivL Q Λ θ β γ N : W →ₗ[k] Ind3 S α̂ β̂ δ N₃') =
      excludedSpace (Algebra.lsmul k k (Ind3 S α̂ β̂ δ N₃') :
        KLRAlgebra k S (α̂ + (β̂ + δ)) →ₐ[k] Module.End k (Ind3 S α̂ β̂ δ N₃'))
        (blocksOneStepOrderedL (a := a) (m := m) (r := r) θ β γ) := by
  ext v
  obtain ⟨w, rfl⟩ := (blocksShuffleInd3EquivL Q Λ θ β γ N).surjective v
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]
  exact (blocksShuffleInd3EquivL_eSum Q Λ θ β γ N w).symm

variable (hQ : KLRSymm Q)

/-- **The iterated partial standardization with three blocks, first cut first, is the one-step
partial standardization**: `BlocksStandardL N ≃ Ind₃ N / (unordered part)`. -/
def blocksStandardOneStepEquivL :
    BlocksStandardL Q Λ θ β γ N hQ ≃ₗ[k] BlocksOneStepQuotL Q Λ θ β γ N :=
  (blocksStandardEquivL Q Λ θ β γ N hQ).symm.trans
    (Submodule.Quotient.equiv _ _ (blocksShuffleInd3EquivL Q Λ θ β γ N)
      (map_excludedSpace_blocksShuffleInd3EquivL Q Λ θ β γ N))

theorem blocksStandardOneStepEquivL_apply (w : W) :
    blocksStandardOneStepEquivL Q Λ θ β γ N hQ (blocksStandardOfShuffleL Q Λ θ β γ N hQ w) =
      Submodule.Quotient.mk (blocksShuffleInd3EquivL Q Λ θ β γ N w) := by
  rw [blocksStandardOneStepEquivL, LinearEquiv.trans_apply, ← blocksStandardEquivL_mk,
    LinearEquiv.symm_apply_apply]
  rfl

/-- The identification is compatible with the affine action of all strands, which acts on
the iterated standardization through `T^λ((θ + β) + γ)`. -/
theorem blocksStandardOneStepEquivL_smul (z : KLRAlgebra k S (α + δ)) (w : W) :
    blocksStandardOneStepEquivL Q Λ θ β γ N hQ
      (blocksStandardActionL Q Λ θ β γ N hQ (TensorProductAlgebra.mk Q Λ ((θ + β) + γ)
        (orderProjection Q Λ ((θ + β) + γ) (StendhalAlgebraAllOrders.ofKLR k Q Λ ((θ + β) + γ)
          (castKLR S (cutInputWeights_add (a := a + m) (r := r) (θ + β) γ) z))))
        (blocksStandardOfShuffleL Q Λ θ β γ N hQ w)) =
      Submodule.Quotient.mk (castKLR S (blocksWeightL_add_eq θ β γ) z •
        blocksShuffleInd3EquivL Q Λ θ β γ N w) := by
  rw [← blocksStandardEquivL_mk, ← blocksStandardEquivL_smul, blocksStandardEquivL_mk,
    blocksStandardOneStepEquivL_apply, blocksShuffleInd3EquivL_smul]

end Categorification.Stendhal
