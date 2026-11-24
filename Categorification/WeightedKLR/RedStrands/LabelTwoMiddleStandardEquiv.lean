/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoMiddleExact

/-!
# Parabolic comparison for the label-two middle standard

The regular separated test module is generated from the identity shuffle.
The diagrammatic test map hits that shuffle and detects both supported
loadings, yielding an equivalence with parabolic standardization.
-/


noncomputable section
namespace Categorification.Stendhal.LabelTwo
open KLR KLRAlgebra TypeA
open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable (k : Type) [Field k]

local notation "singleBlack" => ({()} : Multiset Unit)
local notation "q" => parameter k
local notation "α" => Multiset.map (addRedColor 1) (stendhalWeight 1 singleBlack)
local notation "lc" => Sum.map (id : Unit → Unit) (fun _ : Fin 1 => Fin.last 1)
local notation "δ" => Multiset.map lc (stendhalWeight 1 singleBlack)
local notation "P" => stendhalQ q weights
local notation "R" => KLRAlgebra k P (α + δ)
local notation "A" => TensorProductAlgebra k q weights (singleBlack + singleBlack)
local notation "D" => parabolicFactorAlgebra q weights singleBlack singleBlack
local notation "D₀" => ParabolicInput q weights singleBlack singleBlack D
local notation "V" => ParabolicStandard q weights singleBlack singleBlack D
local notation "X" => ParabolicShuffle q weights singleBlack singleBlack D
local notation "ρ" => parabolicShuffleAction q weights singleBlack singleBlack D
local notation "E" => parabolicOrderedLoadings (ℓ := 1) singleBlack singleBlack
local notation "proj" => Submodule.mkQ (excludedSpace ρ E)
local notation "U" => parabolicStandardUnit q weights singleBlack singleBlack D

private theorem parameterSymmStd : KLRSymm q :=
  fun a b h => (h (Subsingleton.elim a b)).elim

private abbrev affineProj (a : R) : A :=
  tensorOfKLR q weights (singleBlack + singleBlack) (castKLR P (parabolicInputWeights_add (ℓ := 1) singleBlack singleBlack) a)

private theorem affineAct_tmul (r : IndBimod P α δ) (n : D₀) :
    parabolicStandardAction q weights singleBlack singleBlack D (parameterSymmStd k) (affineProj k r.val)
      (U (n : D)) = proj (BalancedTensor.tmul r n : X) := by
  have hm := orderedShuffleAction_mkQ ρ E
    (parabolicShuffle_returns q weights singleBlack singleBlack D (parameterSymmStd k)) r.val (indShuffleUnit D₀ n)
  have ht : r.val • indShuffleUnit D₀ n = BalancedTensor.tmul r n := by
    unfold indShuffleUnit
    have hr : r.val • (oneConcatSubBimod : IndBimod P α δ) = r := Subtype.ext r.property
    exact (BalancedTensor.smul_tmul' _ _ _).trans (congrArg (fun v : IndBimod P α δ => BalancedTensor.tmul v n) hr)
  exact (congrArg (fun f : Module.End k V => f (U (n : D)))
    (parabolicStandardAction_affine q weights singleBlack singleBlack D (parameterSymmStd k) r.val)).trans (hm.trans (congrArg proj ht))

private theorem testModuleMap_range_unit (n : D) : U n ∈ LinearMap.range (testModuleMap k) := by
  let e := leftStandardEndEquivFixed q weights loading loading_ordered
  obtain ⟨f, hf⟩ := standardEnd_detectFactors_surjective k n
  refine ⟨(e f).val, (testModuleMap_fixed k (e f)).trans ?_⟩
  exact congrArg U ((congrArg (standardEnd_detectFactors k) (e.symm_apply_apply f)).trans hf)

/-- The actual middle standard maps onto its parabolic standardization. -/
theorem testModuleMap_surjective : Function.Surjective (testModuleMap k) := by
  intro v
  obtain ⟨x, rfl⟩ := (show Function.Surjective (proj : X →ₗ[k] V) from Submodule.mkQ_surjective _) v
  change proj x ∈ LinearMap.range (testModuleMap k)
  induction x using BalancedTensor.induction_on with
  | zero =>
    rw [map_zero]
    exact Submodule.zero_mem _
  | tmul r n =>
    obtain ⟨z,hz⟩ := testModuleMap_range_unit k (n : D)
    let a := affineProj k r.val
    refine ⟨a • z, ((testModuleMap k).map_smul a z).trans ?_⟩
    exact (congrArg (fun w : V => a • w) hz).trans (affineAct_tmul k r n)
  | add x y hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy

/-- The actual diagrammatic middle standard is its regular-input parabolic
standardization, via the cyclic diagrammatic test map. -/
def middleStandardParabolicEquiv : Standard k ≃ₗ[A] V :=
  LinearEquiv.ofBijective (testModuleMap k) ⟨testModuleMap_injective k, testModuleMap_surjective k⟩

end Categorification.Stendhal.LabelTwo
