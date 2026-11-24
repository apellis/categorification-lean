/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoMiddleFactorSpecialization
import Categorification.WeightedKLR.RedStrands.ParabolicStandardExact

/-!
# Standardization of the label-two middle specialization

Webster, arXiv:1309.3796v2, §8.2. The actual sum-of-dots differential
intertwines with standardization of the sum element on the regular
factor. Exactness of standardization identifies the diagrammatic dot-sum
quotient with the standardization of the specialized factor module.
-/

noncomputable section
set_option maxHeartbeats 2200000

namespace Categorification.Stendhal.LabelTwo

open KLR KLRAlgebra
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable (k : Type) [Field k]

local notation "oneBlack" => ({()} : Multiset Unit)
local notation "blackWeight" => oneBlack + oneBlack
local notation "q" => parameter k
local notation "α" => Multiset.map (addRedColor 1) (stendhalWeight 1 oneBlack)
local notation "lc" => Sum.map (id : Unit → Unit) (fun _ : Fin 1 => Fin.last 1)
local notation "δ" => Multiset.map lc (stendhalWeight 1 oneBlack)
local notation "P" => stendhalQ q weights
local notation "A" => TensorProductAlgebra k q weights blackWeight
local notation "D" => parabolicFactorAlgebra q weights oneBlack oneBlack
local notation "D₀" => ParabolicInput q weights oneBlack oneBlack D
local notation "V" => ParabolicStandard q weights oneBlack oneBlack D
local notation "U" => parabolicStandardUnit q weights oneBlack oneBlack D
local notation "S" => Standard k
local notation "g" => leftStandardUnit q weights loading loading_ordered

private theorem parameterSymmSpecialization : KLRSymm q :=
  fun a b h => (h (Subsingleton.elim a b)).elim

private theorem standardMap_regular_unit (f : Module.End D D) (n : D₀) :
    parabolicStandardMap q weights oneBlack oneBlack f (U n) = U (f n) := by
  let y : D₀ := f n
  change parabolicStandardMap q weights oneBlack oneBlack f
      (Submodule.Quotient.mk (indShuffleUnit (Q := P) (ν := α) (ν' := δ) D₀ n)) =
    Submodule.Quotient.mk (indShuffleUnit (Q := P) (ν := α) (ν' := δ) D₀ y)
  rw [parabolicStandardMap_mk]
  unfold parabolicShuffleMap indShuffleUnit
  simp only [BalancedTensor.mapRight_tmul]
  rfl

private def factorDotSumOnStandard : Module.End A V where
  toFun := parabolicStandardMap q weights oneBlack oneBlack (factorDotSumMap k)
  map_add' := (parabolicStandardMap q weights oneBlack oneBlack (factorDotSumMap k)).map_add
  map_smul' a z :=
    parabolicStandardMap_action q weights oneBlack oneBlack (parameterSymmSpecialization k)
      (factorDotSumMap k) a z

/-- The actual middle dot-sum map is induced from right multiplication
by the actual factor sum element. -/
theorem factorDotSumOnStandard_intertwine (z : S) :
    factorDotSumOnStandard k (testModuleMap k z) = testModuleMap k (diagramPlus k z) := by
  have hm : (factorDotSumOnStandard k).comp (testModuleMap k) =
      (testModuleMap k).comp (diagramPlus k) := by
    apply leftStandard_hom_ext loading loading_ordered
    change factorDotSumOnStandard k (testModuleMap k g) = testModuleMap k (diagramPlus k g)
    calc
      _ = factorDotSumOnStandard k (U (1 : D)) :=
        congrArg (factorDotSumOnStandard k) (testModuleMap_generator k)
      _ = U (factorDotSumMap k (1 : D)) := standardMap_regular_unit k _ (1 : D)
      _ = U (factorDotSum k) := congrArg U (one_mul _)
      _ = _ := (testModuleMap_endomorphism_on_generator k (diagramPlus k)).symm
  exact LinearMap.congr_fun hm z

/-- Standardization of the actual specialized parabolic factor. -/
abbrev SpecializedMiddleStandard :=
  ParabolicStandard q weights oneBlack oneBlack (SpecializedMiddleFactor k)

local notation "Vspec" => SpecializedMiddleStandard k

instance : Module A Vspec :=
  Module.compHom Vspec (parabolicStandardAction q weights oneBlack oneBlack
    (SpecializedMiddleFactor k) (parameterSymmSpecialization k)).toRingHom

instance : IsScalarTower k A Vspec where
  smul_assoc c a x := by
    change (parabolicStandardAction q weights oneBlack oneBlack (SpecializedMiddleFactor k)
      (parameterSymmSpecialization k)) (c • a) x =
      c • (parabolicStandardAction q weights oneBlack oneBlack (SpecializedMiddleFactor k)
        (parameterSymmSpecialization k)) a x
    rw [map_smul, LinearMap.smul_apply]

private def specializationOnParabolic : V →ₗ[A] Vspec where
  toFun := parabolicStandardMap q weights oneBlack oneBlack (factorSpecializeLinear k)
  map_add' := (parabolicStandardMap q weights oneBlack oneBlack (factorSpecializeLinear k)).map_add
  map_smul' a z :=
    parabolicStandardMap_action q weights oneBlack oneBlack (parameterSymmSpecialization k)
      (factorSpecializeLinear k) a z

/-- The actual middle standard mapped to the standardized specialization. -/
def specializationOnMiddleStandard : S →ₗ[A] Vspec :=
  (specializationOnParabolic k).comp (testModuleMap k)

private theorem specializationOnMiddleStandard_surjective :
    Function.Surjective (specializationOnMiddleStandard k) :=
  (parabolicStandardMap_surjective q weights oneBlack oneBlack (parameterSymmSpecialization k)
    (factorSpecializeLinear k) (factorSpecialize_surjective k)).comp (testModuleMap_surjective k)

private theorem factorStd_exact :
    Function.Exact (factorDotSumOnStandard k) (specializationOnParabolic k) :=
  parabolicStandardMap_exact q weights oneBlack oneBlack (parameterSymmSpecialization k)
    (factorDotSumMap k) (factorSpecializeLinear k)
    (show Function.Exact (factorDotSumMap k) (factorSpecializeLinear k)
      from factorDotSumSpecialization_exact k)

theorem dotSum_middleStandard_exact :
    Function.Exact (diagramPlus k) (specializationOnMiddleStandard k) := by
  intro z
  change specializationOnParabolic k (testModuleMap k z) = 0 ↔ _
  rw [factorStd_exact k (testModuleMap k z)]
  constructor
  · rintro ⟨w,hw⟩
    obtain ⟨x,rfl⟩ := testModuleMap_surjective k w
    exact ⟨x, testModuleMap_injective k ((factorDotSumOnStandard_intertwine k x).symm.trans hw)⟩
  · rintro ⟨x,hx⟩
    exact ⟨testModuleMap k x, (factorDotSumOnStandard_intertwine k x).trans (congrArg (testModuleMap k) hx)⟩

/-- The actual diagrammatic dot-sum quotient is the standardization of
the specialized regular parabolic factor. -/
def middleDotSumStandardizationEquiv : StandardDotSumQuotient k ≃ₗ[A] Vspec :=
  (Submodule.quotEquivOfEq _ _ (LinearMap.exact_iff.mp (dotSum_middleStandard_exact k)).symm).trans
    (LinearMap.quotKerEquivOfSurjective (specializationOnMiddleStandard k)
      (specializationOnMiddleStandard_surjective k))

/-- The quotient equivalence identifies the augmentation with induced factor specialization. -/
theorem middleDotSumStandardizationEquiv_mk (x : S) :
    middleDotSumStandardizationEquiv k
      ((LinearMap.range (diagramPlus k)).mkQ x) = specializationOnMiddleStandard k x := by
  simp only [middleDotSumStandardizationEquiv, LinearEquiv.trans_apply, Submodule.mkQ_apply,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]

end Categorification.Stendhal.LabelTwo
