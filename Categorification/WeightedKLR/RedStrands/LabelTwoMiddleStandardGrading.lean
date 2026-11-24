/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoMiddleStandardEquiv
import Categorification.WeightedKLR.RedStrands.ParabolicStandardGrading
import Categorification.WeightedKLR.RedStrands.ParabolicInputGrading

/-!
# Grading of the actual label-two middle standard

For Webster, arXiv:1309.3796v2, §8.2, pull the parabolic grading of the
regular separated factor back to the diagrammatic middle standard.
The comparison is a degree-preserving equivalence with the standardization.
-/

noncomputable section

set_option maxHeartbeats 1600000

namespace Categorification.Stendhal.LabelTwo

open KLR KLRAlgebra Categorification.Graded DirectSum
open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable (k : Type) [Field k]

local notation "oneBlack" => ({()} : Multiset Unit)
local notation "q" => parameter k
local notation "Alg" => TensorProductAlgebra k q weights (oneBlack + oneBlack)
local notation "D" => parabolicFactorAlgebra q weights oneBlack oneBlack
local notation "V" => ParabolicStandard q weights oneBlack oneBlack D
local notation "X" => ParabolicShuffle q weights oneBlack oneBlack D
local notation "D₀" => ParabolicInput q weights oneBlack oneBlack D
local notation "α" => Multiset.map (addRedColor 1) (stendhalWeight 1 oneBlack)
local notation "lc" => Sum.map (id : Unit → Unit) (fun _ : Fin 1 => Fin.last 1)
local notation "δ" => Multiset.map lc (stendhalWeight 1 oneBlack)

private theorem parameterSymmGrade : KLRSymm q :=
  fun a b h => (h (Subsingleton.elim a b)).elim

/-- The usual type A₁ degrees with label-two red strands. -/
def labelTwoGradingDatum : GradingDatum (stendhalQ q weights) :=
  stendhalGradingDatum weights {
    degX := fun _ => 2
    degΨ := fun _ _ => -2
    degΨ_self := by intro; norm_num
    isWeightedHomogeneous := fun a b h => (h (Subsingleton.elim a b)).elim }
    (fun _ => 1) (by intro; norm_num)

variable (datum : KLR.GradingDatum (stendhalQ (parameter k) weights))

/-- The ambient tensor-product grading in the label-two calculation. -/
abbrev middleTensorGrade : ℤ → Submodule k Alg :=
  tensorProductGrade (Q := q) (Λ := weights) datum (oneBlack + oneBlack)

private abbrev middleFactorGrade : ℤ → Submodule k D :=
  tensorGrading (k := k) (tensorProductGrade (Q := q) (Λ := weights ∘ Fin.castSucc)
    (restrictRedGrading q weights datum) oneBlack)
    (CycKLR.grade (restrictBlackGrading q weights datum) (weights (Fin.last 1)) oneBlack)

private def middleRegularFactorsGFin : GFin (k := k) (A := D) (middleFactorGrade k datum) := by
  have hf : Module.Finite k (MvPolynomial (Fin 2) k ⧸ middleDotIdeal k) :=
    Webster.LabelTwo.squareQuotient_finite k
  have : Module.Finite k (Module.End Alg (Standard k)) :=
    Module.Finite.of_surjective (middleDotQuotientAction k).toLinearMap
      (middleDotQuotientAction_surjective k)
  have hD : Module.Finite k D :=
    Module.Finite.of_surjective (standardEnd_detectFactors k) (standardEnd_detectFactors_surjective k)
  exact { toGMod := GMod.regular (k := k) (A := D) (middleFactorGrade k datum), finiteDimensional := hD }

/-- The parabolic grading used to grade the actual middle standard. -/
def middleParabolicGFin : GFin (k := k) (A := Alg) (middleTensorGrade k datum) := by
  let N := parabolicInputGFin (P := q) (K := k) weights datum oneBlack oneBlack (middleRegularFactorsGFin k datum)
  let Ngr : ℤ → Submodule k D₀ := N.grading
  let : Decomposition Ngr := N.decomposition
  let : SetLike.GradedSMul (tensorGrading (datum.grade α) (datum.grade δ)) Ngr := N.gradedSMul
  let : FiniteDimensional k D₀ := N.finiteDimensional
  let M : ℤ → Submodule k X := datum.indGrading α δ Ngr
  let : Decomposition M := balancedDecomposition (tensorGrading (datum.grade α) (datum.grade δ))
    (fun _ _ _ _ hm ht => datum.op_smul_mem_bimodGrading hm ht)
  let : SetLike.GradedSMul (datum.grade (α + δ)) M := gradedSMul_balanced (datum.grade (α + δ))
  let : FiniteDimensional k X :=
    finiteDimensional_ind (stendhalQ_swap_symm q weights (parameterSymmGrade k)) D₀
  exact parabolicStandardGFin weights datum oneBlack oneBlack D (parameterSymmGrade k) M

private abbrev middleStandardTestLinear : Standard k →ₗ[k] V :=
  (testModuleMap k).restrictScalars k

local notation "lmap" => middleStandardTestLinear k

/-- Pull back the natural parabolic grading along the diagrammatic map. -/
def middleStandardGrade : ℤ → Submodule k (Standard k) :=
  Graded.comap (middleParabolicGFin k datum).grading lmap

/-- The actual diagrammatic middle standard as a finite graded module. -/
def middleStandardGFin : GFin (k := k) (A := Alg) (middleTensorGrade k datum) := by
  let M₀ : ℤ → Submodule k V := (middleParabolicGFin k datum).grading
  let M : ℤ → Submodule k (Standard k) := Graded.comap M₀ lmap
  let : Decomposition M₀ := (middleParabolicGFin k datum).decomposition
  have hr (x : Standard k) (d : ℤ) :
      (decompose M₀ (lmap x) d).val ∈ LinearMap.range lmap := by
    obtain ⟨a, ha⟩ := testModuleMap_surjective k (decompose M₀ (lmap x) d).val
    exact ⟨a, ha⟩
  let : Decomposition M := (Graded.isInternal_comap M₀ lmap (testModuleMap_injective k) hr).chooseDecomposition
  let : SetLike.GradedSMul (middleTensorGrade k datum) M := ⟨fun (i j : ℤ) (a : Alg) (b : Standard k) ha hb => by
    change lmap (a • b) ∈ (middleParabolicGFin k datum).grading (i + j)
    have h := (testModuleMap k).map_smul a b
    change lmap (a • b) = a • lmap b at h
    rw [h]
    exact (middleParabolicGFin k datum).gradedSMul.smul_mem ha hb⟩
  have : Module.Finite k V := (middleParabolicGFin k datum).finiteDimensional
  exact { toGMod := GMod.of (Standard k) M
          finiteDimensional := Module.Finite.of_surjective
            ((middleStandardParabolicEquiv k).symm.toLinearMap.restrictScalars k)
              (middleStandardParabolicEquiv k).symm.surjective }

/-- The actual graded standard is identified with the parabolic
standardization of its regular separated factor. -/
def middleStandardGradedEquiv :
    (middleStandardGFin k datum).Iso (middleParabolicGFin k datum) where
  toLinearEquiv := middleStandardParabolicEquiv k
  map_mem' _ _ hx := hx
  symm_map_mem' d y hy := by
    let e := middleStandardParabolicEquiv k
    let y₀ : V := y
    have h : e (e.symm y₀) = y₀ := e.apply_symm_apply y₀
    exact (congrArg (fun z : V => z ∈ (middleParabolicGFin k datum).grading d) h).mpr hy

/-- Forgetting the grading gives the original diagrammatic parabolic map. -/
theorem middleStandardGradedEquiv_toLinearEquiv :
    (middleStandardGradedEquiv k datum).toLinearEquiv = middleStandardParabolicEquiv k := rfl

end Categorification.Stendhal.LabelTwo
