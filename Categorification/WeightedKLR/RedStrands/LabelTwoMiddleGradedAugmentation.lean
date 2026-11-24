/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoMiddleDotDegree
import Categorification.Algebra.Graded.ProjectiveCover
import Categorification.Algebra.Graded.Dimension

/-!
# Degreewise exactness of the label-two diagrammatic middle complex

Webster, arXiv:1309.3796v2, §8.2. Restrict the exact alternating dot
maps to their shifted homogeneous pieces. The actual dot-sum quotient
inherits its quotient grading, and the augmentation is exact and
surjective in each internal degree.
-/

noncomputable section
set_option maxHeartbeats 1600000

namespace Categorification.Stendhal.LabelTwo

open KLR KLRAlgebra Categorification.Graded DirectSum
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable (k : Type) [Field k]

local notation "ν" => (({()} : Multiset Unit) + {()})
local notation "A" => TensorProductAlgebra k (parameter k) weights ν
local notation "S" => Standard k
local notation "G" => labelTwoGradingDatum k
local notation "ℳ" => middleStandardGrade k (G)
local notation "𝒮" => middleStandardGFin k (G)

/-- Restriction of a degree-two map to the source and target degrees. -/
def restrictDegreeTwo (f : Module.End A S) (hf : f ∈ homGrade A ℳ ℳ 2) (d : ℤ) :
    ℳ d →ₗ[k] ℳ (d + 2) :=
  (f.restrictScalars k).restrict fun _ hz => hf hz

/-- Exactness of degree-two maps restricts to each pair of shifted graded pieces. -/
theorem restrictDegreeTwo_exact (f g : Module.End A S)
    (hf : f ∈ homGrade A ℳ ℳ 2) (hg : g ∈ homGrade A ℳ ℳ 2)
    (hfg : Function.Exact f g) (d : ℤ) :
    Function.Exact (restrictDegreeTwo k f hf d) (restrictDegreeTwo k g hg (d + 2)) := by
  let N : ℤ → Submodule k S := fun i => ℳ (i + 2)
  let P : ℤ → Submodule k S := fun i => ℳ ((i + 2) + 2)
  let : Decomposition ℳ := (𝒮).decomposition
  have hN : Graded.shift ℳ (-2) = N := by
    funext i
    change ℳ (i - (-2)) = ℳ (i + 2)
    rw [sub_neg_eq_add]
  let : Decomposition N := hN ▸ inferInstanceAs (Decomposition (Graded.shift ℳ (-2)))
  have hf₀ : PreservesGrading ℳ N (f.restrictScalars k) := fun _ _ hx => hf hx
  have hg₀ : PreservesGrading N P (g.restrictScalars k) := fun _ _ hx => hg hx
  exact Graded.exact_restrict hf₀ hg₀ (show Function.Exact (f.restrictScalars k) (g.restrictScalars k) from hfg) d


/-- The diagrammatic sum differential between two homogeneous pieces. -/
def diagramPlusAtDegree (d : ℤ) := restrictDegreeTwo k (diagramPlus k) (diagramPlus_degree_two k) d

/-- The diagrammatic difference differential between two homogeneous pieces. -/
def diagramMinusAtDegree (d : ℤ) := restrictDegreeTwo k (diagramMinus k) (diagramMinus_degree_two k) d

/-- The sum followed by the difference is exact on shifted homogeneous pieces. -/
theorem diagramPlusMinus_exact_in_degree (d : ℤ) :
    Function.Exact (diagramPlusAtDegree k d) (diagramMinusAtDegree k (d + 2)) :=
  restrictDegreeTwo_exact k _ _ (diagramPlus_degree_two k) (diagramMinus_degree_two k)
    (diagramPlusMinus_exact k) d

/-- The difference followed by the sum is exact on shifted homogeneous pieces. -/
theorem diagramMinusPlus_exact_in_degree (d : ℤ) :
    Function.Exact (diagramMinusAtDegree k d) (diagramPlusAtDegree k (d + 2)) :=
  restrictDegreeTwo_exact k _ _ (diagramMinus_degree_two k) (diagramPlus_degree_two k)
    (diagramMinusPlus_exact k) d

local notation "𝒜" => middleTensorGrade k (G)
local notation "U" => LinearMap.range (diagramPlus k)
local notation "Q" => StandardDotSumQuotient k

local instance middleStandardDecomposition : Decomposition ℳ :=
  (𝒮).decomposition

private theorem dotSumRange_homogeneous :
    (U).IsHomogeneous ℳ := by
  let N := Graded.shift ℳ (-2)
  let f : S →ₗ[k] S := (diagramPlus k).restrictScalars k
  have hf : PreservesGrading ℳ N f := by
    intro d x hx
    change diagramPlus k x ∈ ℳ (d - (-2))
    rw [sub_neg_eq_add]
    exact diagramPlus_degree_two k hx
  intro d z hz
  obtain ⟨x,rfl⟩ := hz
  have h₀ : (decompose N (f x) (d + (-2))).val = f (decompose ℳ x (d + (-2))).val :=
    decompose_map hf x (d + (-2))
  have h₁ : (decompose N (f x) (d + (-2))).val = (decompose ℳ (f x) d).val :=
    decompose_shift ℳ (-2) (f x) d
  exact ⟨(decompose ℳ x (d + (-2))).val, h₀.symm.trans h₁⟩

/-- The actual dot-sum quotient has the quotient grading of the middle standard. -/
def middleDotSumQuotientGrade : ℤ → Submodule k Q :=
  quotGradingA ℳ U

local notation "𝒬" => middleDotSumQuotientGrade k

/-- The actual dot-sum quotient as a graded finite-dimensional tensor module. -/
def middleDotSumQuotientGFin : GFin 𝒜 := by
  let : Decomposition ℳ := (𝒮).decomposition
  let : Decomposition 𝒬 := quotDecompositionA ℳ U (dotSumRange_homogeneous k)
  let : SetLike.GradedSMul 𝒜 ℳ := (𝒮).gradedSMul
  let : SetLike.GradedSMul 𝒜 𝒬 := inferInstanceAs (SetLike.GradedSMul 𝒜 (quotGradingA ℳ U))
  let : FiniteDimensional k S := (𝒮).finiteDimensional
  have hQ : FiniteDimensional k Q :=
    Module.Finite.of_surjective ((U).mkQ.restrictScalars k) (U).mkQ_surjective
  exact { toGMod := GMod.of Q 𝒬, finiteDimensional := hQ }

private theorem quotientMap_preservesGrading :
    PreservesGrading ℳ 𝒬 ((U).mkQ.restrictScalars k) :=
  fun _ _ hx => preservesGrading_mkQ ℳ U hx

/-- The actual degree-zero augmentation on an internal homogeneous piece. -/
def diagramMiddleAugmentationAtDegree (d : ℤ) : ℳ d →ₗ[k] 𝒬 d :=
  ((U).mkQ.restrictScalars k).restrict fun _ hx => quotientMap_preservesGrading k hx

/-- Every homogeneous quotient vector has a lift of the same degree. -/
theorem diagramMiddleAugmentationAtDegree_surjective (d : ℤ) :
    Function.Surjective (diagramMiddleAugmentationAtDegree k d) := by
  intro y
  obtain ⟨x,hx,hy⟩ := y.property
  exact ⟨⟨x,hx⟩, Subtype.ext hy⟩

/-- The shifted sum differential is the kernel of the augmentation in every degree. -/
theorem diagramPlusAugmentation_exact_in_degree (d : ℤ) :
    Function.Exact (diagramPlusAtDegree k d) (diagramMiddleAugmentationAtDegree k (d + 2)) := by
  let N : ℤ → Submodule k S := fun i => ℳ (i + 2)
  let P : ℤ → Submodule k Q := fun i => 𝒬 (i + 2)
  let : Decomposition ℳ := (𝒮).decomposition
  have hN : Graded.shift ℳ (-2) = N := by
    funext i
    change ℳ (i - (-2)) = ℳ (i + 2)
    rw [sub_neg_eq_add]
  let : Decomposition N := hN ▸ inferInstanceAs (Decomposition (Graded.shift ℳ (-2)))
  have hf : PreservesGrading ℳ N ((diagramPlus k).restrictScalars k) :=
    fun _ _ hx => diagramPlus_degree_two k hx
  have hg : PreservesGrading N P ((U).mkQ.restrictScalars k) :=
    fun _ _ hx => quotientMap_preservesGrading k hx
  exact Graded.exact_restrict hf hg (diagramMiddleAugmentation_exact k) d

end Categorification.Stendhal.LabelTwo
