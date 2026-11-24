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

private theorem middleDegreeTwoRange_homogeneous (f₀ : Module.End A S)
    (hf₀ : f₀ ∈ homGrade A ℳ ℳ 2) :
    (LinearMap.range f₀).IsHomogeneous ℳ := by
  let N := Graded.shift ℳ (-2)
  let f : S →ₗ[k] S := f₀.restrictScalars k
  have hf : PreservesGrading ℳ N f := by
    intro d x hx
    change f₀ x ∈ ℳ (d - (-2))
    rw [sub_neg_eq_add]
    exact hf₀ hx
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
  let : Decomposition 𝒬 := quotDecompositionA ℳ U (middleDegreeTwoRange_homogeneous k (diagramPlus k) (diagramPlus_degree_two k))
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


local notation "V" => LinearMap.range (diagramMinus k)
local notation "R" => S ⧸ V

/-- The actual difference quotient has the quotient grading of the middle standard. -/
def middleDotDifferenceQuotientGrade : ℤ → Submodule k R :=
  quotGradingA ℳ V

local notation "ℛ" => middleDotDifferenceQuotientGrade k

/-- The actual difference quotient as a graded finite-dimensional tensor module. -/
def middleDotDifferenceQuotientGFin : GFin 𝒜 := by
  let : Decomposition ℳ := (𝒮).decomposition
  let : Decomposition ℛ := quotDecompositionA ℳ V
    (middleDegreeTwoRange_homogeneous k (diagramMinus k) (diagramMinus_degree_two k))
  let : SetLike.GradedSMul 𝒜 ℳ := (𝒮).gradedSMul
  let : SetLike.GradedSMul 𝒜 ℛ := inferInstanceAs (SetLike.GradedSMul 𝒜 (quotGradingA ℳ V))
  let : FiniteDimensional k S := (𝒮).finiteDimensional
  have hR : FiniteDimensional k R :=
    Module.Finite.of_surjective ((V).mkQ.restrictScalars k) (V).mkQ_surjective
  exact { toGMod := GMod.of R ℛ, finiteDimensional := hR }

private theorem differenceQuotientMap_preservesGrading :
    PreservesGrading ℳ ℛ ((V).mkQ.restrictScalars k) :=
  fun _ _ hx => preservesGrading_mkQ ℳ V hx

/-- The augmentation to the difference quotient in each internal degree. -/
def diagramDifferenceAugmentationAtDegree (d : ℤ) : ℳ d →ₗ[k] ℛ d :=
  ((V).mkQ.restrictScalars k).restrict fun _ hx => differenceQuotientMap_preservesGrading k hx

/-- Each homogeneous difference class has a lift of the same degree. -/
theorem diagramDifferenceAugmentationAtDegree_surjective (d : ℤ) :
    Function.Surjective (diagramDifferenceAugmentationAtDegree k d) := by
  intro y
  obtain ⟨x, hx, hy⟩ := y.property
  exact ⟨⟨x, hx⟩, Subtype.ext hy⟩

/-- The difference map is the kernel of the companion augmentation in each degree. -/
theorem diagramMinusDifferenceAugmentation_exact_in_degree (d : ℤ) :
    Function.Exact (diagramMinusAtDegree k d) (diagramDifferenceAugmentationAtDegree k (d + 2)) := by
  let N : ℤ → Submodule k S := fun i => ℳ (i + 2)
  let P : ℤ → Submodule k R := fun i => ℛ (i + 2)
  let : Decomposition ℳ := (𝒮).decomposition
  have hN : Graded.shift ℳ (-2) = N := by
    funext i
    change ℳ (i - (-2)) = ℳ (i + 2)
    rw [sub_neg_eq_add]
  let : Decomposition N := hN ▸ inferInstanceAs (Decomposition (Graded.shift ℳ (-2)))
  have hf : PreservesGrading ℳ N ((diagramMinus k).restrictScalars k) :=
    fun _ _ hx => diagramMinus_degree_two k hx
  have hg : PreservesGrading N P ((V).mkQ.restrictScalars k) :=
    fun _ _ hx => differenceQuotientMap_preservesGrading k hx
  exact Graded.exact_restrict hf hg (fun x => Submodule.Quotient.mk_eq_zero (V)) d


private def companionInclusion (f g : Module.End A S) (hex : Function.Exact f g) :
    (S ⧸ LinearMap.range f) →ₗ[A] S :=
  (LinearMap.range f).liftQ g
    (fun x hx => LinearMap.mem_ker.mpr ((hex x).mpr hx))

private theorem companionInclusion_injective (f g : Module.End A S) (hex : Function.Exact f g) :
    Function.Injective (companionInclusion k f g hex) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z
  obtain ⟨x, rfl⟩ := (LinearMap.range f).mkQ_surjective z
  intro hx
  exact (Submodule.Quotient.mk_eq_zero (LinearMap.range f)).mpr ((hex x).mp hx)

private def restrictCompanion (f g : Module.End A S) (hex : Function.Exact f g)
    (hg : g ∈ homGrade A ℳ ℳ 2) (d : ℤ) :
    quotGradingA ℳ (LinearMap.range f) d →ₗ[k] ℳ (d + 2) :=
  ((companionInclusion k f g hex).restrictScalars k).restrict fun _ hy => by
    obtain ⟨x, hx, rfl⟩ := hy
    exact hg hx

private theorem restrictCompanion_injective (f g : Module.End A S) (hex : Function.Exact f g)
    (hg : g ∈ homGrade A ℳ ℳ 2) (d : ℤ) :
    Function.Injective (restrictCompanion k f g hex hg d) := by
  intro x y h
  exact Subtype.ext (companionInclusion_injective k f g hex (congrArg Subtype.val h))

/-- The difference quotient maps into the standard by the sum map of degree two. -/
def diagramSumCompanionInclusionAtDegree (d : ℤ) : ℛ d →ₗ[k] ℳ (d + 2) :=
  restrictCompanion k (diagramMinus k) (diagramPlus k) (diagramMinusPlus_exact k)
    (diagramPlus_degree_two k) d

/-- The sum quotient maps into the standard by the difference map of degree two. -/
def diagramDifferenceCompanionInclusionAtDegree (d : ℤ) : 𝒬 d →ₗ[k] ℳ (d + 2) :=
  restrictCompanion k (diagramPlus k) (diagramMinus k) (diagramPlusMinus_exact k)
    (diagramMinus_degree_two k) d

/-- The shifted sum companion map is injective. -/
theorem diagramSumCompanionInclusionAtDegree_injective (d : ℤ) :
    Function.Injective (diagramSumCompanionInclusionAtDegree k d) :=
  restrictCompanion_injective k _ _ _ _ d

/-- The shifted difference companion map is injective. -/
theorem diagramDifferenceCompanionInclusionAtDegree_injective (d : ℤ) :
    Function.Injective (diagramDifferenceCompanionInclusionAtDegree k d) :=
  restrictCompanion_injective k _ _ _ _ d

/-- The shifted difference quotient and the sum augmentation form an exact pair. -/
theorem diagramSumCompanionAugmentation_exact_in_degree (d : ℤ) :
    Function.Exact (diagramSumCompanionInclusionAtDegree k d)
      (diagramMiddleAugmentationAtDegree k (d + 2)) := by
  intro y
  rw [diagramPlusAugmentation_exact_in_degree k d y]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨diagramDifferenceAugmentationAtDegree k d x, rfl⟩
  · rintro ⟨z, rfl⟩
    obtain ⟨x, rfl⟩ := diagramDifferenceAugmentationAtDegree_surjective k d z
    exact ⟨x, rfl⟩

/-- The shifted sum quotient and the difference augmentation form an exact pair. -/
theorem diagramDifferenceCompanionAugmentation_exact_in_degree (d : ℤ) :
    Function.Exact (diagramDifferenceCompanionInclusionAtDegree k d)
      (diagramDifferenceAugmentationAtDegree k (d + 2)) := by
  intro y
  rw [diagramMinusDifferenceAugmentation_exact_in_degree k d y]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨diagramMiddleAugmentationAtDegree k d x, rfl⟩
  · rintro ⟨z, rfl⟩
    obtain ⟨x, rfl⟩ := diagramMiddleAugmentationAtDegree_surjective k d z
    exact ⟨x, rfl⟩

end Categorification.Stendhal.LabelTwo
