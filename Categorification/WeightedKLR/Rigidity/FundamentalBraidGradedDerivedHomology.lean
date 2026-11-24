/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DiagramWeightLocalizedCohomology
import Categorification.WeightedKLR.Rigidity.FundamentalBraidGradedResolutionModel
import Categorification.WeightedKLR.Rigidity.FundamentalBraidGradedTensorHomology
import Categorification.WeightedKLR.Rigidity.WeightTwoStageCohomology

/-!
# The weights and cohomological degrees of the derived fundamental braid

In the fundamental type A₁ case of Webster, arXiv:1309.3796v2, §7.1,
Proposition 7.11, tensor the two-stage loading resolution by the graded
braid and evaluate at each target weight. Only cohomological degree
minus one and physical weight three halves survive.
-/

noncomputable section

namespace Categorification.Stendhal.FundamentalCorner
open DG CategoryTheory BraidedStendhalAlgebra CatModule
open scoped DG.DegreeZero
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance] fundamentalBraidCoendSourceCornerGrades fundamentalBraidCoendTargetCornerGrades
  fundamentalBraidCoendSourceInternal fundamentalBraidCoendTargetInternal
  fundamentalBraidCoendSourceBigraded fundamentalBraidCoendTargetBigraded

local notation "ν" => ({()} : Multiset Unit)
local notation "κ₀" => List.finRange 2
local notation "κ₁" => ([1,0] : List (Fin 2))
local notation "K" => ViolOrderCorner (k := ℚ) (Q := Q) (Λ := wt) («ν» := ν) κ₀
local notation "U" => ViolOrderCorner (k := ℚ) (Q := Q) (Λ := wt) («ν» := ν) κ₁
local notation "V" => violAuxiliaryGrade («ν» := ν) grading
local notation "he" => isIdempotentElem_violMk_redProj ℚ Q wt ν
local notation "h₀" => redProj_mem_violAuxiliaryGrade grading
local notation "DF" => diagramCornerWeightDerivedRightTensor V (he κ₀) (he κ₁) (h₀ κ₀) (h₀ κ₁)
local notation "D" => diagramCornerWeightRightBimodule V (he κ₀) (he κ₁) (h₀ κ₀) (h₀ κ₁)
local notation "f" => fundamentalBraidGradedSourceD₂
local notation "g" => fundamentalBraidGradedSourceD₁
local notation "f'" => CatBimodule.tensorMap D f
local notation "g'" => CatBimodule.tensorMap D g

private theorem tensorSource_comp_zero : f' ≫ g' = 0 := by
  unfold diagramCornerWeightRightBimodule
  exact diagramWeightTensor_comp_zero _ _ _ f g fundamentalBraidGradedSource_comp_zero

/-- The graded tensor crossing complex as a short complex of modules over the reversed weight category. -/
def fundamentalBraidTensorWeightModules : ShortComplex (CatModule.{0} (WeightCategory Uᵐᵒᵖ)) :=
  ShortComplex.mk f' g' tensorSource_comp_zero

/-- The tensor of the source resolution is the two-stage model of the actual tensor maps. -/
private def tensorModelIso :
    (D).tensorFunctor.obj fundamentalBraidGradedResolutionModel ≅
      cone (coneDescent f' g' tensorSource_comp_zero) := by
  unfold diagramCornerWeightRightBimodule fundamentalBraidGradedResolutionModel
  exact diagramWeightTensorTwoStageIso _ _ _ f g fundamentalBraidGradedSource_comp_zero

local notation "Z" n:arg => (WeightCategory.mk n : WeightCategory Uᵐᵒᵖ)
private theorem grading_of_equiv_degreeZero {X Y : Type*} [AddCommGroup X] [DGAddCommGroup X]
    [AddCommGroup Y] (e : DGAddEquiv X (Categorification.InDegreeZero Y)) (i : ℤ) (y : X) :
    y ∈ DG.grading i ↔ i = 0 ∨ y = 0 := by
  constructor
  · intro h
    rcases (Categorification.InDegreeZero.mem_grading_iff (M := Y)).mp (e.map_mem h) with h | h
    · exact Or.inl h
    · exact Or.inr (e.toAddEquiv.injective (h.trans (map_zero e.toAddEquiv).symm))
  · intro h
    have hy : e y ∈ DG.grading i := (Categorification.InDegreeZero.mem_grading_iff (M := Y)).mpr
      (h.imp_right (fun h : y = 0 => (congrArg e h).trans (map_zero e.toAddEquiv)))
    exact e.toAddEquiv.symm_apply_apply y ▸ e.symm.map_mem hy

private theorem coend_mem_degree (s : KLR.Seq (stendhalWeight 2 ν)) (hs : IsRedOrdered s)
    (j n i : ℤ) (y : ((D).tensorFunctor.obj (corner (fundamentalBraidSourceLoadingAt s hs j))).obj (Z n)) :
    y ∈ DG.grading i ↔ i = 0 ∨ y = 0 :=
  grading_of_equiv_degreeZero (fundamentalBraidGradedCutDGEquiv s hs j (Z n)) i y

private theorem midOrd' : IsRedOrdered middle := by unfold IsRedOrdered; decide +kernel
local notation "d₂" => coend_mem_degree middle midOrd' 2
local notation "d₁" => coend_mem_degree terminal terminal_ordered 1
local notation "d₀" => coend_mem_degree middle midOrd' 0
local notation "M" => cone (coneDescent f' g' tensorSource_comp_zero)

/-- The cohomology of the tensor model in degree minus one at weight `n`
is the middle homology of the two tensor crossing maps. -/
def fundamentalBraidGradedModelHomologyIso (n : ℤ) :
    AddCommGrpCat.of (cohomology ((M).obj (Z n)) (-1)) ≅
      (forget₂ (ModuleCat ℤ) AddCommGrpCat).obj (fundamentalBraidGradedTensorComplex n).homology :=
  (twoStageMiddleCohomologyEquiv f' g' tensorSource_comp_zero (Z n) (d₂ n) (d₁ n) (d₀ n)).toAddCommGrpIso

private theorem model_cohomology_zero (n i : ℤ) (hi : i ≠ -1) :
    Limits.IsZero (AddCommGrpCat.of (cohomology ((M).obj (Z n)) i)) := by
  have hu : Function.Injective ((f').app (Z n)) := (fundamentalBraidGradedTensorComplex_ends n).1
  have hv : Function.Surjective ((g').app (Z n)) := (fundamentalBraidGradedTensorComplex_ends n).2
  exact AddCommGrpCat.isZero_of_iff_subsingleton.mpr (subsingleton_of_forall_eq 0
    (twoStageCohomology_eq_zero_of_ne_middle f' g' tensorSource_comp_zero (Z n)
      (d₂ n) (d₁ n) (d₀ n) hu hv i hi))

universe z
variable [CatModule.HasDerivedCategory.{z,0} (WeightCategory Kᵐᵒᵖ)]
  [CatModule.HasDerivedCategory.{z,0} (WeightCategory Uᵐᵒᵖ)]
local notation "br" => CategoryTheory.Functor.obj DF (CatModule.DerivedCategory.Q.obj fundamentalBraidSourceGradedHead)

/-- The localized derived braid is represented by the two successive tensor crossing maps. -/
def fundamentalBraidGradedDerivedConeIso :
    br ≅ CatModule.DerivedCategory.Q.obj (cone (coneDescent fundamentalBraidTensorWeightModules.f
      fundamentalBraidTensorWeightModules.g fundamentalBraidTensorWeightModules.zero)) :=
  fundamentalBraidGradedDerivedModelIso ≪≫ CatModule.DerivedCategory.Q.mapIso tensorModelIso

private def derivedTensorCohomology (n i : ℤ) :
    (CatModule.DerivedCategory.cohomologyFunctor (Z n) i).obj br ≅ AddCommGrpCat.of (cohomology ((M).obj (Z n)) i) :=
  (CatModule.DerivedCategory.cohomologyFunctor (Z n) i).mapIso fundamentalBraidGradedDerivedConeIso ≪≫ localizedWeightCohomologyIso (Z n) i M

/-- The fundamental graded derived braid on the middle simple has a rational
line in cohomological degree minus one and auxiliary weight zero, the physical
weight three halves in Webster v2, §7.1, Proposition 7.11. -/
def fundamentalBraidGradedDerivedHomologyIso :
    (CatModule.DerivedCategory.cohomologyFunctor (Z 0) (-1)).obj br ≅ AddCommGrpCat.of ℚ :=
  derivedTensorCohomology 0 (-1) ≪≫ fundamentalBraidGradedModelHomologyIso 0 ≪≫
    (forget₂ (ModuleCat ℤ) AddCommGrpCat).mapIso fundamentalBraidGradedTensorHomologyIso

/-- Every other pair of cohomological degree and auxiliary weight of the
derived fundamental braid vanishes (Webster v2, Proposition 7.11). -/
theorem fundamentalBraidGradedDerivedCohomology_isZero (n i : ℤ) (h : i ≠ -1 ∨ n ≠ 0) :
    Limits.IsZero ((CatModule.DerivedCategory.cohomologyFunctor (Z n) i).obj br) := by
  by_cases hi : i = -1
  · subst i
    have hn := h.resolve_left (not_not.mpr rfl)
    let e := derivedTensorCohomology n (-1) ≪≫ fundamentalBraidGradedModelHomologyIso n
    exact Limits.IsZero.of_iso ((forget₂ (ModuleCat ℤ) AddCommGrpCat).map_isZero
      ((fundamentalBraidGradedTensorComplex n).exact_iff_isZero_homology.mp (fundamentalBraidGradedTensorComplex_exact n hn))) e
  · exact (model_cohomology_zero n i hi).of_iso (derivedTensorCohomology n i)
end Categorification.Stendhal.FundamentalCorner
