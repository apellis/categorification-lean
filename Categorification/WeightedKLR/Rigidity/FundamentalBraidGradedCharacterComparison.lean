/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.GradedBraidCutInclusion
import Categorification.WeightedKLR.Rigidity.FundamentalBraidGradedHomologyModule
import Categorification.WeightedKLR.Rigidity.FundamentalBraidGradedTargetHead

/-!
# Right action on the homology of the fundamental graded braid

The homogeneous cut complex includes into the ordinary right-module
complex. Since an ungraded boundary has a preimage at the required
weight, the middle homology injects into the known middle target head.
This computes its action in Webster, arXiv:1309.3796v2, §7.2,
Proposition 7.11.
-/
noncomputable section
namespace Categorification.Stendhal.FundamentalCorner
open BraidedStendhalAlgebra DG CategoryTheory CatModule DGOpposite QuantumGroup
open scoped DG.DegreeZero
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

local notation "ν" => ({()} : Multiset Unit)
local notation "κ₀" => List.finRange 2
local notation "κ₁" => ([1,0] : List (Fin 2))
local notation "μ" => stendhalWeight 2 ν
local notation "K" => ViolOrderCorner (k := ℚ) (Q := Q) (Λ := wt) («ν» := ν) κ₀
local notation "U" => ViolOrderCorner (k := ℚ) (Q := Q) (Λ := wt) («ν» := ν) κ₁
local notation "V" => violAuxiliaryGrade («ν» := ν) grading
local notation "hE" => isIdempotentElem_violMk_redProj ℚ Q wt ν
attribute [local instance] fundamentalBraidCoendSourceCornerGrades fundamentalBraidCoendTargetCornerGrades
  fundamentalBraidCoendSourceInternal fundamentalBraidCoendTargetInternal
  fundamentalBraidCoendSourceBigraded fundamentalBraidCoendTargetBigraded
local notation "C" => CartanDatum.ofGraph (⊥ : SimpleGraph Unit)
local notation "cut" s:arg => violCornerAuxiliaryGrade (Λ := wt) C fundamentalBraidParameters s κ₁
local notation "B" => diagramCornerWeightRightBimodule V (hE κ₀) (hE κ₁)
  (redProj_mem_violAuxiliaryGrade grading κ₀) (redProj_mem_violAuxiliaryGrade grading κ₁)

variable (s : KLR.Seq μ) (hs : IsRedOrdered s) (j : ℤ)
local notation "p" => fundamentalBraidSourceLoadingAt s hs j

local notation "Cut" s:arg => violCorner ℚ Q wt ν s κ₁
local notation "E" => ordinaryModuleAtEveryWeight Uᵐᵒᵖ
local notation "Td" => CatBimodule.tensorObj B (corner p)

private def includeCutAt (W : WeightCategory Uᵐᵒᵖ) : (Td).obj W →+ Cut s :=
  ((cut s) (W.as-j)).subtype.toAddMonoidHom.comp (fundamentalBraidGradedCutIso s hs j W).toAddMonoidHom

/-- Include a homogeneous tensor cut into the ordinary module at each target weight. -/
def fundamentalBraidWeightCutInclusion :
    Td ⟶ (E).obj (ModuleCat.of Uᵐᵒᵖ (Cut s)) where
  app W := includeCutAt s hs j W
  map_mem' {W i y} hy := by
    let e := fundamentalBraidGradedCutDGEquiv s hs j W
    have h := (InDegreeZero.mem_grading_iff (M := (cut s) (W.as-j))).mp (e.map_mem hy)
    apply (InDegreeZero.mem_grading_iff (M := Cut s)).mpr
    exact h.imp_right (fun hh => congrArg Subtype.val hh)
  map_d' {W} y := by
    let e := fundamentalBraidGradedCutDGEquiv s hs j W
    have hh : e (d y) = 0 := (e.map_d y).trans (InDegreeZero.d_apply _ _)
    exact congrArg Subtype.val hh
  map_smul' {W W'} a y := Subtype.ext (fundamentalBraidGradedCutIso_lact s hs j W a y)
private theorem orderedM : IsRedOrdered middle := by unfold IsRedOrdered; decide +kernel
local notation "f₂" => fundamentalBraidGradedSourceD₂
local notation "f₁" => fundamentalBraidGradedSourceD₁
local notation "f₂'" => CatBimodule.tensorMap B f₂
local notation "f₁'" => CatBimodule.tensorMap B f₁

private theorem injected_f : f₂' ≫ fundamentalBraidWeightCutInclusion terminal terminal_ordered 1 =
    fundamentalBraidWeightCutInclusion middle orderedM 2 ≫ (E).map fundamentalBraidRightCutComplex.f := by
  apply CatModule.Hom.ext
  intro W y
  exact Subtype.ext (fundamentalBraidGradedCutIso_d₂ W y)

private theorem injected_g : f₁' ≫ fundamentalBraidWeightCutInclusion middle orderedM 0 =
    fundamentalBraidWeightCutInclusion terminal terminal_ordered 1 ≫ (E).map fundamentalBraidRightCutComplex.g := by
  apply CatModule.Hom.ext
  intro W y
  exact Subtype.ext (fundamentalBraidGradedCutIso_d₁ W y)

/-- Inclusion of the three graded crossing terms in their ordinary right-module short complex. -/
def fundamentalBraidGradedCutComplexInclusion :
    fundamentalBraidTensorWeightModules ⟶ fundamentalBraidRightCutComplex.map E :=
  ShortComplex.homMk (fundamentalBraidWeightCutInclusion middle orderedM 2)
    (fundamentalBraidWeightCutInclusion terminal terminal_ordered 1)
    (fundamentalBraidWeightCutInclusion middle orderedM 0) injected_f.symm injected_g.symm

/-- The homology of the graded tensor complex maps to the ordinary reversed middle head. -/
def fundamentalBraidGradedHomologyToTarget :
    fundamentalBraidTensorWeightModules.homology ⟶ (E).obj braidTargetMiddleHead :=
  ShortComplex.homologyMap fundamentalBraidGradedCutComplexInclusion ≫
    (fundamentalBraidRightCutComplex.mapHomologyIso E).hom ≫
    (E).map fundamentalBraidRightCutHomologyIso.hom

local notation "SC" => fundamentalBraidTensorWeightModules
local notation "IC" => fundamentalBraidGradedCutComplexInclusion
local notation "HSC" => fundamentalBraidTensorWeightModules.homology
local notation "Z" n:arg => (WeightCategory.mk n : WeightCategory Uᵐᵒᵖ)

private def evaluatedHomology (n : ℤ) :
    ModuleCat.of ℤ ((HSC).obj (Z n)) ≅ (fundamentalBraidGradedTensorComplex n).homology :=
  ((SC).mapHomologyIso (weightUnderlyingGroup (Z n))).symm

private theorem inclusionHomology_mono : Mono (ShortComplex.homologyMap IC) := by
  apply mono_homologyMap_of_weightwise_mono
  rintro ⟨n⟩
  apply (ModuleCat.mono_iff_injective _).mpr
  apply homologyMap_injective_of_reflects_boundaries
  intro z _ h
  exact fundamentalBraidGradedTensor_reflectBoundary n z h

instance : Mono fundamentalBraidGradedHomologyToTarget := by
  have := inclusionHomology_mono
  dsimp only [fundamentalBraidGradedHomologyToTarget]
  infer_instance

private theorem zero_weight_surjective :
    Function.Surjective (fundamentalBraidGradedHomologyToTarget.app (Z 0)) := by
  let eS : (HSC).obj (Z 0) ≃+ ℚ := ((evaluatedHomology 0 ≪≫ fundamentalBraidGradedTensorHomologyIso).toLinearEquiv).toAddEquiv
  let eT : braidTargetMiddleHead ≃+ ℚ := fundamentalBraidTargetHeadScalarEquiv
  let φ := fundamentalBraidGradedHomologyToTarget.app (Z 0)
  let f := (eT.toAddMonoidHom.comp φ).comp eS.symm.toAddMonoidHom
  have hi : Function.Injective φ := CatModule.injective_of_mono fundamentalBraidGradedHomologyToTarget _
  have hs := surjective_rat_end_of_injective f (eT.injective.comp (hi.comp eS.symm.injective))
  intro y
  obtain ⟨x,hx⟩ := hs (eT y)
  exact ⟨eS.symm x,eT.injective hx⟩

local notation "L" => fundamentalBraidGradedTargetHead
section Target
variable {H : CatModule.{0} (WeightCategory Uᵐᵒᵖ)} (θ : H ⟶ (E).obj braidTargetMiddleHead)
    (hz : ∀ n : ℤ, n ≠ 0 → Subsingleton (H.obj (Z n)))
include hz

private theorem read_target_grade (W : WeightCategory Uᵐᵒᵖ) (y : H.obj W) :
    fundamentalBraidTargetHeadScalarEquiv (θ.app W y) ∈ DG.grading (M := ℚ) (W.as - 0) := by
  rw [InDegreeZero.ring_mem_grading_iff,sub_zero]
  by_cases hw : W.as = 0
  · exact Or.inl hw
  · have hy : y = 0 := (hz W.as hw).allEq _ _
    exact Or.inr ((congrArg (fun x => fundamentalBraidTargetHeadScalarEquiv (θ.app W x)) hy).trans
      ((congrArg fundamentalBraidTargetHeadScalarEquiv (map_zero (θ.app W))).trans (map_zero _)))

private def weightHomologyToGradedTarget : H ⟶ L where
  app W := AddMonoidHom.mk' (fun y => ⟨fundamentalBraidTargetHeadScalarEquiv (θ.app W y), read_target_grade θ hz W y⟩)
    (fun x y => Subtype.ext ((congrArg fundamentalBraidTargetHeadScalarEquiv (map_add (θ.app W) x y)).trans
      (map_add _ _ _)))
  map_mem' {W i x} hx := by
    have hg : i = 0 ∨ θ.app W x = 0 := (InDegreeZero.mem_grading_iff (M := braidTargetMiddleHead)).mp
      (θ.map_mem hx)
    change fundamentalBraidTargetHeadScalarEquiv (θ.app W x) ∈ DG.grading (M := ℚ) i
    apply (InDegreeZero.ring_mem_grading_iff (R := ℚ)).mpr
    rcases hg with hi | hc
    · exact Or.inl hi
    · exact Or.inr ((congrArg fundamentalBraidTargetHeadScalarEquiv hc).trans (map_zero _))
  map_d' {W} x := Subtype.ext ((congrArg fundamentalBraidTargetHeadScalarEquiv
    ((θ.map_d x).trans (InDegreeZero.d_apply _ _))).trans (map_zero _))
  map_smul' {W W'} a x := Subtype.ext ((congrArg fundamentalBraidTargetHeadScalarEquiv (θ.map_smul a x)).trans
    (fundamentalBraidTargetHeadScalarEquiv_smul a.val (θ.app W x)))

private def weightHomologyGradedTargetIso [Mono θ] (hs : Function.Surjective (θ.app (Z 0))) : H ≅ L := by
  let t := weightHomologyToGradedTarget θ hz
  have ht : IsIso t := by
    apply CatModule.isIso_of_bijective
    rintro ⟨n⟩
    refine ⟨fun x y h => (CatModule.injective_of_mono θ (Z n))
      (fundamentalBraidTargetHeadScalarEquiv.injective (congrArg Subtype.val h)), ?_⟩
    intro y
    by_cases hn : n = 0
    · subst n
      obtain ⟨x,hx⟩ := hs (fundamentalBraidTargetHeadScalarEquiv.symm y.val)
      exact ⟨x,Subtype.ext ((congrArg fundamentalBraidTargetHeadScalarEquiv hx).trans
        (fundamentalBraidTargetHeadScalarEquiv.apply_symm_apply _))⟩
    · have hg : y.val ∈ DG.grading (M := ℚ) (n-0) := y.property
      have hy : y.val = 0 := ((InDegreeZero.ring_mem_grading_iff (R := ℚ)).mp hg).resolve_left (by omega)
      exact ⟨0,(map_zero (t.app _)).trans (Subtype.ext hy.symm)⟩
  exact @asIso _ _ _ _ t ht

end Target

/-- The abelian homology object of the graded tensor short complex is the
middle simple with its reversed-order action, in auxiliary weight zero. -/
def fundamentalBraidGradedHomologyTargetIso : HSC ≅ L := by
  refine weightHomologyGradedTargetIso fundamentalBraidGradedHomologyToTarget ?_ zero_weight_surjective
  intro n hn
  have hh := (fundamentalBraidGradedTensorComplex n).exact_iff_isZero_homology.mp
    (fundamentalBraidGradedTensorComplex_exact n hn)
  exact ModuleCat.subsingleton_of_isZero (hh.of_iso (evaluatedHomology n))

local notation "DF" => diagramCornerWeightDerivedRightTensor V (hE κ₀) (hE κ₁)
  (redProj_mem_violAuxiliaryGrade grading κ₀) (redProj_mem_violAuxiliaryGrade grading κ₁)
universe z
variable [CatModule.HasDerivedCategory.{z,0} (WeightCategory Kᵐᵒᵖ)]
  [CatModule.HasDerivedCategory.{z,0} (WeightCategory Uᵐᵒᵖ)]

/-- The derived fundamental braid takes the source middle simple to the target
middle simple supported in cohomological degree minus one. Its physical
weight is three halves (Webster v2, §7.2, Proposition 7.11). -/
def fundamentalBraidGradedDerivedTargetIso :
    (DF).obj (CatModule.DerivedCategory.Q.obj fundamentalBraidSourceGradedHead) ≅
      (CatModule.DerivedCategory.Q.obj L)⟦(1 : ℤ)⟧ :=
  fundamentalBraidGradedDerivedHomologyModuleIso ≪≫
    (shiftFunctor _ (1 : ℤ)).mapIso (CatModule.DerivedCategory.Q.mapIso fundamentalBraidGradedHomologyTargetIso)

end Categorification.Stendhal.FundamentalCorner
