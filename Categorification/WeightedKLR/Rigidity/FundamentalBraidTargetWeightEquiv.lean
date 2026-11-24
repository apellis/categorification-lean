/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidedRelabelGrading
import Categorification.Algebra.WeightRingDerivedRestriction
import Categorification.WeightedKLR.Rigidity.FundamentalBraidGradedTargetHead

/-!
# Graded relabelling of the fundamental target corner

For the cap after the fundamental braid in Webster, arXiv:1309.3796v2,
§7.1, relabelling identifies both orders of equal red labels. The middle
character and all its internal translations agree under this graded
equivalence.
-/

noncomputable section
namespace Categorification.Stendhal.FundamentalCorner
open CategoryTheory DG BraidedStendhalAlgebra QuantumGroup CatModule Coevaluation
open scoped DG.DegreeZero
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance] fundamentalBraidCoendTargetCornerGrades fundamentalBraidCoendTargetInternal
  fundamentalBraidCoendTargetBigraded fundamentalBraidSourceOrderedInternal fundamentalBraidSourceOrderedBigraded
  fundamentalTargetScalarInternal fundamentalTargetScalarBigraded
local notation "ν" => ({()} : Multiset Unit)
local notation "K" κ:arg => ViolOrderCorner (k := ℚ) (Q := Q) (Λ := wt) («ν» := ν) κ
local notation "U" => K ([1,0] : List (Fin 2))
local notation "T" => TensorProductAlgebra ℚ Q wt ν
local notation "V" => violAuxiliaryGrade («ν» := ν) grading
local notation "σ" => Equiv.swap (0 : Fin 2) 1

/-- Preserving the auxiliary grade in the target equivalence from the
reversed to the ordered fundamental diagram algebra. -/
theorem fundamentalBraidTargetEquiv_mem_weight {j : ℤ} (a : U) :
    fundamentalBraidTargetEquiv a ∈ tensorProductGrade grading ν j ↔ a.val ∈ V j := by
  let E : K (List.finRange 2) ≃+* U := violCornerRedPermEquiv (k := ℚ) (Q := Q) (Λ' := wt) (Λ := wt) («ν» := ν) σ (fun _ => rfl) (List.finRange 2)
  have h := violCornerRedPermEquiv_mem_grade_iff (Λ := wt) («ν» := ν) fundamentalBraidParameters σ
    (n := j) (List.finRange 2) (E.symm a)
  have hc := congrArg (fun c : U => c.val ∈ V j) (E.apply_symm_apply a)
  change fundamentalBraidSourceEquiv (E.symm a) ∈ _ ↔ _
  exact (violCornerEquiv_mem_tensorProductGrade_iff wordSpec (fun i l h => (h (Subsingleton.elim i l)).elim)
    grading (E.symm a)).trans (h.symm.trans (iff_of_eq hc))

private theorem targetWeight {j : ℤ} (a : Uᵐᵒᵖ) :
    fundamentalBraidTargetEquiv a.unop ∈ tensorProductGrade grading ν j ↔ a.unop.val ∈ V j :=
  fundamentalBraidTargetEquiv_mem_weight a.unop

/-- Relabelling the reversed target as a functor on diagram weights. -/
abbrev fundamentalBraidTargetWeightFunctor : WeightCategory Uᵐᵒᵖ ⥤ WeightCategory Tᵐᵒᵖ :=
  weightFunctorOfRingEquiv fundamentalBraidTargetEquiv.op targetWeight

instance : fundamentalBraidTargetWeightFunctor.Additive :=
  weightFunctorOfRingEquiv_additive fundamentalBraidTargetEquiv.op targetWeight
instance : fundamentalBraidTargetWeightFunctor.IsDGFunctor :=
  weightFunctorOfRingEquiv_isDGFunctor fundamentalBraidTargetEquiv.op targetWeight

local notation "F" => fundamentalBraidTargetWeightFunctor
local notation "χ" => WeightCategory.mapFunctor gradedMiddleCharacter gradedMiddleCharacter_mem_weight
local notation "υ" => WeightCategory.mapFunctor fundamentalBraidGradedTargetCharacter fundamentalBraidGradedTargetCharacter_mem_weight

/-- Passing through the ordered diagram weights and then taking the middle
character is the character functor of the reversed order. -/
def fundamentalBraidTargetCharacterCompIso : F ⋙ χ ≅ υ :=
  NatIso.ofComponents (fun _ => WeightCategory.isoOfEq rfl) (fun f => by
    apply WeightCategory.hom_ext
    change _ * _ = _ * _
    simp [WeightCategory.isoOfEq]
    rfl)

local notation "sT" j:arg => WeightCategory.shiftFunctor Tᵐᵒᵖ j
local notation "sU" j:arg => WeightCategory.shiftFunctor Uᵐᵒᵖ j
local notation "field" => CatModule.representable (WeightCategory.mk 0 : WeightCategory ℚ)
private def targetShiftedCharacterCompIso (j : ℤ) : F ⋙ sT j ⋙ χ ≅ sU j ⋙ υ :=
  NatIso.ofComponents (fun _ => WeightCategory.isoOfEq rfl) (fun f => by
    apply WeightCategory.hom_ext
    change _ * _ = _ * _
    simp [WeightCategory.isoOfEq]
    rfl)

/-- The graded target middle character agrees in each internal translation
with restriction of the ordered middle character. -/
def fundamentalBraidTargetShiftedRestriction (j : ℤ) :
    (CatModule.precomp F).obj ((CatModule.precomp (sT j)).obj gradedMiddleSimple) ≅
      (CatModule.precomp (sU j)).obj fundamentalBraidGradedTargetHead :=
  (CatModule.precomp F).mapIso (((CatModule.precompCompIso (sT j) χ).app field).symm) ≪≫
    ((CatModule.precompCompIso F (sT j ⋙ χ)).app field).symm ≪≫
    (CatModule.precompNatIso (targetShiftedCharacterCompIso j)
      (fun _ => WeightCategory.mem_grading_zero_of_val_eq_one _ rfl) (fun _ => WeightCategory.d_eq_zero_of_val_eq_one _ rfl)
      (fun _ => WeightCategory.mem_grading_zero_of_val_eq_one _ rfl) (fun _ => WeightCategory.d_eq_zero_of_val_eq_one _ rfl)).app field ≪≫
    (CatModule.precompCompIso (sU j) υ).app field

universe v
variable [CatModule.HasDerivedCategory.{v,0} (WeightCategory Uᵐᵒᵖ)]
  [CatModule.HasDerivedCategory.{v,0} (WeightCategory Tᵐᵒᵖ)]

/-- Restriction along relabelling identifies the derived categories of
ordered and reversed fundamental diagram weights. -/
def fundamentalBraidTargetDerivedWeightEquivalence :
    CatModule.DerivedCategory.{v,0} (WeightCategory Tᵐᵒᵖ) ≌ CatModule.DerivedCategory.{v,0} (WeightCategory Uᵐᵒᵖ) :=
  weightRingEquivDerivedRestriction fundamentalBraidTargetEquiv.op targetWeight

end Categorification.Stendhal.FundamentalCorner
