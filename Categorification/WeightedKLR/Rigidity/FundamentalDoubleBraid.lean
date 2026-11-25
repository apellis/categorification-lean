/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.FundamentalBraidSwapTensor
import Categorification.WeightedKLR.Rigidity.FundamentalBraidGradedCharacterComparison
import Categorification.Algebra.DiagramWeightTensorDerived

/-!
# The double positive fundamental braid on the middle character

The calculation of the double positive braid in Webster, arXiv:1309.3796v2,
§7.2 before Definition 7.12 uses the same transposition on the two
diagonal corners and on the rectangular crossing coefficient.
-/
noncomputable section
namespace Categorification.Stendhal.FundamentalCorner
open KLR KLRAlgebra BraidedStendhalAlgebra CategoryTheory DG CatModule Coevaluation
open scoped DG.DegreeZero
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance] fundamentalBraidCoendSourceCornerGrades fundamentalBraidCoendTargetCornerGrades
  fundamentalBraidCoendSourceInternal fundamentalBraidCoendTargetInternal
  fundamentalBraidCoendSourceBigraded fundamentalBraidCoendTargetBigraded
  fundamentalBraidSourceOrderedInternal fundamentalBraidSourceOrderedBigraded
  fundamentalTargetScalarInternal fundamentalTargetScalarBigraded
local notation "ν" => ({()} : Multiset Unit)
local notation "σ" => Equiv.swap (0 : Fin 2) 1
local notation "K" => ViolOrderCorner (k := ℚ) (Q := Q) (Λ := wt) («ν» := ν) (List.finRange 2)
local notation "U" => ViolOrderCorner (k := ℚ) (Q := Q) (Λ := wt) («ν» := ν) [1,0]
local notation "V" => ViolQuotient ℚ Q wt ν
local notation "G" => violAuxiliaryGrade («ν» := ν) grading
local notation "π" => violMk ℚ Q wt ν
local notation "p" κ:arg => π (redProj ℚ Q wt ν κ)
local notation "κ₀" => List.finRange 2
local notation "κ₁" => ([1,0] : List (Fin 2))
local notation "h" κ:arg => isIdempotentElem_violMk_redProj ℚ Q wt ν κ


local notation "FA" => fundamentalBraidSourceSwapFunctor
local notation "FB" => fundamentalBraidTargetSwapFunctor

private def restrictSourceHead : (CatModule.precomp FB).obj fundamentalBraidSourceGradedHead ≅
    fundamentalBraidGradedTargetHead := by
  refine CatModule.isoMk (fun _ => AddEquiv.refl _) (by intros; exact Iff.rfl) (by intros; rfl) ?_
  intro X Y f z
  apply Subtype.ext
  change middleCharacter (fundamentalBraidSourceEquiv (fundamentalBraidTargetSwap f.val.unop)) * z.val =
    middleCharacter (fundamentalBraidTargetEquiv f.val.unop) * z.val
  rw [fundamentalBraidSourceEquiv_targetSwap]

private def restrictTargetHead : (CatModule.precomp FA).obj fundamentalBraidGradedTargetHead ≅
    fundamentalBraidSourceGradedHead := by
  refine CatModule.isoMk (fun _ => AddEquiv.refl _) (by intros; exact Iff.rfl) (by intros; rfl) ?_
  intro X Y f z
  apply Subtype.ext
  change middleCharacter (fundamentalBraidTargetEquiv (fundamentalBraidSourceSwap f.val.unop)) * z.val =
    middleCharacter (fundamentalBraidSourceEquiv f.val.unop) * z.val
  rw [fundamentalBraidTargetEquiv_sourceSwap]

open QuantumGroup
local notation "C" => CartanDatum.ofGraph (⊥ : SimpleGraph Unit)

/-- On the second, reversed crossing of the two fundamental strands, the
input cut carries the first crossing's physical offset of 3/2.
Definition 6.2 then puts output auxiliary weight n at physical weight n+3. -/
theorem fundamentalDoubleBraidCut_physicalWeight {H : Type*} [AddCommGroup H] [Module ℂ H]
    [Module.Finite ℂ H] (P : Matrix.Realization (UDot.A C) ℂ H)
    (s : Seq (stendhalWeight 2 ν)) (j n : ℤ) :
    Graded.shift (figureFiveCutGrade (Λ := wt) C fundamentalBraidParameters
      (weightPairing C P) (fun _ => braidFundamentalWeight P) s 0 1)
        ((j : ℂ) + 3 / 2) ((n : ℂ) + 3) =
      violCornerAuxiliaryGrade (Λ := wt) C fundamentalBraidParameters s [0,1] (n-j) := by
  let f := fun i : ℤ => (i : ℂ) + (2-weightPairing C P (braidFundamentalWeight P) (braidFundamentalWeight P))
  have hf : Function.Injective f := fun _ _ he => Int.cast_injective (add_right_cancel he)
  have he : f (n-j) = (n : ℂ) + 3 - ((j : ℂ) + 3 / 2) := by
    dsimp [f]
    rw [braidFundamentalWeight_norm, Int.cast_sub]
    ring
  change Function.extend f _ ⊥ _ = _
  rw [← he, hf.extend_apply]

universe v
variable [CatModule.HasDerivedCategory.{v,0} (WeightCategory Kᵐᵒᵖ)]
  [CatModule.HasDerivedCategory.{v,0} (WeightCategory Uᵐᵒᵖ)]
local notation "hG" κ:arg => redProj_mem_violAuxiliaryGrade grading κ
local notation "F₁" => diagramCornerWeightDerivedRightTensor G (h κ₀) (h κ₁) (hG κ₀) (hG κ₁)
local notation "F₂" => diagramCornerWeightDerivedRightTensor G (h κ₁) (h κ₀) (hG κ₁) (hG κ₀)
local notation "inF" => CatModule.DerivedCategory.restrict FB
local notation "outF" => CatModule.DerivedCategory.restrict FA
local notation "Qh" => CatModule.DerivedCategory.Q
local notation "L" => Functor.obj CatModule.DerivedCategory.Q fundamentalBraidSourceGradedHead
local notation "L'" => Functor.obj CatModule.DerivedCategory.Q fundamentalBraidGradedTargetHead

private def restrictSourceDerivedHead : (inF).obj L ≅ L' :=
  (CatModule.DerivedCategory.QCompRestrictIso FB).app fundamentalBraidSourceGradedHead ≪≫
    (Qh).mapIso restrictSourceHead

private def restrictTargetDerivedHead : (outF).obj L' ≅ L :=
  (CatModule.DerivedCategory.QCompRestrictIso FA).app fundamentalBraidGradedTargetHead ≪≫
    (Qh).mapIso restrictTargetHead

/-- The positive crossing starting at the reversed red order takes its
middle character to the ordered character in native cohomological degree −1.
This is the reversed input to Webster v2, Proposition 7.11. -/
def fundamentalBraidReversedHeadIso : (F₂).obj L' ≅ (L)⟦(1 : ℤ)⟧ :=
  (F₂).mapIso restrictSourceDerivedHead.symm ≪≫ fundamentalBraidSwapDerivedIso L ≪≫
    (outF).mapIso fundamentalBraidGradedDerivedTargetIso ≪≫ ((outF).commShiftIso (1 : ℤ)).app L' ≪≫
    (shiftFunctor _ (1 : ℤ)).mapIso restrictTargetDerivedHead

private local instance reverseBraidCommShift : (F₂).CommShift ℤ := by
  unfold diagramCornerWeightDerivedRightTensor
  apply diagramWeightDerivedTensor_commShift

/-- The two successive positive fundamental crossings of Webster v2, §7.2
before Definition 7.12, return the ordered middle character in native
cohomological degree −2 and its original auxiliary weight. -/
def fundamentalDoubleBraidHeadIso : ((F₁) ⋙ (F₂)).obj L ≅ (L)⟦(2 : ℤ)⟧ :=
  (F₂).mapIso fundamentalBraidGradedDerivedTargetIso ≪≫ ((F₂).commShiftIso (1 : ℤ)).app L' ≪≫
    (shiftFunctor _ (1 : ℤ)).mapIso fundamentalBraidReversedHeadIso ≪≫
    ((shiftFunctorAdd' _ (1 : ℤ) 1 2 (by decide)).app L).symm

end Categorification.Stendhal.FundamentalCorner
