/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.FundamentalBraidGradedCoend
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
/-!
# Weight homology of the fundamental braid tensor

For Webster, arXiv:1309.3796v2, §7.2, Proposition 7.11, evaluate the two graded
projective resolution maps after tensoring with the braid. The auxiliary
weight `n` corresponds to physical weight `n + 3/2`. The middle homology
is a rational line at weight zero, and the two ends are exact in every weight.
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
local notation "U" => ViolOrderCorner (k := ℚ) (Q := Q) (Λ := wt) («ν» := ν) κ₁
local notation "V" => violAuxiliaryGrade («ν» := ν) grading
local notation "hE" => isIdempotentElem_violMk_redProj ℚ Q wt ν
attribute [local instance] fundamentalBraidCoendSourceCornerGrades fundamentalBraidCoendTargetCornerGrades
  fundamentalBraidCoendSourceInternal fundamentalBraidCoendTargetInternal
  fundamentalBraidCoendSourceBigraded fundamentalBraidCoendTargetBigraded
local notation "C" => CartanDatum.ofGraph (⊥ : SimpleGraph Unit)
local notation "B" => diagramCornerWeightRightBimodule V (hE κ₀) (hE κ₁)
  (redProj_mem_violAuxiliaryGrade grading κ₀) (redProj_mem_violAuxiliaryGrade grading κ₁)

variable {H : Type*} [AddCommGroup H] [Module ℂ H] [Module.Finite ℂ H]
  (P : Matrix.Realization (UDot.A C) ℂ H)
local notation "G" s:arg => figureFiveCutGrade (Λ := wt) C fundamentalBraidParameters
  (weightPairing C P) (fun _ => braidFundamentalWeight P) s 1 0
private abbrev physicalWeight (n : ℤ) : ℂ := (n : ℂ) + 3 / 2
private theorem midOrd : IsRedOrdered middle := by unfold IsRedOrdered; decide +kernel
variable (n : ℤ)
local notation "Z" => (WeightCategory.mk n : WeightCategory Uᵐᵒᵖ)
local notation "Tens" s:arg hs:arg j:arg => CatModule.obj
  (CatBimodule.tensorObj B (corner (fundamentalBraidSourceLoadingAt s hs j))) Z
local notation "W" => fundamentalBraidWeightComplex P (physicalWeight n)

private def physicalEquiv (s : KLR.Seq μ) (hs : IsRedOrdered s) (j : ℤ)
    (b : ℂ) (hb : (j : ℂ) = b) :
    Tens s hs j ≃+ Graded.shift (G s) b (physicalWeight n) :=
  (fundamentalBraidGradedCutIso s hs j Z).trans
    (LinearEquiv.ofEq _ _ (by
      rw [← hb]
      exact (fundamentalBraidCut_physicalWeight P s j n).symm)).toAddEquiv

private abbrev phys₂ : Tens middle midOrd 2 ≃+ (W).X₁ := physicalEquiv P n middle midOrd 2 2 (by norm_num)
private abbrev phys₁ : Tens terminal terminal_ordered 1 ≃+ (W).X₂ :=
  physicalEquiv P n terminal terminal_ordered 1 1 (by norm_num)
private abbrev phys₀ : Tens middle midOrd 0 ≃+ (W).X₃ := physicalEquiv P n middle midOrd 0 0 (by norm_num)

private abbrev upMap : Tens middle midOrd 2 →+ Tens terminal terminal_ordered 1 :=
  ((B).tensorFunctor.map fundamentalBraidGradedSourceD₂).app Z
private abbrev downMap : Tens terminal terminal_ordered 1 →+ Tens middle midOrd 0 :=
  ((B).tensorFunctor.map fundamentalBraidGradedSourceD₁).app Z

private theorem up_comm (z : Tens middle midOrd 2) :
    phys₁ P n (upMap n z) =
      (W).f (phys₂ P n z) := by
  apply Subtype.ext
  apply Subtype.ext
  exact fundamentalBraidGradedCutIso_d₂ Z z
private theorem down_comm (z : Tens terminal terminal_ordered 1) :
    phys₀ P n (downMap n z) =
      (W).g (phys₁ P n z) := by
  apply Subtype.ext
  apply Subtype.ext
  exact fundamentalBraidGradedCutIso_d₁ Z z

private abbrev stdRealization := Matrix.Realization.std (UDot.A C) ℂ

private def upHom : ModuleCat.of ℤ (Tens middle midOrd 2) ⟶ ModuleCat.of ℤ (Tens terminal terminal_ordered 1) :=
  ModuleCat.ofHom (upMap n).toIntLinearMap
private def downHom : ModuleCat.of ℤ (Tens terminal terminal_ordered 1) ⟶ ModuleCat.of ℤ (Tens middle midOrd 0) :=
  ModuleCat.ofHom (downMap n).toIntLinearMap

private theorem down_up (z : Tens middle midOrd 2) : downMap n (upMap n z) = 0 := by
  let Wstd := fundamentalBraidWeightComplex stdRealization (physicalWeight n)
  apply (phys₀ stdRealization n).injective
  exact (down_comm stdRealization n _).trans ((congrArg Wstd.g (up_comm stdRealization n z)).trans
    ((Wstd.moduleCat_zero_apply _).trans (map_zero _).symm))

private theorem fg_zero : upHom n ≫ downHom n = 0 :=
  ModuleCat.hom_ext (LinearMap.ext fun z => down_up n z)

/-- The two braid tensor differentials evaluated at the given target weight. -/
def fundamentalBraidGradedTensorComplex : ShortComplex (ModuleCat ℤ) :=
  ShortComplex.mk (upHom n) (downHom n) (fg_zero n)

private abbrev forgetQ := ModuleCat.restrictScalars (Int.castRingHom ℚ)
private def termIso {X : Type} [AddCommGroup X] (Y : ModuleCat ℚ) (e : X ≃+ Y) :
    ModuleCat.of ℤ X ≅ forgetQ.obj Y := e.toIntLinearEquiv.toModuleIso

/-- In Webster v2, §7.2, Proposition 7.11, the braid tensor at auxiliary
weight `n` identifies with the cut complex at physical weight `n + 3/2`. -/
def fundamentalBraidGradedTensorCutIso : fundamentalBraidGradedTensorComplex n ≅ (W).map forgetQ :=
  ShortComplex.isoMk (termIso (W).X₁ (phys₂ P n))
    (termIso (W).X₂ (phys₁ P n))
    (termIso (W).X₃ (phys₀ P n))
    (by apply ModuleCat.hom_ext; exact LinearMap.ext fun z => (up_comm P n z).symm)
    (by apply ModuleCat.hom_ext; exact LinearMap.ext fun z => (down_comm P n z).symm)

/-- At every weight the first tensor differential is injective and the second is surjective. -/
theorem fundamentalBraidGradedTensorComplex_ends :
    Function.Injective (fundamentalBraidGradedTensorComplex n).f ∧
      Function.Surjective (fundamentalBraidGradedTensorComplex n).g := by
  obtain ⟨hi, hs⟩ := fundamentalBraidWeightComplex_ends stdRealization (physicalWeight n)
  constructor
  · intro x y h
    apply (phys₂ stdRealization n).injective
    apply hi
    exact (up_comm stdRealization n x).symm.trans
      ((congrArg (phys₁ stdRealization n) h).trans (up_comm stdRealization n y))
  · intro z
    obtain ⟨x, hx⟩ := hs (phys₀ stdRealization n z)
    obtain ⟨y, hy⟩ := (phys₁ stdRealization n).surjective x
    refine ⟨y, (phys₀ stdRealization n).injective ?_⟩
    exact (down_comm stdRealization n y).trans ((congrArg _ hy).trans hx)

/-- The graded tensor complex is exact at every nonzero auxiliary weight. -/
theorem fundamentalBraidGradedTensorComplex_exact (hn : n ≠ 0) :
    (fundamentalBraidGradedTensorComplex n).Exact := by
  have hw : physicalWeight n ≠ 3 / 2 := by
    intro h
    apply hn
    exact_mod_cast (show (n : ℂ) = 0 by dsimp [physicalWeight] at h; linear_combination h)
  exact ShortComplex.exact_of_iso (fundamentalBraidGradedTensorCutIso stdRealization n).symm
    ((fundamentalBraidWeightComplex_exact stdRealization hw).map _)

/-- The middle homology at auxiliary weight zero, or physical weight three halves,
is the additive group of the rational line (Webster v2, Proposition 7.11). -/
def fundamentalBraidGradedTensorHomologyIso :
    (fundamentalBraidGradedTensorComplex 0).homology ≅ forgetQ.obj (ModuleCat.of ℚ ℚ) := by
  let e := fundamentalBraidGradedTensorCutIso stdRealization 0
  have hw : physicalWeight 0 = 3 / 2 := by simp [physicalWeight]
  exact (ShortComplex.homologyFunctor (ModuleCat ℤ)).mapIso e ≪≫
    (fundamentalBraidWeightComplex stdRealization (physicalWeight 0)).mapHomologyIso forgetQ ≪≫
    forgetQ.mapIso (by rw [hw]; exact fundamentalBraidWeightComplex_homologyIso stdRealization)

private theorem terminalCutValue (z : Tens terminal terminal_ordered 1) :
    (phys₁ P n z).val = (fundamentalBraidGradedCutIso terminal terminal_ordered 1 Z z).val :=
  rfl

private theorem liftToTensor (z : Tens terminal terminal_ordered 1)
    (h : ∃ m : (W).X₁, (W).f m = phys₁ P n z) :
    ∃ x : Tens middle midOrd 2, upMap n x = z := by
  obtain ⟨m, hm⟩ := h
  obtain ⟨x,hx⟩ := (phys₂ P n).surjective m
  refine ⟨x,(phys₁ P n).injective ?_⟩
  exact (up_comm P n x).trans ((congrArg (W).f hx).trans hm)

/-- An ungraded boundary belonging to a homogeneous braid cut has a
preimage under the tensor differential at the same target weight. -/
theorem fundamentalBraidGradedTensor_reflectBoundary
    (z : Tens terminal terminal_ordered 1)
    (hz : ∃ y : fundamentalBraidCutComplex.X₁, fundamentalBraidCutComplex.f y =
      (fundamentalBraidGradedCutIso terminal terminal_ordered 1 Z z).val) :
    ∃ x : Tens middle midOrd 2, upMap n x = z := by
  apply liftToTensor stdRealization n z
  apply fundamentalBraidWeightComplex_reflectBoundary
  rw [terminalCutValue]
  exact hz

end Categorification.Stendhal.FundamentalCorner
