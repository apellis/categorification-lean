/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DiagramWeightTensorH0
import DG.Homotopy.CohomologyComparison
import DG.Category.Derived.Compact

/-!
# Weight cohomology on derived diagram tensor models

The cohomology at a weight of a localized dg module is computed on
its explicit dg representative. A K-projective nonpositive resolution
therefore computes ordinary weight tensor in cohomological degree zero.
-/

noncomputable section

set_option maxHeartbeats 1800000
set_option maxRecDepth 2048

namespace Categorification

open CategoryTheory DG MulOpposite
open scoped DG.DegreeZero

universe u v w z
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [DGCategory C]

private def evaluatedHomologyIso (X : C) (n : ℤ) (M : CatModule.{w} C) :
    ((CatModule.evalComplex X).obj M).homology n ≅ AddCommGrpCat.of (cohomology (M.obj X) n) := by
  letI : Algebra ℤ (CategoryTheory.End X) := Ring.toIntAlgebra _
  let E := (CatModule.eval X).obj M
  let L := (DGModuleCat.forget ℤ (CategoryTheory.End X)).obj E
  let F := forget₂ (ModuleCat.{w} ℤ) AddCommGrpCat.{w}
  change ((L.sc n).map F).homology ≅ _
  exact (L.sc n).mapHomologyIso F ≪≫
    (DGModuleCat.cohomologyAddEquiv ℤ E n).symm.toAddCommGrpIso

variable [CatModule.HasDerivedCategory.{z,w} C]

/-- Cohomology on an explicit dg representative at a weight is its ordinary
cohomology as a dg additive group. -/
def localizedWeightCohomologyIso (X : C) (n : ℤ) (M : CatModule.{w} C) :
    (CatModule.DerivedCategory.cohomologyFunctor X n).obj (CatModule.DerivedCategory.Q.obj M) ≅
      AddCommGrpCat.of (cohomology (M.obj X) n) := by
  let J := CatModule.HomotopyCategory.quotient C
  let H := _root_.HomotopyCategory.homologyFunctor AddCommGrpCat.{w} (ComplexShape.up ℤ) n
  exact (CatModule.DerivedCategory.cohomologyFunctorFactorsh X n).app (J.obj M) ≪≫
    H.mapIso ((CatModule.HomotopyCategory.evalFactors X).app M) ≪≫
    (_root_.HomotopyCategory.homologyFunctorFactors AddCommGrpCat.{w} (ComplexShape.up ℤ) n).app
      ((CatModule.evalComplex X).obj M) ≪≫ evaluatedHomologyIso X n M


section DerivedTensor

variable {A B P : Type u} [Ring A] [Ring B]
  [InternalGrading A] [InternalGrading B] [BigradedDGRing A] [BigradedDGRing B]
  [AddCommGroup P] [Module A P] [Module Bᵐᵒᵖ P] [SMulCommClass A Bᵐᵒᵖ P]
  (G : ℤ → AddSubgroup P)
  (hl : ∀ {i j : ℤ} {a : A} {x : P}, a ∈ wgrading i → x ∈ G j → a • x ∈ G (i+j))
  (hr : ∀ {i j : ℤ} {b : B} {x : P}, b ∈ wgrading i → x ∈ G j → op b • x ∈ G (j+i))
  [CatModule.HasDerivedCategory.{z,u} (WeightCategory A)]
  [CatModule.HasDerivedCategory.{z,u} (WeightCategory B)]

local notation "D₀" => diagramWeightBimodule G hl hr
local notation "F₀" => diagramWeightDerivedTensor G hl hr

/-- A K-projective nonpositive resolution computes the degree-zero part of
derived tensor by the ordinary endpoint coend. -/
def diagramWeightDerivedTensorH0IsoOfResolution
    {K E : CatModule.{u} (WeightCategory B)} (f : K ⟶ E)
    (hK : CatModule.IsKProjective K) (hf : CatModule.IsQuasiIso f)
    (hK₀ : ∀ (Y : WeightCategory B) {x : K.obj Y}, x ∈ DG.grading (0 : ℤ) → d x = 0)
    (hE : ∀ Y, PureDegreeZero (E.obj Y)) (X : WeightCategory A) :
    (CatModule.DerivedCategory.cohomologyFunctor X 0).obj
      ((F₀).obj (CatModule.DerivedCategory.Q.obj E)) ≅
      AddCommGrpCat.of (((D₀).tensorFunctor.obj E).obj X) := by
  let Q := CatModule.DerivedCategory.Q (C := WeightCategory B)
  let H := CatModule.DerivedCategory.cohomologyFunctor X 0
  letI : IsIso (Q.map f) := (CatModule.DerivedCategory.isIso_Q_map_iff f).mpr hf
  let b := ((F₀).mapIso (asIso (Q.map f))).symm ≪≫ diagramWeightDerivedTensorObjIso G hl hr hK
  have hR : ∀ Y, PureDegreeZero (((D₀).right X).obj (DG.DGOpposite.op Y)) :=
    fun _ => ⟨InDegreeZero.mem_grading_zero, InDegreeZero.d_apply _⟩
  exact H.mapIso b ≪≫ localizedWeightCohomologyIso X 0 (((D₀).tensorFunctor.obj K)) ≪≫
    (catTensorCohomologyZeroEquivOfQuasiIso hR hE hK₀ f hf
      (fun {_ _} g => WeightCategory.mem_grading_iff.mpr
        (InDegreeZero.ring_mem_grading_zero g.val))).toAddCommGrpIso

end DerivedTensor

end Categorification
