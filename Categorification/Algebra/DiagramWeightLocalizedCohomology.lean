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

/-- Evaluate a dg module map on the cohomology of its component at a weight. -/
def weightEvalCohomologyMap (X : C) (n : ℤ) {M N : CatModule.{w} C} (f : M ⟶ N) :
    AddCommGrpCat.of (cohomology (M.obj X) n) ⟶ AddCommGrpCat.of (cohomology (N.obj X) n) :=
  AddCommGrpCat.ofHom (cohomology.mapAddMonoidHom (f.app X) f.map_mem f.map_d n)

set_option backward.isDefEq.respectTransparency false in
private theorem evaluatedHomologyIso_naturality (X : C) (n : ℤ)
    {M N : CatModule.{w} C} (f : M ⟶ N) :
    HomologicalComplex.homologyMap ((CatModule.evalComplex X).map f) n ≫
        (evaluatedHomologyIso X n N).hom =
      (evaluatedHomologyIso X n M).hom ≫ weightEvalCohomologyMap X n f := by
  let : Algebra ℤ (CategoryTheory.End X) := Ring.toIntAlgebra _
  let M₀ := (CatModule.eval X).obj M
  let N₀ := (CatModule.eval X).obj N
  let f₀ : M₀ ⟶ N₀ := (CatModule.eval X).map f
  let F := forget₂ (ModuleCat.{w} ℤ) AddCommGrpCat.{w}
  let L := DGModuleCat.forget ℤ (CategoryTheory.End X)
  let h := (HomologicalComplex.shortComplexFunctor (ModuleCat.{w} ℤ) (ComplexShape.up ℤ) n).map
    (L.map f₀)
  have hn := ShortComplex.mapHomologyIso_hom_naturality h F
  let eM : AddCommGrpCat.of (cohomology (M.obj X) n) ≅ F.obj ((L.obj M₀).homology n) :=
    (DGModuleCat.cohomologyAddEquiv ℤ M₀ n).toAddCommGrpIso
  let eN : AddCommGrpCat.of (cohomology (N.obj X) n) ≅ F.obj ((L.obj N₀).homology n) :=
    (DGModuleCat.cohomologyAddEquiv ℤ N₀ n).toAddCommGrpIso
  have h₁ : weightEvalCohomologyMap X n f ≫ eN.hom =
      eM.hom ≫ F.map (HomologicalComplex.homologyMap (L.map f₀) n) := by
    apply AddCommGrpCat.ext
    intro x
    exact DGModuleCat.cohomologyAddEquiv_naturality ℤ f₀ n x
  have h₂ : F.map (HomologicalComplex.homologyMap (L.map f₀) n) ≫ eN.inv =
      eM.inv ≫ weightEvalCohomologyMap X n f := by
    rw [← cancel_epi eM.hom, ← Category.assoc, ← h₁, Category.assoc,
      Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  change ShortComplex.homologyMap (F.mapShortComplex.map h) ≫
      (((L.obj N₀).sc n).mapHomologyIso F).hom ≫ eN.inv =
    ((((L.obj M₀).sc n).mapHomologyIso F).hom ≫ eM.inv) ≫ _
  calc
    _ = (ShortComplex.homologyMap (F.mapShortComplex.map h) ≫
        (((L.obj N₀).sc n).mapHomologyIso F).hom) ≫ eN.inv :=
      (Category.assoc _ _ _).symm
    _ = ((((L.obj M₀).sc n).mapHomologyIso F).hom ≫
        F.map (ShortComplex.homologyMap h)) ≫ eN.inv :=
      congrArg (fun x => x ≫ eN.inv) hn
    _ = _ := by
      have hh : F.map (ShortComplex.homologyMap h) ≫ eN.inv =
          eM.inv ≫ weightEvalCohomologyMap X n f := h₂
      rw [Category.assoc]
      exact (congrArg (fun x => (((L.obj M₀).sc n).mapHomologyIso F).hom ≫ x) hh).trans
        (Category.assoc _ _ _).symm

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


set_option backward.isDefEq.respectTransparency false in
/-- The comparison with a dg representative is natural at each weight. -/
theorem localizedWeightCohomologyIso_naturality (X : C) (n : ℤ)
    {M N : CatModule.{w} C} (f : M ⟶ N) :
    (CatModule.DerivedCategory.cohomologyFunctor X n).map (CatModule.DerivedCategory.Q.map f) ≫
        (localizedWeightCohomologyIso X n N).hom =
      (localizedWeightCohomologyIso X n M).hom ≫ weightEvalCohomologyMap X n f := by
  let J := CatModule.HomotopyCategory.quotient C
  let H := _root_.HomotopyCategory.homologyFunctor AddCommGrpCat.{w} (ComplexShape.up ℤ) n
  let e₁ := CatModule.DerivedCategory.cohomologyFunctorFactorsh X n
  let e₂ := CatModule.HomotopyCategory.evalFactors X
  let e₃ := _root_.HomotopyCategory.homologyFunctorFactors AddCommGrpCat.{w} (ComplexShape.up ℤ) n
  have h₁ := e₁.hom.naturality (J.map f)
  have h₂ := congrArg H.map (e₂.hom.naturality f)
  have h₃ := e₃.hom.naturality ((CatModule.evalComplex X).map f)
  simp only [Functor.comp_map, Functor.map_comp] at h₁ h₂ h₃
  let i₁M := e₁.hom.app (J.obj M)
  let i₁N := e₁.hom.app (J.obj N)
  let i₂M := H.map (e₂.hom.app M)
  let i₂N := H.map (e₂.hom.app N)
  let i₃M := e₃.hom.app ((CatModule.evalComplex X).obj M)
  let i₃N := e₃.hom.app ((CatModule.evalComplex X).obj N)
  let i₄M := (evaluatedHomologyIso X n M).hom
  let i₄N := (evaluatedHomologyIso X n N).hom
  let m₀ := (CatModule.DerivedCategory.cohomologyFunctor X n).map
    (CatModule.DerivedCategory.Q.map f)
  let m₁ := H.map ((CatModule.HomotopyCategory.eval.{w} X).map (J.map f))
  let m₂ := H.map ((_root_.HomotopyCategory.quotient _ _).map ((CatModule.evalComplex X).map f))
  let m₃ := HomologicalComplex.homologyMap ((CatModule.evalComplex X).map f) n
  let m₄ := weightEvalCohomologyMap X n f
  have hh₁ : m₀ ≫ i₁N = i₁M ≫ m₁ := h₁
  have hh₂ : m₁ ≫ i₂N = i₂M ≫ m₂ := h₂
  have hh₃ : m₂ ≫ i₃N = i₃M ≫ m₃ := h₃
  change m₀ ≫ (i₁N ≫ i₂N ≫ i₃N ≫ i₄N) =
    (i₁M ≫ i₂M ≫ i₃M ≫ i₄M) ≫ m₄
  calc
    _ = (m₀ ≫ i₁N) ≫ i₂N ≫ i₃N ≫ i₄N := by simp only [Category.assoc]
    _ = (i₁M ≫ m₁) ≫ i₂N ≫ i₃N ≫ i₄N :=
      congrArg (fun x => x ≫ i₂N ≫ i₃N ≫ i₄N) hh₁
    _ = i₁M ≫ (m₁ ≫ i₂N) ≫ i₃N ≫ i₄N := by simp only [Category.assoc]
    _ = i₁M ≫ (i₂M ≫ m₂) ≫ i₃N ≫ i₄N :=
      congrArg (fun x => i₁M ≫ x ≫ i₃N ≫ i₄N) hh₂
    _ = i₁M ≫ i₂M ≫ (m₂ ≫ i₃N) ≫ i₄N := by simp only [Category.assoc]
    _ = i₁M ≫ i₂M ≫ (i₃M ≫ m₃) ≫ i₄N :=
      congrArg (fun x => i₁M ≫ i₂M ≫ x ≫ i₄N) hh₃
    _ = i₁M ≫ i₂M ≫ i₃M ≫ (m₃ ≫ i₄N) := by simp only [Category.assoc]
    _ = i₁M ≫ i₂M ≫ i₃M ≫ (i₄M ≫ m₄) :=
      congrArg (fun x => i₁M ≫ i₂M ≫ i₃M ≫ x) (evaluatedHomologyIso_naturality X n f)
    _ = _ := by simp only [Category.assoc]

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

/-- The tensor of a K-projective dg model is natural in maps of models. -/
theorem diagramWeightDerivedTensorObjIso_naturality
    {K L : CatModule.{u} (WeightCategory B)} (a : K ⟶ L)
    (hK : CatModule.IsKProjective K) (hL : CatModule.IsKProjective L) :
    (F₀).map (CatModule.DerivedCategory.Q.map a) ≫
        (diagramWeightDerivedTensorObjIso G hl hr hL).hom =
      (diagramWeightDerivedTensorObjIso G hl hr hK).hom ≫
        CatModule.DerivedCategory.Q.map ((D₀).tensorFunctor.map a) := by
  let C₀ := WeightCategory B
  let C₁ := WeightCategory A
  let J := CatModule.HomotopyCategory.quotient C₀
  let S := CatModule.HomotopyCategory.subcategoryKProjective.{u} C₀
  let I := CatModule.DerivedCategory.kProjectiveEquivalence C₀
  let V : S.FullSubcategory :=
    ⟨J.obj K, (CatModule.HomotopyCategory.quotient_obj_mem_subcategoryKProjective_iff K).mpr hK⟩
  let W : S.FullSubcategory :=
    ⟨J.obj L, (CatModule.HomotopyCategory.quotient_obj_mem_subcategoryKProjective_iff L).mpr hL⟩
  let g : V ⟶ W := ObjectProperty.homMk (J.map a)
  let T := S.ι ⋙ diagramWeightTensorHomotopy G hl hr ⋙ CatModule.DerivedCategory.Qh (C := C₁)
  have h := congrArg T.map (I.unitIso.inv.naturality g)
  rw [Functor.map_comp, Functor.map_comp] at h
  exact h

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
