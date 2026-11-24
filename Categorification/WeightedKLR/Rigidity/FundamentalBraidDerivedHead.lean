/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.TwoStageDerivedHomology
import Categorification.WeightedKLR.Rigidity.FundamentalBraidTargetHead

/-!
# The fundamental positive braid on the coevaluation head

Webster, arXiv:1309.3796v2, Proposition 7.11. For two fundamental type A₁
factors over ℚ, the right derived tensor sends the middle head to the
reversed-order middle head in cohomological degree minus one.
-/

noncomputable section
open CategoryTheory DG
open scoped DG.DegreeZero
namespace Categorification.Stendhal.FundamentalCorner

universe w
section Projective
variable {A B : Type} [Ring A] [Ring B] (M : Type) [AddCommGroup M]
  [Module A M] [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]
  [DG.HasDerivedCategory.{w,0} A] [DG.HasDerivedCategory.{w,0} B]
private abbrev tensorD := DGModuleCat.tensorFunctor (B := B) A (InDegreeZero M)
private abbrev tens (X : ModuleCat.{0} B) := TensorProductOver B (InDegreeZero M) (InDegreeZero X)

private def placedTensorIso (X : ModuleCat.{0} B) :
    (tensorD M).obj ((degreeZeroModuleFunctor B).obj X) ≅
      (degreeZeroModuleFunctor A).obj (ModuleCat.of A (tens M X)) := by
  let e : tens M X ≃ᵈᵍ[A] InDegreeZero (tens M X) := DGModuleEquiv.ofDegreeZero (LinearEquiv.refl A _)
    (fun hx hn => TensorProductOver.eq_zero_of_mem_grading_inDegreeZero hn hx)
    TensorProductOver.d_inDegreeZero InDegreeZero.mem_grading_zero (InDegreeZero.d_apply _)
  exact DGModuleCat.isoOfDGModuleEquiv e

private def projectiveTensorIso (X : ModuleCat.{0} B) [Module.Projective B X] :
    (derivedTensor.{w} A B M).obj ((degreeZeroDerivedFunctor B).obj X) ≅
      (degreeZeroDerivedFunctor A).obj (ModuleCat.of A (tens M X)) :=
  derivedTensorObjIso (A := A) (B := B) (M := M) (P := (degreeZeroModuleFunctor B).obj X)
    (show IsKProjective B (InDegreeZero X) from InDegreeZero.isKProjective) ≪≫
    DG.DerivedCategory.Q.mapIso (placedTensorIso M X)

private theorem projectiveTensorIso_naturality {X Y : ModuleCat.{0} B} [Module.Projective B X] [Module.Projective B Y]
    (f : X ⟶ Y) (g : ModuleCat.of A (tens M X) ⟶ ModuleCat.of A (tens M Y))
    (hg : ∀ (m : InDegreeZero M) (x : InDegreeZero X), g (TensorProductOver.tmul B m x) = TensorProductOver.tmul B m (f x)) :
    (derivedTensor.{w} A B M).map ((degreeZeroDerivedFunctor B).map f) ≫ (projectiveTensorIso M Y).hom =
      (projectiveTensorIso M X).hom ≫ (degreeZeroDerivedFunctor A).map g := by
  have sq : (tensorD M).map ((degreeZeroModuleFunctor B).map f) ≫ (placedTensorIso M Y).hom =
      (placedTensorIso M X).hom ≫ (degreeZeroModuleFunctor A).map g := by
    apply DGModuleCat.tensor_hom_ext
    exact fun m x => (hg m x).symm
  let hX : IsKProjective B ((degreeZeroModuleFunctor B).obj X) := (show IsKProjective B (InDegreeZero X) from InDegreeZero.isKProjective)
  let hY : IsKProjective B ((degreeZeroModuleFunctor B).obj Y) := (show IsKProjective B (InDegreeZero Y) from InDegreeZero.isKProjective)
  have h := derivedTensorObjIso_naturality (A := A) (M := M) ((degreeZeroModuleFunctor B).map f) hX hY
  change (derivedTensor A B M).map (DG.DerivedCategory.Q.map ((degreeZeroModuleFunctor B).map f)) ≫ (derivedTensorObjIso hY).hom ≫ DG.DerivedCategory.Q.map _ =
    ((derivedTensorObjIso hX).hom ≫ DG.DerivedCategory.Q.map _) ≫ DG.DerivedCategory.Q.map _
  rw [← Category.assoc, h, Category.assoc, ← Functor.map_comp, sq, Functor.map_comp, Category.assoc]

end Projective

open KLR BraidedStendhalAlgebra
local notation "ν" => ({()} : Multiset Unit)
local notation "K" => ViolOrderCorner (k := ℚ) (Q := Q) (Λ := wt) («ν» := ν) (List.finRange 2)
local notation "U" => ViolOrderCorner (k := ℚ) (Q := Q) (Λ := wt) («ν» := ν) [1,0]
local notation "F" => braidingFunctor ℚ Q wt ν (List.finRange 2) [1,0]
private abbrev bim := OpBimodule K (braidingBimodule ℚ Q wt ν (List.finRange 2) [1,0])
private theorem ordM : redWord middle = List.finRange 2 := by decide +kernel
private theorem ordT : redWord terminal = List.finRange 2 := by decide +kernel
private abbrev Pm := ModuleCat.of Kᵐᵒᵖ (rIdeal (violLoadingIdem (k := ℚ) (Q := Q) (Λ := wt) ordM))
private abbrev Pt := ModuleCat.of Kᵐᵒᵖ (rIdeal (violLoadingIdem (k := ℚ) (Q := Q) (Λ := wt) ordT))
private abbrev sourceF : Pm ⟶ Pt := ModuleCat.ofHom braidSourceD₂
private abbrev sourceG : Pt ⟶ Pm := ModuleCat.ofHom braidSourceD₁
private abbrev aug : Pm ⟶ braidSourceMiddleHead := ConcreteCategory.ofHom (C := ModuleCat Kᵐᵒᵖ) braidSourceMiddleAugmentation
local notation "T" => fundamentalBraidRightTensorComplex
variable [DG.HasDerivedCategory.{w,0} Kᵐᵒᵖ] [DG.HasDerivedCategory.{w,0} Uᵐᵒᵖ]

private instance : Module.Projective Kᵐᵒᵖ Pm := fundamentalBraidSourceResolution.1
private instance : Module.Projective Kᵐᵒᵖ Pt := fundamentalBraidSourceResolution.2.1

private def eM : (F).obj ((degreeZeroDerivedFunctor Kᵐᵒᵖ).obj Pm) ≅
    (degreeZeroDerivedFunctor Uᵐᵒᵖ).obj (T).X₁ :=
  projectiveTensorIso (A := Uᵐᵒᵖ) bim Pm

private def eT : (F).obj ((degreeZeroDerivedFunctor Kᵐᵒᵖ).obj Pt) ≅
    (degreeZeroDerivedFunctor Uᵐᵒᵖ).obj (T).X₂ :=
  projectiveTensorIso (A := Uᵐᵒᵖ) bim Pt

private theorem up_square :
    (F).map ((degreeZeroDerivedFunctor Kᵐᵒᵖ).map sourceF) ≫ eT.hom = eM.hom ≫ (degreeZeroDerivedFunctor Uᵐᵒᵖ).map (T).f :=
  projectiveTensorIso_naturality (A := Uᵐᵒᵖ) bim sourceF (T).f (fun _ _ => rfl)

private theorem down_square :
    (F).map ((degreeZeroDerivedFunctor Kᵐᵒᵖ).map sourceG) ≫ eM.hom = eT.hom ≫ (degreeZeroDerivedFunctor Uᵐᵒᵖ).map (T).g :=
  projectiveTensorIso_naturality (A := Uᵐᵒᵖ) bim sourceG (T).g (fun _ _ => rfl)

/-- The positive derived braid carries the fundamental coevaluation head to
the opposite-order middle head concentrated in cohomological degree minus one.
This is the ungraded, type A₁ fundamental instance of Webster v2, Proposition 7.11. -/
def fundamentalBraidDerivedHeadIso :
    (F).obj ((degreeZeroDerivedFunctor Kᵐᵒᵖ).obj braidSourceMiddleHead) ≅
      ((degreeZeroDerivedFunctor Uᵐᵒᵖ).obj braidTargetMiddleHead)⟦(1 : ℤ)⟧ := by
  letI : (F).CommShift ℤ := (inferInstance : (derivedTensor Uᵐᵒᵖ Kᵐᵒᵖ bim).CommShift ℤ)
  letI : (F).IsTriangulated := (inferInstance : (derivedTensor Uᵐᵒᵖ Kᵐᵒᵖ bim).IsTriangulated)
  let h := fundamentalBraidSourceResolution.2.2
  let ends := fundamentalBraidRightTensorComplex_ends
  let e := (nonempty_shiftedHomologyIso_of_exactResolution (F) sourceF sourceG aug h.1 h.2.1 h.2.2.1 h.2.2.2
    (T) ((ModuleCat.mono_iff_injective _).mpr ends.1) ((ModuleCat.epi_iff_surjective _).mpr ends.2)
    eM eT eM up_square down_square).some
  exact e ≪≫ (shiftFunctor _ (1 : ℤ)).mapIso ((degreeZeroDerivedFunctor Uᵐᵒᵖ).mapIso fundamentalBraidRightTensorHomologyIso)


attribute [local instance 1200] Ring.toIntAlgebra

private abbrev output := (F).obj ((degreeZeroDerivedFunctor Kᵐᵒᵖ).obj braidSourceMiddleHead)
private abbrev placedHead := (degreeZeroModuleFunctor Uᵐᵒᵖ).obj braidTargetMiddleHead
local notation "H" n:arg => DG.DerivedCategory.homologyFunctor (A := Uᵐᵒᵖ) ℤ n

private noncomputable local instance : (H 0).ShiftSequence ℤ := by
  letI : (DG.HomotopyCategory.homologyFunctor.{0} ℤ Uᵐᵒᵖ 0).ShiftSequence ℤ := by
    change (DG.HomotopyCategory.forget.{0} ℤ Uᵐᵒᵖ ⋙
      _root_.HomotopyCategory.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.up ℤ) 0).ShiftSequence ℤ
    infer_instance
  exact Functor.ShiftSequence.induced (DG.DerivedCategory.homologyFunctorFactorsh ℤ 0) ℤ
    (DG.DerivedCategory.homologyFunctor ℤ) (DG.DerivedCategory.homologyFunctorFactorsh ℤ)

private def shiftedReadout (n m : ℤ) (h : 1 + n = m) :
    (H n).obj output ≅ (H m).obj (DG.DerivedCategory.Q.obj placedHead) :=
  (H n).mapIso fundamentalBraidDerivedHeadIso ≪≫ ((H 0).shiftIso (1 : ℤ) n m h).app _

/-- In native cohomological degree minus one the underlying additive group
is the target middle head. Its full target action is given by
`fundamentalBraidDerivedHeadIso`. -/
def fundamentalBraidDerivedHeadHMinusOne :
    (H (-1)).obj ((F).obj ((degreeZeroDerivedFunctor Kᵐᵒᵖ).obj braidSourceMiddleHead)) ≃+ braidTargetMiddleHead :=
  (shiftedReadout (-1) 0 (by decide)).toLinearEquiv.toAddEquiv.trans
    (DG.DerivedCategory.degreeZeroHomologyQEquiv placedHead InDegreeZero.mem_grading_zero (InDegreeZero.d_apply _)).symm

/-- The fundamental positive braid has zero cohomology in every other degree. -/
theorem fundamentalBraidDerivedHead_isZero (n : ℤ) (hn : n ≠ -1) :
    Limits.IsZero ((H n).obj ((F).obj ((degreeZeroDerivedFunctor Kᵐᵒᵖ).obj braidSourceMiddleHead))) := by
  let m := 1 + n
  have hm : m ≠ 0 := by dsimp [m]; omega
  have hc : Subsingleton (cocycles (InDegreeZero braidTargetMiddleHead) m) := by
    refine ⟨fun x y => Subtype.ext ?_⟩
    exact (((InDegreeZero.mem_grading_iff _).mp (mem_cocycles.mp x.2).1).resolve_left hm).trans
      (((InDegreeZero.mem_grading_iff _).mp (mem_cocycles.mp y.2).1).resolve_left hm).symm
  have hH : Subsingleton (cohomology placedHead m) :=
    (cohomology.mk_surjective (InDegreeZero braidTargetMiddleHead) m).subsingleton
  apply (shiftedReadout n m rfl).isZero_iff.mpr
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact (DG.DerivedCategory.cohomologyAddEquiv ℤ placedHead m).subsingleton_congr.mp hH

end Categorification.Stendhal.FundamentalCorner
