/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CapProjectives
import Categorification.WeightedKLR.Rigidity.FundamentalCupCap
import Categorification.WeightedKLR.Rigidity.FundamentalCupRegular
import Categorification.Algebra.DerivedTensorDegreeZero
import Categorification.Algebra.ProjectiveKProjective
import DG.Homotopy.ComparisonRing
import DG.Derived.Basic
import Mathlib.CategoryTheory.Triangulated.Adjunction
import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# The fundamental derived cap and its cup–evaluation coefficient

A terminal-character benchmark for Webster, arXiv:1309.3796v2, §7.1,
Definition 7.4. Over `ℚ`, the derived tensor of the terminal characters is `ℚ` in
degree zero. The mixed-crossing resolution reduces this to the two
idempotent images in the left coefficient.
-/

noncomputable section

namespace Categorification.Stendhal.FundamentalCorner

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  DG MulOpposite Coevaluation
open scoped DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

local notation "T" => TensorProductAlgebra ℚ Q wt ({()} : Multiset Unit)
local notation "L" => FundamentalCoefficient
local notation "CM" => OpBimodule T L
local notation "RP" f:arg => InDegreeZero (rIdeal f)
local notation "BT" f:arg => TensorProductOver Tᵐᵒᵖ (InDegreeZero CM) (RP f)

/-- The middle loading acts by zero on the left cap coefficient. -/
@[simp] theorem middleIdem_smul_fundamentalCoefficient (x : L) : middleIdem • x = 0 := by
  change terminalCharacter middleIdem * (show ℚ from x) = 0
  rw [terminalCharacter_middleIdem, zero_mul]

/-- The terminal loading acts as the identity on the left cap coefficient. -/
@[simp] theorem terminalIdem_smul_fundamentalCoefficient (x : L) : terminalIdem • x = x := by
  change terminalCharacter terminalIdem * (show ℚ from x) = _
  rw [terminalCharacter_terminalIdem, one_mul]

/-- Balancing the terminal coefficient with a loading projective gives the
image of that loading idempotent. -/
def coefficientLoadingTensorEquiv {f : T} (hf : IsIdempotentElem f) :
    BT f ≃ₗ[ℚ] fixSub ℚ L f :=
  Coevaluation.coefficientLoadingTensorEquiv ℚ T L hf

private theorem loadingIdem_idempotent (s : KLR.Seq (stendhalWeight 2 ({()} : Multiset Unit))) :
    IsIdempotentElem (project (StendhalAlgebraAllOrders.e s)) :=
  IsIdempotentElem.map (by simp [IsIdempotentElem, StendhalAlgebraAllOrders.e_mul_e]) project

universe v

variable [HasDerivedCategory.{v,0} ℚ] [HasDerivedCategory.{v,0} Tᵐᵒᵖ]

local notation "C" => DG.DerivedCategory.Q.obj
local notation "zeroObj" R:arg N:arg => C (DGModuleCat.of R (InDegreeZero N))

/-- The cap on a loading projective is its idempotent image in degree zero. -/
def fundamentalCap_loadingProjectiveIso {f : T} (hf : IsIdempotentElem f) :
    fundamentalCap.obj (zeroObj Tᵐᵒᵖ (rIdeal f)) ≅ zeroObj ℚ (fixSub ℚ L f) :=
  capFunctor_projectiveIso ℚ T L hf

private theorem fundamentalCap_middle_isZero :
    IsZero (fundamentalCap.obj (zeroObj Tᵐᵒᵖ (rIdeal middleIdem))) := by
  let e := fundamentalCap_loadingProjectiveIso (loadingIdem_idempotent middle)
  have : Subsingleton (fixSub ℚ L middleIdem) := ⟨fun x y => Subtype.ext (by
    have hx := (mem_fixSub.mp x.property)
    have hy := (mem_fixSub.mp y.property)
    rw [middleIdem_smul_fundamentalCoefficient] at hx hy
    exact hx.symm.trans hy)⟩
  let : Subsingleton (InDegreeZero (fixSub ℚ L middleIdem)) :=
    (InDegreeZero.equiv (fixSub ℚ L middleIdem)).injective.subsingleton
  exact (DG.DerivedCategory.Q.map_isZero (DGModuleCat.isZero_of_subsingleton
    (DGModuleCat.of ℚ (InDegreeZero (fixSub ℚ L middleIdem))))).of_iso e

private def fundamentalCap_terminalIso :
    fundamentalCap.obj (zeroObj Tᵐᵒᵖ (rIdeal terminalIdem)) ≅ zeroObj ℚ ℚ := by
  let e : fixSub ℚ L terminalIdem ≃ₗ[ℚ] ℚ :=
    LinearEquiv.ofBijective (fixSub ℚ L terminalIdem).subtype
      ⟨Subtype.val_injective, fun x => ⟨⟨x, terminalIdem_smul_fundamentalCoefficient x⟩, rfl⟩⟩
  let h : InDegreeZero (fixSub ℚ L terminalIdem) ≃ᵈᵍ[ℚ] InDegreeZero ℚ :=
    DGModuleEquiv.ofDegreeZero e
      (fun hx hn => ((InDegreeZero.mem_grading_iff _).mp hx).resolve_left hn)
      (InDegreeZero.d_apply _)
      (fun y => (InDegreeZero.mem_grading_iff _).mpr (Or.inl rfl))
      (InDegreeZero.d_apply _)
  exact fundamentalCap_loadingProjectiveIso (loadingIdem_idempotent terminal) ≪≫
    DG.DerivedCategory.Q.mapIso (DGModuleCat.isoOfDGModuleEquiv h)

section Comparison

omit [HasDerivedCategory.{v,0} ℚ] [HasDerivedCategory.{v,0} Tᵐᵒᵖ]

variable (R : Type) [Ring R] [HasDerivedCategory.{v,0} R]
    [_root_.HasDerivedCategory.{1} (ModuleCat.{0} R)]

local notation "Qₕ" => DG.DerivedCategory.Qh (A := R)
local notation "Fₕ" => DegreeZero.homotopyFunctor R
local notation "H" => Fₕ ⋙ _root_.DerivedCategory.Qh

private def comparison : DG.DerivedCategory.{v,0} R ⥤ _root_.DerivedCategory (ModuleCat.{0} R) :=
  Localization.lift H
    (fun _ _ f hf => Localization.inverts _root_.DerivedCategory.Qh
      (_root_.HomotopyCategory.quasiIso _ _) _ ((DegreeZero.mem_quasiIso_iff f).mp hf)) Qₕ

set_option backward.isDefEq.respectTransparency false in
private instance comparisonLifting :
    Localization.Lifting Qₕ (DG.HomotopyCategory.quasiIso R) H (comparison R) :=
  inferInstanceAs (Localization.Lifting _ _ _ (Localization.lift _ _ Qₕ))

private def comparisonFactors : Qₕ ⋙ comparison R ≅ H :=
  Localization.Lifting.iso Qₕ (DG.HomotopyCategory.quasiIso R) _ _

private def comparisonLocalizer : LocalizerMorphism (DG.HomotopyCategory.quasiIso R)
    (_root_.HomotopyCategory.quasiIso (ModuleCat.{0} R) (ComplexShape.up ℤ)) where
  functor := Fₕ
  map _ _ f hf := (DegreeZero.mem_quasiIso_iff f).mp hf

private instance : (comparisonLocalizer R).IsLocalizedEquivalence := by
  have : (comparisonLocalizer R).functor.IsEquivalence := DegreeZero.homotopyFunctor_isEquivalence
  apply LocalizerMorphism.IsLocalizedEquivalence.of_equivalence
  change _ ≤ (DG.HomotopyCategory.quasiIso R).map Fₕ
  have hq : DG.HomotopyCategory.quasiIso R =
      (_root_.HomotopyCategory.quasiIso (ModuleCat.{0} R) (ComplexShape.up ℤ)).inverseImage Fₕ := by
    apply MorphismProperty.ext
    intro A B φ
    exact DegreeZero.mem_quasiIso_iff φ
  rw [hq, MorphismProperty.map_inverseImage_eq_of_isEquivalence]

private instance : CatCommSq (comparisonLocalizer R).functor Qₕ
    _root_.DerivedCategory.Qh (comparison R) := ⟨(comparisonFactors R).symm⟩

private instance : (comparison R).IsEquivalence :=
  (comparisonLocalizer R).isEquivalence Qₕ _root_.DerivedCategory.Qh _

private instance : (comparison R).CommShift ℤ :=
  Functor.commShiftOfLocalization Qₕ (DG.HomotopyCategory.quasiIso R) ℤ H (comparison R)

private instance : NatTrans.CommShift (comparisonFactors R).hom ℤ :=
  NatTrans.commShift_iso_hom_of_localization _ _ _ _ _

private instance : (comparison R).IsTriangulated :=
  Functor.isTriangulated_of_precomp_iso (comparisonFactors R)

private def comparisonEquivalence :
    DG.DerivedCategory.{v,0} R ≌ _root_.DerivedCategory (ModuleCat.{0} R) :=
  (comparison R).asEquivalence

private instance : (comparisonEquivalence R).functor.CommShift ℤ :=
  (inferInstance : (comparison R).CommShift ℤ)

private instance : (comparisonEquivalence R).inverse.CommShift ℤ :=
  (comparisonEquivalence R).commShiftInverse ℤ

private instance : (comparisonEquivalence R).CommShift ℤ :=
  (comparisonEquivalence R).commShift_of_functor ℤ

private instance : (comparisonEquivalence R).IsTriangulated :=
  Equivalence.IsTriangulated.mk' (comparisonEquivalence R)
    (inferInstance : (comparison R).IsTriangulated)

private def comparisonDegreeZero (N : Type) [AddCommGroup N] [Module R N] :
    (comparison R).obj (zeroObj R N) ≅
      (_root_.DerivedCategory.singleFunctor (ModuleCat.{0} R) 0).obj (ModuleCat.of R N) := by
  let U := DGModuleCat.of R (InDegreeZero N)
  let K := (DegreeZero.complexFunctor R).obj U
  have hz (n : ℤ) (hn : n ≠ 0) : IsZero (K.X n) := by
    have : Subsingleton (DegreeZero.gradingSubmodule R U n) := ⟨fun x y => Subtype.ext (by
      rw [((InDegreeZero.mem_grading_iff N).mp x.2).resolve_left hn,
        ((InDegreeZero.mem_grading_iff N).mp y.2).resolve_left hn])⟩
    have : Subsingleton (K.X n) := this
    exact ModuleCat.isZero_of_subsingleton _
  let f := HomologicalComplex.mkHomToSingle (K := K) (j := 0)
    (ModuleCat.ofHom (Submodule.subtype _))
    (fun i hi => (hz i (by simp at hi; omega)).eq_of_src _ _)
  letI : ∀ n, IsIso (f.f n) := fun n => by
    by_cases hn : n = 0
    · subst hn
      rw [show f.f 0 = _ from HomologicalComplex.mkHomToSingle_f _ _]
      have : IsIso (ModuleCat.ofHom
          (Submodule.subtype (DegreeZero.gradingSubmodule R U 0))) :=
        (LinearEquiv.ofBijective (Submodule.subtype _) ⟨Subtype.val_injective,
          fun r => ⟨⟨r, (InDegreeZero.mem_grading_iff N).mpr (Or.inl rfl)⟩, rfl⟩⟩).toModuleIso.isIso_hom
      exact IsIso.comp_isIso' this inferInstance
    · exact ⟨0, (hz n hn).eq_of_src _ _,
        (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn).eq_of_src _ _⟩
  have hf : IsIso f := HomologicalComplex.Hom.isIso_of_components f
  exact (comparisonFactors R).app ((DG.HomotopyCategory.quotient R).obj U) ≪≫
    _root_.DerivedCategory.Qh.mapIso ((DegreeZero.homotopyFunctorFactors R).app U) ≪≫
    (_root_.DerivedCategory.quotientCompQhIso (ModuleCat.{0} R)).app K ≪≫
    _root_.DerivedCategory.Q.mapIso (@asIso _ _ _ _ f hf)

/-- A short exact sequence of ordinary modules gives a distinguished triangle on
their degree-zero dg modules. This transports the standard derived-category triangle
across the comparison with dg modules over a degree-zero ring. -/
theorem exists_degreeZero_triangle_of_shortExact (S : ShortComplex (ModuleCat.{0} R)) (hs : S.ShortExact) :
    ∃ D : Triangle (DG.DerivedCategory.{v,0} R), D ∈ distTriang _ ∧
      Nonempty (D.obj₁ ≅ zeroObj R S.X₁) ∧ Nonempty (D.obj₂ ≅ zeroObj R S.X₂) ∧
      Nonempty (D.obj₃ ≅ zeroObj R S.X₃) := by
  let E := comparisonEquivalence R
  let iso (N : ModuleCat.{0} R) :
      E.inverse.obj ((_root_.DerivedCategory.singleFunctor (ModuleCat.{0} R) 0).obj N) ≅ zeroObj R N :=
    E.inverse.mapIso (comparisonDegreeZero R N).symm ≪≫ E.unitIso.symm.app _
  exact ⟨E.inverse.mapTriangle.obj hs.singleTriangle, E.inverse.map_distinguished _ hs.singleTriangle_distinguished,
    ⟨iso S.X₁⟩, ⟨iso S.X₂⟩, ⟨iso S.X₃⟩⟩

/-- Every morphism from a degree-zero module shifted by one to a degree-zero
module vanishes, by orthogonality in the standard t-structure. -/
theorem degreeZero_shift_one_hom_eq_zero (M N : ModuleCat.{0} R)
    (f : (zeroObj R M)⟦(1 : ℤ)⟧ ⟶ zeroObj R N) : f = 0 := by
  let F := comparison R
  let s := _root_.DerivedCategory.singleFunctor (ModuleCat.{0} R) 0
  let e₁ : F.obj ((zeroObj R M)⟦(1 : ℤ)⟧) ≅ (s.obj M)⟦(1 : ℤ)⟧ :=
    (F.commShiftIso (1 : ℤ)).app _ ≪≫ (shiftFunctor _ (1 : ℤ)).mapIso (comparisonDegreeZero R M)
  let e₂ : F.obj (zeroObj R N) ≅ s.obj N := comparisonDegreeZero R N
  let t : CategoryTheory.Triangulated.TStructure (_root_.DerivedCategory (ModuleCat.{0} R)) :=
    _root_.DerivedCategory.TStructure.t
  have hz : e₁.inv ≫ F.map f ≫ e₂.hom = 0 :=
    t.zero_of_isLE_of_isGE _ (-1) 0 (by decide)
      (t.isLE_shift (s.obj M) 0 1 (-1) (by decide)) (inferInstanceAs ((s.obj N).IsGE 0))
  apply F.map_injective
  rw [Functor.map_zero, ← cancel_epi e₁.inv, ← cancel_mono e₂.hom]
  simpa only [Category.assoc, comp_zero, zero_comp] using hz

end Comparison

/-- The derived cap of the unshifted right simple for the two fundamental
type A₁ factors is the ground field concentrated in cohomological degree
zero. The middle projective of its two-term resolution has zero cap. -/
def fundamentalCap_terminalSimpleIso :
    fundamentalCap.obj (zeroObj Tᵐᵒᵖ (rIdeal terminalIdem ⧸ fundamentalCutTrace)) ≅ zeroObj ℚ ℚ := by
  let := _root_.HasDerivedCategory.standard (ModuleCat.{0} Tᵐᵒᵖ)
  let E := comparisonEquivalence Tᵐᵒᵖ
  let : fundamentalCap.CommShift ℤ := (inferInstance : (capFunctor ℚ T L).CommShift ℤ)
  let : fundamentalCap.IsTriangulated := (inferInstance : (capFunctor ℚ T L).IsTriangulated)
  let G := E.inverse ⋙ fundamentalCap
  let tri := fundamentalResolution_shortExact.singleTriangle
  let out := G.mapTriangle.obj tri
  have hdist : out ∈ distTriang _ :=
    G.map_distinguished tri fundamentalResolution_shortExact.singleTriangle_distinguished
  let imageIso (N : Type) [AddCommGroup N] [Module Tᵐᵒᵖ N] :
      G.obj ((_root_.DerivedCategory.singleFunctor (ModuleCat.{0} Tᵐᵒᵖ) 0).obj
        (ModuleCat.of Tᵐᵒᵖ N)) ≅ fundamentalCap.obj (zeroObj Tᵐᵒᵖ N) :=
    fundamentalCap.mapIso (E.inverse.mapIso (comparisonDegreeZero Tᵐᵒᵖ N).symm ≪≫
      E.unitIso.symm.app _)
  have hz : IsZero out.obj₁ := fundamentalCap_middle_isZero.of_iso (imageIso (rIdeal middleIdem))
  have : IsIso out.mor₂ := (out.isZero₁_iff_isIso₂ hdist).mp hz
  exact (imageIso (rIdeal terminalIdem ⧸ fundamentalCutTrace)).symm ≪≫
    (asIso out.mor₂).symm ≪≫ imageIso (rIdeal terminalIdem) ≪≫ fundamentalCap_terminalIso

private abbrev terminalSimpleDG :=
  zeroObj Tᵐᵒᵖ (rIdeal terminalIdem ⧸ fundamentalCutTrace)

private instance fundamentalCapShift : fundamentalCap.CommShift ℤ :=
  (inferInstance : (capFunctor ℚ T L).CommShift ℤ)

private def functorShiftObjIso {C₁ C₂ : Type*} [Category C₁] [Category C₂]
    [HasShift C₁ ℤ] [HasShift C₂ ℤ] (F : C₁ ⥤ C₂) [F.CommShift ℤ]
    (n : ℤ) (Y : C₁) :
    F.obj ((shiftFunctor C₁ n).obj Y) ≅ (shiftFunctor C₂ n).obj (F.obj Y) :=
  (F.commShiftIso n).app Y

/-- The terminal-character cup followed by the terminal-character cap gives
the scalar line shifted by minus one on the ground field. The shift uses
the convention of Webster, arXiv:1309.3796v2, Definition 7.4. -/
def fundamentalCupEvaluationRegularIso :
    (fundamentalCup ⋙ fundamentalCap).obj (C (DGModuleCat.of ℚ ℚ)) ≅
      (shiftFunctor (DG.DerivedCategory.{v,0} ℚ) (-1)).obj (zeroObj ℚ ℚ) := by
  let h := (shiftFunctor (DG.DerivedCategory.{v,0} ℚ) (-1)).mapIso fundamentalCap_terminalSimpleIso
  exact fundamentalCap.mapIso fundamentalCupRegularIso ≪≫ functorShiftObjIso fundamentalCap (-1) terminalSimpleDG ≪≫ h

end Categorification.Stendhal.FundamentalCorner
