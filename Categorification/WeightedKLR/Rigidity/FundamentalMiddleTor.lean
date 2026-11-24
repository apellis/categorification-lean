/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.FundamentalMiddleCup
import Categorification.WeightedKLR.Rigidity.FundamentalMiddleResolution
import Categorification.WeightedKLR.Rigidity.FundamentalDerivedCircle

/-!
# The derived tensor of the fundamental middle characters

For the fundamental two-red type A₁ block over the rationals, the cap with
the left middle character sends the right middle head to two scalar lines
in cohomological degrees zero and minus two. The calculation uses the two
mixed differentials in the resolution of the cut (0,1).
-/

noncomputable section
namespace Categorification.Stendhal.FundamentalCorner
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Coevaluation DG
open scoped DG.DegreeZero
attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
universe v
local notation "T" => TensorProductAlgebra ℚ Q wt ({()} : Multiset Unit)
local notation "zeroObj" R:arg N:arg => DG.DerivedCategory.Q.obj (DGModuleCat.of R (InDegreeZero N))
local notation "line" => zeroObj ℚ ℚ
local notation "cap" => capBimoduleFunctor ℚ T MiddleCoefficient

variable [CatModule.HasDerivedCategory.{v,0} (SingleObj ℚ)]
    [CatModule.HasDerivedCategory.{v,0} (SingleObj Tᵐᵒᵖ)]
    [HasDerivedCategory.{v,0} ℚ] [HasDerivedCategory.{v,0} Tᵐᵒᵖ]

private instance : (cap).CommShift ℤ := by unfold capBimoduleFunctor; infer_instance
private instance : (cap).IsTriangulated := by unfold capBimoduleFunctor; infer_instance

private theorem exists_capTriangle (S : ShortComplex (ModuleCat.{0} Tᵐᵒᵖ)) (hs : S.ShortExact) :
    ∃ D : Triangle (DG.DerivedCategory.{v,0} ℚ), D ∈ distTriang _ ∧
      Nonempty (D.obj₁ ≅ (cap).obj (zeroObj Tᵐᵒᵖ S.X₁)) ∧
      Nonempty (D.obj₂ ≅ (cap).obj (zeroObj Tᵐᵒᵖ S.X₂)) ∧
      Nonempty (D.obj₃ ≅ (cap).obj (zeroObj Tᵐᵒᵖ S.X₃)) := by
  let := _root_.HasDerivedCategory.standard (ModuleCat.{0} Tᵐᵒᵖ)
  obtain ⟨D, hD, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ := exists_degreeZero_triangle_of_shortExact Tᵐᵒᵖ S hs
  exact ⟨(cap).mapTriangle.obj D, (cap).map_distinguished D hD, ⟨(cap).mapIso e₁⟩, ⟨(cap).mapIso e₂⟩, ⟨(cap).mapIso e₃⟩⟩

/-- The middle cap of the terminal simple is the scalar line in cohomological degree minus one. -/
def middleAdjointCap_terminalSimpleIso :
    (cap).obj (zeroObj Tᵐᵒᵖ (rIdeal terminalIdem ⧸ fundamentalCutTrace)) ≅ line⟦(1 : ℤ)⟧ :=
  Classical.choice <| by
    obtain ⟨D, hD, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ := exists_capTriangle fundamentalResolution fundamentalResolution_shortExact
    have hz : IsZero D.obj₂ := middleAdjointCap_terminal_isZero.of_iso e₂
    have : IsIso D.mor₃ := (D.isZero₂_iff_isIso₃ hD).mp hz
    exact ⟨e₃.symm ≪≫ asIso D.mor₃ ≪≫ (shiftFunctor _ (1 : ℤ)).mapIso (e₁ ≪≫ middleAdjointCap_middleIso)⟩

/-- The derived tensor of the right and left middle characters has one scalar
line in each of homological degrees zero and two. -/
def middleAdjointCap_middleSimpleIso :
    (cap).obj (zeroObj Tᵐᵒᵖ (rIdeal middleIdem ⧸ middleCutTrace)) ≅ line ⊞ line⟦(2 : ℤ)⟧ :=
  Classical.choice <| by
    let := _root_.HasDerivedCategory.standard (ModuleCat.{0} ℚ)
    obtain ⟨D, hD, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ := exists_capTriangle middleTraceSequence middleTraceSequence_shortExact
    let i₁ : D.obj₁ ≅ line⟦(1 : ℤ)⟧ := e₁ ≪≫ middleAdjointCap_terminalSimpleIso
    let i₂ : D.obj₂ ≅ line := e₂ ≪≫ middleAdjointCap_middleIso
    have hm : D.mor₁ = 0 := by
      rw [← cancel_epi i₁.inv, ← cancel_mono i₂.hom]
      simpa only [Category.assoc, comp_zero, zero_comp] using
        degreeZero_shift_one_hom_eq_zero ℚ (ModuleCat.of ℚ ℚ) (ModuleCat.of ℚ ℚ) (i₁.inv ≫ D.mor₁ ≫ i₂.hom)
    have hrot : D.rotate.mor₃ = 0 := by
      change -(shiftFunctor _ (1 : ℤ)).map D.mor₁ = 0
      rw [hm, Functor.map_zero, neg_zero]
    obtain ⟨split, _, _⟩ := exists_iso_binaryBiproduct_of_distTriang D.rotate (rot_of_distTriang _ hD) hrot
    let i₃ : D.obj₁⟦(1 : ℤ)⟧ ≅ line⟦(2 : ℤ)⟧ :=
      (shiftFunctor _ (1 : ℤ)).mapIso i₁ ≪≫ ((shiftFunctorAdd' _ (1 : ℤ) 1 2 (by decide)).app line).symm
    exact ⟨e₃.symm ≪≫ split ≪≫ biprod.mapIso i₂ i₃⟩

/-- Applying the unshifted cap to the shifted cup of Definition 7.4 gives
two scalar lines in cohomological degrees one and minus one. -/
def middleCupCap_fieldIso :
    (middleCup ⋙ (cap)).obj (DG.DerivedCategory.Q.obj (DGModuleCat.of ℚ ℚ)) ≅
      line⟦(-1 : ℤ)⟧ ⊞ line⟦(1 : ℤ)⟧ := by
  let shift := shiftFunctor (DG.DerivedCategory.{v,0} ℚ) (-1 : ℤ)
  let source := zeroObj Tᵐᵒᵖ (rIdeal middleIdem ⧸ middleCutTrace)
  let e₁ := (cap).mapIso middleCup_fieldIso
  let e₂ := ((cap).commShiftIso (-1 : ℤ)).app source
  let e₃ := shift.mapIso middleAdjointCap_middleSimpleIso
  let e₄ := shift.mapBiprod line (line⟦(2 : ℤ)⟧)
  let e₅ := biprod.mapIso (Iso.refl (shift.obj line))
    ((shiftFunctorAdd' (DG.DerivedCategory.{v,0} ℚ) (2 : ℤ) (-1) 1 (by decide)).app line).symm
  exact e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄ ≪≫ e₅

end Categorification.Stendhal.FundamentalCorner
