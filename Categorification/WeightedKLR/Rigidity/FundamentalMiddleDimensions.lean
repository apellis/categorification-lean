/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.FundamentalMiddleTor
import DG.K0.Field
import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-!
# Scalar Tor dimensions for the fundamental cup and cap

In Webster's fundamental two-red type A₁ block over the rationals, the
left and right simple middle characters have a one-dimensional Tor in
homological degrees zero and two. The shift of Definition 7.4 moves the
two scalar cohomology groups of the composite to degrees minus one and one.
-/

noncomputable section
namespace Categorification.Stendhal.FundamentalCorner
open CategoryTheory CategoryTheory.Limits Coevaluation DG
open scoped DG.DegreeZero
attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
universe v
local notation "T" => TensorProductAlgebra ℚ Q wt ({()} : Multiset Unit)
local notation "zeroObj" R:arg N:arg => DG.DerivedCategory.Q.obj (DGModuleCat.of R (InDegreeZero N))
local notation "line" => zeroObj ℚ ℚ
local notation "cap" => capBimoduleFunctor ℚ T MiddleCoefficient

variable [HasDerivedCategory.{v,0} ℚ]

private theorem scalarBiprod_finrank (n : ℤ) {X Y : DG.DerivedCategory.{v,0} ℚ}
    (hX : DG.DerivedCategory.HasFiniteCohomology ℚ X)
    (hY : DG.DerivedCategory.HasFiniteCohomology ℚ Y) :
    DG.DerivedCategory.finrankHomology ℚ n (X ⊞ Y) =
      DG.DerivedCategory.finrankHomology ℚ n X + DG.DerivedCategory.finrankHomology ℚ n Y := by
  let H := DG.DerivedCategory.homologyFunctor (A := ℚ) ℚ n
  let : Module.Finite ℚ (H.obj X) := hX.1 n
  let : Module.Finite ℚ (H.obj Y) := hY.1 n
  exact ((H.mapBiprod X Y ≪≫ ModuleCat.biprodIsoProd _ _).toLinearEquiv.finrank_eq).trans (Module.finrank_prod ..)

variable [CatModule.HasDerivedCategory.{v,0} (SingleObj ℚ)]
    [CatModule.HasDerivedCategory.{v,0} (SingleObj Tᵐᵒᵖ)] [HasDerivedCategory.{v,0} Tᵐᵒᵖ]

/-- Scalar Tor of the two middle simple coefficients at every homological degree. -/
theorem middleTor_finrank (n : ℤ) :
    DG.DerivedCategory.finrankHomology ℚ (-n)
      ((cap).obj (zeroObj Tᵐᵒᵖ (rIdeal middleIdem ⧸ middleCutTrace))) =
        if n = 0 ∨ n = 2 then 1 else 0 := by
  have hf : DG.DerivedCategory.HasFiniteCohomology ℚ line := DG.DerivedCategory.hasFiniteCohomology_Q_self
  rw [DG.DerivedCategory.finrankHomology_eq_of_iso ℚ _ middleAdjointCap_middleSimpleIso,
    scalarBiprod_finrank _ hf (DG.DerivedCategory.hasFiniteCohomology_shift ℚ hf (2 : ℤ)),
    DG.DerivedCategory.finrankHomology_shift]
  change (DG.DerivedCategory.finrankHomology ℚ (-n) (DG.DerivedCategory.Q.obj (DGModuleCat.of ℚ ℚ)) +
    DG.DerivedCategory.finrankHomology ℚ (2 + -n) (DG.DerivedCategory.Q.obj (DGModuleCat.of ℚ ℚ))) = _
  rw [DG.DerivedCategory.finrankHomology_Q_self, DG.DerivedCategory.finrankHomology_Q_self]
  split_ifs <;> omega

/-- The shifted RHom cup followed by its unshifted left adjoint has scalar cohomology in degrees ±1. -/
theorem middleCupCap_finrank (n : ℤ) :
    DG.DerivedCategory.finrankHomology ℚ n
      ((middleCup ⋙ (cap)).obj (DG.DerivedCategory.Q.obj (DGModuleCat.of ℚ ℚ))) =
        if n = -1 ∨ n = 1 then 1 else 0 := by
  have hf : DG.DerivedCategory.HasFiniteCohomology ℚ line := DG.DerivedCategory.hasFiniteCohomology_Q_self
  rw [DG.DerivedCategory.finrankHomology_eq_of_iso ℚ _ middleCupCap_fieldIso,
    scalarBiprod_finrank _ (DG.DerivedCategory.hasFiniteCohomology_shift ℚ hf (-1 : ℤ))
      (DG.DerivedCategory.hasFiniteCohomology_shift ℚ hf (1 : ℤ)),
    DG.DerivedCategory.finrankHomology_shift, DG.DerivedCategory.finrankHomology_shift]
  change (DG.DerivedCategory.finrankHomology ℚ (-1 + n) (DG.DerivedCategory.Q.obj (DGModuleCat.of ℚ ℚ)) +
    DG.DerivedCategory.finrankHomology ℚ (1 + n) (DG.DerivedCategory.Q.obj (DGModuleCat.of ℚ ℚ))) = _
  rw [DG.DerivedCategory.finrankHomology_Q_self, DG.DerivedCategory.finrankHomology_Q_self]
  split_ifs <;> omega

end Categorification.Stendhal.FundamentalCorner
