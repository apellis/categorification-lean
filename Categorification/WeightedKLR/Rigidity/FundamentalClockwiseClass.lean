/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.FundamentalQuantumTrace

/-!
# The compact scalar class of the clockwise fundamental circle

For the clockwise fundamental type A₁ circle of Webster, arXiv:1309.3796v2,
Proposition 7.13 and §8.1, both scalar summands have odd cohomological shifts.
Their classes give the ST signed quantum dimension in compact scalar K₀.
-/

noncomputable section
namespace Categorification.Stendhal.FundamentalCorner
open CategoryTheory CategoryTheory.Limits DG CatModule
open scoped DG.DegreeZero
attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts
local instance : InternalGrading ℚ := scalarInternalGrading ℚ
local instance : BigradedDGRing ℚ := scalarBigradedDGRing ℚ
universe v
variable [CatModule.HasDerivedCategory.{v,0} (WeightCategory ℚ)]
private abbrev ScalarDerived := CatModule.DerivedCategory.{v,0} (WeightCategory ℚ)
private abbrev scalarCompact := compactSubcategory.{0} ScalarDerived
local notation "line" j:arg => CatModule.DerivedCategory.Q.obj (representable (⟨j⟩ : WeightCategory ℚ))

/-- The compact scalar representable in internal weight j. -/
def compactScalarLine (j : ℤ) : scalarCompact.FullSubcategory :=
  ⟨line j, CatModule.DerivedCategory.isCompact_Q_obj (isCornerGenerator_representable (⟨j⟩ : WeightCategory ℚ))⟩

private def translatedScalar (j : ℤ) :
    (precomp (WeightCategory.shiftFunctor ℚ j)).obj (representable (⟨0⟩ : WeightCategory ℚ)) ≅
      representable (⟨-j⟩ : WeightCategory ℚ) := by
  have h (k : WeightCategory ℚ) : (k.as+j)-0=k.as-(-j) := by omega
  refine CatModule.isoMk (fun k => ?_) ?_ ?_ ?_
  · exact {
      toFun := fun x => ⟨x.val, (h k) ▸ x.property⟩
      invFun := fun y => ⟨y.val, (h k).symm ▸ y.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  · intro _ _ _; exact Iff.rfl
  · intro _ _; rfl
  · intro _ _ _ _; rfl

/-- In compact K₀ a scalar generator of weight −j is qʲ times the weight-zero generator. -/
theorem compactScalarLine_class (j : ℤ) :
    DG.K0.mk (compactScalarLine (-j)) = (LaurentPolynomial.T j : LaurentPolynomial ℤ) •
      DG.K0.mk (compactScalarLine 0) := by
  rw [CatModule.DerivedCategory.T_smul_mk_compact]
  apply DG.K0.mk_eq_of_iso_obj
  exact ((CatModule.DerivedCategory.QCompInternalShiftIso ℚ j).app _ ≪≫
    CatModule.DerivedCategory.Q.mapIso (translatedScalar j)).symm

private theorem isCompact_twoLines {X : ScalarDerived} (e : X ≅ (line (-1))⟦(-1 : ℤ)⟧ ⊞ (line 1)⟦(1 : ℤ)⟧) :
    IsCompact.{0} X := IsCompact.of_iso e ((isCompact_biprod_iff _ _).mpr
      ⟨(show IsCompact.{0} (line (-1)) from (compactScalarLine (-1)).property).shift (-1),
       (show IsCompact.{0} (line 1) from (compactScalarLine 1).property).shift 1⟩)

omit [CatModule.HasDerivedCategory.{v,0} (WeightCategory ℚ)] in
private theorem negatedWeightSum {M : Type*} [AddCommGroup M] [Module (LaurentPolynomial ℤ) M]
    (l r u : M) (hl : l = (LaurentPolynomial.T 1 : LaurentPolynomial ℤ) • u)
    (hr : r = (LaurentPolynomial.T (-1) : LaurentPolynomial ℤ) • u) :
    -l + -r = (-(LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) : LaurentPolynomial ℤ) • u := by
  rw [hl, hr, _root_.neg_smul, _root_.add_smul]
  abel

private theorem twoLineWeights :
    -DG.K0.mk (compactScalarLine (-1)) + -DG.K0.mk (compactScalarLine 1) =
      (-(LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) : LaurentPolynomial ℤ) • DG.K0.mk (compactScalarLine 0) := by
  apply negatedWeightSum (DG.K0.mk (compactScalarLine (-1))) (DG.K0.mk (compactScalarLine 1)) (DG.K0.mk (compactScalarLine 0))
  · exact compactScalarLine_class 1
  · simpa only [neg_neg] using compactScalarLine_class (-1)

private theorem twoLines_class {X : ScalarDerived} (e : X ≅ (line (-1))⟦(-1 : ℤ)⟧ ⊞ (line 1)⟦(1 : ℤ)⟧) :
    DG.K0.mk (⟨X, isCompact_twoLines e⟩ : scalarCompact.FullSubcategory) =
      (-(LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) : LaurentPolynomial ℤ) • DG.K0.mk (compactScalarLine 0) := by
  let A := compactScalarLine (-1)
  let B := compactScalarLine 1
  have he : X ≅ ((A⟦(-1 : ℤ)⟧) ⊞ (B⟦(1 : ℤ)⟧)).obj := by
    let a := ((scalarCompact.ι.commShiftIso (-1 : ℤ)).app A).symm
    let b := ((scalarCompact.ι.commShiftIso (1 : ℤ)).app B).symm
    exact e ≪≫ biprod.mapIso a b ≪≫ (scalarCompact.ι.mapBiprod (A⟦(-1 : ℤ)⟧) (B⟦(1 : ℤ)⟧)).symm
  have h : DG.K0.mk (⟨X, isCompact_twoLines e⟩ : scalarCompact.FullSubcategory) = DG.K0.mk ((A⟦(-1 : ℤ)⟧) ⊞ (B⟦(1 : ℤ)⟧)) :=
    DG.K0.mk_eq_of_iso_obj he
  rw [h, DG.K0.mk_biprod, DG.K0.mk_shift_neg_one, DG.K0.mk_shift_one]
  exact twoLineWeights

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
local notation "T" => TensorProductAlgebra ℚ Q wt ({()} : Multiset Unit)
local notation "G" => Graded.oppositeGrade (tensorProductGrade grading ({()} : Multiset Unit))
local instance : InternalGrading Tᵐᵒᵖ := gradedAlgebraInternalGrading G
local instance : BigradedDGRing Tᵐᵒᵖ := gradedAlgebraBigradedDGRing G
variable [CatModule.HasDerivedCategory.{v,0} (WeightCategory Tᵐᵒᵖ)]

/-- The derived clockwise circle on the field as a compact graded scalar object. -/
def compactFundamentalClockwiseCircle : scalarCompact.FullSubcategory :=
  ⟨(gradedMiddleCup ⋙ gradedFundamentalQuantumTrace).obj (line 0),
    isCompact_twoLines gradedFundamentalClockwiseCircleIso⟩

/-- The ST quantum trace of the fundamental circle has compact class
−(q + q⁻¹) times the ground scalar line. -/
theorem fundamentalClockwiseCircle_class :
    DG.K0.mk compactFundamentalClockwiseCircle =
      (-(LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) : LaurentPolynomial ℤ) •
        DG.K0.mk (compactScalarLine 0) :=
  twoLines_class gradedFundamentalClockwiseCircleIso

end Categorification.Stendhal.FundamentalCorner
