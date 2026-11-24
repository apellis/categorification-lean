/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.FundamentalMiddleHead
import Categorification.WeightedKLR.Rigidity.GradedFundamentalCupCap

/-!
# The graded cup at the fundamental middle cut

Webster, arXiv:1309.3796v2, §7.1, Lemma 7.3, Definition 7.4 and
Proposition 7.5, for two fundamental weights of type A₁ over the rationals.
The scalar module supported on the middle loading has one weight-zero
generator. Applying the cup to the field gives this character with the
internal shift one and the cohomological shift minus one.
-/

noncomputable section
namespace Categorification.Stendhal.FundamentalCorner
open CategoryTheory DG MulOpposite Coevaluation
open scoped DG.DegreeZero
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

local notation "T" => TensorProductAlgebra ℚ Q wt ({()} : Multiset Unit)
local notation "G" => Graded.oppositeGrade (tensorProductGrade grading ({()} : Multiset Unit))
local instance : InternalGrading Tᵐᵒᵖ := gradedAlgebraInternalGrading G
local instance : BigradedDGRing Tᵐᵒᵖ := gradedAlgebraBigradedDGRing G
local instance : InternalGrading ℚ := scalarInternalGrading ℚ
local instance : BigradedDGRing ℚ := scalarBigradedDGRing ℚ

/-- The scalar character of the middle-cut head on the opposite diagram algebra. -/
def gradedMiddleCharacter : Tᵐᵒᵖ →ᵈᵍ+* ℚ := oppositeScalarCharacter middleCharacter.toRingHom

@[simp] theorem gradedMiddleCharacter_op (a : T) :
    gradedMiddleCharacter (op a) = middleCharacter a := rfl

/-- The action on the middle-cut head respects the diagram grading. -/
theorem gradedMiddleCharacter_mem_weight {j : ℤ} {a : Tᵐᵒᵖ} (ha : a ∈ wgrading j) :
    gradedMiddleCharacter a ∈ wgrading j := by
  refine oppositeScalarCharacter_mem_weight middleCharacter.toRingHom (fun hj hz => ?_) ha
  exact FirstWeight.boundaryCharacter_eq_zero_of_ne_grade Q wt grading
    (by intro r; simp [wt]) middle (by unfold IsRedOrdered; decide +kernel)
    (by unfold IsViolated; decide +kernel) hj hz

local notation "Fχ" => WeightCategory.mapFunctor gradedMiddleCharacter gradedMiddleCharacter_mem_weight
local notation "ground" => CatModule.representable (⟨0⟩ : WeightCategory ℚ)

/-- The unshifted graded middle character as a module over the diagram weight category. -/
def gradedMiddleSimple : CatModule.{0} (WeightCategory Tᵐᵒᵖ) := (CatModule.precomp Fχ).obj ground

/-- The action on the scalar coordinate of the graded simple is precisely the middle loading character. -/
theorem gradedMiddleSimple_act {j l : WeightCategory Tᵐᵒᵖ} (a : j ⟶ l) (z : gradedMiddleSimple.obj j) :
    ((gradedMiddleSimple.act a) z).val = middleCharacter a.val.unop * z.val := rfl

/-- Away from its weight-zero generator the unshifted character is zero. -/
theorem gradedMiddleSimple_subsingleton (j : ℤ) (hj : j ≠ 0) : Subsingleton (gradedMiddleSimple.obj ⟨j⟩) := by
  refine ⟨fun x y => Subtype.ext ?_⟩
  have hx := (InDegreeZero.ring_mem_grading_iff (R := ℚ)).mp x.property
  have hy := (InDegreeZero.ring_mem_grading_iff (R := ℚ)).mp y.property
  have h : j - 0 ≠ 0 := by simpa using hj
  exact (hx.resolve_left h).trans (hy.resolve_left h).symm

/-- The generator at internal degree zero is a scalar line. -/
def gradedMiddleSimple_zeroEquiv : gradedMiddleSimple.obj ⟨0⟩ ≃+ ℚ where
  toFun x := x.val
  invFun x := ⟨x, (InDegreeZero.ring_mem_grading_iff (R := ℚ)).mpr (Or.inl (by decide))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The weight-zero space of the graded simple identifies with the right
simple quotient by the smaller-cut trace in Webster, Lemma 7.3. -/
def gradedMiddleSimple_headEquiv :
    (rIdeal middleIdem ⧸ middleCutTrace) ≃+ gradedMiddleSimple.obj ⟨0⟩ :=
  middleQuotientDualEquiv.toAddEquiv.trans
    ((LinearMap.ringLmapEquivSelf ℚ ℚ ℚ).toAddEquiv.trans gradedMiddleSimple_zeroEquiv.symm)

/-- Under the identification with the right simple quotient, every diagram acts
on its weight-zero coordinate through the middle character. -/
theorem gradedMiddleSimple_headEquiv_smul (a : Tᵐᵒᵖ) (x : rIdeal middleIdem ⧸ middleCutTrace) :
    (gradedMiddleSimple_headEquiv (a • x)).val =
      middleCharacter a.unop * (gradedMiddleSimple_headEquiv x).val := by
  change (show Module.Dual ℚ MiddleCoefficient from middleQuotientDualEquiv (a • x)) (1 : ℚ) =
    middleCharacter a.unop * (show Module.Dual ℚ MiddleCoefficient from middleQuotientDualEquiv x) (1 : ℚ)
  rw [map_smul]
  exact middleDual_smul_apply a.unop _ _

/-- The middle coefficient after the internal shift of Definition 7.4. -/
def normalizedMiddleSimple : CatModule.{0} (WeightCategory Tᵐᵒᵖ) :=
  (CatModule.precomp (WeightCategory.shiftFunctor Tᵐᵒᵖ 1)).obj gradedMiddleSimple

/-- With the convention M⟨1⟩ at j is M at j+1, the generator lies at weight minus one. -/
def normalizedMiddleSimple_line : normalizedMiddleSimple.obj ⟨-1⟩ ≃+ ℚ := gradedMiddleSimple_zeroEquiv

theorem normalizedMiddleSimple_subsingleton (j : ℤ) (hj : j ≠ -1) :
    Subsingleton (normalizedMiddleSimple.obj ⟨j⟩) :=
  gradedMiddleSimple_subsingleton (j + 1) (by omega)

universe v
variable [CatModule.HasDerivedCategory.{v,0} (WeightCategory ℚ)]
  [CatModule.HasDerivedCategory.{v,0} (WeightCategory Tᵐᵒᵖ)]

/-- The normalized middle-character cup of Webster, Definition 7.4. -/
def gradedMiddleCup :=
  shiftedCharacterCup gradedMiddleCharacter gradedMiddleCharacter_mem_weight 1 (-1)

/-- The middle-character cap of Webster, Definition 7.4. -/
def gradedMiddleCap := characterCap gradedMiddleCharacter gradedMiddleCharacter_mem_weight

/-- The graded cap is left adjoint to restriction along the unshifted middle character. -/
def gradedMiddleCapCupAdjunction :
    gradedMiddleCap ⊣ characterCup gradedMiddleCharacter gradedMiddleCharacter_mem_weight :=
  characterCapCupAdjunction _ _

/-- On the scalar representable the normalized graded cup gives the internally
and cohomologically shifted middle character. -/
def gradedMiddleCup_fieldIso :
    gradedMiddleCup.obj (CatModule.DerivedCategory.Q.obj ground) ≅
      (CatModule.DerivedCategory.Q.obj normalizedMiddleSimple)⟦(-1 : ℤ)⟧ := by
  let e := characterCupObjIso gradedMiddleCharacter gradedMiddleCharacter_mem_weight ground
  let es := (CatModule.DerivedCategory.QCompInternalShiftIso Tᵐᵒᵖ 1).app gradedMiddleSimple
  exact (shiftFunctor _ (-1 : ℤ)).mapIso ((CatModule.DerivedCategory.internalShift Tᵐᵒᵖ 1).mapIso e ≪≫ es)

end Categorification.Stendhal.FundamentalCorner
