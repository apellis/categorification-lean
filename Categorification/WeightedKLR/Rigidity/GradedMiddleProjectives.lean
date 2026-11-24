/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.GradedMiddleCupCap
import DG.Category.Derived.InductionCell

/-!
# The graded fundamental cap on its loading projectives

Webster, arXiv:1309.3796v2, §7.1, Proposition 7.5. The unshifted graded
cap at the fundamental middle cut sends the middle loading projective
to the scalar line in weight zero and the terminal projective to zero.
The proof applies induction to the loading idempotents in the weight category.
-/

namespace Categorification.Stendhal.FundamentalCorner
open CategoryTheory DG CatModule DGCategory
noncomputable section
universe v
variable {C D : Type} [Category.{0} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [DGCategory C]
    [Category.{0} D] [Preadditive D] [∀ X Y : D, DGAddCommGroup (X ⟶ Y)] [DGCategory D]

private def liftedCorner {X : C} (e : Idempotent X) :
    Retract (ulift.{0} (corner e)) (ulift.{0} (representable X)) where
  i := uliftMap (cornerRetract e).i
  r := uliftMap (cornerRetract e).r
  retract := by rw [← uliftMap_comp, (cornerRetract e).retract, uliftMap_id]

private theorem liftedCorner_projection {X : C} (e : Idempotent X) :
    (liftedCorner e).r ≫ (liftedCorner e).i = uliftMap.{0} (cornerIdem e) :=
  (uliftMap_comp (cornerRetract e).r (cornerRetract e).i).symm

variable (F : C ⥤ D) [F.Additive] [F.IsDGFunctor]

private def induceCorner {X : C} (e : Idempotent X) :
    (CatModule.induction.{0} F).obj (ulift.{0} (corner e)) ≅ ulift.{0} (corner (e.map F)) := by
  let I := CatModule.induction.{0} F
  let a := liftedCorner e
  let b := liftedCorner (e.map F)
  let σ : I.obj (ulift.{0} (representable X)) ≅ ulift.{0} (representable (F.obj X)) :=
    inductionULiftRepresentableIso.{0} F X
  refine isoOfRetractOfEq (I.map a.i ≫ σ.hom) (σ.inv ≫ I.map a.r) b.i b.r ?_ b.retract ?_
  · rw [Category.assoc, Iso.hom_inv_id_assoc, ← I.map_comp, a.retract, CategoryTheory.Functor.map_id]
  · have h : I.map (a.r ≫ a.i) ≫ σ.hom = σ.hom ≫ (b.r ≫ b.i) := by
      rw [liftedCorner_projection, liftedCorner_projection]
      exact induction_map_uliftMap_cornerIdem F e
    rw [Category.assoc, ← Functor.map_comp_assoc, h, Iso.inv_hom_id_assoc]

variable [CatModule.HasDerivedCategory.{v,0} C] [CatModule.HasDerivedCategory.{v,0} D]

private def inducedLoadingProjectiveIso {X : C} (e : Idempotent X) :
    (CatModule.DerivedCategory.induction F).obj (CatModule.DerivedCategory.Q.obj (ulift.{0} (corner e))) ≅
      CatModule.DerivedCategory.Q.obj (ulift.{0} (corner (e.map F))) :=
  (CatModule.DerivedCategory.inductionObjIso F (isCornerGenerator_corner e).ulift.isKProjective).symm ≪≫
    CatModule.DerivedCategory.Q.mapIso (induceCorner F e)
private def uliftSelfIso (M : CatModule.{0} D) : ulift.{0} M ≅ M where
  hom := { app := fun _ => ULift.downAddHom _
           map_mem' := fun h => h
           map_d' := fun _ => rfl
           map_smul' := fun _ _ => rfl }
  inv := { app := fun _ => ULift.upAddHom _
           map_mem' := fun h => h
           map_d' := fun _ => rfl
           map_smul' := fun _ _ => rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

private def cornerIsoOfId {X : D} (e : Idempotent X) (he : e.val = 𝟙 X) :
    ulift.{0} (corner e) ≅ representable X := by
  let t := liftedCorner e
  have h : cornerIdem e = 𝟙 _ := by
    ext Y z
    change e.val ≫ (z : X ⟶ Y) = (z : X ⟶ Y)
    rw [he]
    exact Category.id_comp _
  refine (show ulift.{0} (corner e) ≅ ulift.{0} (representable X) from
    ⟨t.i, t.r, t.retract, ?_⟩) ≪≫ uliftSelfIso _
  rw [liftedCorner_projection, h, uliftMap_id]

omit [CatModule.HasDerivedCategory.{v,0} D] in
private theorem cornerIsZeroOfZero {X : D} (e : Idempotent X) (he : e.val = 0) :
    Limits.IsZero (ulift.{0} (corner e)) := by
  let : ∀ Y, Subsingleton ((ulift.{0} (corner e)).obj Y) := fun Y => ⟨fun x y => by
    apply ULift.ext
    apply Subtype.ext
    have hz (z : (corner e).obj Y) : (z.val : X ⟶ Y) = 0 := by
      have hz' : e.val ≫ (z.val : X ⟶ Y) = z.val := z.property
      exact hz'.symm.trans ((congrArg (· ≫ (z.val : X ⟶ Y)) he).trans Limits.zero_comp)
    exact (hz x.down).trans (hz y.down).symm⟩
  exact isZero_of_subsingleton _

end

noncomputable section
open CategoryTheory DG MulOpposite Coevaluation CatModule DGCategory
open scoped DG.DegreeZero
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
local notation "T" => TensorProductAlgebra ℚ Q wt ({()} : Multiset Unit)
local notation "G" => Graded.oppositeGrade (tensorProductGrade grading ({()} : Multiset Unit))
local notation "μ" => stendhalWeight 2 ({()} : Multiset Unit)
local instance : InternalGrading Tᵐᵒᵖ := gradedAlgebraInternalGrading G
local instance : BigradedDGRing Tᵐᵒᵖ := gradedAlgebraBigradedDGRing G
local instance : InternalGrading ℚ := scalarInternalGrading ℚ
local instance : BigradedDGRing ℚ := scalarBigradedDGRing ℚ
local notation "Fχ" => WeightCategory.mapFunctor gradedMiddleCharacter gradedMiddleCharacter_mem_weight
local notation "wzero" => (⟨0⟩ : WeightCategory Tᵐᵒᵖ)
local notation "ground" => representable (⟨0⟩ : WeightCategory ℚ)

/-- The degree-zero diagram projector at the generating weight j. -/
def gradedLoadingIdempotentAt (s : KLR.Seq μ) (hs : IsRedOrdered s) (j : ℤ) :
    Idempotent (⟨j⟩ : WeightCategory Tᵐᵒᵖ) where
  val := WeightCategory.homMk (op (TensorProductAlgebra.mk Q wt {()} (StendhalAlgebra.e s hs))) (by
    change _ ∈ G (j-j)
    rw [sub_self]
    exact mk_e_mem_tensorProductGrade grading {()} s hs)
  mem_cocycles := ⟨WeightCategory.mem_grading_iff.mpr ((InDegreeZero.ring_mem_grading_iff (R := Tᵐᵒᵖ)).mpr
    (Or.inl rfl)), WeightCategory.hom_ext (InDegreeZero.ring_d_apply
      (op (TensorProductAlgebra.mk Q wt {()} (StendhalAlgebra.e s hs))))⟩
  comp_self := WeightCategory.hom_ext (congrArg op (isIdempotentElem_mk_e (Q := Q) (Λ := wt) s hs).eq)

/-- The degree-zero diagram projector for the loading at internal weight zero. -/
abbrev gradedLoadingIdempotent (s : KLR.Seq μ) (hs : IsRedOrdered s) : Idempotent wzero :=
  gradedLoadingIdempotentAt s hs 0

private theorem projectedCharacter (s : KLR.Seq μ) (hs : IsRedOrdered s) (j : ℤ) :
    ((gradedLoadingIdempotentAt s hs j).map Fχ).val.val = if s = middle then (1 : ℚ) else 0 := by
  change middleCharacter (TensorProductAlgebra.mk Q wt {()} (StendhalAlgebra.e s hs)) = _
  simp only [middleCharacter, FirstWeight.boundaryCharacter_e]

/-- The diagram projective with its generator placed at internal weight j. -/
def shiftedLoadingModule (s : KLR.Seq μ) (hs : IsRedOrdered s) (j : ℤ) : CatModule.{0} (WeightCategory Tᵐᵒᵖ) :=
  corner (gradedLoadingIdempotentAt s hs j)

variable [CatModule.HasDerivedCategory.{v,0} (WeightCategory ℚ)]
  [CatModule.HasDerivedCategory.{v,0} (WeightCategory Tᵐᵒᵖ)]

/-- The graded loading projective as a summand of the weight-zero representable. -/
def gradedLoadingProjective (s : KLR.Seq μ) (hs : IsRedOrdered s) :
    CatModule.DerivedCategory.{v,0} (WeightCategory Tᵐᵒᵖ) :=
  CatModule.DerivedCategory.Q.obj (ulift.{0} (corner (gradedLoadingIdempotent s hs)))

/-- The graded cap on the (0,1) loading projective is the weight-zero scalar line. -/
def gradedMiddleCap_middleIso :
    gradedMiddleCap.obj (gradedLoadingProjective middle (by unfold IsRedOrdered; decide +kernel)) ≅
      CatModule.DerivedCategory.Q.obj ground := by
  let e := gradedLoadingIdempotent middle (by unfold IsRedOrdered; decide +kernel)
  have h : (e.map Fχ).val = 𝟙 _ := WeightCategory.hom_ext
    ((projectedCharacter middle _ 0).trans (ite_eq_left rfl))
  exact inducedLoadingProjectiveIso Fχ e ≪≫ CatModule.DerivedCategory.Q.mapIso (cornerIsoOfId _ h)

/-- The graded cap annihilates the terminal loading projective (0,0). -/
theorem gradedMiddleCap_terminal_isZero :
    Limits.IsZero (gradedMiddleCap.obj (gradedLoadingProjective terminal terminal_ordered)) := by
  let e := gradedLoadingIdempotent terminal terminal_ordered
  have h : (e.map Fχ).val = 0 := WeightCategory.hom_ext
    ((projectedCharacter terminal _ 0).trans (ite_eq_right (by decide +kernel)))
  exact (CategoryTheory.Functor.map_isZero CatModule.DerivedCategory.Q (cornerIsZeroOfZero _ h)).of_iso
    (inducedLoadingProjectiveIso Fχ e)

/-- On a middle projective generated at weight j the cap gives the scalar
representable at the same weight. -/
def gradedMiddleCap_shiftedMiddleIso (j : ℤ) :
    gradedMiddleCap.obj (CatModule.DerivedCategory.Q.obj
      (shiftedLoadingModule middle (by unfold IsRedOrdered; decide +kernel) j)) ≅
      CatModule.DerivedCategory.Q.obj (representable (⟨j⟩ : WeightCategory ℚ)) := by
  let e := gradedLoadingIdempotentAt middle (by unfold IsRedOrdered; decide +kernel) j
  have h : (e.map Fχ).val = 𝟙 _ := WeightCategory.hom_ext
    ((projectedCharacter middle _ j).trans (ite_eq_left rfl))
  exact gradedMiddleCap.mapIso (CatModule.DerivedCategory.Q.mapIso (uliftSelfIso (corner e)).symm) ≪≫
    inducedLoadingProjectiveIso Fχ e ≪≫ CatModule.DerivedCategory.Q.mapIso (cornerIsoOfId _ h)

/-- The cap kills the terminal projective at every generating weight. -/
theorem gradedMiddleCap_shiftedTerminal_isZero (j : ℤ) :
    Limits.IsZero (gradedMiddleCap.obj (CatModule.DerivedCategory.Q.obj
      (shiftedLoadingModule terminal terminal_ordered j))) := by
  let e := gradedLoadingIdempotentAt terminal terminal_ordered j
  have h : (e.map Fχ).val = 0 := WeightCategory.hom_ext
    ((projectedCharacter terminal _ j).trans (ite_eq_right (by decide +kernel)))
  exact (CategoryTheory.Functor.map_isZero CatModule.DerivedCategory.Q (cornerIsZeroOfZero _ h)).of_iso
    (gradedMiddleCap.mapIso (CatModule.DerivedCategory.Q.mapIso (uliftSelfIso (corner e)).symm) ≪≫ inducedLoadingProjectiveIso Fχ e)

end
end Categorification.Stendhal.FundamentalCorner
