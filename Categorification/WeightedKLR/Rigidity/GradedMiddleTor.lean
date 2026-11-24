/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.GradedMiddleComplex
import Categorification.WeightedKLR.Rigidity.WeightModuleExactTriangle
import DG.Category.Derived.Compact

/-!
# The bigraded scalar tensor of the fundamental middle characters

For the fundamental two-red type A₁ block of Webster, arXiv:1309.3796v2,
§7.1, the derived cap kills the middle term of the projective resolution.
The surviving projectives give one scalar each, in internal degrees zero and
two before the normalization of Definition 7.4.
-/

noncomputable section
namespace Categorification.Stendhal.FundamentalCorner
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated DG CatModule MulOpposite
open scoped DG.DegreeZero
attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
local notation "T" => TensorProductAlgebra ℚ Q wt ({()} : Multiset Unit)
local notation "G" => Graded.oppositeGrade (tensorProductGrade grading ({()} : Multiset Unit))
local notation "μ" => stendhalWeight 2 ({()} : Multiset Unit)
local instance : InternalGrading Tᵐᵒᵖ := gradedAlgebraInternalGrading G
local instance : BigradedDGRing Tᵐᵒᵖ := gradedAlgebraBigradedDGRing G
local instance : InternalGrading ℚ := scalarInternalGrading ℚ
local instance : BigradedDGRing ℚ := scalarBigradedDGRing ℚ

private theorem orderedMiddle : IsRedOrdered middle := by unfold IsRedOrdered; decide +kernel
local notation "P₀" => shiftedLoadingModule middle orderedMiddle 0
local notation "P₁" => shiftedLoadingModule terminal terminal_ordered 1
local notation "P₂" => shiftedLoadingModule middle orderedMiddle 2
private abbrev syzygy := CatModule.Hom.range gradedMiddleD₁

private def toSyzygy : P₁ ⟶ syzygy.toCatModule := CatSubmodule.codRestrict (S := syzygy) gradedMiddleD₁ (fun _ x => ⟨x, rfl⟩)

private theorem firstSequence_exact :
    gradedMiddleD₂ ≫ toSyzygy = 0 ∧
      (∀ k, Function.Exact (gradedMiddleD₂.app k) (toSyzygy.app k)) ∧
      (∀ k, Function.Surjective (toSyzygy.app k)) := by
  refine ⟨CatModule.hom_ext (fun k x => Subtype.ext (((gradedMiddleComplex_exact k).2.1 _).mpr ⟨x, rfl⟩)), ?_, ?_⟩
  · intro k x
    exact ⟨fun h => ((gradedMiddleComplex_exact k).2.1 x).mp (congrArg Subtype.val h),
      fun h => Subtype.ext (((gradedMiddleComplex_exact k).2.1 x).mpr h)⟩
  · rintro k ⟨x, y, hy⟩
    exact ⟨y, Subtype.ext hy⟩

private theorem secondSequence_exact :
    syzygy.subtype ≫ gradedMiddleAugmentation = 0 ∧
      ∀ k, Function.Exact (syzygy.subtype.app k) (gradedMiddleAugmentation.app k) := by
  refine ⟨CatModule.hom_ext (fun k x => ((gradedMiddleComplex_exact k).2.2.1 _).mpr x.property), ?_⟩
  intro k x
  constructor
  · intro h
    exact ⟨⟨x, ((gradedMiddleComplex_exact k).2.2.1 x).mp h⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ((gradedMiddleComplex_exact k).2.2.1 _).mpr x.property

private def translateCorner {R : Type} [Ring R] [DGAddCommGroup R] [DGRing R]
    [InternalGrading R] [BigradedDGRing R] (j t : ℤ)
    (e : DGCategory.Idempotent (⟨j⟩ : WeightCategory R))
    (e' : DGCategory.Idempotent (⟨j-t⟩ : WeightCategory R)) (he : e'.val.val = e.val.val) :
    (CatModule.precomp (WeightCategory.shiftFunctor R t)).obj (corner e) ≅ corner e' := by
  have hw (l : WeightCategory R) : (l.as+t)-j=l.as-(j-t) := by omega
  refine CatModule.isoMk (fun l => ?_) ?_ ?_ ?_
  · exact {
      toFun := fun x => ⟨WeightCategory.homMk x.val.val ((hw l) ▸ x.val.property),
        WeightCategory.hom_ext (show x.val.val * e'.val.val = x.val.val by
          rw [he]; exact WeightCategory.val_congr x.property)⟩
      invFun := fun x => ⟨WeightCategory.homMk x.val.val ((hw l).symm ▸ x.val.property),
        WeightCategory.hom_ext (show x.val.val * e.val.val = x.val.val by
          rw [← he]; exact WeightCategory.val_congr x.property)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  · intro _ _ _; exact Iff.rfl
  · intro _ _; rfl
  · intro _ _ _ _; rfl

private def translateLoading (s : KLR.Seq μ) (hs : IsRedOrdered s) (j t : ℤ) :
    (CatModule.precomp (WeightCategory.shiftFunctor Tᵐᵒᵖ t)).obj (shiftedLoadingModule s hs j) ≅
      shiftedLoadingModule s hs (j-t) :=
  translateCorner j t (gradedLoadingIdempotentAt s hs j) (gradedLoadingIdempotentAt s hs (j-t)) rfl

private theorem scalar_off_weight {i : ℤ} {k : WeightCategory ℚ} (h : k.as ≠ i)
    (x : (representable (⟨i⟩ : WeightCategory ℚ)).obj k) : x = 0 := by
  refine Subtype.ext ?_
  exact ((InDegreeZero.ring_mem_grading_iff (R := ℚ)).mp x.property).resolve_left (sub_ne_zero.mpr h)

universe v
variable [CatModule.HasDerivedCategory.{v,0} (WeightCategory ℚ)]
  [CatModule.HasDerivedCategory.{v,0} (WeightCategory Tᵐᵒᵖ)]
local notation "line" j:arg => CatModule.DerivedCategory.Q.obj (representable (⟨j⟩ : WeightCategory ℚ))
local notation "shiftCap" t:arg => CatModule.DerivedCategory.internalShift Tᵐᵒᵖ t ⋙ gradedMiddleCap

private instance : gradedMiddleCap.CommShift ℤ := by unfold gradedMiddleCap Coevaluation.characterCap; infer_instance
private instance : gradedMiddleCap.IsTriangulated := by unfold gradedMiddleCap Coevaluation.characterCap; infer_instance

private def shiftCapLoading (s : KLR.Seq μ) (hs : IsRedOrdered s) (j t : ℤ) :
    (shiftCap t).obj (CatModule.DerivedCategory.Q.obj (shiftedLoadingModule s hs j)) ≅
      gradedMiddleCap.obj (CatModule.DerivedCategory.Q.obj (shiftedLoadingModule s hs (j-t))) :=
  gradedMiddleCap.mapIso ((CatModule.DerivedCategory.QCompInternalShiftIso Tᵐᵒᵖ t).app _ ≪≫
    CatModule.DerivedCategory.Q.mapIso (translateLoading s hs j t))

private theorem exists_cap_triangle (t : ℤ) {A B E : CatModule.{0} (WeightCategory Tᵐᵒᵖ)}
    (f : A ⟶ B) (g : B ⟶ E) (fg : f ≫ g = 0)
    (hi : ∀ X, Function.Injective (f.app X)) (he : ∀ X, Function.Exact (f.app X) (g.app X))
    (hs : ∀ X, Function.Surjective (g.app X)) :
    ∃ D : Triangle (CatModule.DerivedCategory.{v,0} (WeightCategory ℚ)), D ∈ distTriang _ ∧
      Nonempty (D.obj₁ ≅ (shiftCap t).obj (CatModule.DerivedCategory.Q.obj A)) ∧ Nonempty (D.obj₂ ≅ (shiftCap t).obj (CatModule.DerivedCategory.Q.obj B)) ∧
      Nonempty (D.obj₃ ≅ (shiftCap t).obj (CatModule.DerivedCategory.Q.obj E)) := by
  obtain ⟨D, hD, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ := exists_weight_triangle_of_exact f g fg hi he hs
  exact ⟨(shiftCap t).mapTriangle.obj D, (shiftCap t).map_distinguished D hD,
    ⟨(shiftCap t).mapIso e₁⟩, ⟨(shiftCap t).mapIso e₂⟩, ⟨(shiftCap t).mapIso e₃⟩⟩

private def shiftCapSyzygy (t : ℤ) : (shiftCap t).obj (CatModule.DerivedCategory.Q.obj syzygy.toCatModule) ≅ (line (2-t))⟦(1 : ℤ)⟧ :=
  Classical.choice <| by
    obtain ⟨D, hD, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ := exists_cap_triangle t gradedMiddleD₂ toSyzygy firstSequence_exact.1
      (fun k => (gradedMiddleComplex_exact k).1) firstSequence_exact.2.1 firstSequence_exact.2.2
    have hz : IsZero D.obj₂ := (gradedMiddleCap_shiftedTerminal_isZero (1-t)).of_iso
      (e₂ ≪≫ shiftCapLoading terminal terminal_ordered 1 t)
    have : IsIso D.mor₃ := (D.isZero₂_iff_isIso₃ hD).mp hz
    exact ⟨e₃.symm ≪≫ asIso D.mor₃ ≪≫ (shiftFunctor _ (1 : ℤ)).mapIso
      (e₁ ≪≫ shiftCapLoading middle orderedMiddle 2 t ≪≫ gradedMiddleCap_shiftedMiddleIso (2-t))⟩

omit [CatModule.HasDerivedCategory.{v,0} (WeightCategory Tᵐᵒᵖ)] in
private theorem scalar_shift_hom_zero (i j : ℤ) (hij : i ≠ j) (f : (line i)⟦(1 : ℤ)⟧ ⟶ line j) : f = 0 := by
  let e := (CatModule.DerivedCategory.Q.commShiftIso (1 : ℤ)).app (representable (⟨i⟩ : WeightCategory ℚ))
  rw [← cancel_epi e.hom, comp_zero]
  obtain ⟨g, hg⟩ := CatModule.DerivedCategory.exists_Q_map_eq
    ((isKProjective_representable (⟨i⟩ : WeightCategory ℚ)).shift 1) (e.hom ≫ f)
  have h : g = 0 := by
    apply CatModule.hom_ext
    intro k x
    by_cases hk : k.as = j
    · have hx : x = 0 := congrArg (shift.mk 1) (scalar_off_weight (hk ▸ Ne.symm hij) (shift.unmk 1 x))
      rw [hx, map_zero]
      rfl
    · exact scalar_off_weight hk _
  exact hg.symm.trans (by rw [h, Functor.map_zero]; rfl)

/-- After an internal shift by t, the unshifted cap gives scalar lines
generated in weights −t and 2−t, in homological degrees zero and two. -/
def gradedMiddleCap_shiftedSimpleIso (t : ℤ) :
    (shiftCap t).obj (CatModule.DerivedCategory.Q.obj gradedMiddleSimple) ≅ (line (0-t)) ⊞ (line (2-t))⟦(2 : ℤ)⟧ :=
  Classical.choice <| by
    obtain ⟨D, hD, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ := exists_cap_triangle t syzygy.subtype gradedMiddleAugmentation secondSequence_exact.1
      syzygy.subtype_injective secondSequence_exact.2 (fun k => (gradedMiddleComplex_exact k).2.2.2)
    let i₁ := e₁ ≪≫ shiftCapSyzygy t
    let i₂ := e₂ ≪≫ shiftCapLoading middle orderedMiddle 0 t ≪≫ gradedMiddleCap_shiftedMiddleIso (0-t)
    have hm : D.mor₁ = 0 := by
      rw [← cancel_epi i₁.inv, ← cancel_mono i₂.hom]
      simpa only [Category.assoc, comp_zero, zero_comp] using
        scalar_shift_hom_zero (2-t) (0-t) (by omega) (i₁.inv ≫ D.mor₁ ≫ i₂.hom)
    have hrot : D.rotate.mor₃ = 0 := by
      change -(shiftFunctor _ (1 : ℤ)).map D.mor₁ = 0
      rw [hm, Functor.map_zero, neg_zero]
    obtain ⟨split, _, _⟩ := exists_iso_binaryBiproduct_of_distTriang D.rotate (rot_of_distTriang _ hD) hrot
    let i₃ := (shiftFunctor _ (1 : ℤ)).mapIso i₁ ≪≫
      ((shiftFunctorAdd' _ (1 : ℤ) 1 2 (by decide)).app (line (2-t))).symm
    exact ⟨e₃.symm ≪≫ split ≪≫ biprod.mapIso i₂ i₃⟩

/-- Before the cup normalization the two scalar generators lie in internal
weights zero and two and in homological degrees zero and two. -/
def gradedMiddleCap_simpleIso :
    gradedMiddleCap.obj (CatModule.DerivedCategory.Q.obj gradedMiddleSimple) ≅
      (line 0) ⊞ (line 2)⟦(2 : ℤ)⟧ :=
  gradedMiddleCap.mapIso (((CatModule.DerivedCategory.internalShiftZeroIso Tᵐᵒᵖ).app _).symm) ≪≫
    gradedMiddleCap_shiftedSimpleIso 0

/-- The normalized fundamental cup followed by the cap gives the scalar
lines of bidegrees (internal, cohomological) (−1,1) and (1,−1). -/
def gradedMiddleCupCap_fieldIso :
    (gradedMiddleCup ⋙ gradedMiddleCap).obj (line 0) ≅
      (line (-1))⟦(-1 : ℤ)⟧ ⊞ (line 1)⟦(1 : ℤ)⟧ := by
  let sh := shiftFunctor (CatModule.DerivedCategory.{v,0} (WeightCategory ℚ)) (-1 : ℤ)
  let e := (CatModule.DerivedCategory.QCompInternalShiftIso Tᵐᵒᵖ 1).app gradedMiddleSimple
  let e₁ := gradedMiddleCap.mapIso gradedMiddleCup_fieldIso
  let e₂ := (gradedMiddleCap.commShiftIso (-1 : ℤ)).app (CatModule.DerivedCategory.Q.obj normalizedMiddleSimple)
  let e₃ := sh.mapIso (gradedMiddleCap.mapIso e.symm ≪≫ gradedMiddleCap_shiftedSimpleIso 1)
  let e₄ := sh.mapBiprod (line (-1)) ((line 1)⟦(2 : ℤ)⟧)
  let e₅ := biprod.mapIso (Iso.refl (sh.obj (line (-1))))
    ((shiftFunctorAdd' _ (2 : ℤ) (-1) 1 (by decide)).app (line 1)).symm
  exact e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄ ≪≫ e₅

end Categorification.Stendhal.FundamentalCorner
