/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DiagramWeightRingEquiv
import Categorification.WeightedKLR.RedStrands.BraidedIdentityGrading
import Categorification.WeightedKLR.RedStrands.BraidingAuxiliaryLoading
import Categorification.WeightedKLR.Rigidity.FundamentalBraidProjectives
import Categorification.WeightedKLR.Rigidity.GradedMiddleComplex

/-!
# The graded fundamental resolution in the source of the braid

For Webster, arXiv:1309.3796v2, Proposition 7.11 in fundamental type A₁,
the diagonal braid corner and the ordered tensor product algebra have the
same diagram grading. Restricting the resolution along that equivalence
gives the exact mixed crossing sequence in the source of the graded braid.
-/

noncomputable section
namespace Categorification.Stendhal.FundamentalCorner
open BraidedStendhalAlgebra DG CategoryTheory CatModule
open scoped DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
local notation "ν" => ({()} : Multiset Unit)
local notation "κ₀" => List.finRange 2
local notation "K" => ViolOrderCorner (k := ℚ) (Q := Q) (Λ := wt) («ν» := ν) κ₀
local notation "T" => TensorProductAlgebra ℚ Q wt ν
local notation "V" => violAuxiliaryGrade («ν» := ν) grading
local notation "hE" => isIdempotentElem_violMk_redProj ℚ Q wt ν κ₀
local notation "S" => Graded.oppositeGrade (Graded.cornerGrading V hE)
local notation "G" => Graded.oppositeGrade (tensorProductGrade grading ν)
local instance fundamentalBraidSourceCornerGrades : GradedAlgebra (Graded.cornerGrading V hE) :=
  Graded.cornerGradedAlgebra V hE (redProj_mem_violAuxiliaryGrade grading κ₀)
local instance fundamentalBraidSourceCornerInternal : InternalGrading Kᵐᵒᵖ := gradedAlgebraInternalGrading S
local instance fundamentalBraidSourceCornerBigraded : BigradedDGRing Kᵐᵒᵖ := gradedAlgebraBigradedDGRing S
local instance fundamentalBraidSourceOrderedInternal : InternalGrading Tᵐᵒᵖ := gradedAlgebraInternalGrading G
local instance fundamentalBraidSourceOrderedBigraded : BigradedDGRing Tᵐᵒᵖ := gradedAlgebraBigradedDGRing G

private theorem sourceWeight {j : ℤ} (a : Kᵐᵒᵖ) :
    fundamentalBraidSourceEquiv a.unop ∈ tensorProductGrade grading ν j ↔ a.unop.val ∈ V j :=
  violCornerEquiv_mem_tensorProductGrade_iff wordSpec
    (fun i j h => (h (Subsingleton.elim i j)).elim) grading a.unop

/-- The diagram-weight dg equivalence from the native braid source corner
to the ordered algebra of the fundamental middle resolution. -/
abbrev fundamentalBraidSourceWeightFunctor : WeightCategory Kᵐᵒᵖ ⥤ WeightCategory Tᵐᵒᵖ :=
  weightFunctorOfRingEquiv fundamentalBraidSourceEquiv.op sourceWeight

instance : fundamentalBraidSourceWeightFunctor.Additive :=
  weightFunctorOfRingEquiv_additive fundamentalBraidSourceEquiv.op sourceWeight

instance : fundamentalBraidSourceWeightFunctor.IsDGFunctor :=
  weightFunctorOfRingEquiv_isDGFunctor fundamentalBraidSourceEquiv.op sourceWeight

instance : fundamentalBraidSourceWeightFunctor.IsEquivalence :=
  weightFunctorOfRingEquiv_isEquivalence fundamentalBraidSourceEquiv.op sourceWeight

/-- The actual middle simple as a weight module on the diagonal braid corner. -/
def fundamentalBraidSourceGradedHead : CatModule.{0} (WeightCategory Kᵐᵒᵖ) :=
  (CatModule.precomp fundamentalBraidSourceWeightFunctor).obj gradedMiddleSimple

local notation "res" => CatModule.precomp fundamentalBraidSourceWeightFunctor

/-- At every diagram weight the two mixed crossings followed by the middle
character give the augmented exact sequence in the source of the graded braid
(Webster v2, Lemma 7.3 and the proof of Proposition 7.11). -/
theorem fundamentalBraidSourceGradedResolution (X : WeightCategory Kᵐᵒᵖ) :
    Function.Injective (((res).map gradedMiddleD₂).app X) ∧
    Function.Exact (((res).map gradedMiddleD₂).app X) (((res).map gradedMiddleD₁).app X) ∧
    Function.Exact (((res).map gradedMiddleD₁).app X) (((res).map gradedMiddleAugmentation).app X) ∧
    Function.Surjective (((res).map gradedMiddleAugmentation).app X) :=
  gradedMiddleComplex_exact (fundamentalBraidSourceWeightFunctor.obj X)


local notation "μ" => stendhalWeight 2 ν

/-- A fundamental loading projector at its generating weight, evaluated in
the source diagonal corner of the braid (Webster v2, Proposition 7.11). -/
def fundamentalBraidSourceLoadingAt (s : KLR.Seq μ) (hs : IsRedOrdered s) (j : ℤ) :
    DGCategory.Idempotent (⟨j⟩ : WeightCategory Kᵐᵒᵖ) where
  val := auxiliaryGradedLoadingHom grading ((redWord_eq_finRange_iff s).mpr hs) ⟨j⟩
  mem_cocycles := ⟨WeightCategory.mem_grading_iff.mpr
    ((InDegreeZero.ring_mem_grading_iff (R := Kᵐᵒᵖ)).mpr (Or.inl rfl)),
    WeightCategory.hom_ext (InDegreeZero.ring_d_apply (MulOpposite.op
      (violLoadingIdem (k := ℚ) (Q := Q) (Λ := wt) ((redWord_eq_finRange_iff s).mpr hs))))⟩
  comp_self := WeightCategory.hom_ext (congrArg MulOpposite.op
    (isIdempotentElem_violLoadingIdem (k := ℚ) (Q := Q) (Λ := wt)
      ((redWord_eq_finRange_iff s).mpr hs)).eq)

/-- The source weight functor takes each native loading to its ordered loading. -/
theorem fundamentalBraidSourceWeightFunctor_loading (s : KLR.Seq μ) (hs : IsRedOrdered s) (j : ℤ) :
    fundamentalBraidSourceWeightFunctor.map (fundamentalBraidSourceLoadingAt s hs j).val =
      (gradedLoadingIdempotentAt s hs j).val := by
  let ho := (redWord_eq_finRange_iff s).mpr hs
  have h : diagonalDiagram (KLR.KLRAlgebra.e s) = violLoadingIdem (k := ℚ) (Q := Q) (Λ := wt) ho :=
    Subtype.ext (congrArg (violMk ℚ Q wt ν) (cornerMk_e_val ho))
  apply WeightCategory.hom_ext
  apply congrArg MulOpposite.op
  change fundamentalBraidSourceEquiv (violLoadingIdem ho) = _
  rw [← h,fundamentalBraidSourceEquiv_diagram]
  exact projectedLoading_eq_mk_e s hs

/-- Restriction of the resolution's diagram projectives gives the native
shifted loading projectives in the source braid corner. -/
def fundamentalBraidSourceLoadingIso (s : KLR.Seq μ) (hs : IsRedOrdered s) (j : ℤ) :
    CatModule.corner (fundamentalBraidSourceLoadingAt s hs j) ≅
      (res).obj (shiftedLoadingModule s hs j) :=
  weightRingEquivCornerIso fundamentalBraidSourceEquiv.op sourceWeight _
    (fundamentalBraidSourceLoadingAt s hs j) (gradedLoadingIdempotentAt s hs j) (fundamentalBraidSourceWeightFunctor_loading s hs j)

/-- Each term of the restricted graded resolution is K-projective. -/
theorem fundamentalBraidSourceLoading_isKProjective (s : KLR.Seq μ) (hs : IsRedOrdered s) (j : ℤ) :
    CatModule.IsKProjective ((res).obj (shiftedLoadingModule s hs j)) :=
  (CatModule.isKProjective_corner _).of_iso (fundamentalBraidSourceLoadingIso s hs j).symm

local notation "F" => fundamentalBraidSourceWeightFunctor
local notation "P" s:arg hs:arg j:arg => fundamentalBraidSourceLoadingAt s hs j
local notation "L" s:arg hs:arg j:arg => fundamentalBraidSourceLoadingIso s hs j
private theorem orderedMiddle : IsRedOrdered middle := by unfold IsRedOrdered; decide +kernel

private theorem iso_gen (s : KLR.Seq μ) (hs : IsRedOrdered s) (j : ℤ) :
    ((L s hs j).hom.app ⟨j⟩) (cornerGen (P s hs j)) = cornerGen (gradedLoadingIdempotentAt s hs j) :=
  Subtype.ext (fundamentalBraidSourceWeightFunctor_loading s hs j)

private theorem iso_inv {s : KLR.Seq μ} {hs : IsRedOrdered s} {j : ℤ} (X : WeightCategory Kᵐᵒᵖ)
    (y : (shiftedLoadingModule s hs j).obj ((F).obj X)) :
    (F).map (((L s hs j).inv.app X y).val) = y.val :=
  (F).map_preimage y.val

private abbrev loadingMapInSource {s t : KLR.Seq μ} {hs : IsRedOrdered s} {ht : IsRedOrdered t} {i j : ℤ}
    (g : shiftedLoadingModule s hs i ⟶ shiftedLoadingModule t ht j) :=
  (L s hs i).hom ≫ (CatModule.precomp F).map g ≫ (L t ht j).inv

private theorem loadingMapInSource_generator {s t : KLR.Seq μ} {hs : IsRedOrdered s} {ht : IsRedOrdered t}
    {i j : ℤ} (g : shiftedLoadingModule s hs i ⟶ shiftedLoadingModule t ht j) :
    fundamentalBraidSourceEquiv (((loadingMapInSource g).app ⟨i⟩ (cornerGen (P s hs i))).val.val).unop =
      ((g.app ((F).obj ⟨i⟩) (cornerGen (gradedLoadingIdempotentAt s hs i))).val.val).unop := by
  have hx : (F).map (((loadingMapInSource g).app ⟨i⟩ (cornerGen (P s hs i))).val) =
      (g.app ((F).obj ⟨i⟩) (cornerGen (gradedLoadingIdempotentAt s hs i))).val := by
    change (F).map (((L t ht j).inv.app _ (g.app _ (((L s hs i).hom.app _) _))).val) = _
    rw [iso_gen]
    exact iso_inv _ _
  exact congrArg (fun h : (F).obj ⟨j⟩ ⟶ (F).obj ⟨i⟩ => h.val.unop) hx

/-- The first mixed crossing on the native shifted braid-source projectives. -/
abbrev fundamentalBraidGradedSourceD₂ :=
  loadingMapInSource (s := middle) (hs := orderedMiddle) (i := 2)
    (t := terminal) (ht := terminal_ordered) (j := 1) gradedMiddleD₂

/-- The second mixed crossing on the native shifted braid-source projectives. -/
abbrev fundamentalBraidGradedSourceD₁ :=
  loadingMapInSource (s := terminal) (hs := terminal_ordered) (i := 1)
    (t := middle) (ht := orderedMiddle) (j := 0) gradedMiddleD₁

/-- The first differential takes its generator to the mixed crossing on
the middle loading. -/
theorem fundamentalBraidGradedSourceD₂_generator :
    ((fundamentalBraidGradedSourceD₂.app ⟨2⟩ (cornerGen (P middle orderedMiddle 2))).val.val).unop =
      diagonalDiagram (KLR.KLRAlgebra.ψ 1 * KLR.KLRAlgebra.e middle) := by
  apply fundamentalBraidSourceEquiv.injective
  rw [fundamentalBraidSourceEquiv_crossings.1]
  refine (loadingMapInSource_generator gradedMiddleD₂).trans ?_
  change (project (StendhalAlgebraAllOrders.ψ 1) * middleIdem) *
    (TensorProductAlgebra.mk Q wt ν (StendhalAlgebra.e middle orderedMiddle)) = _
  rw [← projectedLoading_eq_mk_e,mul_assoc]
  exact congrArg (project (StendhalAlgebraAllOrders.ψ 1) * ·)
    (IsIdempotentElem.map (by simp [IsIdempotentElem, StendhalAlgebraAllOrders.e_mul_e]) project).eq

/-- The second differential takes its generator to the mixed crossing on
the terminal loading. -/
theorem fundamentalBraidGradedSourceD₁_generator :
    ((fundamentalBraidGradedSourceD₁.app ⟨1⟩ (cornerGen (P terminal terminal_ordered 1))).val.val).unop =
      diagonalDiagram (KLR.KLRAlgebra.ψ 1 * KLR.KLRAlgebra.e terminal) := by
  apply fundamentalBraidSourceEquiv.injective
  rw [fundamentalBraidSourceEquiv_crossings.2]
  refine (loadingMapInSource_generator gradedMiddleD₁).trans ?_
  change (project (StendhalAlgebraAllOrders.ψ 1) * terminalIdem) *
    (TensorProductAlgebra.mk Q wt ν (StendhalAlgebra.e terminal terminal_ordered)) = _
  rw [← projectedLoading_eq_mk_e,mul_assoc]
  exact congrArg (project (StendhalAlgebraAllOrders.ψ 1) * ·)
    (IsIdempotentElem.map (by simp [IsIdempotentElem, StendhalAlgebraAllOrders.e_mul_e]) project).eq

end Categorification.Stendhal.FundamentalCorner
