/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.OrderedWeightDGResolution
import Categorification.Algebra.GradedLoadingPieceComparison

/-!
# K-projectivity of the actual ordered loading resolution

Webster, arXiv:1309.3796v2, Lemma 6.11. In degree zero the literal
resolution has the original loading projective. In negative cohomological
degrees it has sums of representable corners at the higher loadings and
their generator weights. The bounded-above dg model is K-projective.
-/

noncomputable section

namespace Categorification.ModuleFiltration

open CategoryTheory DG
open scoped DG.DegreeZero

variable {R : Type} [Ring R] [InternalGrading R] [BigradedDGRing R]
  {Label : Type} {S : Label → ModuleCat R} {e : Label → R} {above : Label → Label → Prop}
  (data : OrderedStandardCovers S e above) (s : Label)
  (he₀ : ∀ i, e i ∈ wgrading (M := R) 0)
  (he : ∀ i, IsIdempotentElem (e i)) (htrans : ∀ a b c, above a b → above b c → above a c)
  (T : ℤ → AddSubgroup (S s)) [DirectSum.Decomposition T]
  (hq : ∀ ⦃n : ℤ⦄ ⦃x : lIdeal (e s)⦄, x.val ∈ wgrading n → data.quotient s x ∈ T n)

local notation "A" => wgrading (M := R)
local notation "W" => WeightCategory R
open scoped Classical CatModule

private abbrev orderedCochain := weightCochainOfGradedChain
  (orderedWeightTerms data s he₀ he htrans T hq)
  (orderedWeightDifferentials data s he₀ he htrans T hq)
  (orderedWeightDifferentials_mem data s he₀ he htrans T hq)
  (orderedWeightDifferentials_comp data s he₀ he htrans T hq)

local instance instOrderedWeightCornerCochainAdditive :
    (orderedCochain data s he₀ he htrans T hq).Additive := by
  exact Categorification.instAdditiveWeightCategoryCochainComplexModuleCatIntWeightCochainOfGradedChain
    _ _ _ _

private abbrev higherIdem := fun i : {i : Label // above s i} => e i.val

private abbrev syzygyGrade (n : ℕ) :=
  (gradedLoadingResolutionSyzygy data s A (orderedWeightScalarMul (R := R)) he₀ he htrans T hq n).grade

private abbrev positiveGenerators (n : ℕ) :=
  WeightGenerators (syzygyGrade data s he₀ he htrans T hq n) (higherIdem (e := e) (above := above) s)

private def positiveProjector (n : ℕ) (t : positiveGenerators data s he₀ he htrans T hq n) :
    DGCategory.Idempotent
      (generatorWeight (syzygyGrade data s he₀ he htrans T hq n)
        (higherIdem (e := e) (above := above) s) t) :=
  loadingWeightIdempotent (e t.1.val) (he₀ t.1.val) (he t.1.val) ⟨t.2.1⟩

private def positiveCorners (n : ℕ) : CatModule W :=
  CatModule.directSum (fun t => CatModule.corner (positiveProjector data s he₀ he htrans T hq n t))

private def orderedPositiveCoords (n : ℕ) (X : W) :
    (positiveCorners data s he₀ he htrans T hq n).obj X ≃+
      (orderedWeightTerms data s he₀ he htrans T hq (n+1)).grade X.as :=
  higherWeightCornerSumEquiv (syzygyGrade data s he₀ he htrans T hq n)
    (higherIdem (e := e) (above := above) s)
    (positiveProjector data s he₀ he htrans T hq n) (fun _ => rfl) X

/-- The positive terms of the literal ordered resolution are sums of shifted representable corners. -/
def orderedWeightDgPositivePieceIso (n : ℕ) :
    weightComplexPiece (orderedCochain data s he₀ he htrans T hq) (-((n+1 : ℕ) : ℤ)) ≅
      CatModule.shift ((n+1 : ℕ) : ℤ) (positiveCorners data s he₀ he htrans T hq n) := by
  let K := positiveCorners data s he₀ he htrans T hq n
  let B := orderedPositiveCoords data s he₀ he htrans T hq n
  apply weightComplexPieceIsoOfGradeCoords
    (orderedWeightTerms data s he₀ he htrans T hq)
    (orderedWeightDifferentials data s he₀ he htrans T hq)
    (orderedWeightDifferentials_mem data s he₀ he htrans T hq)
    (orderedWeightDifferentials_comp data s he₀ he htrans T hq)
    (n+1) K (fun X => (B X).symm)
    (cornerSum_mem_zero_iff (positiveProjector data s he₀ he htrans T hq n))
    (cornerSum_d_zero (positiveProjector data s he₀ he htrans T hq n))
  intro X Y a x y ha
  apply (B Y).injective
  rw [AddEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [ha]
  have h := higherWeightCornerSumEquiv_act (syzygyGrade data s he₀ he htrans T hq n)
    (higherIdem (e := e) (above := above) s)
    (positiveProjector data s he₀ he htrans T hq n) (fun _ => rfl) a ((B X).symm x)
  change (B Y (K.act a ((B X).symm x))).val =
    a.val • (B X ((B X).symm x)).val at h
  rw [AddEquiv.apply_symm_apply] at h
  exact h.symm

private def initialCorner : CatModule W :=
  CatModule.corner (loadingWeightIdempotent (e s) (he₀ s) (he s) ⟨0⟩)

private def orderedInitialCoords (X : W) :
    (initialCorner s he₀ he).obj X ≃+ (orderedWeightTerms data s he₀ he htrans T hq 0).grade X.as := by
  let P₀ := loadingWeightIdempotent (e s) (he₀ s) (he s) (⟨0⟩ : W)
  change (CatModule.corner P₀).obj X ≃+ loadingIdealGrading A (e s) X.as
  exact {
    toFun := fun x => ⟨⟨x.val.val, congrArg Subtype.val x.property⟩, by
      change x.val.val ∈ A X.as
      have h : x.val.val ∈ A (X.as-0) := x.val.property
      simpa only [sub_zero] using h⟩
    invFun := fun y => ⟨⟨y.val.val, by
      change y.val.val ∈ A (X.as-0)
      have hy : y.val.val ∈ A X.as := y.property
      simpa only [sub_zero] using hy⟩, WeightCategory.hom_ext y.val.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl }

/-- Degree zero uses the original unshifted loading projective. -/
def orderedWeightDgInitialPieceIso :
    weightComplexPiece (orderedCochain data s he₀ he htrans T hq) 0 ≅
      CatModule.shift 0 (initialCorner s he₀ he) := by
  let K := initialCorner s he₀ he
  let B := orderedInitialCoords data s he₀ he htrans T hq
  apply weightComplexPieceIsoOfGradeCoords
    (orderedWeightTerms data s he₀ he htrans T hq)
    (orderedWeightDifferentials data s he₀ he htrans T hq)
    (orderedWeightDifferentials_mem data s he₀ he htrans T hq)
    (orderedWeightDifferentials_comp data s he₀ he htrans T hq)
    0 K (fun X => (B X).symm)
    (fun X => corner_mem_zero_iff (loadingWeightIdempotent (e s) (he₀ s) (he s) (⟨0⟩ : W)))
    (fun X => corner_d_zero (loadingWeightIdempotent (e s) (he₀ s) (he s) (⟨0⟩ : W)))
  intro X Y a x y ha
  apply (B Y).injective
  rw [AddEquiv.apply_symm_apply]
  apply Subtype.ext
  apply Subtype.ext
  have hx := congrArg (fun z : (orderedWeightTerms data s he₀ he htrans T hq 0).grade X.as => z.val.val)
    ((B X).apply_symm_apply x)
  have hy := congrArg (fun z : lIdeal (e s) => z.val) ha
  change y.val.val = a.val * ((B X).symm x).val.val
  exact hy.trans (congrArg ((a.val : R) * ·) hx.symm)

/-- The full homogeneous ordered resolution is K-projective in the weight dg category. -/
theorem orderedWeightDgResolution_isKProjective :
    CatModule.IsKProjective (orderedWeightDgResolution data s he₀ he htrans T hq) := by
  change CatModule.IsKProjective (diagramWeightModuleOfComplex
    (orderedCochain data s he₀ he htrans T hq))
  apply diagramWeightModuleOfComplex_isKProjective
  · exact weightCochainOfGradedChain_positive_isZero
      (orderedWeightTerms data s he₀ he htrans T hq) (orderedWeightDifferentials data s he₀ he htrans T hq)
      (orderedWeightDifferentials_mem data s he₀ he htrans T hq) (orderedWeightDifferentials_comp data s he₀ he htrans T hq)
  · intro n
    cases n with
    | zero =>
      apply CatModule.IsKProjective.of_iso _
        (orderedWeightDgInitialPieceIso data s he₀ he htrans T hq)
      exact (CatModule.isKProjective_corner (loadingWeightIdempotent (e s) (he₀ s) (he s)
        (⟨0⟩ : W))).shift 0
    | succ n =>
      apply CatModule.IsKProjective.of_iso _
        (orderedWeightDgPositivePieceIso data s he₀ he htrans T hq n)
      exact (CatModule.IsKProjective.directSum fun t =>
        CatModule.isKProjective_corner (positiveProjector data s he₀ he htrans T hq n t)).shift _

end Categorification.ModuleFiltration
