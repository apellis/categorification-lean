/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.GradedOrderedProjectiveResolution
import Categorification.Algebra.GradedChainWeightDG

/-!
# The dg augmentation of an ordered standard resolution

Realize the homogeneous ordered chain and its actual augmentation on the
weight category. This is the resolution used in Webster,
arXiv:1309.3796v2, Lemma 6.11.
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
  (hsmul : ∀ {i j : ℤ} {a : R} {x : S s}, a ∈ wgrading i → x ∈ T j → a • x ∈ T (i + j))
  (hq : ∀ ⦃n : ℤ⦄ ⦃x : lIdeal (e s)⦄, x.val ∈ wgrading n → data.quotient s x ∈ T n)

local notation "A" => wgrading (M := R)
local notation "W" => WeightCategory R
theorem orderedWeightScalarMul ⦃i j : ℤ⦄ ⦃a b : R⦄
    (ha : a ∈ A i) (hb : b ∈ A j) : a * b ∈ A (i+j) :=
  mul_mem_wgrading ha hb

private def gradedTermFromSyzygy (G : GradedLoadingSyzygy (R := R) A) : WeightGradedTerm R :=
  { obj := G.obj
    grade := G.grade
    decomp := G.decomp
    smul_mem := fun {_ _ _ _} ha hx => G.smul_mem ha hx }

abbrev orderedWeightTerms (n : ℕ) :=
  gradedTermFromSyzygy (gradedLoadingResolutionTerm data s A (orderedWeightScalarMul (R := R)) he₀ he htrans T hq n)

abbrev orderedWeightDifferentials :=
  gradedLoadingResolutionChainMap data s A (orderedWeightScalarMul (R := R)) he₀ he htrans T hq

theorem orderedWeightDifferentials_mem (n : ℕ) (j : ℤ) {x : (orderedWeightTerms data s he₀ he htrans T hq (n+1)).obj}
    (hx : x ∈ (orderedWeightTerms data s he₀ he htrans T hq (n+1)).grade j) :
    orderedWeightDifferentials data s he₀ he htrans T hq n x ∈ (orderedWeightTerms data s he₀ he htrans T hq n).grade j :=
  gradedLoadingResolutionChainMap_mem data s A (orderedWeightScalarMul (R := R)) he₀ he htrans T hq n hx

theorem orderedWeightDifferentials_comp (n : ℕ) (x : (orderedWeightTerms data s he₀ he htrans T hq (n+2)).obj) :
    orderedWeightDifferentials data s he₀ he htrans T hq n (orderedWeightDifferentials data s he₀ he htrans T hq (n+1) x) = 0 :=
  (gradedLoadingResolutionChainMap_exact data s A (orderedWeightScalarMul (R := R)) he₀ he htrans T hq n).apply_apply_eq_zero x

/-- The homogeneous ordered resolution viewed as a dg module on the weight category. -/
def orderedWeightDgResolution : CatModule W :=
  weightDgModuleOfGradedChain (orderedWeightTerms data s he₀ he htrans T hq)
    (orderedWeightDifferentials data s he₀ he htrans T hq)
    (orderedWeightDifferentials_mem data s he₀ he htrans T hq)
    (orderedWeightDifferentials_comp data s he₀ he htrans T hq)

/-- The target of the ordered resolution, with its supplied homogeneous standard grading. -/
def orderedWeightDgTarget : CatModule W :=
  weightDgModuleOfGradedTerm ({ obj := S s, grade := T, decomp := ‹_›, smul_mem := hsmul } : WeightGradedTerm R)

/-- The degree-preserving augmentation of the native ordered dg model. -/
def orderedWeightDgAugmentation :
    orderedWeightDgResolution data s he₀ he htrans T hq ⟶ orderedWeightDgTarget s T hsmul :=
  weightDgGradedChainAugmentation (orderedWeightTerms data s he₀ he htrans T hq)
    (orderedWeightDifferentials data s he₀ he htrans T hq)
    (orderedWeightDifferentials_mem data s he₀ he htrans T hq) (orderedWeightDifferentials_comp data s he₀ he htrans T hq)
    { obj := S s, grade := T, decomp := ‹_›, smul_mem := hsmul } (data.quotient s)
    (fun _ {_} hx => hq hx) ((gradedLoadingResolutionChainMap_augmentation_exact data s A (orderedWeightScalarMul (R := R)) he₀ he htrans T hq).apply_apply_eq_zero)

/-- The actual graded augmentation of the ordered resolution is a dg quasi-isomorphism. -/
theorem orderedWeightDgAugmentation_quasiIso :
    CatModule.IsQuasiIso (orderedWeightDgAugmentation data s he₀ he htrans T hsmul hq) :=
  weightDgGradedChainAugmentation_quasiIso _ _ _ _ _ _ _ _
    (gradedLoadingResolutionChainMap_exact data s A (orderedWeightScalarMul (R := R)) he₀ he htrans T hq)
    (gradedLoadingResolutionChainMap_augmentation_exact data s A (orderedWeightScalarMul (R := R)) he₀ he htrans T hq)
    (data.surjective s)

end Categorification.ModuleFiltration
