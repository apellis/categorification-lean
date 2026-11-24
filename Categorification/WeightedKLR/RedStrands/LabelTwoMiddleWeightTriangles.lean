/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DiagramWeightExact
import Categorification.WeightedKLR.RedStrands.LabelTwoMiddleGradedAugmentation
import Categorification.WeightedKLR.Rigidity.WeightModuleExactTriangle
import Categorification.WeightedKLR.RedStrands.LabelTwoMiddleAmbientTor

/-!
# The label-two middle companion triangles in the weight category

The two alternating dot inclusions in the actual middle standard
shift internal degree by two. Their short exact sequences give
distinguished triangles of the corresponding dg weight modules.
-/

noncomputable section

namespace Categorification.Stendhal.LabelTwo

open KLR CategoryTheory CategoryTheory.Pretriangulated DG MulOpposite Categorification.Graded
open Categorification.Stendhal.FundamentalCorner (exists_distinguished_weightTriangle_of_exact)
open scoped DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable (k : Type) [Field k]

local notation "ν₂" => (({()} : Multiset Unit) + {()})
local notation "A₂" => TensorProductAlgebra k (parameter k) weights ν₂
local notation "S₂" => Standard k
local notation "𝒜₂" => middleTensorGrade k (labelTwoGradingDatum k)
local notation "ℳ₂" => middleStandardGrade k (labelTwoGradingDatum k)
local notation "𝒬₂" => middleDotSumQuotientGrade k
local notation "ℛ₂" => middleDotDifferenceQuotientGrade k

local instance : InternalGrading A₂ := gradedAlgebraInternalGrading 𝒜₂
local instance : BigradedDGRing A₂ := gradedAlgebraBigradedDGRing 𝒜₂
local instance : InternalGrading k := scalarInternalGrading k
local instance : BigradedDGRing k := scalarBigradedDGRing k

private def scalarUnop : kᵐᵒᵖ →+* k where
  toFun := unop
  map_one' := rfl
  map_mul' a b := by
    change b.unop * a.unop = a.unop * b.unop
    exact mul_comm _ _
  map_zero' := rfl
  map_add' _ _ := rfl

local instance (X : Type) [AddCommGroup X] [Module k X] : Module kᵐᵒᵖ X :=
  Module.compHom X (scalarUnop k)

local instance {X : Type} [AddCommGroup X] [Module k X] [Module A₂ X]
    [SMulCommClass A₂ k X] : SMulCommClass A₂ kᵐᵒᵖ X :=
  ⟨fun a c x => smul_comm a c.unop x⟩

private theorem rightScalarWeight {X : Type} [AddCommGroup X] [Module k X]
    (P : ℤ → Submodule k X) {i j : ℤ} {c : k} {x : X}
    (hc : c ∈ wgrading i) (hx : x ∈ P j) : op c • x ∈ P (j + i) := by
  change c • x ∈ P (j + i)
  rcases InDegreeZero.ring_mem_grading_iff.mp hc with rfl | rfl
  · rw [add_zero]
    exact (P j).smul_mem _ hx
  · rw [zero_smul]
    exact zero_mem _

private theorem leftModuleWeight {X : Type} [AddCommGroup X] [Module k X] [Module A₂ X]
    (P : ℤ → Submodule k X) [SetLike.GradedSMul 𝒜₂ P] {i j : ℤ} {a : A₂} {x : X}
    (ha : a ∈ wgrading i) (hx : x ∈ P j) : a • x ∈ P (i + j) :=
  SetLike.GradedSMul.smul_mem (A := 𝒜₂) (B := P) ha hx

private def totalWeightBimodule {X : Type} [AddCommGroup X] [Module k X] [Module A₂ X]
    [SMulCommClass A₂ k X] (P : ℤ → Submodule k X) [SetLike.GradedSMul 𝒜₂ P] :=
  diagramWeightBimodule (fun i => (P i).toAddSubgroup)
    (fun {_ _ _ _} ha hx => SetLike.GradedSMul.smul_mem (A := 𝒜₂) (B := P) ha hx)
    (rightScalarWeight k P)

/-- The standard viewed as a dg module over the weight category. -/
def middleStandardWeightModule : CatModule (WeightCategory A₂) :=
  letI : SetLike.GradedSMul 𝒜₂ ℳ₂ := (middleStandardGFin k (labelTwoGradingDatum k)).gradedSMul
  (totalWeightBimodule k ℳ₂).left ⟨0⟩

/-- The sum quotient viewed as a weight module with a chosen internal shift. -/
def middleSumWeightModule (j : ℤ) : CatModule (WeightCategory A₂) :=
  letI : SetLike.GradedSMul 𝒜₂ 𝒬₂ := (middleDotSumQuotientGFin k).gradedSMul
  (totalWeightBimodule k (Graded.shift 𝒬₂ j)).left ⟨0⟩

/-- The difference quotient viewed as a weight module with a chosen internal shift. -/
def middleDifferenceWeightModule (j : ℤ) : CatModule (WeightCategory A₂) :=
  letI : SetLike.GradedSMul 𝒜₂ ℛ₂ := (middleDotDifferenceQuotientGFin k).gradedSMul
  (totalWeightBimodule k (Graded.shift ℛ₂ j)).left ⟨0⟩


private def liftedWeightMap {X Y : Type}
    [AddCommGroup X] [Module k X] [Module A₂ X] [SMulCommClass A₂ k X]
    [AddCommGroup Y] [Module k Y] [Module A₂ Y] [SMulCommClass A₂ k Y]
    (P : ℤ → Submodule k X) (Q' : ℤ → Submodule k Y)
    [SetLike.GradedSMul 𝒜₂ P] [SetLike.GradedSMul 𝒜₂ Q']
    (f : X →ₗ[A₂] Y) (hf : ∀ d {x : X}, x ∈ P d → f x ∈ Q' d) :
    (totalWeightBimodule k P).left ⟨0⟩ ⟶ (totalWeightBimodule k Q').left ⟨0⟩ :=
  diagramWeightLeftLinearMap (fun i => (P i).toAddSubgroup) (fun i => (Q' i).toAddSubgroup)
    (fun {_ _ _ _} ha hx => SetLike.GradedSMul.smul_mem (A := 𝒜₂) (B := P) ha hx)
    (rightScalarWeight k P)
    (fun {_ _ _ _} ha hx => SetLike.GradedSMul.smul_mem (A := 𝒜₂) (B := Q') ha hx)
    (rightScalarWeight k Q') ⟨0⟩ f hf

private def sumCompanionLinear :=
  (LinearMap.range (diagramMinus k)).liftQ (diagramPlus k)
    (fun x hx => LinearMap.mem_ker.mpr ((diagramMinusPlus_exact k x).mpr hx))

private def differenceCompanionLinear :=
  (LinearMap.range (diagramPlus k)).liftQ (diagramMinus k)
    (fun x hx => LinearMap.mem_ker.mpr ((diagramPlusMinus_exact k x).mpr hx))

/-- The sum map from the shifted difference quotient into the actual middle standard. -/
def middleSumWeightCompanion : middleDifferenceWeightModule k 2 ⟶ middleStandardWeightModule k := by
  letI : SetLike.GradedSMul 𝒜₂ ℳ₂ := (middleStandardGFin k (labelTwoGradingDatum k)).gradedSMul
  letI : SetLike.GradedSMul 𝒜₂ ℛ₂ := (middleDotDifferenceQuotientGFin k).gradedSMul
  refine liftedWeightMap k (Graded.shift ℛ₂ 2) ℳ₂ (sumCompanionLinear k) ?_
  intro d x hx
  have h := (diagramSumCompanionInclusionAtDegree k (d - 2) ⟨x, hx⟩).property
  change sumCompanionLinear k x ∈ ℳ₂ (d - 2 + 2) at h
  rwa [sub_add_cancel] at h

/-- The difference map from the shifted sum quotient into the actual middle standard. -/
def middleDifferenceWeightCompanion : middleSumWeightModule k 2 ⟶ middleStandardWeightModule k := by
  letI : SetLike.GradedSMul 𝒜₂ ℳ₂ := (middleStandardGFin k (labelTwoGradingDatum k)).gradedSMul
  letI : SetLike.GradedSMul 𝒜₂ 𝒬₂ := (middleDotSumQuotientGFin k).gradedSMul
  refine liftedWeightMap k (Graded.shift 𝒬₂ 2) ℳ₂ (differenceCompanionLinear k) ?_
  intro d x hx
  have h := (diagramDifferenceCompanionInclusionAtDegree k (d - 2) ⟨x, hx⟩).property
  change differenceCompanionLinear k x ∈ ℳ₂ (d - 2 + 2) at h
  rwa [sub_add_cancel] at h

/-- The actual sum augmentation on weight modules. -/
def middleSumWeightAugmentation : middleStandardWeightModule k ⟶ middleSumWeightModule k 0 := by
  letI : SetLike.GradedSMul 𝒜₂ ℳ₂ := (middleStandardGFin k (labelTwoGradingDatum k)).gradedSMul
  letI : SetLike.GradedSMul 𝒜₂ 𝒬₂ := (middleDotSumQuotientGFin k).gradedSMul
  refine liftedWeightMap k ℳ₂ (Graded.shift 𝒬₂ 0) (LinearMap.range (diagramPlus k)).mkQ ?_
  intro d x hx
  change _ ∈ 𝒬₂ (d - 0)
  rw [sub_zero]
  exact (diagramMiddleAugmentationAtDegree k d ⟨x, hx⟩).property

/-- The actual difference augmentation on weight modules. -/
def middleDifferenceWeightAugmentation :
    middleStandardWeightModule k ⟶ middleDifferenceWeightModule k 0 := by
  letI : SetLike.GradedSMul 𝒜₂ ℳ₂ := (middleStandardGFin k (labelTwoGradingDatum k)).gradedSMul
  letI : SetLike.GradedSMul 𝒜₂ ℛ₂ := (middleDotDifferenceQuotientGFin k).gradedSMul
  refine liftedWeightMap k ℳ₂ (Graded.shift ℛ₂ 0) (LinearMap.range (diagramMinus k)).mkQ ?_
  intro d x hx
  change _ ∈ ℛ₂ (d - 0)
  rw [sub_zero]
  exact (diagramDifferenceAugmentationAtDegree k d ⟨x, hx⟩).property


@[instance_reducible] private def addSubgroupDecomposition {X : Type} [AddCommGroup X] [Module k X]
    (P : ℤ → Submodule k X) [DirectSum.Decomposition P] :
    DirectSum.Decomposition (fun i => (P i).toAddSubgroup) where
  decompose' := DirectSum.Decomposition.decompose' (ℳ := P)
  left_inv := DirectSum.Decomposition.left_inv (ℳ := P)
  right_inv := DirectSum.Decomposition.right_inv (ℳ := P)

universe v

variable [CatModule.HasDerivedCategory.{v,0} (WeightCategory
  (TensorProductAlgebra k (parameter k) weights (({()} : Multiset Unit) + {()})))]

private theorem existsWeightTriangleOfHomogeneousMaps {X Y Z : Type}
    [AddCommGroup X] [Module k X] [Module A₂ X] [SMulCommClass A₂ k X]
    [AddCommGroup Y] [Module k Y] [Module A₂ Y] [SMulCommClass A₂ k Y]
    [AddCommGroup Z] [Module k Z] [Module A₂ Z] [SMulCommClass A₂ k Z]
    (P : ℤ → Submodule k X) (Q' : ℤ → Submodule k Y) (R : ℤ → Submodule k Z)
    [SetLike.GradedSMul 𝒜₂ P] [SetLike.GradedSMul 𝒜₂ Q'] [SetLike.GradedSMul 𝒜₂ R]
    [DirectSum.Decomposition P] [DirectSum.Decomposition Q'] [DirectSum.Decomposition R]
    (f : X →ₗ[A₂] Y) (hf : ∀ d {x : X}, x ∈ P d → f x ∈ Q' d)
    (g : Y →ₗ[A₂] Z) (hg : ∀ d {y : Y}, y ∈ Q' d → g y ∈ R d)
    (hi : Function.Injective f) (hex : Function.Exact f g) (hs : Function.Surjective g) :
    let f' := liftedWeightMap k P Q' f hf
    let g' := liftedWeightMap k Q' R g hg
    let L := CatModule.DerivedCategory.Q (C := WeightCategory A₂)
    ∃ δ : L.obj ((totalWeightBimodule k R).left ⟨0⟩) ⟶
      (L.obj ((totalWeightBimodule k P).left ⟨0⟩))⟦(1 : ℤ)⟧,
      Triangle.mk (L.map f') (L.map g') δ ∈ distTriang _ := by
  let f' := liftedWeightMap k P Q' f hf
  let g' := liftedWeightMap k Q' R g hg
  let : DirectSum.Decomposition (fun i => (P i).toAddSubgroup) := addSubgroupDecomposition k P
  let : DirectSum.Decomposition (fun i => (Q' i).toAddSubgroup) := addSubgroupDecomposition k Q'
  let : DirectSum.Decomposition (fun i => (R i).toAddSubgroup) := addSubgroupDecomposition k R
  have hzero : f' ≫ g' = 0 :=
    CatModule.Hom.ext fun _ x => Subtype.ext (hex.apply_apply_eq_zero x.val)
  refine exists_distinguished_weightTriangle_of_exact f' g' hzero ?_ ?_ ?_
  · exact diagramWeightLeftLinearMap_injective
      (fun i => (P i).toAddSubgroup) (fun i => (Q' i).toAddSubgroup)
      (leftModuleWeight k P) (rightScalarWeight k P)
      (leftModuleWeight k Q') (rightScalarWeight k Q') ⟨0⟩ f hf hi
  · exact diagramWeightLeftLinearMap_exact
      (fun i => (P i).toAddSubgroup) (fun i => (Q' i).toAddSubgroup)
      (leftModuleWeight k P) (rightScalarWeight k P)
      (leftModuleWeight k Q') (rightScalarWeight k Q') ⟨0⟩ f hf
      (fun i => (R i).toAddSubgroup) (leftModuleWeight k R) (rightScalarWeight k R) g hg hex
  · exact diagramWeightLeftLinearMap_surjective
      (fun i => (Q' i).toAddSubgroup) (fun i => (R i).toAddSubgroup)
      (leftModuleWeight k Q') (rightScalarWeight k Q')
      (leftModuleWeight k R) (rightScalarWeight k R) ⟨0⟩ g hg hs


/-- The actual internal shift in the first label-two companion gives a distinguished triangle. -/
theorem middleSumWeight_distinguished :
    let L := CatModule.DerivedCategory.Q (C := WeightCategory A₂)
    ∃ δ : L.obj (middleSumWeightModule k 0) ⟶ (L.obj (middleDifferenceWeightModule k 2))⟦(1 : ℤ)⟧,
      Triangle.mk (L.map (middleSumWeightCompanion k)) (L.map (middleSumWeightAugmentation k))
        δ ∈ distTriang _ := by
  let : SetLike.GradedSMul 𝒜₂ ℳ₂ := (middleStandardGFin k (labelTwoGradingDatum k)).gradedSMul
  let : SetLike.GradedSMul 𝒜₂ 𝒬₂ := (middleDotSumQuotientGFin k).gradedSMul
  let : SetLike.GradedSMul 𝒜₂ ℛ₂ := (middleDotDifferenceQuotientGFin k).gradedSMul
  let : DirectSum.Decomposition ℳ₂ := (middleStandardGFin k (labelTwoGradingDatum k)).decomposition
  let : DirectSum.Decomposition 𝒬₂ := (middleDotSumQuotientGFin k).decomposition
  let : DirectSum.Decomposition ℛ₂ := (middleDotDifferenceQuotientGFin k).decomposition
  let sc := middleSumShortExactSequence k
  have hs := middleSumShortExactSequence_exact k
  refine existsWeightTriangleOfHomogeneousMaps k (Graded.shift ℛ₂ 2) ℳ₂ (Graded.shift 𝒬₂ 0)
    (sumCompanionLinear k) ?_ (LinearMap.range (diagramPlus k)).mkQ ?_
    ((ModuleCat.mono_iff_injective sc.f).mp hs.mono_f)
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact sc).mp hs.exact)
    ((ModuleCat.epi_iff_surjective sc.g).mp hs.epi_g)

/-- The actual internal shift in the second label-two companion gives a distinguished triangle. -/
theorem middleDifferenceWeight_distinguished :
    let L := CatModule.DerivedCategory.Q (C := WeightCategory A₂)
    ∃ δ : L.obj (middleDifferenceWeightModule k 0) ⟶ (L.obj (middleSumWeightModule k 2))⟦(1 : ℤ)⟧,
      Triangle.mk (L.map (middleDifferenceWeightCompanion k))
        (L.map (middleDifferenceWeightAugmentation k)) δ ∈ distTriang _ := by
  let : SetLike.GradedSMul 𝒜₂ ℳ₂ := (middleStandardGFin k (labelTwoGradingDatum k)).gradedSMul
  let : SetLike.GradedSMul 𝒜₂ 𝒬₂ := (middleDotSumQuotientGFin k).gradedSMul
  let : SetLike.GradedSMul 𝒜₂ ℛ₂ := (middleDotDifferenceQuotientGFin k).gradedSMul
  let : DirectSum.Decomposition ℳ₂ := (middleStandardGFin k (labelTwoGradingDatum k)).decomposition
  let : DirectSum.Decomposition 𝒬₂ := (middleDotSumQuotientGFin k).decomposition
  let : DirectSum.Decomposition ℛ₂ := (middleDotDifferenceQuotientGFin k).decomposition
  let sc := middleDifferenceShortExactSequence k
  have hs := middleDifferenceShortExactSequence_exact k
  refine existsWeightTriangleOfHomogeneousMaps k (Graded.shift 𝒬₂ 2) ℳ₂ (Graded.shift ℛ₂ 0)
    (differenceCompanionLinear k) ?_ (LinearMap.range (diagramMinus k)).mkQ ?_
    ((ModuleCat.mono_iff_injective sc.f).mp hs.mono_f)
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact sc).mp hs.exact)
    ((ModuleCat.epi_iff_surjective sc.g).mp hs.epi_g)

end Categorification.Stendhal.LabelTwo
