/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoIncomingLiftTensor
import Categorification.WeightedKLR.RedStrands.LabelTwoIncomingExteriorAcyclic
import Categorification.WeightedKLR.RedStrands.LabelTwoMiddleOrdinaryTensor
import Categorification.Algebra.BalancedTensorReflection
import Categorification.Algebra.DerivedTensorOrdinaryLinear

import Categorification.WeightedKLR.RedStrands.LabelTwoIncomingLiftNonzero
import Categorification.WeightedKLR.RedStrands.LabelTwoIncomingLiftSequence
import Categorification.WeightedKLR.RedStrands.LabelTwoIncomingMiddleMixed
import Categorification.Algebra.DerivedHomologyShift

/-!
# The incoming coefficient map on the first Tor of the middle cokernel

The reflected incoming crossing acts nontrivially on first ambient Tor
with the incoming cokernel. Move the detecting tensor through reflection
and use the boundary map of the incoming preimage sequence.
-/

set_option backward.isDefEq.respectTransparency false

namespace Categorification.Stendhal.LabelTwo

open KLR CategoryTheory DG DG.DerivedCategory MulOpposite
open scoped DG.DegreeZero

noncomputable section

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe w
section CoefficientNonvanishing

variable {𝕜 A M M' X : Type} [Field 𝕜] [Ring A] [Algebra 𝕜 A]
    [AddCommGroup M] [Module 𝕜 M] [Module A M] [Module Aᵐᵒᵖ M]
    [IsScalarTower 𝕜 A M] [SMulCommClass 𝕜 Aᵐᵒᵖ M]
    [AddCommGroup M'] [Module 𝕜 M'] [Module A M'] [Module Aᵐᵒᵖ M']
    [IsScalarTower 𝕜 A M'] [SMulCommClass 𝕜 Aᵐᵒᵖ M']
    [AddCommGroup X] [Module 𝕜 X] [Module A X] [Module Aᵐᵒᵖ X]
    [IsScalarTower 𝕜 A X] [SMulCommClass 𝕜 Aᵐᵒᵖ X]
    [DG.HasDerivedCategory.{w,0} 𝕜] [DG.HasDerivedCategory.{w,0} A]

private theorem coefficientMap_nonzero_of_reflection (σ : A → A) (hσ : Function.Involutive σ)
    (hR : ∀ (a : A) (m : M'), op a • m = σ a • m)
    (hX : ∀ (a : A) (m : X), op a • m = σ a • m)
    (hGround : ∀ (c : 𝕜) (m : M'), op (algebraMap 𝕜 A c) • m = c • m)
    (f : M →ₗ[A] M') (hf : ∀ (a : A) (m : M), f (op a • m) = op a • f m)
    (hnz : BalancedTensor.mapRight (k := 𝕜) (B := 𝕜) (M := X) f ≠ 0) :
    (homologyFunctor 𝕜 0).map
      ((derivedTensorCoefficientMap (f.restrictScalars 𝕜) hf).app
        (Q.obj (DGModuleCat.of A (InDegreeZero X)))) ≠ 0 := by
  intro hz
  apply hnz
  apply BalancedTensor.ext
  intro x m
  change BalancedTensor.tmul x (f m) = 0
  have h := ambientH0CoefficientMap_tmul (f.restrictScalars 𝕜) hf m x
  rw [hz] at h
  have hv : TensorProductOver.tmul A (f m) x = 0 :=
    h.symm.trans ((ambientDerivedTensorH0Equiv (N := M') X).map_zero)
  let e₁ := ordinaryBalancedTensorAddEquiv (A := 𝕜) (N := X) hGround
  let e₂ := BalancedTensor.reflectionSwap (k := 𝕜) σ hσ hR hX
  have h₁ := congrArg (fun z => e₂ (e₁ z)) hv
  change BalancedTensor.tmul x (f m) = e₂ (e₁ 0) at h₁
  rw [map_zero, map_zero] at h₁
  exact h₁

end CoefficientNonvanishing

open CategoryTheory.Limits CategoryTheory.Pretriangulated

section CoefficientConnectingMap

variable {𝕜 A M M' : Type} [Field 𝕜] [Ring A]
    [AddCommGroup M] [Module 𝕜 M] [Module Aᵐᵒᵖ M] [SMulCommClass 𝕜 Aᵐᵒᵖ M]
    [AddCommGroup M'] [Module 𝕜 M'] [Module Aᵐᵒᵖ M'] [SMulCommClass 𝕜 Aᵐᵒᵖ M']
    [DG.HasDerivedCategory.{w,0} 𝕜] [DG.HasDerivedCategory.{w,0} A]

private theorem coefficientMap_ne_zero_of_shortExact
    (f : M →ₗ[𝕜] M') (hf : ∀ (a : A) (m : M), f (op a • m) = op a • f m)
    (S : ShortComplex (ModuleCat A)) (hS : S.ShortExact)
    (hMiddle : IsZero ((homologyFunctor 𝕜 0).obj ((derivedTensor 𝕜 A M).obj
      (Q.obj (DGModuleCat.of A (InDegreeZero S.X₂))))))
    (hMap : (homologyFunctor 𝕜 0).map ((derivedTensorCoefficientMap f hf).app
      (Q.obj (DGModuleCat.of A (InDegreeZero S.X₁)))) ≠ 0) :
    (homologyFunctor 𝕜 (-1)).map ((derivedTensorCoefficientMap f hf).app
      (Q.obj (DGModuleCat.of A (InDegreeZero S.X₃)))) ≠ 0 := by
  let C := S.map (degreeZeroModuleFunctor A)
  have hC : C.ShortExact := degreeZeroModuleFunctor_shortExact _ hS
  obtain ⟨δ,hδ⟩ := exists_distinguished_of_shortExact C hC
  let D := Triangle.mk (Q.map C.f) (Q.map C.g) δ
  have hD : D ∈ distTriang (DerivedCategory.{w,0} A) := hδ
  let F := derivedTensor.{w} 𝕜 A M
  let φ := derivedTensorCoefficientTriangleMap f hf D
  exact homology_map_ne_zero_of_middle_next_isZero 𝕜 (F.map_distinguished D hD) φ (-1) hMiddle hMap

end CoefficientConnectingMap

variable (k : Type) [Field k]
local notation "ν" => (({()} : Multiset Unit) + {()})
local notation "T" => TensorProductAlgebra k (parameter k) weights ν
local notation "TRaw" => TensorProductAlgebra k (parameter k)
  (fun (_ : Fin 2) => Finsupp.single () 2) (Multiset.replicate 2 ())
local notation "P" => labelTwoRightExteriorDividedStandard (parameter k)
local notation "J" => incomingLiftSubmodule k
local notation "C" => StandardDotSumQuotient k
local notation "R" => MiddleTensorCoefficient k
local notation "I" => IncomingExteriorCoefficient k
local notation "L" => IncomingLiftCoefficient k

local instance : Module T P := inferInstanceAs (Module TRaw P)
local instance : Module Tᵐᵒᵖ I := inferInstanceAs (Module TRawᵐᵒᵖ I)
local instance : SMulCommClass k Tᵐᵒᵖ I := inferInstanceAs (SMulCommClass k TRawᵐᵒᵖ I)
local instance : Module T I := inferInstanceAs (Module TRaw P)
local instance : Module T R := inferInstanceAs (Module T C)
local instance : Module T L := inferInstanceAs (Module T J)
local instance : IsScalarTower k T I := inferInstanceAs (IsScalarTower k TRaw P)
local instance : IsScalarTower k T R := inferInstanceAs (IsScalarTower k T C)
local instance : IsScalarTower k T L := inferInstanceAs (IsScalarTower k T J)

private abbrev reflectedScalar (a : T) : T :=
  (tensorReflect (Q := parameter k) (Λ := weights) («ν» := ν) a).unop

private theorem reflectedScalar_involutive : Function.Involutive (reflectedScalar k) :=
  unop_tensorReflect_unop_tensorReflect

/-- The incoming map on right modules obtained by horizontal reflection. -/
def reflectedIncomingMap : I →ₗ[k] R := (normalizedIncoming k).restrictScalars k

/-- The reflected incoming map is right linear. -/
theorem reflectedIncomingMap_op_smul (a : T) (z : I) :
    reflectedIncomingMap k (op a • z) = op a • reflectedIncomingMap k z := by
  change normalizedIncoming k (reflectedScalar k a • (show P from z)) =
    reflectedScalar k a • normalizedIncoming k (show P from z)
  exact (normalizedIncoming k).map_smul _ _

private theorem reflected_middle_action (a : T) (z : R) :
    op a • z = reflectedScalar k a • z :=
  middleTensorCoefficient_op_smul k a z

variable [DG.HasDerivedCategory.{w,0} k]
  [DG.HasDerivedCategory.{w,0} (TensorProductAlgebra k (parameter k) weights (({()} : Multiset Unit) + {()}))]

/-- A nonzero ordinary incoming tensor map yields a nonzero degree-zero
derived map in the reflected coefficient. -/
theorem incomingLiftH0CoefficientMap_nonzero_of_balanced
    (hnz : BalancedTensor.mapRight (k := k) (B := k) (M := L) (normalizedIncoming k) ≠ 0) :
    (homologyFunctor k 0).map
      ((derivedTensorCoefficientMap (reflectedIncomingMap k) (reflectedIncomingMap_op_smul k)).app
        (Q.obj (DGModuleCat.of T (InDegreeZero L)))) ≠ 0 := by
  let f : I →ₗ[T] R := normalizedIncoming k
  have hf (a : T) (z : I) : f (op a • z) = op a • f z :=
    reflectedIncomingMap_op_smul k a z
  have hJ (a : T) (z : L) : op a • z = reflectedScalar k a • z :=
    incomingLiftCoefficient_op_smul k a z
  have hb : BalancedTensor.mapRight (k := k) (B := k) (M := L) f ≠ 0 := hnz
  exact coefficientMap_nonzero_of_reflection (𝕜 := k) (A := T) (M := I) (M' := R) (X := L) (reflectedScalar k)
    (reflectedScalar_involutive k) (reflected_middle_action k) hJ
    (middleTensorCoefficient_algebraMap_smul k) f hf hb

open CategoryTheory.Limits CategoryTheory.Pretriangulated

/-- The incoming exterior coefficient has a nonzero map to the middle
coefficient on the first ambient Tor of the incoming cokernel. -/
theorem incomingCokernelTorOne_map_nonzero :
    (homologyFunctor k (-1)).map
      ((derivedTensorCoefficientMap (reflectedIncomingMap k) (reflectedIncomingMap_op_smul k)).app
        (Q.obj (DGModuleCat.of T (InDegreeZero (IncomingMiddleCokernel k))))) ≠ 0 := by
  let S := incomingLiftShortComplex k
  have hMiddle := incomingMiddleStandardHomology_zero_isZero k
  have hMap := incomingLiftH0CoefficientMap_nonzero_of_balanced k (incomingLiftTensorMap_nonzero k)
  exact coefficientMap_ne_zero_of_shortExact (reflectedIncomingMap k)
    (reflectedIncomingMap_op_smul k) S (incomingLiftShortComplex_shortExact k) hMiddle hMap

end
end Categorification.Stendhal.LabelTwo
