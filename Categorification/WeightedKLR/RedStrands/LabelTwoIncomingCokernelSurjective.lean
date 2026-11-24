/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoIncomingCokernelTor

/-!
# The incoming map onto the first Tor of the middle cokernel

The connecting map embeds the first Tor target into the line detected
by the balanced incoming-preimage readout. A nonzero map onto such a
subspace is surjective.
-/

namespace Categorification.Stendhal.LabelTwo

open KLR CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated DG DG.DerivedCategory MulOpposite
open scoped DG.DegreeZero
noncomputable section

universe w

private theorem surjective_of_ne_zero_of_injective_to_scalar
    {k V W : Type*} [Field k] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (f : V →ₗ[k] W) (i : W →ₗ[k] k) (hi : Function.Injective i) (hf : f ≠ 0) :
    Function.Surjective f := by
  have hx : ∃ x, f x ≠ 0 := by
    by_contra! h
    exact hf (LinearMap.ext fun x => h x)
  obtain ⟨x,hx⟩ := hx
  have hn : i (f x) ≠ 0 := fun h => hx (hi (h.trans i.map_zero.symm))
  intro y
  refine ⟨(i y / i (f x)) • x, hi ?_⟩
  rw [f.map_smul, i.map_smul, smul_eq_mul, div_mul_cancel₀ _ hn]

private def balancedEquivLinear {k A M N : Type*} [Field k] [Ring A] [Algebra k A]
    [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M] [SMulCommClass k Aᵐᵒᵖ M]
    [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
    (hg : ∀ (c : k) (m : M), op (algebraMap k A c) • m = c • m) :
    TensorProductOver A M N ≃ₗ[k] BalancedTensor k k A M N where
  __ := ordinaryBalancedTensorAddEquiv (A := k) hg
  map_smul' c x := by
    change ordinaryBalancedTensorAddEquiv (A := k) hg (c • x) =
      c • ordinaryBalancedTensorAddEquiv (A := k) hg x
    induction x using TensorProductOver.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | tmul m n =>
      rw [TensorProductOver.smul_tmul, ordinaryBalancedTensorAddEquiv_tmul,
        ordinaryBalancedTensorAddEquiv_tmul]
      rfl
    | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

variable {k A R : Type} [Field k] [Ring A] [Algebra k A]
    [AddCommGroup R] [Module k R] [Module Aᵐᵒᵖ R] [SMulCommClass k Aᵐᵒᵖ R]
    [DG.HasDerivedCategory.{w,0} k] [DG.HasDerivedCategory.{w,0} A]

private local instance : (homologyFunctor (A := k) k 0).ShiftSequence ℤ := by
  let : (DG.HomotopyCategory.homologyFunctor.{0} k k 0).ShiftSequence ℤ := by
    change (DG.HomotopyCategory.forget.{0} k k ⋙
      _root_.HomotopyCategory.homologyFunctor (ModuleCat k) (ComplexShape.up ℤ) 0).ShiftSequence ℤ
    infer_instance
  exact Functor.ShiftSequence.induced (homologyFunctorFactorsh k 0) ℤ
    (homologyFunctor k) (homologyFunctorFactorsh k)

private abbrev ambientObject (X : ModuleCat A) :=
  (derivedTensor k A R).obj (Q.obj (DGModuleCat.of A (InDegreeZero X)))

private noncomputable def injectIntoH0OfShortExact
    (S : ShortComplex (ModuleCat A)) (hS : S.ShortExact)
    (h : IsZero ((homologyFunctor (A := k) k (-1)).obj (ambientObject (k := k) (R := R) S.X₂))) :
    { j : (homologyFunctor (A := k) k (-1)).obj (ambientObject (k := k) (R := R) S.X₃) ⟶
      (homologyFunctor (A := k) k 0).obj (ambientObject (k := k) (R := R) S.X₁) // Mono j } := by
  let C := S.map (degreeZeroModuleFunctor A)
  let ex := exists_distinguished_of_shortExact C (degreeZeroModuleFunctor_shortExact S hS)
  let δ := Classical.choose ex
  let D := Triangle.mk (Q.map C.f) (Q.map C.g) δ
  let F := derivedTensor k A R
  let D' := F.mapTriangle.obj D
  have hd : D' ∈ distTriang _ := F.map_distinguished D (Classical.choose_spec ex)
  let G := homologyFunctor (A := k) k 0
  let δ' := G.homologySequenceδ D' (-1) 0 (by decide)
  have hm : Mono δ' :=
    (G.homologySequence_exact₃ D' hd (-1) 0 (by decide)).mono_g_iff.mpr
      (h.eq_of_src _ _)
  exact ⟨δ', hm⟩

section LabelTwo

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable (l : Type) [Field l]
local notation "ν" => (({()} : Multiset Unit) + {()})
local notation "T" => TensorProductAlgebra l (parameter l) weights ν
local notation "J" => incomingLiftSubmodule l
local notation "L" => IncomingLiftCoefficient l
local notation "C" => StandardDotSumQuotient l
local notation "R" => MiddleTensorCoefficient l

local notation "TRaw" => TensorProductAlgebra l (parameter l)
  (fun (_ : Fin 2) => Finsupp.single () 2) (Multiset.replicate 2 ())
local notation "I" => IncomingExteriorCoefficient l

local instance : Module Tᵐᵒᵖ I := inferInstanceAs (Module TRawᵐᵒᵖ I)
local instance : SMulCommClass l Tᵐᵒᵖ I := inferInstanceAs (SMulCommClass l TRawᵐᵒᵖ I)

local instance : Module T R := inferInstanceAs (Module T C)
local instance : Module T L := inferInstanceAs (Module T J)
local instance : IsScalarTower l T R := inferInstanceAs (IsScalarTower l T C)
local instance : IsScalarTower l T L := inferInstanceAs (IsScalarTower l T J)

private abbrev reflectedScalar (a : T) : T :=
  (tensorReflect (Q := parameter l) (Λ := weights) («ν» := ν) a).unop

variable [DG.HasDerivedCategory.{w,0} l]
  [DG.HasDerivedCategory.{w,0} (TensorProductAlgebra l (parameter l) weights (({()} : Multiset Unit) + {()}))]

private def liftOriginalH0Equiv [NeZero (2 : l)] :
    (homologyFunctor (A := l) l 0).obj (ambientObject (k := l) («R» := R) (ModuleCat.of T J)) ≃ₗ[l] l :=
  let e₁ := ambientDerivedTensorH0Equiv (k := l) (A := T) (N := R) J
  let e₂ := balancedEquivLinear (N := L) (middleTensorCoefficient_algebraMap_smul l)
  let e₃ := BalancedTensor.reflectionSwap (k := l) (M := R) (N := L) (reflectedScalar l)
    unop_tensorReflect_unop_tensorReflect (middleTensorCoefficient_op_smul l)
    (incomingLiftCoefficient_op_smul l)
  e₁.trans (e₂.trans (e₃.trans (incomingLiftTensorEquiv l)))

/-- If the ambient middle standard is acyclic in degree −1, the line
detected by the reflected incoming crossing exhausts the first Tor target. -/
theorem incomingCokernelTorOne_map_surjective_of_middleAcyclic [NeZero (2 : l)]
    (h : IsZero ((homologyFunctor l (-1)).obj
      (ambientObject (k := l) («R» := R) (ModuleCat.of T (Standard l))))) :
    Function.Surjective ((homologyFunctor l (-1)).map
      ((derivedTensorCoefficientMap (reflectedIncomingMap l) (reflectedIncomingMap_op_smul l)).app
        (Q.obj (DGModuleCat.of T (InDegreeZero (IncomingMiddleCokernel l)))))) := by
  let S := incomingLiftShortComplex l
  let j := injectIntoH0OfShortExact (k := l) («R» := R) S (incomingLiftShortComplex_shortExact l) h
  have hj : Function.Injective j.val := (ModuleCat.mono_iff_injective j.val).mp j.property
  let e := liftOriginalH0Equiv l
  exact surjective_of_ne_zero_of_injective_to_scalar _ (e.toLinearMap.comp j.val.hom)
    (e.injective.comp hj) (fun hz => incomingCokernelTorOne_map_nonzero l (ModuleCat.hom_ext hz))

end LabelTwo

end
end Categorification.Stendhal.LabelTwo
