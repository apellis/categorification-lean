/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DerivedTensorTriangulated
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Derived tensor models for Webster cups and caps

Webster, arXiv:1309.3796v2, Definition 7.4. A coefficient left
module induces the cap by derived tensor. Its scalar dual induces the
cup with a specified cohomological shift. For finite-dimensional coefficients
the ordinary tensor-Hom identification intertwines the right algebra
action with precomposition. These are models after forgetting the internal grading.
-/

noncomputable section

namespace Categorification.Stendhal.Coevaluation

open CategoryTheory DG MulOpposite
open scoped DG.DegreeZero TensorProduct

universe u v
variable (k A : Type u) [Field k] [Ring A] [Algebra k A]
  (L : Type u) [AddCommGroup L] [Module k L] [Module A L] [IsScalarTower k A L]

/-- The coefficient of the cup is the linear dual of the left coefficient module. -/
def CupCoefficient := Module.Dual k L

instance : AddCommGroup (CupCoefficient k L) := inferInstanceAs (AddCommGroup (Module.Dual k L))

instance : Module k (CupCoefficient k L) := inferInstanceAs (Module k (Module.Dual k L))

private def leftAction (a : A) : L →ₗ[k] L where
  toFun x := a • x
  map_add' := smul_add a
  map_smul' c x := smul_algebra_smul_comm c a x

private def dualAction : Aᵐᵒᵖ →+* Module.End k (CupCoefficient k L) where
  toFun a := (leftAction k A L a.unop).dualMap
  map_zero' := LinearMap.ext fun f => LinearMap.ext fun x => by
    change f ((0 : A) • x) = 0
    rw [zero_smul, map_zero]
  map_one' := LinearMap.ext fun f => LinearMap.ext fun x => by
    change f ((1 : A) • x) = f x
    rw [one_smul]
  map_add' a b := LinearMap.ext fun f => LinearMap.ext fun x => by
    change f ((a.unop + b.unop) • x) = f (a.unop • x) + f (b.unop • x)
    rw [add_smul, map_add]
  map_mul' a b := LinearMap.ext fun f => LinearMap.ext fun x => by
    change f ((b.unop * a.unop) • x) = f (b.unop • (a.unop • x))
    rw [mul_smul]

instance : Module Aᵐᵒᵖ (CupCoefficient k L) := Module.compHom _ (dualAction k A L)

theorem cup_op_smul_apply (a : A) (f : CupCoefficient k L) (x : L) :
    (show Module.Dual k L from op a • f) x = (show Module.Dual k L from f) (a • x) := rfl

private def scalarUnop : kᵐᵒᵖ →+* k where
  toFun := unop
  map_one' := rfl
  map_zero' := rfl
  map_add' := unop_add
  map_mul' a b := (unop_mul a b).trans (mul_comm _ _)

instance : Module kᵐᵒᵖ (CupCoefficient k L) := Module.compHom _ (scalarUnop k)

instance : SMulCommClass Aᵐᵒᵖ kᵐᵒᵖ (CupCoefficient k L) where
  smul_comm a c f := by
    change (dualAction k A L a) (c.unop • f) = c.unop • (dualAction k A L a) f
    exact map_smul (dualAction k A L a) _ _

private instance : SMulCommClass A k L where
  smul_comm a c x := smul_algebra_smul_comm c a x

/-- The algebraic dual-tensor model of the unshifted cup from Definition 7.4.
Its coefficient still carries the Webster action, by precomposition. -/
def cupFunctor [HasDerivedCategory.{v,u} k] [HasDerivedCategory.{v,u} Aᵐᵒᵖ] :
    DerivedCategory.{v,u} k ⥤ DerivedCategory.{v,u} Aᵐᵒᵖ :=
  derivedTensor Aᵐᵒᵖ k (CupCoefficient k L)

/-- Apply the specified cohomological shift after the cup. -/
def shiftedCupFunctor [HasDerivedCategory.{v,u} k] [HasDerivedCategory.{v,u} Aᵐᵒᵖ]
    (shift : ℤ) : DerivedCategory.{v,u} k ⥤ DerivedCategory.{v,u} Aᵐᵒᵖ :=
  cupFunctor k A L ⋙ shiftFunctor (DerivedCategory.{v,u} Aᵐᵒᵖ) shift

/-- Ordinary coefficient model of the cap of Definition 7.4. -/
def capFunctor [HasDerivedCategory.{v,u} k] [HasDerivedCategory.{v,u} Aᵐᵒᵖ] :
    DerivedCategory.{v,u} Aᵐᵒᵖ ⥤ DerivedCategory.{v,u} k :=
  derivedTensor k Aᵐᵒᵖ (OpBimodule A L)

section Triangulated

variable [HasDerivedCategory.{v,u} k] [HasDerivedCategory.{v,u} Aᵐᵒᵖ]

instance : (cupFunctor k A L).CommShift ℤ := by
  unfold cupFunctor
  infer_instance

instance : (cupFunctor k A L).IsTriangulated := by
  unfold cupFunctor
  infer_instance

instance : (capFunctor k A L).CommShift ℤ := by
  unfold capFunctor
  infer_instance

instance : (capFunctor k A L).IsTriangulated := by
  unfold capFunctor
  infer_instance

end Triangulated

/-- The finite-dimensional cup coefficient computes the expected scalar Hom
on ordinary modules. -/
def cupTensorHomEquiv [FiniteDimensional k L] (V : Type u) [AddCommGroup V] [Module k V] :
    CupCoefficient k L ⊗[k] V ≃ₗ[k] (L →ₗ[k] V) :=
  dualTensorHomEquiv k L V

/-- On a pure tensor, the opposite algebra action corresponds to precomposition
by its left action on the coefficient module. -/
theorem cupTensorHomEquiv_op_tmul [FiniteDimensional k L]
    {V : Type u} [AddCommGroup V] [Module k V]
    (a : A) (f : CupCoefficient k L) (v : V) (x : L) :
    cupTensorHomEquiv k L V ((op a • f : CupCoefficient k L) ⊗ₜ[k] v) x =
      cupTensorHomEquiv k L V (f ⊗ₜ[k] v) (a • x) :=
  rfl

end Categorification.Stendhal.Coevaluation
