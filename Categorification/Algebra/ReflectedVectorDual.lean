/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.TwistedVectorDual
import Categorification.Algebra.DualRightModule
import Categorification.Algebra.DerivedTensor

/-!
# Reflection and the vector-space dual

A reflection changes handedness. An involutive reflection applied to
the twisted dual therefore gives the ordinary right dual of a left
module, with the usual action by precomposition.
-/

namespace Categorification

open MulOpposite

noncomputable section

universe u v

variable {k A : Type*} [Field k] [Ring A] [Algebra k A]

/-- A left module regarded as a right module using an algebra anti-homomorphism. -/
def ReflectedRight (_τ : A →ₐ[k] Aᵐᵒᵖ) (M : Type u) := M

namespace ReflectedRight

variable (τ : A →ₐ[k] Aᵐᵒᵖ) {M : Type u} [AddCommGroup M] [Module k M] [Module A M]

instance : AddCommGroup (ReflectedRight τ M) := inferInstanceAs (AddCommGroup M)
instance : Module k (ReflectedRight τ M) := inferInstanceAs (Module k M)
instance : Module Aᵐᵒᵖ (ReflectedRight τ M) :=
  Module.compHom M ((RingEquiv.opOp A).symm.toRingHom.comp τ.toRingHom.op)

omit [Module k M] in
/-- A right scalar acts by the reflected left scalar. -/
theorem op_smul (a : A) (m : ReflectedRight τ M) :
    (op a • m : ReflectedRight τ M) = ((τ a).unop • (show M from m) : M) := rfl

variable [IsScalarTower k A M]

instance : IsScalarTower k Aᵐᵒᵖ (ReflectedRight τ M) := by
  apply IsScalarTower.of_algebraMap_smul
  intro c m
  change (op (algebraMap k A c) • m : ReflectedRight τ M) = c • m
  rw [op_smul, AlgHom.commutes]
  exact algebraMap_smul A c (show M from m)

instance : SMulCommClass k Aᵐᵒᵖ (ReflectedRight τ M) := by
  constructor
  intro c a m
  obtain ⟨a,rfl⟩ := op_surjective a
  rw [op_smul, op_smul]
  exact smul_comm c (τ a).unop (show M from m)

variable {N : Type v} [AddCommGroup N] [Module A N]

/-- An equivalence of left modules gives an equivalence after reflection. -/
def ofLinearEquiv (e : M ≃ₗ[A] N) : ReflectedRight τ M ≃ₗ[Aᵐᵒᵖ] ReflectedRight τ N where
  toFun m := e (show M from m)
  invFun n := e.symm (show N from n)
  left_inv := e.left_inv
  right_inv := e.right_inv
  map_add' := e.map_add
  map_smul' a m := by
    obtain ⟨a,rfl⟩ := op_surjective a
    exact e.map_smul (τ a).unop (show M from m)

/-- Reflecting the twisted dual gives the ordinary evaluation rule
for the right dual of a left module. -/
theorem twistDual_op_smul_apply
    (hτ : ∀ a : A, (τ (τ a).unop).unop = a)
    (a : A) (f : ReflectedRight τ (TwistDual τ M)) (m : M) :
    (TwistDual.toDual τ (show TwistDual τ M from op a • f)) m =
      (TwistDual.toDual τ (show TwistDual τ M from f)) (a • m) := by
  change TwistDual.toDual τ ((τ a).unop • (show TwistDual τ M from f)) m = _
  rw [TwistDual.smul_apply, hτ]

end ReflectedRight

namespace VectorDualRight

variable (k A) (M : Type u) [AddCommGroup M] [Module k M] [Module A M]
  [IsScalarTower k A M]

/-- The ordinary vector-space dual of a left module, as a right module. -/
def RightDual := Module.Dual k (OpBimodule A M)

instance : AddCommGroup (RightDual k A M) := inferInstanceAs (AddCommGroup (Module.Dual k M))
instance : Module k (RightDual k A M) := inferInstanceAs (Module k (Module.Dual k M))

local instance doubleOppositeTower : IsScalarTower k Aᵐᵒᵖᵐᵒᵖ (OpBimodule A M) :=
  IsScalarTower.of_algebraMap_smul fun c m => algebraMap_smul A c (show M from m)

instance : Module Aᵐᵒᵖ (RightDual k A M) :=
  DualRightModule.dualModule k Aᵐᵒᵖ (OpBimodule A M)

/-- The ordinary right dual acts by precomposition with the left action. -/
theorem op_smul_apply (a : A) (f : RightDual k A M) (m : M) :
    (show Module.Dual k M from op a • f) m = (show Module.Dual k M from f) (a • m) :=
  rfl

variable {k A M}

/-- Under an involution, the reflection of the twisted dual is the ordinary
right dual by the identity on linear functionals. -/
def reflectedTwistDualEquiv (τ : A →ₐ[k] Aᵐᵒᵖ)
    (hτ : ∀ a : A, (τ (τ a).unop).unop = a) :
    ReflectedRight τ (TwistDual τ M) ≃ₗ[Aᵐᵒᵖ] RightDual k A M where
  toFun z := z
  invFun z := z
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a z := by
    obtain ⟨a,rfl⟩ := op_surjective a
    apply LinearMap.ext
    intro m
    exact (ReflectedRight.twistDual_op_smul_apply τ hτ a z m).trans
      (op_smul_apply k A M a z m).symm

/-- A self-duality for the twisted left dual identifies the reflected module
with the ordinary right vector-space dual. -/
def reflectedEquivOfTwistDual (τ : A →ₐ[k] Aᵐᵒᵖ)
    (hτ : ∀ a : A, (τ (τ a).unop).unop = a) (e : M ≃ₗ[A] TwistDual τ M) :
    ReflectedRight τ M ≃ₗ[Aᵐᵒᵖ] RightDual k A M :=
  (ReflectedRight.ofLinearEquiv (N := TwistDual τ M) τ e).trans (reflectedTwistDualEquiv τ hτ)

end VectorDualRight
end
end Categorification
