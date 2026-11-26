/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TensorFormOrdered

/-!
# Bar-twisted duals of tensor products

For a `ℚ(v)`-vector space `M`, `ConjDual M` is the space of `ℚ(v)`-linear functionals on `M`
with `ℚ(v)` acting through the bar involution. For the ordered tensor product `V_λ`, `U_q` acts
on `ConjDual V_λ` by `ξ ↦ ξ ∘ τ(u)` (`dualAction`), where `τ` is the anti-automorphism of the
form of B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
Proposition 4.33, and `x ↦ B(x, -)` is a `U_q`-linear map `V_λ → ConjDual V_λ` (`formDual`).
The class of a finite-dimensional module, read through the form of Theorem 4.38, lands in
`ConjDual V_λ`; this is the setting of Webster's Corollary 6.10.

## Main definitions and results

* `ConjDual M`, `ConjDual.precomp`, `ConjDual.eval`.
* `dualAction wt` : `U_q →ₐ[ℚ(v)] End (ConjDual V_λ)`, `u ↦ (ξ ↦ ξ ∘ τ(u))`.
* `formDual wt` : `V_λ →ₗ[ℚ(v)] ConjDual V_λ`, `x ↦ B(x, -)`, and `formDual_rho`.
-/

noncomputable section

namespace Categorification.Stendhal.FirstWeight

open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF

local notation "𝕂" => RatFunc ℚ
local notation "v" => (RatFunc.X : 𝕂)
local instance tensorConjDualInst1 : NeZero v := ⟨RatFunc.X_ne_zero⟩


/-- `ℚ(v)`-linear functionals on `M`, with `ℚ(v)` acting through the bar involution. -/
def ConjDual (M : Type*) [AddCommGroup M] [Module 𝕂 M] : Type _ := M →ₗ[𝕂] 𝕂

namespace ConjDual

variable {M : Type*} [AddCommGroup M] [Module 𝕂 M]

instance : AddCommGroup (ConjDual M) := inferInstanceAs (AddCommGroup (M →ₗ[𝕂] 𝕂))

instance : Module 𝕂 (ConjDual M) := Module.compHom (M →ₗ[𝕂] 𝕂) barRingHom

/-- A functional, as an element of the bar-twisted dual. -/
def of : (M →ₗ[𝕂] 𝕂) ≃+ ConjDual M := AddEquiv.refl _

theorem smul_of (c : 𝕂) (f : M →ₗ[𝕂] 𝕂) : c • of f = of (barRingHom c • f) := rfl

/-- `ξ ↦ ξ ∘ g` on the bar-twisted dual. -/
def precomp (g : M →ₗ[𝕂] M) : ConjDual M →ₗ[𝕂] ConjDual M where
  toFun ξ := of ((of.symm ξ).comp g)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem precomp_of (g : M →ₗ[𝕂] M) (f : M →ₗ[𝕂] 𝕂) : precomp g (of f) = of (f.comp g) := rfl

/-- Evaluation at a vector, a bar-semilinear functional on the bar-twisted dual. -/
def eval (w : M) : ConjDual M →ₛₗ[barRingHom] 𝕂 where
  toFun ξ := of.symm ξ w
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem eval_of (w : M) (f : M →ₗ[𝕂] 𝕂) : eval w (of f) = f w := rfl

theorem ext {ξ ξ' : ConjDual M} (h : ∀ w, eval w ξ = eval w ξ') : ξ = ξ' :=
  LinearMap.ext h

end ConjDual

section Tensor

variable {I Y : Type*} [DecidableEq I] [AddCommGroup Y] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} [Finite I] (hR : R.IsXRegular) {n : ℕ}

local notation "𝕌" => LieLean.QuantumGroup R v

/-- **`U_q` on the bar-twisted dual of `V_λ`**: `u ξ = ξ ∘ τ(u)`, with `τ` the anti-automorphism
of Webster's form (arXiv:1309.3796v2, Proposition 4.33). -/
def dualAction (wt : Fin n → Dom R) : 𝕌 →ₐ[𝕂] Module.End 𝕂 (ConjDual (TensorSpace wt)) where
  toFun u := ConjDual.precomp (tensorRepresentation wt (barHom R (rho R v u)))
  map_one' := LinearMap.ext fun ξ => ConjDual.ext fun w => by
    change ConjDual.of.symm ξ (tensorRepresentation wt (barHom R (rho R v 1)) w) = _
    rw [rho_one, map_one, map_one]
    rfl
  map_mul' a b := LinearMap.ext fun ξ => ConjDual.ext fun w => by
    change ConjDual.of.symm ξ (tensorRepresentation wt (barHom R (rho R v (a * b))) w) =
      ConjDual.of.symm ξ (tensorRepresentation wt (barHom R (rho R v b))
        (tensorRepresentation wt (barHom R (rho R v a)) w))
    rw [rho_mul, map_mul, map_mul, Module.End.mul_apply]
  map_zero' := LinearMap.ext fun ξ => ConjDual.ext fun w => by
    change ConjDual.of.symm ξ (tensorRepresentation wt (barHom R (rho R v 0)) w) = 0
    rw [map_zero, map_zero, map_zero, LinearMap.zero_apply, map_zero]
  map_add' a b := LinearMap.ext fun ξ => ConjDual.ext fun w => by
    change ConjDual.of.symm ξ (tensorRepresentation wt (barHom R (rho R v (a + b))) w) =
      ConjDual.of.symm ξ (tensorRepresentation wt (barHom R (rho R v a)) w) +
        ConjDual.of.symm ξ (tensorRepresentation wt (barHom R (rho R v b)) w)
    rw [map_add, map_add, map_add, LinearMap.add_apply, map_add]
  commutes' c := LinearMap.ext fun ξ => ConjDual.ext fun w => by
    rw [Module.algebraMap_end_apply, map_smulₛₗ]
    change ConjDual.of.symm ξ (tensorRepresentation wt (barHom R (rho R v (algebraMap 𝕂 _ c))) w) = _
    rw [rho_algebraMap, barHom_algebraMap, AlgHom.commutes, Module.algebraMap_end_apply, map_smul]
    rfl

omit [Finite I] in
theorem dualAction_of (wt : Fin n → Dom R) (u : 𝕌) (f : TensorSpace wt →ₗ[𝕂] 𝕂) :
    dualAction wt u (ConjDual.of f) =
      ConjDual.of (f.comp (tensorRepresentation wt (barHom R (rho R v u)))) := rfl

/-- `x ↦ B(x, -)`, from `V_λ` to its bar-twisted dual. -/
def formDual (wt : Fin n → Dom R) : TensorSpace wt →ₗ[𝕂] ConjDual (TensorSpace wt) where
  toFun x := ConjDual.of (TensorPairing.orderedForm hR wt x)
  map_add' x y := by rw [map_add, map_add]
  map_smul' c x := by rw [map_smulₛₗ, RingHom.id_apply, ConjDual.smul_of]

theorem formDual_apply (wt : Fin n → Dom R) (x : TensorSpace wt) :
    formDual hR wt x = ConjDual.of (TensorPairing.orderedForm hR wt x) := rfl

/-- `x ↦ B(x, -)` is `U_q`-linear for `dualAction` (Webster, Proposition 4.33). -/
theorem formDual_rho (wt : Fin n → Dom R) (u : 𝕌) (x : TensorSpace wt) :
    formDual hR wt (tensorRepresentation wt u x) = dualAction wt u (formDual hR wt x) :=
  ConjDual.ext fun w => TensorPairing.orderedForm_adjoint hR wt u x w

end Tensor

end Categorification.Stendhal.FirstWeight
