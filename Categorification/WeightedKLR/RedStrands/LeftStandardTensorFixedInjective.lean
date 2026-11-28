/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LeftStandardTensorFixed
import Categorification.Algebra.DerivedTensorHomology

/-!
# Tensoring with a left standard is exact on coefficients killed above the loading

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.22, gap (c), injectivity of `Tor₀` against the standard `S_s` of the diagonal
pair. For a right coefficient `N` killed by the loading idempotents strictly above `s`,
`N ⊗_T S_s ≅ e(s) N` (`leftStandardTensorEquivFixed`). Composing with the comparison
`ordinaryBalancedTensorAddEquiv` gives an additive injection `N ⊗_T S_s → N`,
`m ⊗ a [e(s)] ↦ m · a e(s)` (`leftStandardTensorOverEval`). It is natural in `N`, so for
coefficients killed above `s` the map `f ⊗_T id` is injective whenever `f` is
(`injective_tensorProductOver_map_leftStandard`). No route hypotheses.

## Main definitions

* `Stendhal.leftStandardTensorOverEval`: `N ⊗_T S_s → N`, `m ⊗ [y] ↦ m · y`.

## Main results

* `Stendhal.leftStandardTensorOverEval_injective`.
* `Stendhal.leftStandardTensorOverEval_tmul_mk`.
* `Stendhal.injective_tensorProductOver_map_leftStandard`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR MulOpposite DG

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} {ν : Multiset I}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
  (s : Seq (stendhalWeight ℓ ν)) (hs : IsRedOrdered s)

local notation "TA" => TensorProductAlgebra k Q Λ ν
local notation "S" => leftStandard Q Λ s hs

section Eval

variable (N : Type) [AddCommGroup N] [Module k N] [Module (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ N]
  [IsScalarTower k (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ N]
  [SMulCommClass k (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ N]
  (h : ∀ (t : Seq (stendhalWeight ℓ ν)) (ht : IsRedOrdered t),
    StendhalLT s t → ∀ m : N, op (seqIdem Q Λ t ht) • m = 0)

omit [SMulCommClass k (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ N] in
theorem op_algebraMap_smul_eq (c : k) (m : N) : op (algebraMap k TA c) • m = c • m := by
  rw [← algebraMap_smul (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ c m]
  rfl

/-- **Evaluation of a tensor with the standard** (Webster, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.22): for `N` killed by the loading idempotents strictly above `s`, the additive
map `N ⊗_T S_s → N`, `m ⊗ [y] ↦ m · y`, through `N ⊗_T S_s ≅ e(s) N`. -/
def leftStandardTensorOverEval : TensorProductOver TA N S →+ N :=
  (fixSub k N (op (seqIdem Q Λ s hs))).subtype.toAddMonoidHom.comp
    ((leftStandardTensorEquivFixed Q Λ s hs N h).toAddEquiv.toAddMonoidHom.comp
      (ordinaryBalancedTensorAddEquiv (A := k) (k := k)
        (op_algebraMap_smul_eq Q Λ N)).toAddMonoidHom)

theorem leftStandardTensorOverEval_injective :
    Function.Injective (leftStandardTensorOverEval Q Λ s hs N h) :=
  Subtype.val_injective.comp ((leftStandardTensorEquivFixed Q Λ s hs N h).injective.comp
    (ordinaryBalancedTensorAddEquiv (A := k) (k := k) (op_algebraMap_smul_eq Q Λ N)).injective)

theorem leftStandardTensorOverEval_tmul_unit (m : N) :
    leftStandardTensorOverEval Q Λ s hs N h
      (TensorProductOver.tmul TA m (leftStandardUnit Q Λ s hs)) =
        op (seqIdem Q Λ s hs) • m := rfl

/-- On a generator `m ⊗ a [e(s)]`, the evaluation is `m · a e(s)`. -/
theorem leftStandardTensorOverEval_tmul_smul_unit (m : N) (a : TA) :
    leftStandardTensorOverEval Q Λ s hs N h
      (TensorProductOver.tmul TA m (a • leftStandardUnit Q Λ s hs)) =
        op (seqIdem Q Λ s hs) • (op a • m) := by
  rw [← TensorProductOver.op_smul_tmul, leftStandardTensorOverEval_tmul_unit]

end Eval

section Map

variable (N N' : Type) [AddCommGroup N] [Module k N] [Module (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ N]
  [IsScalarTower k (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ N]
  [SMulCommClass k (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ N]
  [AddCommGroup N'] [Module k N'] [Module (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ N']
  [IsScalarTower k (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ N']
  [SMulCommClass k (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ N']
  (h : ∀ (t : Seq (stendhalWeight ℓ ν)) (ht : IsRedOrdered t),
    StendhalLT s t → ∀ m : N, op (seqIdem Q Λ t ht) • m = 0)
  (h' : ∀ (t : Seq (stendhalWeight ℓ ν)) (ht : IsRedOrdered t),
    StendhalLT s t → ∀ m : N', op (seqIdem Q Λ t ht) • m = 0)

/-- The evaluation is natural in the coefficient. -/
theorem leftStandardTensorOverEval_map (f : N →ₗ[TAᵐᵒᵖ] N') (x : TensorProductOver TA N S) :
    leftStandardTensorOverEval Q Λ s hs N' h'
        (TensorProductOver.map f (LinearMap.id : S →ₗ[TA] S) x) =
      f (leftStandardTensorOverEval Q Λ s hs N h x) := by
  induction x using TensorProductOver.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul m z =>
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ z
    rw [TensorProductOver.map_tmul, LinearMap.id_apply]
    change leftStandardTensorOverEval Q Λ s hs N' h'
        (TensorProductOver.tmul TA (f m) (Submodule.Quotient.mk y : S)) =
      f (leftStandardTensorOverEval Q Λ s hs N h
        (TensorProductOver.tmul TA m (Submodule.Quotient.mk y : S)))
    rw [leftStandard_mk_eq_smul_unit, leftStandardTensorOverEval_tmul_smul_unit,
      leftStandardTensorOverEval_tmul_smul_unit, map_smul, map_smul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

include h h' in
/-- **`f ⊗_T S_s` is injective for injective `f`** (Webster, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.22, gap (c)): on right coefficients killed by the loading idempotents strictly
above `s`, tensoring with the left standard `S_s` preserves injectivity. -/
theorem injective_tensorProductOver_map_leftStandard (f : N →ₗ[TAᵐᵒᵖ] N')
    (hf : Function.Injective f) :
    Function.Injective (TensorProductOver.map f (LinearMap.id : S →ₗ[TA] S)) := by
  intro x x' hx
  apply leftStandardTensorOverEval_injective Q Λ s hs N h
  apply hf
  rw [← leftStandardTensorOverEval_map Q Λ s hs N N' h h', hx,
    leftStandardTensorOverEval_map Q Λ s hs N N' h h']

end Map

end Categorification.Stendhal
