/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LeftStandardModule
import Categorification.Algebra.BalancedTensor
import Categorification.Algebra.IdempotentEquiv

/-!
# Tensoring a left standard with a right coefficient

When the right coefficient is annihilated by idempotents strictly above the
standard's loading, its tensor with the standard is its fixed subspace at
that loading.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR MulOpposite

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} {ν : Multiset I}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
  (s : Seq (stendhalWeight ℓ ν)) (hs : IsRedOrdered s)

local notation "A" => TensorProductAlgebra k Q Λ ν
local notation "E" => seqIdem Q Λ s hs
local notation "S" => leftStandard Q Λ s hs
local notation "g" => leftStandardUnit Q Λ s hs
local notation "P" => lIdeal E
set_option quotPrecheck false in
local notation "U" => (leftUpper Q Λ s hs).comap (lIdeal E).subtype

variable (N : Type) [AddCommGroup N] [Module k N] [Module (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ N]
  [IsScalarTower k (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ N]
  [SMulCommClass k (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ N]

local notation "W" => fixSub k N (op E)
local notation "Tens" => BalancedTensor k k A N S

private def evalProjective (m : N) : P →ₗ[k] W where
  toFun y := ⟨op y.val • m, by
    change op E • (op y.val • m) = _
    rw [← mul_smul, ← op_mul, y.property]⟩
  map_add' y z := Subtype.ext (add_smul (op y.val) (op z.val) m)
  map_smul' c y := Subtype.ext (by
    change op (c • y.val) • m = c • (op y.val • m)
    rw [op_smul, smul_assoc])

variable (h : ∀ (t : Seq (stendhalWeight ℓ ν)) (ht : IsRedOrdered t),
  StendhalLT s t → ∀ m : N, op (seqIdem Q Λ t ht) • m = 0)

include h in
omit [SMulCommClass k (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ N] in
private theorem evalUpper_eq_zero (m : N) (y : P) (hy : y ∈ U) :
    evalProjective Q Λ s hs N m y = 0 := by
  apply Subtype.ext
  change op y.val • m = 0
  change y.val ∈ leftUpper Q Λ s hs at hy
  generalize hz : y.val = z at hy ⊢
  clear hz y
  induction hy using Submodule.span_induction generalizing m with
  | mem z hz =>
      obtain ⟨t, ht, a, hst, rfl⟩ := hz
      rw [op_mul, op_mul, mul_smul, mul_smul, h t ht hst, smul_zero, smul_zero]
  | zero => rw [op_zero, zero_smul]
  | add a b _ _ ha hb => rw [op_add, add_smul, ha, hb, add_zero]
  | smul a b _ hb =>
      rw [smul_eq_mul, op_mul, mul_smul]
      exact hb _

private def evalStandard (m : N) : S →ₗ[k] W :=
  ((U).restrictScalars k).liftQ (evalProjective Q Λ s hs N m)
    (fun y hy => LinearMap.mem_ker.mpr (evalUpper_eq_zero Q Λ s hs N h m y hy))

private def evalBil : N →ₗ[k] S →ₗ[k] W where
  toFun := evalStandard Q Λ s hs N h
  map_add' m n := by
    apply LinearMap.ext
    intro z
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective U z
    apply Subtype.ext
    exact smul_add (op y.val) m n
  map_smul' c m := by
    apply LinearMap.ext
    intro z
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective U z
    apply Subtype.ext
    exact smul_comm (op y.val) c m

private def evalTensor : Tens →ₗ[k] W :=
  BalancedTensor.lift (evalBil Q Λ s hs N h) (fun m a z => by
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective U z
    apply Subtype.ext
    change op y.val • (op a • m) = op (a * y.val) • m
    rw [op_mul, mul_smul])

/-- A right coefficient killed by all strictly higher loading idempotents sees
only its fixed subspace at the standard's loading when tensoring with the standard. -/
def leftStandardTensorEquivFixed : Tens ≃ₗ[k] W := by
  let inv : W →ₗ[k] Tens := ((BalancedTensor.mkBil k k A N S).flip g).comp (W).subtype
  have hl : inv.comp (evalTensor Q Λ s hs N h) = LinearMap.id := by
    apply BalancedTensor.ext
    intro m z
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective U z
    change BalancedTensor.tmul (op y.val • m) g = BalancedTensor.tmul m ((U).mkQ y)
    rw [BalancedTensor.op_smul_tmul, ← leftStandard_mk_eq_smul_unit s hs y]
    rfl
  refine { evalTensor Q Λ s hs N h with
    invFun := inv, left_inv := DFunLike.congr_fun hl, right_inv := ?_ }
  intro w
  apply Subtype.ext
  exact w.property

/-- On the generator, the tensor equivalence is the loading-idempotent projection. -/
theorem leftStandardTensorEquivFixed_tmul_generator (m : N) :
    (leftStandardTensorEquivFixed Q Λ s hs N h (BalancedTensor.tmul m g)).val =
      op E • m := rfl

/-- The inverse represents a fixed vector by tensoring it with the standard generator. -/
theorem leftStandardTensorEquivFixed_symm_apply (w : W) :
    (leftStandardTensorEquivFixed Q Λ s hs N h).symm w = BalancedTensor.tmul w.val g := rfl

/-- An endomorphism given by a diagram on the standard generator acts after tensoring
by the corresponding right diagram action, projected to the fixed cut. -/
theorem leftStandardTensorEquivFixed_mapRight (f : Module.End A S) (a : A)
    (hf : f g = a • g) (w : W) :
    (leftStandardTensorEquivFixed Q Λ s hs N h
      (BalancedTensor.mapRight f ((leftStandardTensorEquivFixed Q Λ s hs N h).symm w))).val =
      op E • (op a • w.val) := by
  rw [leftStandardTensorEquivFixed_symm_apply, BalancedTensor.mapRight_tmul, hf,
    ← BalancedTensor.op_smul_tmul, leftStandardTensorEquivFixed_tmul_generator]

end Categorification.Stendhal
