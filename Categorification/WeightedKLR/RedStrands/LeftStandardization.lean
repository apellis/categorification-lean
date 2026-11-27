/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LeftRootStandard
import Categorification.Algebra.BalancedTensorTransport

/-!
# The standardization functor in left-module form

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1,
Definition 5.4. When no sequence of root function `α` is violated (for instance when
`b_0 = 0`), the standard bimodule `S_α` is the reflection of the left root standard module
`S^L_α` (`rootReflectEquiv`), compatibly with the block action of Proposition 5.3
(`leftBlockAction`). Hence the standardization `S(M) = M ⊗_B S_α` of a right module `M` over the
block algebra `B` is the reflection of `M ⊗_B S^L_α`, a left `T^λ`-module
(`standardizationReflectEquiv`): the right action of `a ∈ T̃^λ` becomes the left action of
`flip(a)` (`standardizationReflectEquiv_smul`).

## Main definitions

* `StendhalAlgebra.BlockLeftStandard`: `S^L_α` as a `(T^λ, B)`-bimodule.
* `StendhalAlgebra.LeftStandardization`: `M ⊗_B S^L_α`, a left `T^λ`-module.
* `StendhalAlgebra.standardizationReflectEquiv`: `S(M) ≅ M ⊗_B S^L_α`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

namespace Categorification.Stendhal

open KLR MulOpposite

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {b : Fin (ℓ + 1) → Multiset I}
  {ν : Multiset I}

namespace StendhalAlgebra

local notation "T" => TensorProductAlgebra k Q Λ ν
local notation "L" => LeftRootStandard (ν := ν) Q Λ (blockRoot b)
local notation "B" => BlockAlgebra k Q Λ b
local notation "Sα" => rootStandard (ν := ν) Q Λ (blockRoot b)

section General

variable (hb : blockPrefix b (ℓ + 1) = ν)

variable (Q Λ b) in
/-- The block action of Proposition 5.3 on `S^L_α`, through the reflection, for a root function
none of whose sequences is violated. The black weight `ν` is any weight equal to
`b_0 + ⋯ + b_ℓ`. -/
def leftBlockActionOf (hα : RootNonViolated (ν := ν) (blockRoot b)) :
    B →ₐ[k] Module.End T L :=
  (rootReflectConj Q Λ hα).comp (blockAction Q Λ (b := b) hb)

theorem leftBlockActionOf_rootReflect
    (hα : RootNonViolated (ν := ν) (blockRoot b)) (x : B) (v : Sα) :
    leftBlockActionOf Q Λ b hb hα x (rootReflect Q Λ v) =
      rootReflect Q Λ (blockAction Q Λ (b := b) hb x v) :=
  rootReflectConj_apply _ _ v

variable (Q Λ b) in
/-- **The left root standard module as a bimodule**: `S^L_α` with its left `T^λ`-module
structure and the reflected block action of `B`, written as a module over `Bᵐᵒᵖᵐᵒᵖ`. -/
def BlockLeftStandard (_hb : blockPrefix b (ℓ + 1) = ν)
    (_hα : RootNonViolated (ν := ν) (blockRoot b)) : Type := L

variable (hα : RootNonViolated (ν := ν) (blockRoot b))

instance : AddCommGroup (BlockLeftStandard Q Λ b hb hα) := inferInstanceAs (AddCommGroup L)
instance : Module k (BlockLeftStandard Q Λ b hb hα) := inferInstanceAs (Module k L)
instance : Module T (BlockLeftStandard Q Λ b hb hα) := inferInstanceAs (Module T L)
instance : IsScalarTower k T (BlockLeftStandard Q Λ b hb hα) := inferInstanceAs (IsScalarTower k T L)

instance : Module Bᵐᵒᵖᵐᵒᵖ (BlockLeftStandard Q Λ b hb hα) :=
  Module.compHom L ((leftBlockActionOf Q Λ b hb hα).toRingHom.comp
    (RingEquiv.opOp B).symm.toRingHom)

theorem op_op_smul_blockLeftStandard (x : B) (v : BlockLeftStandard Q Λ b hb hα) :
    (op (op x) : Bᵐᵒᵖᵐᵒᵖ) • v =
      (show BlockLeftStandard Q Λ b hb hα from leftBlockActionOf Q Λ b hb hα x (show L from v)) :=
  rfl

instance : SMulCommClass T Bᵐᵒᵖᵐᵒᵖ (BlockLeftStandard Q Λ b hb hα) where
  smul_comm t x v := by
    induction x using MulOpposite.rec' with | _ x =>
    induction x using MulOpposite.rec' with | _ x =>
    rw [op_op_smul_blockLeftStandard, op_op_smul_blockLeftStandard]
    exact (map_smul (leftBlockActionOf Q Λ b hb hα x) t (show L from v)).symm

variable (Q Λ b) in
/-- **The standardization in left-module form**: `M ⊗_B S^L_α`, a left `T^λ`-module, for a right
module `M` over the block algebra. -/
abbrev LeftStandardization (M : Type*) [AddCommGroup M] [Module k M]
    [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M] : Type _ :=
  BalancedTensor k T Bᵐᵒᵖ (BlockLeftStandard Q Λ b hb hα) M

end General

variable (hα : RootNonViolated (ν := blockPrefix b (ℓ + 1)) (blockRoot b))

variable {M : Type*} [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]

theorem rootReflectEquiv_op_smul (a : Bᵐᵒᵖ) (v : rootStandard (ν := blockPrefix b (ℓ + 1)) Q Λ (blockRoot b)) :
    rootReflectEquiv Q Λ hα (op a • v) =
      (op a • (show BlockLeftStandard Q Λ b rfl hα from rootReflectEquiv Q Λ hα v) :
        BlockLeftStandard Q Λ b rfl hα) := by
  induction a using MulOpposite.rec' with | _ x =>
  rw [op_op_smul_standard, op_op_smul_blockLeftStandard, rootReflectEquiv_apply,
    rootReflectEquiv_apply, leftBlockActionOf_rootReflect]

variable (Q Λ b M) in
/-- **The standardization of Definition 5.4 is the reflection of its left-module form**:
`M ⊗_B S_α ≅ M ⊗_B S^L_α`. -/
def standardizationReflectEquiv :
    Standardization Q Λ b M ≃ₗ[k] LeftStandardization Q Λ b rfl hα M :=
  BalancedTensor.changeRingEquiv (RingEquiv.refl (BlockAlgebra k Q Λ b)ᵐᵒᵖ)
    (show rootStandard (ν := blockPrefix b (ℓ + 1)) Q Λ (blockRoot b) ≃ₗ[k] BlockLeftStandard Q Λ b rfl hα from rootReflectEquiv Q Λ hα)
    (LinearEquiv.refl k M) (fun a v => rootReflectEquiv_op_smul hα a v) (fun _ _ => rfl)

theorem standardizationReflectEquiv_tmul (v : rootStandard (ν := blockPrefix b (ℓ + 1)) Q Λ (blockRoot b)) (m : M) :
    standardizationReflectEquiv Q Λ b hα M (BalancedTensor.tmul v m) =
      BalancedTensor.tmul (show BlockLeftStandard Q Λ b rfl hα from rootReflect Q Λ v) m :=
  rfl

/-- The right action of `a ∈ T̃^λ` on `S(M)` is the left action of `flip(a)` on `M ⊗_B S^L_α`. -/
theorem standardizationReflectEquiv_smul (a : StendhalAlgebra k Q Λ (blockPrefix b (ℓ + 1)))
    (z : Standardization Q Λ b M) :
    standardizationReflectEquiv Q Λ b hα M (op a • z) =
      tensorFlip (TensorProductAlgebra.mk Q Λ (blockPrefix b (ℓ + 1)) a) •
        standardizationReflectEquiv Q Λ b hα M z := by
  induction z using BalancedTensor.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]
  | tmul v m =>
    rw [BalancedTensor.smul_tmul', standardizationReflectEquiv_tmul,
      standardizationReflectEquiv_tmul, BalancedTensor.smul_tmul']
    congr 1
    exact rootReflect_op_smul a v

end StendhalAlgebra

end Categorification.Stendhal
