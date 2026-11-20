/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.RedStrands.StandardBlockAction
import Categorification.Algebra.BalancedTensor

/-!
# The standardization functor

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1,
Definition 5.4.

By Proposition 5.3 (`StendhalAlgebra.blockAction`) the standard module `S_α` is a bimodule:
the algebra `R(b_0) ⊗ R^{λ_0}(b_1) ⊗ ⋯ ⊗ R^{λ_{ℓ-1}}(b_ℓ)` acts on it on the left, commuting with
the right action of `T̃^λ`. The standardization functor tensors a right module over that algebra
with this bimodule: `S(M) = M ⊗ S_α`, a right `T̃^λ`-module.

We work with one decomposition `b_0 + ⋯ + b_ℓ` at a time, with black weight
`ν = b_0 + ⋯ + b_ℓ`; Webster's bimodule `S = ⊕_α S_α` is the direct sum over the decompositions.
Right modules are left modules over the opposite algebra, so `M ⊗_B S_α` is the balanced tensor
product `S_α ⊗_{Bᵐᵒᵖ} M` (`BalancedTensor`) of the `(T̃^λ ᵐᵒᵖ, Bᵐᵒᵖ)`-bimodule `S_α` with the
left `Bᵐᵒᵖ`-module `M`. When `b_0 = 0` the factor `R(b_0)` is `k` and this is Webster's functor
`V_{λ_1;…;λ_ℓ} → V_λ`.

## Main definitions

* `Stendhal.StendhalAlgebra.BlockAlgebra`: the algebra of Proposition 5.3.
* `Stendhal.StendhalAlgebra.Standardization`: the standardization `S(M)` of a right
  `BlockAlgebra`-module `M`, a right `T̃^λ`-module.
* `Stendhal.StendhalAlgebra.standardizationMap`: the standardization of a module map, with
  `standardizationMap_id` and `standardizationMap_comp`.
-/

namespace Categorification.Stendhal

open KLR KLRAlgebra MulOpposite
open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {b : Fin (ℓ + 1) → Multiset I}

namespace StendhalAlgebra

variable (k Q Λ b) in
/-- The algebra `R(b_0) ⊗ R^{λ_0}(b_1) ⊗ ⋯ ⊗ R^{λ_{ℓ-1}}(b_ℓ)` of Proposition 5.3. -/
abbrev BlockAlgebra : Type _ :=
  KLRAlgebra k Q (leftBlock b) ⊗[k] (⨂[k] r : Fin ℓ, CycKLR k Q (redCyc Λ r) (rightBlock b r))

local notation "T" => StendhalAlgebra k Q Λ (blockPrefix b (ℓ + 1))
local notation "S" => rootStandard (ν := blockPrefix b (ℓ + 1)) Q Λ (blockRoot b)

/-- The left action of the block algebra on `S_α` (Proposition 5.3), as a right action of the
opposite algebra. -/
noncomputable instance standardBlockModule : Module (BlockAlgebra k Q Λ b)ᵐᵒᵖᵐᵒᵖ S :=
  Module.compHom S ((blockAction Q Λ (b := b) rfl).toRingHom.comp
    (RingEquiv.opOp (BlockAlgebra k Q Λ b)).symm.toRingHom)

theorem op_op_smul_standard (x : BlockAlgebra k Q Λ b) (s : S) :
    (op (op x) : (BlockAlgebra k Q Λ b)ᵐᵒᵖᵐᵒᵖ) • s = blockAction Q Λ (b := b) rfl x s :=
  rfl

/-- The block action commutes with the right action of `T̃^λ`. -/
instance : SMulCommClass Tᵐᵒᵖ (BlockAlgebra k Q Λ b)ᵐᵒᵖᵐᵒᵖ S where
  smul_comm t x s := by
    induction x using MulOpposite.rec' with | _ x =>
    induction x using MulOpposite.rec' with | _ x =>
    rw [op_op_smul_standard, op_op_smul_standard, map_smul]

variable (Q Λ b) in
/-- **Definition 5.4** of arXiv:1309.3796v3: the standardization `S(M) = M ⊗_B S_α` of a right
module `M` over the block algebra `B`, a right `T̃^λ`-module. -/
abbrev Standardization (M : Type*) [AddCommGroup M] [Module k M]
    [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M] : Type _ :=
  BalancedTensor k Tᵐᵒᵖ (BlockAlgebra k Q Λ b)ᵐᵒᵖ S M

variable {M M' M'' : Type*} [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M] [AddCommGroup M'] [Module k M']
  [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M'] [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M']
  [AddCommGroup M''] [Module k M''] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M'']
  [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M'']

/-- The standardization of a map of right modules over the block algebra. -/
noncomputable def standardizationMap (g : M →ₗ[(BlockAlgebra k Q Λ b)ᵐᵒᵖ] M') :
    Standardization Q Λ b M →ₗ[Tᵐᵒᵖ] Standardization Q Λ b M' :=
  BalancedTensor.mapRight g

theorem standardizationMap_tmul (g : M →ₗ[(BlockAlgebra k Q Λ b)ᵐᵒᵖ] M') (s : S) (m : M) :
    standardizationMap g (BalancedTensor.tmul s m) = BalancedTensor.tmul s (g m) :=
  rfl

theorem standardizationMap_id :
    standardizationMap (LinearMap.id : M →ₗ[(BlockAlgebra k Q Λ b)ᵐᵒᵖ] M) = LinearMap.id :=
  BalancedTensor.mapRight_id

theorem standardizationMap_comp (g : M →ₗ[(BlockAlgebra k Q Λ b)ᵐᵒᵖ] M')
    (g' : M' →ₗ[(BlockAlgebra k Q Λ b)ᵐᵒᵖ] M'') :
    standardizationMap (g' ∘ₗ g) = standardizationMap g' ∘ₗ standardizationMap g :=
  BalancedTensor.mapRight_comp g g'

end StendhalAlgebra

end Categorification.Stendhal
