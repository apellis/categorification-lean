/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LeftStandardization

/-!
# Transport of block algebras and standardizations along equal block families

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1. Two
equal families of blocks `c = c'` give isomorphic block algebras (`blockAlgebraCast`), and the
standardization `M ⊗_B S^L_α` of a right `B(c)`-module is that of `M` regarded as a
`B(c')`-module (`leftStandardizationCast`). These transports are used in the proof of
Proposition 5.5, where the blocks of the first `ℓ` red strands of two families agree only up to
equality.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

namespace Categorification.Stendhal

open KLR MulOpposite

namespace StendhalAlgebra

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) {c c' : Fin (ℓ + 1) → Multiset I}
  {ν : Multiset I}

/-- The block algebras of equal families of blocks. -/
def blockAlgebraCast (h : c = c') : BlockAlgebra k Q Λ c ≃ₐ[k] BlockAlgebra k Q Λ c' := by
  subst h
  exact AlgEquiv.refl

@[simp] theorem blockAlgebraCast_rfl (x : BlockAlgebra k Q Λ c) :
    blockAlgebraCast Q Λ (rfl : c = c) x = x := rfl

/-- A right `B(c)`-module regarded as a right `B(c')`-module, for `c = c'`. -/
@[nolint unusedArguments]
def CastBlockModule (_Q : I → I → MvPolynomial (Fin 2) k) (_Λ : Fin ℓ → I →₀ ℕ) (_h : c = c')
    (N : Type*) : Type _ := N

variable (N : Type*) [AddCommGroup N] [Module k N] [Module (BlockAlgebra k Q Λ c)ᵐᵒᵖ N]
  [IsScalarTower k (BlockAlgebra k Q Λ c)ᵐᵒᵖ N] (h : c = c')

instance : AddCommGroup (CastBlockModule Q Λ h N) := inferInstanceAs (AddCommGroup N)
instance : Module k (CastBlockModule Q Λ h N) := inferInstanceAs (Module k N)
instance : Module (BlockAlgebra k Q Λ c')ᵐᵒᵖ (CastBlockModule Q Λ h N) :=
  Module.compHom N (RingHom.op (blockAlgebraCast Q Λ h).symm.toRingEquiv.toRingHom)
instance : IsScalarTower k (BlockAlgebra k Q Λ c')ᵐᵒᵖ (CastBlockModule Q Λ h N) where
  smul_assoc a x n := by
    subst h
    exact smul_assoc a x (show N from n)

omit [IsScalarTower k (BlockAlgebra k Q Λ c)ᵐᵒᵖ N] in
variable {N} in
/-- The identity `N → CastBlockModule Q Λ h N`. -/
def castBlockModuleOf : N ≃ₗ[k] CastBlockModule Q Λ h N := LinearEquiv.refl k N

omit [IsScalarTower k (BlockAlgebra k Q Λ c)ᵐᵒᵖ N] in
theorem op_smul_castBlockModuleOf (x : BlockAlgebra k Q Λ c') (n : N) :
    (op x : (BlockAlgebra k Q Λ c')ᵐᵒᵖ) • castBlockModuleOf Q Λ h n =
      castBlockModuleOf Q Λ h
        ((op ((blockAlgebraCast Q Λ h).symm x) : (BlockAlgebra k Q Λ c)ᵐᵒᵖ) • n) :=
  rfl

/-- **Standardization along equal families of blocks.** -/
def leftStandardizationCast (hb : blockPrefix c (ℓ + 1) = ν) (hb' : blockPrefix c' (ℓ + 1) = ν)
    (hα : RootNonViolated (ν := ν) (blockRoot c)) (hα' : RootNonViolated (ν := ν) (blockRoot c')) :
    LeftStandardization Q Λ c hb hα N ≃ₗ[TensorProductAlgebra k Q Λ ν]
      LeftStandardization Q Λ c' hb' hα' (CastBlockModule Q Λ h N) := by
  subst h
  exact LinearEquiv.refl _ _

omit [IsScalarTower k (BlockAlgebra k Q Λ c)ᵐᵒᵖ N] in
theorem leftStandardizationCast_tmul (hb : blockPrefix c (ℓ + 1) = ν)
    (hb' : blockPrefix c' (ℓ + 1) = ν) (hα : RootNonViolated (ν := ν) (blockRoot c))
    (hα' : RootNonViolated (ν := ν) (blockRoot c')) (v : BlockLeftStandard Q Λ c hb hα) (n : N) :
    ∃ v' : BlockLeftStandard Q Λ c' hb' hα',
      leftStandardizationCast Q Λ N h hb hb' hα hα' (BalancedTensor.tmul v n) =
        BalancedTensor.tmul v' (castBlockModuleOf Q Λ h n) := by
  subst h
  exact ⟨v, rfl⟩

end StendhalAlgebra

end Categorification.Stendhal
