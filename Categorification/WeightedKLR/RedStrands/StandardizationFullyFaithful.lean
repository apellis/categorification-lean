/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.StandardizationHomFullyFaithful

/-!
# The standardization of Definition 5.4 on endomorphisms

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
Proposition 5.26. For blocks `b` with `b_0 = 0` and a right module `M` over the block algebra
`B = R^{λ_1}(b_1) ⊗ ⋯ ⊗ R^{λ_ℓ}(b_ℓ)` of Proposition 5.3, the standardization
`S(M) = M ⊗_B S^L_α` of Definition 5.4 satisfies `End_B(M) ≅ End_{T^λ}(S(M))` as algebras,
through `g ↦ g ⊗ 1` (`standardizationEndEquiv`): the case `M' = M` of full faithfulness
(`standardizationHomBijective`). For `M = B` this identifies the block algebra with the
endomorphisms of the root standard module `S^L_α` (`bijective_leftBlockActionOf`), i.e.
`End(S_α) ≅ T^{μ_1} ⊗ ⋯ ⊗ T^{μ_ℓ}`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra MulOpposite
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

namespace StendhalAlgebra

variable {I : Type} [DecidableEq I] {k : Type} [Field k] (Q : I → I → MvPolynomial (Fin 2) k)

/-- Standardization on endomorphisms, `g ↦ g ⊗ 1`, as a map of algebras. -/
abbrev standardizationEndAlg {n : ℕ} (Λ : Fin n → I →₀ ℕ) {b : Fin (n + 1) → Multiset I}
    {ν : Multiset I} (hb : blockPrefix b (n + 1) = ν) (hα : RootNonViolated (ν := ν) (blockRoot b))
    (M : Type) [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
    [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M] :
    Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M →ₐ[k]
      Module.End (TensorProductAlgebra k Q Λ ν) (LeftStandardization Q Λ b hb hα M) :=
  BalancedTensor.endMapRight k (TensorProductAlgebra k Q Λ ν) (BlockLeftStandard Q Λ b hb hα)
    (N := M)

/-- The statement that standardization with `n` red strands is bijective on endomorphisms. -/
def StandardizationEndBijective (n : ℕ) : Prop :=
  ∀ (Λ : Fin n → I →₀ ℕ) (b : Fin (n + 1) → Multiset I) (ν : Multiset I)
    (hb : blockPrefix b (n + 1) = ν) (hα : RootNonViolated (ν := ν) (blockRoot b)), b 0 = 0 →
    ∀ (M : Type) [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
      [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M],
      Function.Bijective (standardizationEndAlg Q Λ hb hα M)

/-- **Standardization is bijective on endomorphisms** for every number of red strands: the
case `M' = M` of `standardizationHomBijective`. -/
theorem standardizationEndBijective (hQ : KLRSymm Q) (n : ℕ) : StandardizationEndBijective Q n :=
  fun Λ b ν hb hα hb0 M _ _ _ _ => standardizationHomBijective Q hQ n Λ b ν hb hα hb0 M M

/-- **Endomorphisms of a standardization** (Webster, arXiv:1309.3796v3, Proposition 5.26, full
faithfulness of the standardization of Definition 5.4 on endomorphisms): for blocks `b` with
`b_0 = 0` and every right module `M` over the block algebra `B`,
`End_B(M) ≅ End_{T^λ}(M ⊗_B S^L_α)` through `g ↦ g ⊗ 1`. -/
def standardizationEndEquiv (hQ : KLRSymm Q) {n : ℕ} (Λ : Fin n → I →₀ ℕ)
    (b : Fin (n + 1) → Multiset I) (hb0 : b 0 = 0)
    (hα : RootNonViolated (ν := blockPrefix b (n + 1)) (blockRoot b))
    (M : Type) [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
    [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M] :
    Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M ≃ₐ[k]
      Module.End (TensorProductAlgebra k Q Λ (blockPrefix b (n + 1)))
        (LeftStandardization Q Λ b rfl hα M) :=
  AlgEquiv.ofBijective (standardizationEndAlg Q Λ rfl hα M)
    (standardizationEndBijective Q hQ n Λ b _ rfl hα hb0 M)

theorem standardizationEndEquiv_apply (hQ : KLRSymm Q) {n : ℕ} (Λ : Fin n → I →₀ ℕ)
    (b : Fin (n + 1) → Multiset I) (hb0 : b 0 = 0)
    (hα : RootNonViolated (ν := blockPrefix b (n + 1)) (blockRoot b))
    (M : Type) [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
    [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M] (g : Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M) :
    standardizationEndEquiv Q hQ Λ b hb0 hα M g =
      BalancedTensor.mapRight (k := k) (B := TensorProductAlgebra k Q Λ (blockPrefix b (n + 1)))
        (M := BlockLeftStandard Q Λ b rfl hα) g :=
  rfl

section RootStandardEnd

variable {n : ℕ} (Λ : Fin n → I →₀ ℕ) (b : Fin (n + 1) → Multiset I)
  (hα : RootNonViolated (ν := blockPrefix b (n + 1)) (blockRoot b))

instance blockLeftStandard_isScalarTower_opOp :
    IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖᵐᵒᵖ (BlockLeftStandard Q Λ b rfl hα) where
  smul_assoc c a l := by
    induction a using MulOpposite.rec' with | _ a =>
    induction a using MulOpposite.rec' with | _ x =>
    have h1 := LinearMap.congr_fun (show leftBlockActionOf Q Λ b rfl hα (c • x) =
        leftBlockActionOf Q Λ b rfl hα (algebraMap k _ c) * leftBlockActionOf Q Λ b rfl hα x from
      (congrArg (leftBlockActionOf Q Λ b rfl hα) (Algebra.smul_def c x)).trans (map_mul _ _ _)) l
    rw [AlgHom.commutes] at h1
    exact h1

/-- **Endomorphisms of the root standard module** (Webster, arXiv:1309.3796v3,
Proposition 5.26, `End(S_α) ≅ T^{μ_1} ⊗ ⋯ ⊗ T^{μ_ℓ}`, in left-module form): for blocks with
`b_0 = 0`, the block action of Proposition 5.3 identifies the block algebra with the
endomorphism algebra of the left root standard module `S^L_α`. -/
theorem bijective_leftBlockActionOf (hQ : KLRSymm Q) (hb0 : b 0 = 0) :
    Function.Bijective (leftBlockActionOf Q Λ b rfl hα) := by
  let A := (BlockAlgebra k Q Λ b)ᵐᵒᵖ
  let r := BalancedTensor.rid k (TensorProductAlgebra k Q Λ (blockPrefix b (n + 1))) A
    (BlockLeftStandard Q Λ b rfl hα)
  let h : BlockAlgebra k Q Λ b → Module.End A A :=
    fun x => AlgEquiv.moduleEndSelf (A := A) k (op (op x))
  have hh : Function.Bijective h :=
    (AlgEquiv.moduleEndSelf (A := A) k).bijective.comp
      ((MulOpposite.opEquiv.trans MulOpposite.opEquiv).bijective)
  have hS := standardizationEndBijective Q hQ n Λ b _ rfl hα hb0 A
  let C : Module.End (TensorProductAlgebra k Q Λ (blockPrefix b (n + 1)))
      (LeftStandardization Q Λ b rfl hα A) ≃
      Module.End (TensorProductAlgebra k Q Λ (blockPrefix b (n + 1)))
        (BlockLeftStandard Q Λ b rfl hα) :=
    { toFun := fun φ => r.toLinearMap ∘ₗ φ ∘ₗ r.symm.toLinearMap
      invFun := fun ψ => r.symm.toLinearMap ∘ₗ ψ ∘ₗ r.toLinearMap
      left_inv := fun φ => LinearMap.ext fun y => by
        change r.symm (r (φ (r.symm (r y)))) = φ y
        rw [r.symm_apply_apply, r.symm_apply_apply]
      right_inv := fun ψ => LinearMap.ext fun y => by
        change r (r.symm (ψ (r (r.symm y)))) = ψ y
        rw [r.apply_symm_apply, r.apply_symm_apply] }
  have heq : (leftBlockActionOf Q Λ b rfl hα : BlockAlgebra k Q Λ b → _) =
      C ∘ (standardizationEndAlg Q Λ rfl hα A) ∘ h := by
    funext x
    refine LinearMap.ext fun l => ?_
    change _ = r (BalancedTensor.mapRight (h x) (r.symm l))
    rw [BalancedTensor.rid_symm_apply, BalancedTensor.mapRight_tmul]
    change _ = r (BalancedTensor.tmul l ((op (op x) : Aᵐᵒᵖ) • (1 : A)))
    rw [BalancedTensor.rid_tmul]
    change _ = (op ((1 : A) * op x) : Aᵐᵒᵖ) • (show BlockLeftStandard Q Λ b rfl hα from l)
    rw [one_mul, op_op_smul_blockLeftStandard]
  rw [heq]
  exact C.bijective.comp (hS.comp hh)

end RootStandardEnd

end StendhalAlgebra

end Categorification.Stendhal
