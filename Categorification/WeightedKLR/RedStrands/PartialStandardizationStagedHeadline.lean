/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PartialStandardizationStagedCompare

/-!
# The standardization in stages without spectator

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1,
Definition 5.4. For a right module `M` over the block algebra of blocks `b` with `b_0 = 0`,
identified with a module `Z` over the algebra of the singleton blocks, the standardization in
stages of `Z` is the standardization `M ⊗_B S_α` of Definition 5.4
(`stagedStandardizationEquiv`), and the identification intertwines the action of `flip(a)`
with the right action of `a ∈ T̃^λ` (`stagedStandardizationEquiv_smul`).
-/

noncomputable section

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

namespace Categorification.Stendhal

open CategoryTheory KLR MulOpposite StendhalAlgebra
open scoped TensorProduct

attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower

variable {I : Type} [DecidableEq I] {k : Type} [Field k] (Q : I → I → MvPolynomial (Fin 2) k)
  (hQ : KLRSymm Q)

section Headline

variable (n : ℕ) (Λ : Fin n → I →₀ ℕ) (b : Fin (n + 1) → Multiset I) (θ : Fin n → Multiset I)
  (hθ : b ∘ Fin.succ = θ) (hb0 : leftBlock b = 0)
  (hα : RootNonViolated (ν := blockPrefix b (n + 1)) (blockRoot b)) {M : Type}
  [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  (Z : ModuleCat.{0} (singAlg Q n Λ θ ⊗[k] (AlgCat.of k k : AlgCat.{0} k))) (ψ : Z ≃+ M)
  (hψl : ∀ (s : singAlg Q n Λ θ) (z : Z),
    ψ ((s ⊗ₜ[k] (1 : AlgCat.of k k)) • z) = singBlockHomOf Q n Λ b hθ s • ψ z)
  (hψr : ∀ (c : k) (z : Z),
    ψ (((1 : singAlg Q n Λ θ) ⊗ₜ[k] (c : AlgCat.of k k)) • z) = c • ψ z)

omit [DecidableEq I] in
include hθ hb0 in
/-- The black weight of the standardization in stages is the total weight of the blocks. -/
theorem singWeight_eq_blockPrefix_of : singWeight n θ = blockPrefix b (n + 1) := by
  subst hθ
  exact singWeight_eq_blockPrefix n b hb0

/-- **The standardization in stages without spectator is the standardization of Definition 5.4**
(Webster, arXiv:1309.3796v3, §5.1): `S_staged(Z) ≅ M ⊗_B S_α`. -/
def stagedStandardizationEquiv :
    (singStd Q hQ n Λ θ (AlgCat.of k k)).obj Z ≃ₗ[k] Standardization Q Λ b M :=
  (stagedComparison Q hQ n Λ b θ hθ hb0 rfl (singWeight_eq_blockPrefix_of n b θ hθ hb0) hα
      (AlgCat.of k k) (Algebra.ofId k _) Z ψ hψl
      fun c z => (hψr c z).trans rfl).linearEquiv.trans
    (standardizationReflectEquiv Q Λ b hα M).symm

/-- **The comparison is linear over the Stendhal algebra**: the right action of `a ∈ T̃^λ` on
`M ⊗_B S_α` is the action of `flip(a)` on the standardization in stages. -/
theorem stagedStandardizationEquiv_smul (a : StendhalAlgebra k Q Λ (blockPrefix b (n + 1)))
    (x : (singStd Q hQ n Λ θ (AlgCat.of k k)).obj Z) :
    stagedStandardizationEquiv Q hQ n Λ b θ hθ hb0 hα Z ψ hψl hψr
        ((castTensorProductAlgebra Q Λ (singWeight_eq_blockPrefix_of n b θ hθ hb0).symm
          (tensorFlip (TensorProductAlgebra.mk Q Λ (blockPrefix b (n + 1)) a)) ⊗ₜ[k]
            (1 : AlgCat.of k k)) • x) =
      op a • stagedStandardizationEquiv Q hQ n Λ b θ hθ hb0 hα Z ψ hψl hψr x := by
  apply (standardizationReflectEquiv Q Λ b hα M).injective
  rw [standardizationReflectEquiv_smul]
  change standardizationReflectEquiv Q Λ b hα M ((standardizationReflectEquiv Q Λ b hα M).symm
      ((stagedComparison Q hQ n Λ b θ hθ hb0 rfl (singWeight_eq_blockPrefix_of n b θ hθ hb0) hα
        (AlgCat.of k k) (Algebra.ofId k _) Z ψ hψl
        fun c z => (hψr c z).trans rfl).equiv _)) =
    _ • standardizationReflectEquiv Q Λ b hα M ((standardizationReflectEquiv Q Λ b hα M).symm
      ((stagedComparison Q hQ n Λ b θ hθ hb0 rfl (singWeight_eq_blockPrefix_of n b θ hθ hb0) hα
        (AlgCat.of k k) (Algebra.ofId k _) Z ψ hψl
        fun c z => (hψr c z).trans rfl).equiv x))
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, StagedComparison.smul_left,
    castTensorProductAlgebra_trans]
  rfl

end Headline

end Categorification.Stendhal
