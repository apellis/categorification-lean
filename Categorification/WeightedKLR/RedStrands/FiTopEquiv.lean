/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FiFiltrationStatement

/-!
# `Fᵢ` of the standardization as `Fᵢ` of a two-piece standardization

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5, `F`-part. For blocks `b` of `ℓ + 1` red strands with first weight `θ` and last
block `β`, the isomorphism `M ⊗_B S^L_α ≅ S(X_M)` induces `Fᵢ(M ⊗_B S^L_α) ≅ Fᵢ S(X_M)`, as
modules over `T(i + (θ + β)) ⊗ C` (`fiTopEquiv`). This is the middle term of the sequence of the
induction step.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra MulOpposite InductionAlong
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

namespace StendhalAlgebra

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (hQ : KLRSymm Q)
  (i : I) (b : Fin (ℓ + 2) → Multiset I)
  (M : Type) [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  (hα₁ : RootNonViolated (ν := initWeight b) (blockRoot (initBlocks b)))
  (hb : blockPrefix b (ℓ + 2) = initWeight b + lastBlock b)
  (hα : RootNonViolated (ν := initWeight b + lastBlock b) (blockRoot b))
  (C : Type) [Ring C] [Algebra k C] (ρ : C →ₐ[k] Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M)

/-- Naturality of `Fᵢ` of `M ⊗_B S^L_α ≅ S(X_M)` in endomorphisms of `M`. -/
theorem fiTopEquiv_natural (g : Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M)
    (x : IndK k (LeftStandardization Q Λ b (blockPrefix_last b) hα M)
      (appendBlackNU (Q := Q) (Λ := Λ) i (initWeight b + lastBlock b))) :
    IndK.map (k := k) (splitStandardEquiv Q Λ hQ b hα₁ hα M).toLinearMap
        (IndK.map (k := k) (BalancedTensor.mapRight (k := k)
          (B := TensorProductAlgebra k Q Λ (initWeight b + lastBlock b))
          (M := BlockLeftStandard Q Λ b (blockPrefix_last b) hα) g) x) =
      IndK.map (k := k) (parabolicStandardMapT Q Λ hQ (twoPieceEnd Q Λ b hα₁ g))
        (IndK.map (k := k) (splitStandardEquiv Q Λ hQ b hα₁ hα M).toLinearMap x) :=
  IndK.map_comm_apply (splitStandardEquiv_mapRight Q Λ hQ b hα₁ hα (M := M) g) x

/-- **`Fᵢ(M ⊗_B S^L_α) ≅ Fᵢ S(X_M)` over `T(i + (θ + β)) ⊗ C`.** -/
def fiTopEquiv :
    TensorAct k (TensorProductAlgebra k Q Λ (({i} : Multiset I) + (initWeight b + lastBlock b))) C
      (fiTopAction Q i Λ b (initWeight b + lastBlock b) hb hα C M ρ) ≃ₗ[
      TensorProductAlgebra k Q Λ (({i} : Multiset I) + (initWeight b + lastBlock b)) ⊗[k] C]
      FiMid Q Λ hQ i (initWeight b) (lastBlock b) C ((twoPieceEndAlg Q Λ b hα₁).comp ρ) :=
  TensorAct.equiv (Ind.mapEquiv (splitStandardEquiv Q Λ hQ b hα₁ hα M))
    fun c x => fiTopEquiv_natural Q Λ hQ i b M hα₁ hα (ρ c) x

end StendhalAlgebra

end Categorification.Stendhal
