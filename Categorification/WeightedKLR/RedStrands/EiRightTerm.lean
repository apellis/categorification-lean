/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.EiLeftInput
import Categorification.WeightedKLR.RedStrands.EiCaseBoth
import Categorification.WeightedKLR.RedStrands.StandardSplitFiltration

/-!
# The right term of the last-strand sequence

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5. For blocks `b` of `ℓ + 1` red strands with first weight `i + θ₀` and last block
`i + β₀`, the right term `S(₁Eᵢ X_M)` of the last-strand sequence (`bothSeqOne`) is the
standardization of `Eᵢ(M|_{B'} ⊗_{B'} S^L_{α'})`, the module of the induction hypothesis, as a
module over `T(θ₀ + i + β₀) ⊗ C` (`rightTermEquiv`).
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
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (hQ : KLRSymm Q) (i : I)
  (b : Fin (ℓ + 2) → Multiset I)
  (M : Type) [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  {θ₀ β₀ : Multiset I} (hθ : initWeight b = ({i} : Multiset I) + θ₀)
  (hβ : lastBlock b = ({i} : Multiset I) + β₀)
  (hα₁ : RootNonViolated (ν := initWeight b) (blockRoot (initBlocks b)))
  (hα₁' : RootNonViolated (ν := ({i} : Multiset I) + θ₀) (blockRoot (initBlocks b)))
  (C : Type) [Ring C] [Algebra k C] (ρ : C →ₐ[k] Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M)

/-- **`S(₁Eᵢ X_M) ≅ S(Eᵢ(M|_{B'} ⊗_{B'} S^L_{α'}))` over `T(θ₀ + i + β₀) ⊗ C`.** -/
def rightTermEquiv :
    BothRight Q Λ hQ i θ₀ β₀ C (twoPieceCastAction Q Λ b M hθ hβ hα₁ C ρ) ≃ₗ[
      TensorProductAlgebra k Q Λ (θ₀ + (({i} : Multiset I) + β₀)) ⊗[k] C]
      TensorAct k (TensorProductAlgebra k Q Λ (θ₀ + (({i} : Multiset I) + β₀))) C
        (splitStandardAction Q Λ hQ (eiTop Q i (Λ ∘ Fin.castSucc) (initBlocks b) θ₀ hθ hα₁'
          ((CycKLR k Q (fun i : I => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i)
            (({i} : Multiset I) + β₀)) ⊗[k] C) (InitRestrict Q Λ b M)
          (inductionAction Q Λ b M hβ C ρ))) :=
  standardActEquiv Q Λ hQ (leftInputEquiv Q Λ i b M hθ hβ hα₁ hα₁' C ρ)
    fun c z => leftInputEquiv_natural Q Λ i b M hθ hβ hα₁ hα₁' C ρ c z

end StendhalAlgebra

end Categorification.Stendhal
