/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FiLeftInput
import Categorification.WeightedKLR.RedStrands.StandardSplitFiltration
import Categorification.Algebra.TensorActRestrict

/-!
# The sub term of the last-strand sequence of `Fᵢ`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5, `F`-part. For blocks `b` of `ℓ + 1` red strands with first weight `θ` and last
block `β`, the sub term `S(₁Fᵢ X_M)` of the last-strand sequence (`fiSeqOne`) is, over
`T(i + (θ + β)) ⊗ C`, the standardization of `Fᵢ(M|_{B'} ⊗_{B'} S^L_{α'})`, the module of the
induction hypothesis, restricted along the identification of weights
`i + (θ + β) = (i + θ) + β` (`fiSubEquiv`).
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

section Restrict

variable (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (hQ : KLRSymm Q)
  (i : I) (θ β : Multiset I) (C : Type) [Ring C] [Algebra k C]
  {N : Type} [AddCommGroup N] [Module k N] [Module (parabolicFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N]
  (τ : C →ₐ[k] Module.End (parabolicFactorAlgebra Q Λ θ β) N)

local notation "Si" j => (Singleton.singleton j : Multiset I)
local notation "cst₁" => castTensorProductAlgebra Q Λ (firstInd_blackWeight i θ β)

/-- The ring map `T(i + (θ + β)) ⊗ C → T((i + θ) + β) ⊗ C` of the identification of weights. -/
abbrev firstIndCastHom :
    TensorProductAlgebra k Q Λ ((Si i) + (θ + β)) ⊗[k] C →+*
      TensorProductAlgebra k Q Λ (((Si i) + θ) + β) ⊗[k] C :=
  TensorAct.firstFactorHom cst₁

/-- **`S(₁Fᵢ N)` over `T(i + (θ + β)) ⊗ C` is the restriction of `S(₁Fᵢ N)` over
`T((i + θ) + β) ⊗ C`.** -/
def fiSubRestrictEquiv :
    FiSub Q Λ hQ i θ β C τ ≃ₗ[TensorProductAlgebra k Q Λ ((Si i) + (θ + β)) ⊗[k] C]
      (ModuleCat.restrictScalars (firstIndCastHom Q Λ i θ β C)).obj
        (standardAct Q Λ hQ C (fiLeftAction Q Λ i θ β C τ)) :=
  TensorAct.restrictEquiv cst₁ (AddEquiv.refl _) (fun _ _ => rfl) (fun _ _ => rfl)

end Restrict

variable (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (hQ : KLRSymm Q)
  (i : I) (b : Fin (ℓ + 2) → Multiset I)
  (M : Type) [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  (hα₁ : RootNonViolated (ν := initWeight b) (blockRoot (initBlocks b)))
  (C : Type) [Ring C] [Algebra k C] (ρ : C →ₐ[k] Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M)

local notation "Cyc" =>
  CycKLR k Q (fun i : I => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i) (lastBlock b)
local notation "ρ₁" => inductionAction Q Λ b M (rfl : lastBlock b = lastBlock b) C ρ
/-- The module of the induction hypothesis. -/
local notation "Y₁" => fiTop Q i (Λ ∘ Fin.castSucc) (initBlocks b) (initWeight b) rfl hα₁
  (Cyc ⊗[k] C) (InitRestrict Q Λ b M) ρ₁

/-- **`S(₁Fᵢ X_M) ≅ S(Fᵢ(M|_{B'} ⊗_{B'} S^L_{α'}))`**, over `T(i + (θ + β)) ⊗ C` through the
identification of weights. -/
def fiSubEquiv :
    FiSub Q Λ hQ i (initWeight b) (lastBlock b) C ((twoPieceEndAlg Q Λ b hα₁).comp ρ) ≃ₗ[
      TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) +
        (initWeight b + lastBlock b)) ⊗[k] C]
      (ModuleCat.restrictScalars (firstIndCastHom Q Λ i (initWeight b) (lastBlock b) C)).obj
        (splitStandard Q Λ hQ ((Singleton.singleton i : Multiset I) + initWeight b) (lastBlock b) C
          Y₁) :=
  (fiSubRestrictEquiv Q Λ hQ i (initWeight b) (lastBlock b) C
    ((twoPieceEndAlg Q Λ b hα₁).comp ρ)).trans
    ((ModuleCat.restrictScalars (firstIndCastHom Q Λ i (initWeight b) (lastBlock b) C)).mapIso
      (standardActEquiv Q Λ hQ (fiLeftInputEquiv Q Λ i b M hα₁ C ρ)
        (fun c w => fiLeftInputEquiv_natural Q Λ i b M hα₁ C ρ c w)).toModuleIso).toLinearEquiv

end StendhalAlgebra

end Categorification.Stendhal
