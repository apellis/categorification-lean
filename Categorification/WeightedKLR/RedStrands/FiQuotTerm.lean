/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FiLastInput
import Categorification.WeightedKLR.RedStrands.FiInitLayer

/-!
# The quotient term of the last-strand sequence of `Fᵢ`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5, `F`-part. For blocks `b` of `ℓ + 1` red strands and the blocks `c` with one
black strand of colour `i` added to the last block, the quotient term `S(₂Fᵢ X_M)` of the
last-strand sequence (`fiSeqTwo`) is the layer `ₗFᵢ M ⊗_{B(c)} S^L_{α_c}` of the last red
strand, over `T(i + (θ + β)) ⊗ C` (`fiQuotEquiv`).
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
local notation "cst₂" => castTensorProductAlgebra Q Λ (lastInd_blackWeight i θ β)

/-- The ring map `T(i + (θ + β)) ⊗ C → T(θ + (i + β)) ⊗ C` of the identification of weights. -/
abbrev lastIndCastHom :
    TensorProductAlgebra k Q Λ ((Si i) + (θ + β)) ⊗[k] C →+*
      TensorProductAlgebra k Q Λ (θ + ((Si i) + β)) ⊗[k] C :=
  TensorAct.firstFactorHom cst₂

/-- **`S(₂Fᵢ N)` over `T(i + (θ + β)) ⊗ C` is the restriction of `S(₂Fᵢ N)` over
`T(θ + (i + β)) ⊗ C`.** -/
def fiQuotRestrictEquiv :
    FiQuot Q Λ hQ i θ β C τ ≃ₗ[TensorProductAlgebra k Q Λ ((Si i) + (θ + β)) ⊗[k] C]
      (ModuleCat.restrictScalars (lastIndCastHom Q Λ i θ β C)).obj
        (standardAct Q Λ hQ C (fiRightAction Q Λ i θ β C τ)) :=
  TensorAct.restrictEquiv cst₂ (AddEquiv.refl _) (fun _ _ => rfl) (fun _ _ => rfl)

end Restrict

section LayerRestrict

variable (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I)
  {b c : Fin (ℓ + 2) → Multiset I} (κ : Fin (ℓ + 1)) (h0 : leftBlock b = leftBlock c)
  (hr : ∀ r, r ≠ κ → rightBlock b r = rightBlock c r)
  (hκ : {i} + rightBlock b κ = rightBlock c κ)
  (M : Type) [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  (C : Type) [Ring C] [Algebra k C] (ρ : C →ₐ[k] Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M)
  {ν μ : Multiset I} (hcast : (Singleton.singleton i : Multiset I) + ν = μ)
  (hb' : blockPrefix c (ℓ + 1 + 1) = (Singleton.singleton i : Multiset I) + ν)
  (hα' : RootNonViolated (ν := (Singleton.singleton i : Multiset I) + ν) (blockRoot c))
  (hbμ : blockPrefix c (ℓ + 1 + 1) = μ) (hαμ : RootNonViolated (ν := μ) (blockRoot c))

local notation "Mf" => BlockBlackInd Q Λ i κ h0 hr hκ M

/-- **`ₖFᵢ M ⊗_B S^L_{α_c}` over `T(i + ν) ⊗ C`** is the restriction of the same module over
`T(μ) ⊗ C` along an identification of weights `i + ν = μ`. -/
def fiLayerRestrictEquivOf :
    (ModuleCat.restrictScalars (TensorAct.firstFactorHom (C := C)
        (castTensorProductAlgebra Q Λ hcast))).obj
      (ModuleCat.of (TensorProductAlgebra k Q Λ μ ⊗[k] C)
        (TensorAct k (TensorProductAlgebra k Q Λ μ) C
          (BalancedTensor.endAction k (TensorProductAlgebra k Q Λ μ)
            (BlockLeftStandard Q Λ c hbμ hαμ)
            ((blockBlackIndEnd Q Λ i κ h0 hr hκ M).comp ρ)))) ≃ₗ[
        TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν) ⊗[k] C]
      fiLayer Q i Λ ν κ h0 hr hκ hb' hα' C M ρ :=
  (TensorAct.restrictEquiv (castTensorProductAlgebra Q Λ hcast)
    (ρ := BalancedTensor.endAction k (TensorProductAlgebra k Q Λ μ)
      (BlockLeftStandard Q Λ c hbμ hαμ) ((blockBlackIndEnd Q Λ i κ h0 hr hκ M).comp ρ))
    (ρ' := BalancedTensor.endAction k
      (TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν))
      (BlockLeftStandard Q Λ c hb' hα') ((blockBlackIndEnd Q Λ i κ h0 hr hκ M).comp ρ))
    ((leftStandardizationFamilyCast (Q := Q) (Λ := Λ) Mf hcast.symm hbμ hb'
      hαμ hα').toAddEquiv : LeftStandardization Q Λ c hb' hα' Mf ≃+
        LeftStandardization Q Λ c hbμ hαμ Mf)
    (fun a v => (map_smul (leftStandardizationFamilyCast (Q := Q) (Λ := Λ) Mf hcast.symm
      hbμ hb' hαμ hα') a v).trans
        (familyCast_tensorProductAlgebra_smul hcast.symm
          (P := LeftStandardization Q Λ c hbμ hαμ Mf) a _))
    (fun x v => leftStandardizationFamilyCast_mapRight hcast.symm hbμ hb' hαμ
      hα' ((blockBlackIndEnd Q Λ i κ h0 hr hκ M) (ρ x)) v)).symm

end LayerRestrict

variable (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (hQ : KLRSymm Q)
  (i : I) {b c : Fin (ℓ + 2) → Multiset I} (h0 : leftBlock b = leftBlock c)
  (hr : ∀ r, r ≠ Fin.last ℓ → rightBlock b r = rightBlock c r)
  (hκ : {i} + rightBlock b (Fin.last ℓ) = rightBlock c (Fin.last ℓ))
  (M : Type) [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  (hα₁ : RootNonViolated (ν := initWeight b) (blockRoot (initBlocks b)))
  (hαc : RootNonViolated (ν := initWeight c) (blockRoot (initBlocks c)))
  (C : Type) [Ring C] [Algebra k C] (ρ : C →ₐ[k] Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M)
  (hbc : blockPrefix c (ℓ + 2) = initWeight b + ((Singleton.singleton i : Multiset I) +
    lastBlock b))
  (hαbc : RootNonViolated (ν := initWeight b + ((Singleton.singleton i : Multiset I) +
    lastBlock b)) (blockRoot c))

local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "Mf" => BlockBlackInd Q Λ i (Fin.last ℓ) h0 hr hκ M
local notation "τ" => AlgHom.comp (twoPieceEndAlg Q Λ b hα₁) ρ

theorem fiLastInputEquiv_action (x : C)
    (z : LastIndRight Q Λ i (initWeight b) (lastBlock b) (TwoPieceInput Q Λ b M hα₁)) :
    fiLastInputEquiv Q Λ i h0 hr hκ M hα₁ hαc
        (fiRightAction Q Λ i (initWeight b) (lastBlock b) C τ x z) =
      twoPieceCastAction Q Λ c Mf (initWeight_lastBig h0 hr) (lastBlock_lastBig i hκ) hαc C
        ((blockBlackIndEnd Q Λ i (Fin.last ℓ) h0 hr hκ M).comp ρ) x
        (fiLastInputEquiv Q Λ i h0 hr hκ M hα₁ hαc z) := by
  rw [twoPieceCastAction_apply]
  exact fiLastInputEquiv_natural Q Λ i h0 hr hκ M hα₁ hαc (ρ x) z

/-- **`S(₂Fᵢ X_M) ≅ ₗFᵢ M ⊗_{B(c)} S^L_{α_c}`** over `T(θ + (i + β)) ⊗ C`. -/
def fiQuotCoreEquiv :
    TensorAct k (TensorProductAlgebra k Q Λ (initWeight b + (Si + lastBlock b))) C
        (standardActionT Q Λ hQ C (fiRightAction Q Λ i (initWeight b) (lastBlock b) C τ)) ≃ₗ[
      TensorProductAlgebra k Q Λ (initWeight b + (Si + lastBlock b)) ⊗[k] C]
      TensorAct k (TensorProductAlgebra k Q Λ (initWeight b + (Si + lastBlock b))) C
        (BalancedTensor.endAction k (TensorProductAlgebra k Q Λ (initWeight b + (Si + lastBlock b)))
          (BlockLeftStandard Q Λ c hbc hαbc)
          ((blockBlackIndEnd Q Λ i (Fin.last ℓ) h0 hr hκ M).comp ρ)) :=
  (standardActEquiv Q Λ hQ (ρ := fiRightAction Q Λ i (initWeight b) (lastBlock b) C τ)
    (ρ' := twoPieceCastAction Q Λ c Mf (initWeight_lastBig h0 hr) (lastBlock_lastBig i hκ) hαc C
      ((blockBlackIndEnd Q Λ i (Fin.last ℓ) h0 hr hκ M).comp ρ))
    (fiLastInputEquiv Q Λ i h0 hr hκ M hα₁ hαc)
    (fiLastInputEquiv_action Q Λ i h0 hr hκ M hα₁ hαc C ρ)).trans
    (standardTwoPieceActEquiv Q Λ hQ c Mf (initWeight_lastBig h0 hr) (lastBlock_lastBig i hκ)
      hαc hbc hαbc C ((blockBlackIndEnd Q Λ i (Fin.last ℓ) h0 hr hκ M).comp ρ)).symm

/-- **`S(₂Fᵢ X_M) ≅ ₗFᵢ M ⊗_{B(c)} S^L_{α_c}`** (Webster, arXiv:1309.3796v3, proof of
Proposition 5.5, `F`-part): the quotient term of the last-strand sequence is the layer of the last
red strand, over `T(i + (θ + β)) ⊗ C`. -/
def fiQuotEquiv (hb' : blockPrefix c (ℓ + 1 + 1) = Si + (initWeight b + lastBlock b))
    (hα' : RootNonViolated (ν := Si + (initWeight b + lastBlock b)) (blockRoot c)) :
    FiQuot Q Λ hQ i (initWeight b) (lastBlock b) C τ ≃ₗ[
      TensorProductAlgebra k Q Λ (Si + (initWeight b + lastBlock b)) ⊗[k] C]
      fiLayer Q i Λ (initWeight b + lastBlock b) (Fin.last ℓ) h0 hr hκ hb' hα' C M ρ := by
  have hbc : blockPrefix c (ℓ + 2) = initWeight b + (Si + lastBlock b) :=
    hb'.trans (lastInd_blackWeight i _ _)
  have hαbc : RootNonViolated (ν := initWeight b + (Si + lastBlock b)) (blockRoot c) :=
    lastInd_blackWeight i (initWeight b) (lastBlock b) ▸ hα'
  exact (fiQuotRestrictEquiv Q Λ hQ i (initWeight b) (lastBlock b) C τ).trans
    ((((ModuleCat.restrictScalars (lastIndCastHom Q Λ i (initWeight b) (lastBlock b) C)).mapIso
      (fiQuotCoreEquiv Q Λ hQ i h0 hr hκ M hα₁ hαc C ρ hbc hαbc).toModuleIso).toLinearEquiv).trans
      (fiLayerRestrictEquivOf Q Λ i (Fin.last ℓ) h0 hr hκ M C ρ (lastInd_blackWeight i _ _) hb' hα'
        hbc hαbc))

end StendhalAlgebra

end Categorification.Stendhal
