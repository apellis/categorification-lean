/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.EiStandardChain

/-!
# The layers of the induction hypothesis, standardized

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5. Let `κ` be one of the first `ℓ` red strands of blocks `b` of `ℓ + 1` red strands,
and `c` the blocks with one black strand of colour `i` removed from block `κ + 1`. The layer
`ₖEᵢ(M|_{B'}) ⊗ S^L_{α'}` of the induction hypothesis, a module over
`T^{λ'}(θ₀) ⊗ (R^{λ_ℓ}(β') ⊗ C)`, regarded over the factor algebra `T^{λ'}(θ₀) ⊗ R^{λ_ℓ}(β')`, is
the two-piece input `X_{M e}` of `M e = ₖEᵢ M` over the blocks `c` (`initLayerEquiv`), compatibly
with the actions of `C`. Standardizing, the layers of the induction hypothesis become the layers
`ₖEᵢ M ⊗_B S^L_{α_c}` for `ℓ + 1` red strands (`initLayerStandardEquiv`).
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
  (i : I) (κ : Fin ℓ) {b c : Fin (ℓ + 2) → Multiset I} (h0 : leftBlock c = leftBlock b)
  (hr : ∀ r, r ≠ κ.castSucc → rightBlock c r = rightBlock b r)
  (hκ : {i} + rightBlock c κ.castSucc = rightBlock b κ.castSucc)
  (M : Type) [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  (C : Type) [Ring C] [Algebra k C] (ρ : C →ₐ[k] Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M)

local notation "Cyc" β =>
  CycKLR k Q (fun i : I => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i) β
local notation "Tfam" => TensorProductAlgebra k Q (Λ ∘ Fin.castSucc)
local notation "M''" => BlockBlackRes Q Λ i κ.castSucc h0 hr hκ M
local notation "R₁" => BlockBlackRes Q (Λ ∘ Fin.castSucc) i κ (b := initBlocks b)
  (b' := initBlocks c) h0 (initBlocks_rightBlock_of_ne κ hr) hκ (InitRestrict Q Λ b M)

section Core

variable (hβ : lastBlock b = lastBlock c)
  (hα₁c : RootNonViolated (ν := initWeight c) (blockRoot (initBlocks c)))

local notation "ρ₁" => inductionAction Q Λ b M hβ C ρ
local notation "ρL" => BalancedTensor.endAction k (Tfam (initWeight c))
  (BlockLeftStandard Q (Λ ∘ Fin.castSucc) (initBlocks c) rfl hα₁c)
  (AlgHom.comp (blockBlackResEnd Q (Λ ∘ Fin.castSucc) i κ (b := initBlocks b)
    (b' := initBlocks c) h0 (initBlocks_rightBlock_of_ne κ hr) hκ (InitRestrict Q Λ b M)) ρ₁)
local notation "L₁" => TensorAct k (Tfam (initWeight c)) ((Cyc (lastBlock c)) ⊗[k] C) ρL
local notation "SL" => SplitLeft k (Tfam (initWeight c)) (Cyc (lastBlock c)) C L₁
local notation "X₁" => LeftStandardization Q (Λ ∘ Fin.castSucc) (initBlocks c) rfl hα₁c R₁
local notation "XL" => LeftStandardization Q (Λ ∘ Fin.castSucc) (initBlocks c) rfl hα₁c
  (InitRestrict Q Λ c M'')
local notation "Xc" => TwoPieceInput Q Λ c M'' hα₁c
local notation "ofX" => twoPieceInputOf Q Λ c M'' hα₁c
local notation "e₀" => BalancedTensor.congrRight (k := k) (B := Tfam (initWeight c))
  (M := BlockLeftStandard Q (Λ ∘ Fin.castSucc) (initBlocks c) rfl hα₁c)
  (initBlackResEquiv Q Λ i κ h0 hr hκ M)

/-- The unwrapping `SL → X₁`. -/
def splitLeftUnwrap : SL ≃+ X₁ :=
  (SplitLeft.of (k := k) (A₁ := Tfam (initWeight c)) (A₂ := Cyc (lastBlock c)) (C := C)
    (Y := L₁)).symm.trans (TensorAct.of (ρ := ρL)).symm.toAddEquiv

/-- The underlying additive map of `SL ≅ X_{M e}`. -/
def initLayerHom : SL →+ Xc :=
  ((ofX).toAddEquiv.toAddMonoidHom.comp (e₀).toAddEquiv.toAddMonoidHom).comp
    (splitLeftUnwrap Q Λ i κ h0 hr hκ M C ρ hβ hα₁c).toAddMonoidHom

theorem initLayerHom_of_of (x : X₁) :
    initLayerHom Q Λ i κ h0 hr hκ M C ρ hβ hα₁c
        (SplitLeft.of (k := k) (A₁ := Tfam (initWeight c)) (A₂ := Cyc (lastBlock c)) (C := C)
          (TensorAct.of (ρ := ρL) x)) = ofX (e₀ x) := rfl

theorem e₀_mapRight_lastFactorEnd (z : Cyc (lastBlock c)) (y : X₁) :
    e₀ (BalancedTensor.mapRight (Res.map (lastFactorEnd Q Λ b
        (CyclotomicAction.castCyc Q (fun i : I => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i)
          hβ.symm z))) y) =
      BalancedTensor.mapRight (lastFactorEnd Q Λ c z) (e₀ y) := by
  change ((BalancedTensor.mapRight (initBlackResEquiv Q Λ i κ h0 hr hκ M).toLinearMap).comp
      (BalancedTensor.mapRight _)) y =
    ((BalancedTensor.mapRight (lastFactorEnd Q Λ c z)).comp
      (BalancedTensor.mapRight (initBlackResEquiv Q Λ i κ h0 hr hκ M).toLinearMap)) y
  rw [← BalancedTensor.mapRight_comp, ← BalancedTensor.mapRight_comp]
  exact LinearMap.congr_fun (congrArg BalancedTensor.mapRight
    (LinearMap.ext fun x => initBlackResEquiv_lastFactorEnd Q Λ i κ h0 hr hκ M z x)) y

theorem e₀_mapRight_initRestrictEnd (g : Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M) (y : X₁) :
    e₀ (BalancedTensor.mapRight (Res.map (initRestrictEnd Q Λ b g)) y) =
      BalancedTensor.mapRight (initRestrictEnd Q Λ c (Res.map g)) (e₀ y) := by
  change ((BalancedTensor.mapRight (initBlackResEquiv Q Λ i κ h0 hr hκ M).toLinearMap).comp
      (BalancedTensor.mapRight _)) y =
    ((BalancedTensor.mapRight (initRestrictEnd Q Λ c (Res.map g))).comp
      (BalancedTensor.mapRight (initBlackResEquiv Q Λ i κ h0 hr hκ M).toLinearMap)) y
  rw [← BalancedTensor.mapRight_comp, ← BalancedTensor.mapRight_comp]
  exact LinearMap.congr_fun (congrArg BalancedTensor.mapRight
    (LinearMap.ext fun x => initBlackResEquiv_natural Q Λ i κ h0 hr hκ M g x)) y

local notation "ofL" y => SplitLeft.of (k := k) (A₁ := Tfam (initWeight c))
  (A₂ := Cyc (lastBlock c)) (C := C) (TensorAct.of (ρ := ρL) y)

theorem initLayerHom_tmul_one_of (t : Tfam (initWeight c)) (y : X₁) :
    initLayerHom Q Λ i κ h0 hr hκ M C ρ hβ hα₁c
        ((t ⊗ₜ 1 : parabolicFactorAlgebra Q Λ (initWeight c) (lastBlock c)) • ofL y) =
      (t ⊗ₜ 1 : parabolicFactorAlgebra Q Λ (initWeight c) (lastBlock c)) •
        initLayerHom Q Λ i κ h0 hr hκ M C ρ hβ hα₁c (ofL y) := by
  rw [SplitLeft.tmul_one_smul_of_of]
  change ofX (e₀ (t • y)) = (t ⊗ₜ 1 : parabolicFactorAlgebra Q Λ (initWeight c) (lastBlock c)) •
    ofX (e₀ y)
  rw [map_smul, twoPieceInput_smul_def, twoPieceInputAction_tmul, lastFactorEnd_one]
  exact congrArg (fun w => ofX (t • w)) (LinearMap.congr_fun (BalancedTensor.mapRight_id (k := k)
    (B := Tfam (initWeight c)) (M := BlockLeftStandard Q (Λ ∘ Fin.castSucc) (initBlocks c) rfl
      hα₁c)) (e₀ y)).symm

theorem initLayerHom_one_tmul_of (z : Cyc (lastBlock c)) (y : X₁) :
    initLayerHom Q Λ i κ h0 hr hκ M C ρ hβ hα₁c
        ((1 ⊗ₜ z : parabolicFactorAlgebra Q Λ (initWeight c) (lastBlock c)) • ofL y) =
      (1 ⊗ₜ z : parabolicFactorAlgebra Q Λ (initWeight c) (lastBlock c)) •
        initLayerHom Q Λ i κ h0 hr hκ M C ρ hβ hα₁c (ofL y) := by
  rw [SplitLeft.one_tmul_smul_of_of]
  change ofX (e₀ (BalancedTensor.mapRight (Res.map (ρ₁ (z ⊗ₜ 1))) y)) =
    (1 ⊗ₜ z : parabolicFactorAlgebra Q Λ (initWeight c) (lastBlock c)) • ofX (e₀ y)
  rw [twoPieceInput_smul_def, twoPieceInputAction_tmul, one_smul]
  rw [inductionAction_tmul_one Q Λ b M hβ C ρ, e₀_mapRight_lastFactorEnd Q Λ i κ h0 hr hκ M hβ hα₁c]

theorem initLayerHom_tmul_one (t : Tfam (initWeight c)) (x : SL) :
    initLayerHom Q Λ i κ h0 hr hκ M C ρ hβ hα₁c
        ((t ⊗ₜ 1 : parabolicFactorAlgebra Q Λ (initWeight c) (lastBlock c)) • x) =
      (t ⊗ₜ 1 : parabolicFactorAlgebra Q Λ (initWeight c) (lastBlock c)) •
        initLayerHom Q Λ i κ h0 hr hκ M C ρ hβ hα₁c x := by
  obtain ⟨y, rfl⟩ := (splitLeftUnwrap Q Λ i κ h0 hr hκ M C ρ hβ hα₁c).symm.surjective x
  exact initLayerHom_tmul_one_of Q Λ i κ h0 hr hκ M C ρ hβ hα₁c t y

theorem initLayerHom_one_tmul (z : Cyc (lastBlock c)) (x : SL) :
    initLayerHom Q Λ i κ h0 hr hκ M C ρ hβ hα₁c
        ((1 ⊗ₜ z : parabolicFactorAlgebra Q Λ (initWeight c) (lastBlock c)) • x) =
      (1 ⊗ₜ z : parabolicFactorAlgebra Q Λ (initWeight c) (lastBlock c)) •
        initLayerHom Q Λ i κ h0 hr hκ M C ρ hβ hα₁c x := by
  obtain ⟨y, rfl⟩ := (splitLeftUnwrap Q Λ i κ h0 hr hκ M C ρ hβ hα₁c).symm.surjective x
  exact initLayerHom_one_tmul_of Q Λ i κ h0 hr hκ M C ρ hβ hα₁c z y

/-- **The layer of the induction hypothesis as the input `X_{M e}`**, over the factor algebra. -/
def initLayerEquiv :
    SL ≃ₗ[parabolicFactorAlgebra Q Λ (initWeight c) (lastBlock c)] Xc :=
  LinearEquiv.ofBijective
    (tensorLinearOfGenerators (A := Tfam (initWeight c)) (C := Cyc (lastBlock c))
      (initLayerHom Q Λ i κ h0 hr hκ M C ρ hβ hα₁c)
      (initLayerHom_tmul_one Q Λ i κ h0 hr hκ M C ρ hβ hα₁c)
      (initLayerHom_one_tmul Q Λ i κ h0 hr hκ M C ρ hβ hα₁c))
    ((ofX).bijective.comp ((e₀).bijective.comp
      (splitLeftUnwrap Q Λ i κ h0 hr hκ M C ρ hβ hα₁c).bijective))

theorem initLayerEquiv_of_of (x : X₁) :
    initLayerEquiv Q Λ i κ h0 hr hκ M C ρ hβ hα₁c (ofL x) = ofX (e₀ x) := rfl

theorem initLayerEquiv_action_of (x : C) (y : X₁) :
    initLayerEquiv Q Λ i κ h0 hr hκ M C ρ hβ hα₁c (SplitLeft.action L₁ x (ofL y)) =
      twoPieceEnd Q Λ c hα₁c (blockBlackResEnd Q Λ i κ.castSucc h0 hr hκ M (ρ x))
        (initLayerEquiv Q Λ i κ h0 hr hκ M C ρ hβ hα₁c (ofL y)) := by
  rw [SplitLeft.action_of_of]
  change ofX (e₀ (BalancedTensor.mapRight (Res.map (ρ₁ (1 ⊗ₜ x))) y)) =
    twoPieceEnd Q Λ c hα₁c (blockBlackResEnd Q Λ i κ.castSucc h0 hr hκ M (ρ x)) (ofX (e₀ y))
  rw [twoPieceEnd_of]
  rw [inductionAction_one_tmul Q Λ b M hβ C ρ, e₀_mapRight_initRestrictEnd Q Λ i κ h0 hr hκ M hα₁c]
  rfl

/-- **`initLayerEquiv` intertwines the actions of `C`.** -/
theorem initLayerEquiv_action (x : C) (z : SL) :
    initLayerEquiv Q Λ i κ h0 hr hκ M C ρ hβ hα₁c (SplitLeft.action L₁ x z) =
      twoPieceEnd Q Λ c hα₁c (blockBlackResEnd Q Λ i κ.castSucc h0 hr hκ M (ρ x))
        (initLayerEquiv Q Λ i κ h0 hr hκ M C ρ hβ hα₁c z) := by
  obtain ⟨y, rfl⟩ := (splitLeftUnwrap Q Λ i κ h0 hr hκ M C ρ hβ hα₁c).symm.surjective z
  exact initLayerEquiv_action_of Q Λ i κ h0 hr hκ M C ρ hβ hα₁c x y

end Core

section Standard

variable {θ₀ β' : Multiset I} (hβ : lastBlock b = β') (hβc : lastBlock c = β')
  (hθc : initWeight c = θ₀)
  (hα₁c : RootNonViolated (ν := initWeight c) (blockRoot (initBlocks c)))
  (hb'₁ : blockPrefix (initBlocks c) (ℓ + 1) = θ₀)
  (hα'₁ : RootNonViolated (ν := θ₀) (blockRoot (initBlocks c)))
  (hb'' : blockPrefix c (ℓ + 2) = θ₀ + β') (hα'' : RootNonViolated (ν := θ₀ + β') (blockRoot c))

/-- **The standardized layer of the induction hypothesis is the layer for `ℓ + 1` red strands**:
`S(ₖEᵢ(M|_{B'}) ⊗ S^L_{α'}) ≅ ₖEᵢ M ⊗_B S^L_{α_c}` over `T(θ₀ + β') ⊗ C`. -/
def initLayerStandardEquiv :
    splitStandard Q Λ hQ θ₀ β' C (eiLayer Q i (Λ ∘ Fin.castSucc) (b := initBlocks b)
      (b' := initBlocks c) θ₀ κ h0 (initBlocks_rightBlock_of_ne κ hr) hκ hb'₁ hα'₁
      ((Cyc β') ⊗[k] C) (InitRestrict Q Λ b M) (inductionAction Q Λ b M hβ C ρ)) ≃ₗ[
      TensorProductAlgebra k Q Λ (θ₀ + β') ⊗[k] C]
      eiLayer Q i Λ (b := b) (b' := c) (θ₀ + β') κ.castSucc h0 hr hκ hb'' hα'' C M ρ := by
  subst hθc hβc
  exact (standardActEquiv Q Λ hQ ((initLayerEquiv Q Λ i κ h0 hr hκ M C ρ hβ hα₁c).trans
      ((factorCastRfl Q Λ _).trans (factorCastRfl Q Λ _)))
      (fun x z => initLayerEquiv_action Q Λ i κ h0 hr hκ M C ρ hβ hα₁c x z)).trans
    (standardTwoPieceActEquiv Q Λ hQ c (BlockBlackRes Q Λ i κ.castSucc h0 hr hκ M) rfl rfl hα₁c
      hb'' hα'' C ((blockBlackResEnd Q Λ i κ.castSucc h0 hr hκ M).comp ρ)).symm

end Standard

end StendhalAlgebra

end Categorification.Stendhal
