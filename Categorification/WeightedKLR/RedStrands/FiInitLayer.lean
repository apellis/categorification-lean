/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FiInitInduction
import Categorification.WeightedKLR.RedStrands.FiSubTerm

/-!
# The layers of the induction hypothesis of the `Fᵢ` filtration, standardized

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5, `F`-part. Let `κ` be one of the first `ℓ` red strands of blocks `b` of `ℓ + 1`
red strands, and `c` the blocks with one black strand of colour `i` added to block `κ + 1`. The
layer `ₖFᵢ(M|_{B'}) ⊗ S^L_{α'}` of the induction hypothesis, a module over
`T^{λ'}(θ') ⊗ (R^{λ_ℓ}(β') ⊗ C)`, regarded over the factor algebra, is the two-piece input
`X_{ₖFᵢ M}` of `ₖFᵢ M` over the blocks `c` (`fiInitLayerEquiv`), compatibly with the actions of
`C`. Standardizing, and restricting along an identification of weights `i + ν = θ' + β'`, the
layers of the induction hypothesis become the layers `ₖFᵢ M ⊗_B S^L_{α_c}` for `ℓ + 1` red
strands (`fiInitLayerStandardEquiv`).
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace Categorification

open scoped TensorProduct

namespace SplitLeft.TensorAct

variable {k : Type*} [CommRing k] {A₁ A₂ C : Type*} [Ring A₁] [Algebra k A₁] [Ring A₂]
  [Algebra k A₂] [Ring C] [Algebra k C] {X : Type*} [AddCommGroup X] [Module k X] [Module A₁ X]
  [IsScalarTower k A₁ X] (ρ : A₂ ⊗[k] C →ₐ[k] Module.End A₁ X)

/-- A map out of `SplitLeft (TensorAct ρ)` intertwines the action of `c ∈ C` with a map `g` as
soon as it does so on generators. -/
theorem map_action_of_of {Z F : Type*}
    [FunLike F (SplitLeft k A₁ A₂ C (TensorAct k A₁ (A₂ ⊗[k] C) ρ)) Z]
    (f : F) (g : Z → Z) (c : C)
    (h : ∀ x : X, f (of (k := k) (A₁ := A₁) (A₂ := A₂) (C := C) (TensorAct.of (ρ := ρ)
      (ρ (1 ⊗ₜ c) x))) =
        g (f (of (k := k) (A₁ := A₁) (A₂ := A₂) (C := C) (TensorAct.of (ρ := ρ) x))))
    (z : SplitLeft k A₁ A₂ C (TensorAct k A₁ (A₂ ⊗[k] C) ρ)) :
    f (action (TensorAct k A₁ (A₂ ⊗[k] C) ρ) c z) = g (f z) := by
  obtain ⟨w, rfl⟩ := (of (k := k) (A₁ := A₁) (A₂ := A₂) (C := C)).surjective z
  obtain ⟨x, rfl⟩ := (TensorAct.of (ρ := ρ)).surjective w
  rw [action_of_of]
  exact h x

end SplitLeft.TensorAct

end Categorification

namespace Categorification.Stendhal

open KLR KLRAlgebra MulOpposite InductionAlong
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

namespace StendhalAlgebra

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (hQ : KLRSymm Q)
  (i : I) (κ : Fin ℓ) {b c : Fin (ℓ + 2) → Multiset I} (h0 : leftBlock b = leftBlock c)
  (hr : ∀ r, r ≠ κ.castSucc → rightBlock b r = rightBlock c r)
  (hκ : {i} + rightBlock b κ.castSucc = rightBlock c κ.castSucc)
  (M : Type) [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  (C : Type) [Ring C] [Algebra k C] (ρ : C →ₐ[k] Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M)

local notation "Cyc" β =>
  CycKLR k Q (fun i : I => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i) β
local notation "Tfam" => TensorProductAlgebra k Q (Λ ∘ Fin.castSucc)
local notation "Mf" => BlockBlackInd Q Λ i κ.castSucc (b := c) (b' := b) h0 hr hκ M
local notation "φ₁" => blockBlackResOp Q (Λ ∘ Fin.castSucc) i κ (b := initBlocks c)
  (b' := initBlocks b) h0 (initBlocks_rightBlock_of_ne κ hr) hκ
local notation "R₁" => IndK k (InitRestrict Q Λ b M) φ₁
local notation "hβ" => (lastBlock_eq_of_castSucc (b := c) (b' := b) (κ := κ) hr :
  lastBlock b = lastBlock c)

section Core

variable (hα₁c : RootNonViolated (ν := initWeight c) (blockRoot (initBlocks c)))

local notation "ρ₁" => inductionAction Q Λ b M (β' := lastBlock c) hβ C ρ
local notation "ρL" => BalancedTensor.endAction k (Tfam (initWeight c))
  (BlockLeftStandard Q (Λ ∘ Fin.castSucc) (initBlocks c) rfl hα₁c)
  (AlgHom.comp (blockBlackIndEnd Q (Λ ∘ Fin.castSucc) i κ (b := initBlocks c)
    (b' := initBlocks b) h0 (initBlocks_rightBlock_of_ne κ hr) hκ (InitRestrict Q Λ b M)) ρ₁)
local notation "L₁" => TensorAct k (Tfam (initWeight c)) ((Cyc (lastBlock c)) ⊗[k] C) ρL
local notation "SL" => SplitLeft k (Tfam (initWeight c)) (Cyc (lastBlock c)) C L₁
local notation "X₁" => LeftStandardization Q (Λ ∘ Fin.castSucc) (initBlocks c) rfl hα₁c R₁
local notation "Xc" => TwoPieceInput Q Λ c Mf hα₁c
local notation "ofX" => twoPieceInputOf Q Λ c Mf hα₁c
local notation "e₀" => BalancedTensor.congrRight (k := k) (B := Tfam (initWeight c))
  (M := BlockLeftStandard Q (Λ ∘ Fin.castSucc) (initBlocks c) rfl hα₁c)
  (initBlackIndEquiv Q Λ i κ h0 hr hκ M)
local notation "mR" => BalancedTensor.mapRight (k := k) (B := Tfam (initWeight c))
  (M := BlockLeftStandard Q (Λ ∘ Fin.castSucc) (initBlocks c) rfl hα₁c)

/-- The unwrapping `SL → X₁`. -/
def fiSplitLeftUnwrap : SL ≃+ X₁ :=
  (SplitLeft.of (k := k) (A₁ := Tfam (initWeight c)) (A₂ := Cyc (lastBlock c)) (C := C)
    (Y := L₁)).symm.trans (TensorAct.of (ρ := ρL)).symm.toAddEquiv

/-- The underlying additive map of `SL ≅ X_{ₖFᵢ M}`. -/
def fiInitLayerHom : SL →+ Xc :=
  ((ofX).toAddEquiv.toAddMonoidHom.comp (e₀).toAddEquiv.toAddMonoidHom).comp
    (fiSplitLeftUnwrap Q Λ i κ h0 hr hκ M C ρ hα₁c).toAddMonoidHom

theorem e₀_mapRight_lastFactorEndF (z : Cyc (lastBlock c)) (y : X₁) :
    e₀ (mR (IndK.map (lastFactorEnd Q Λ b
        (CyclotomicAction.castCyc Q (fun i : I => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i)
          (hβ).symm z))) y) =
      mR (lastFactorEnd Q Λ c z) (e₀ y) := by
  change ((BalancedTensor.mapRight (initBlackIndEquiv Q Λ i κ h0 hr hκ M).toLinearMap).comp
      (BalancedTensor.mapRight _)) y =
    ((BalancedTensor.mapRight (lastFactorEnd Q Λ c z)).comp
      (BalancedTensor.mapRight (initBlackIndEquiv Q Λ i κ h0 hr hκ M).toLinearMap)) y
  rw [← BalancedTensor.mapRight_comp, ← BalancedTensor.mapRight_comp]
  refine LinearMap.congr_fun (congrArg BalancedTensor.mapRight (LinearMap.ext fun x => ?_)) y
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    initBlackIndEquiv_lastFactorEnd, castCyc_symm_castCyc Q (hβ).symm z]

theorem e₀_mapRight_initRestrictEndF (g : Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M) (y : X₁) :
    e₀ (mR (IndK.map (initRestrictEnd Q Λ b g)) y) =
      mR (initRestrictEnd Q Λ c (IndK.map g)) (e₀ y) := by
  change ((BalancedTensor.mapRight (initBlackIndEquiv Q Λ i κ h0 hr hκ M).toLinearMap).comp
      (BalancedTensor.mapRight _)) y =
    ((BalancedTensor.mapRight (initRestrictEnd Q Λ c (IndK.map g))).comp
      (BalancedTensor.mapRight (initBlackIndEquiv Q Λ i κ h0 hr hκ M).toLinearMap)) y
  rw [← BalancedTensor.mapRight_comp, ← BalancedTensor.mapRight_comp]
  exact LinearMap.congr_fun (congrArg BalancedTensor.mapRight
    (LinearMap.ext fun x => initBlackIndEquiv_natural Q Λ i κ h0 hr hκ M g x)) y

local notation "ofL" y => SplitLeft.of (k := k) (A₁ := Tfam (initWeight c))
  (A₂ := Cyc (lastBlock c)) (C := C) (TensorAct.of (ρ := ρL) y)

theorem fiInitLayerHom_tmul_one_of (t : Tfam (initWeight c)) (y : X₁) :
    fiInitLayerHom Q Λ i κ h0 hr hκ M C ρ hα₁c
        ((t ⊗ₜ 1 : Tfam (initWeight c) ⊗[k] Cyc (lastBlock c)) • ofL y) =
      (t ⊗ₜ 1 : Tfam (initWeight c) ⊗[k] Cyc (lastBlock c)) •
        fiInitLayerHom Q Λ i κ h0 hr hκ M C ρ hα₁c (ofL y) := by
  refine (congrArg (fiInitLayerHom Q Λ i κ h0 hr hκ M C ρ hα₁c)
    (SplitLeft.tmul_one_smul_of_of (k := k) (A₁ := Tfam (initWeight c)) (A₂ := Cyc (lastBlock c))
    (C := C) ρL t y)).trans ?_
  change ofX (e₀ (t • y)) = (t ⊗ₜ 1 : parabolicFactorAlgebra Q Λ (initWeight c) (lastBlock c)) •
    ofX (e₀ y)
  rw [map_smul, twoPieceInput_smul_def, twoPieceInputAction_tmul, lastFactorEnd_one]
  exact congrArg (fun w => ofX (t • w)) (LinearMap.congr_fun (BalancedTensor.mapRight_id (k := k)
    (B := Tfam (initWeight c)) (M := BlockLeftStandard Q (Λ ∘ Fin.castSucc) (initBlocks c) rfl
      hα₁c)) (e₀ y)).symm

theorem fiInitLayerHom_one_tmul_of (z : Cyc (lastBlock c)) (y : X₁) :
    fiInitLayerHom Q Λ i κ h0 hr hκ M C ρ hα₁c
        ((1 ⊗ₜ z : Tfam (initWeight c) ⊗[k] Cyc (lastBlock c)) • ofL y) =
      (1 ⊗ₜ z : Tfam (initWeight c) ⊗[k] Cyc (lastBlock c)) •
        fiInitLayerHom Q Λ i κ h0 hr hκ M C ρ hα₁c (ofL y) := by
  refine (congrArg (fiInitLayerHom Q Λ i κ h0 hr hκ M C ρ hα₁c)
    (SplitLeft.one_tmul_smul_of_of (k := k) (A₁ := Tfam (initWeight c)) (A₂ := Cyc (lastBlock c))
    (C := C) ρL z y)).trans ?_
  change ofX (e₀ (mR (IndK.map (ρ₁ (z ⊗ₜ 1))) y)) =
    (1 ⊗ₜ z : Tfam (initWeight c) ⊗[k] Cyc (lastBlock c)) • ofX (e₀ y)
  rw [twoPieceInput_smul_def, twoPieceInputAction_tmul, one_smul]
  rw [inductionAction_tmul_one Q Λ b M (β' := lastBlock c) hβ C ρ]
  exact congrArg (ofX) (e₀_mapRight_lastFactorEndF Q Λ i κ h0 hr hκ M hα₁c z y)

theorem fiInitLayerHom_tmul_one (t : Tfam (initWeight c)) (x : SL) :
    fiInitLayerHom Q Λ i κ h0 hr hκ M C ρ hα₁c
        ((t ⊗ₜ 1 : Tfam (initWeight c) ⊗[k] Cyc (lastBlock c)) • x) =
      (t ⊗ₜ 1 : Tfam (initWeight c) ⊗[k] Cyc (lastBlock c)) •
        fiInitLayerHom Q Λ i κ h0 hr hκ M C ρ hα₁c x := by
  obtain ⟨y, rfl⟩ := (fiSplitLeftUnwrap Q Λ i κ h0 hr hκ M C ρ hα₁c).symm.surjective x
  exact fiInitLayerHom_tmul_one_of Q Λ i κ h0 hr hκ M C ρ hα₁c t y

theorem fiInitLayerHom_one_tmul (z : Cyc (lastBlock c)) (x : SL) :
    fiInitLayerHom Q Λ i κ h0 hr hκ M C ρ hα₁c
        ((1 ⊗ₜ z : Tfam (initWeight c) ⊗[k] Cyc (lastBlock c)) • x) =
      (1 ⊗ₜ z : Tfam (initWeight c) ⊗[k] Cyc (lastBlock c)) •
        fiInitLayerHom Q Λ i κ h0 hr hκ M C ρ hα₁c x := by
  obtain ⟨y, rfl⟩ := (fiSplitLeftUnwrap Q Λ i κ h0 hr hκ M C ρ hα₁c).symm.surjective x
  exact fiInitLayerHom_one_tmul_of Q Λ i κ h0 hr hκ M C ρ hα₁c z y

/-- **The layer of the induction hypothesis as the input `X_{ₖFᵢ M}`**, over the factor
algebra. -/
def fiInitLayerEquiv :
    SL ≃ₗ[parabolicFactorAlgebra Q Λ (initWeight c) (lastBlock c)] Xc :=
  LinearEquiv.ofBijective
    (tensorLinearOfGenerators (A := Tfam (initWeight c)) (C := Cyc (lastBlock c))
      (fiInitLayerHom Q Λ i κ h0 hr hκ M C ρ hα₁c)
      (fiInitLayerHom_tmul_one Q Λ i κ h0 hr hκ M C ρ hα₁c)
      (fiInitLayerHom_one_tmul Q Λ i κ h0 hr hκ M C ρ hα₁c))
    ((ofX).bijective.comp ((e₀).bijective.comp
      (fiSplitLeftUnwrap Q Λ i κ h0 hr hκ M C ρ hα₁c).bijective))

theorem fiInitLayerEquiv_apply (z : SL) :
    fiInitLayerEquiv Q Λ i κ h0 hr hκ M C ρ hα₁c z =
      fiInitLayerHom Q Λ i κ h0 hr hκ M C ρ hα₁c z := rfl

theorem fiInitLayerHom_action_of (x : C) (y : X₁) :
    fiInitLayerHom Q Λ i κ h0 hr hκ M C ρ hα₁c (ofL (ρL (1 ⊗ₜ x) y)) =
      twoPieceEnd Q Λ c hα₁c (blockBlackIndEnd Q Λ i κ.castSucc h0 hr hκ M (ρ x))
        (fiInitLayerHom Q Λ i κ h0 hr hκ M C ρ hα₁c (ofL y)) := by
  change ofX (e₀ (mR (IndK.map (ρ₁ (1 ⊗ₜ x))) y)) =
    twoPieceEnd Q Λ c hα₁c (blockBlackIndEnd Q Λ i κ.castSucc h0 hr hκ M (ρ x)) (ofX (e₀ y))
  rw [twoPieceEnd_of, inductionAction_one_tmul Q Λ b M (β' := lastBlock c) hβ C ρ]
  exact congrArg (ofX) (e₀_mapRight_initRestrictEndF Q Λ i κ h0 hr hκ M hα₁c (ρ x) y)

/-- **`fiInitLayerEquiv` intertwines the actions of `C`.** -/
theorem fiInitLayerEquiv_action (x : C) (z : SL) :
    fiInitLayerEquiv Q Λ i κ h0 hr hκ M C ρ hα₁c (SplitLeft.action L₁ x z) =
      twoPieceEnd Q Λ c hα₁c (blockBlackIndEnd Q Λ i κ.castSucc h0 hr hκ M (ρ x))
        (fiInitLayerEquiv Q Λ i κ h0 hr hκ M C ρ hα₁c z) := by
  refine SplitLeft.TensorAct.map_action_of_of ρL
    (fiInitLayerEquiv Q Λ i κ h0 hr hκ M C ρ hα₁c) _ x (fun y => ?_) z
  exact fiInitLayerHom_action_of Q Λ i κ h0 hr hκ M C ρ hα₁c x y

/-- **The standardized layer as `ₖFᵢ M ⊗_B S^L_{α_c}`** over `T(θ_c + β_c) ⊗ C`, with
`θ_c + β_c` the weight of the blocks `c` split off the last one. -/
def fiInitLayerStandardCore
    (hαc : RootNonViolated (ν := initWeight c + lastBlock c) (blockRoot c)) :
    splitStandard Q Λ hQ (initWeight c) (lastBlock c) C (ModuleCat.of _ L₁) ≃ₗ[
      TensorProductAlgebra k Q Λ (initWeight c + lastBlock c) ⊗[k] C]
      TensorAct k (TensorProductAlgebra k Q Λ (initWeight c + lastBlock c)) C
        (BalancedTensor.endAction k (TensorProductAlgebra k Q Λ (initWeight c + lastBlock c))
          (BlockLeftStandard Q Λ c (blockPrefix_last c) hαc)
          ((blockBlackIndEnd Q Λ i κ.castSucc h0 hr hκ M).comp ρ)) :=
  (standardActEquiv Q Λ hQ (ρ' := (twoPieceEndAlg Q Λ c hα₁c).comp
      ((blockBlackIndEnd Q Λ i κ.castSucc h0 hr hκ M).comp ρ))
    (fiInitLayerEquiv Q Λ i κ h0 hr hκ M C ρ hα₁c)
    (fun x z => fiInitLayerEquiv_action Q Λ i κ h0 hr hκ M C ρ hα₁c x z)).trans
    (TensorAct.equiv (C := C) (splitStandardEquiv Q Λ hQ c hα₁c hαc Mf)
      (ρ := BalancedTensor.endAction k (TensorProductAlgebra k Q Λ (initWeight c + lastBlock c))
          (BlockLeftStandard Q Λ c (blockPrefix_last c) hαc)
          ((blockBlackIndEnd Q Λ i κ.castSucc h0 hr hκ M).comp ρ))
      (ρ' := standardActionT Q Λ hQ C ((twoPieceEndAlg Q Λ c hα₁c).comp
        ((blockBlackIndEnd Q Λ i κ.castSucc h0 hr hκ M).comp ρ)))
      (fun _ y => splitStandardEquiv_mapRight Q Λ hQ c hα₁c hαc (M := Mf) _ y)).symm

end Core

section Restrict

variable {ν : Multiset I}
  (hcast : (Singleton.singleton i : Multiset I) + ν = initWeight c + lastBlock c)
  (hb' : blockPrefix c (ℓ + 1 + 1) = (Singleton.singleton i : Multiset I) + ν)
  (hα' : RootNonViolated (ν := (Singleton.singleton i : Multiset I) + ν) (blockRoot c))
  (hαc : RootNonViolated (ν := initWeight c + lastBlock c) (blockRoot c))

/-- **`ₖFᵢ M ⊗_B S^L_{α_c}` over `T(i + ν) ⊗ C`** is the restriction of the same module over
`T(θ_c + β_c) ⊗ C` along an identification of weights. -/
def fiLayerRestrictEquiv :
    (ModuleCat.restrictScalars (TensorAct.firstFactorHom (C := C)
        (castTensorProductAlgebra Q Λ hcast))).obj
      (ModuleCat.of (TensorProductAlgebra k Q Λ (initWeight c + lastBlock c) ⊗[k] C)
        (TensorAct k (TensorProductAlgebra k Q Λ (initWeight c + lastBlock c)) C
          (BalancedTensor.endAction k (TensorProductAlgebra k Q Λ (initWeight c + lastBlock c))
            (BlockLeftStandard Q Λ c (blockPrefix_last c) hαc)
            ((blockBlackIndEnd Q Λ i κ.castSucc h0 hr hκ M).comp ρ)))) ≃ₗ[
        TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν) ⊗[k] C]
      fiLayer Q i Λ ν κ.castSucc h0 hr hκ hb' hα' C M ρ :=
  (TensorAct.restrictEquiv (castTensorProductAlgebra Q Λ hcast)
    (ρ := BalancedTensor.endAction k (TensorProductAlgebra k Q Λ (initWeight c + lastBlock c))
      (BlockLeftStandard Q Λ c (blockPrefix_last c) hαc)
      ((blockBlackIndEnd Q Λ i κ.castSucc h0 hr hκ M).comp ρ))
    (ρ' := BalancedTensor.endAction k
      (TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν))
      (BlockLeftStandard Q Λ c hb' hα') ((blockBlackIndEnd Q Λ i κ.castSucc h0 hr hκ M).comp ρ))
    ((leftStandardizationFamilyCast (Q := Q) (Λ := Λ) Mf hcast.symm (blockPrefix_last c) hb'
      hαc hα').toAddEquiv : LeftStandardization Q Λ c hb' hα' Mf ≃+
        LeftStandardization Q Λ c (blockPrefix_last c) hαc Mf)
    (fun a v => (map_smul (leftStandardizationFamilyCast (Q := Q) (Λ := Λ) Mf hcast.symm
      (blockPrefix_last c) hb' hαc hα') a v).trans
        (familyCast_tensorProductAlgebra_smul hcast.symm
          (P := LeftStandardization Q Λ c (blockPrefix_last c) hαc Mf) a _))
    (fun x v => leftStandardizationFamilyCast_mapRight hcast.symm (blockPrefix_last c) hb' hαc
      hα' ((blockBlackIndEnd Q Λ i κ.castSucc h0 hr hκ M) (ρ x)) v)).symm

end Restrict

section Standard

variable {θ' β' : Multiset I} (hθc : initWeight c = θ') (hβc : lastBlock c = β')
  (hβ' : lastBlock b = β') (hb'₁ : blockPrefix (initBlocks c) (ℓ + 1) = θ')
  (hα'₁ : RootNonViolated (ν := θ') (blockRoot (initBlocks c))) {ν : Multiset I}
  (hcast : (Singleton.singleton i : Multiset I) + ν = θ' + β')
  (hb' : blockPrefix c (ℓ + 1 + 1) = (Singleton.singleton i : Multiset I) + ν)
  (hα' : RootNonViolated (ν := (Singleton.singleton i : Multiset I) + ν) (blockRoot c))

/-- The layer `ₖFᵢ(M|_{B'}) ⊗_{B'} S^L_{α'}` of the induction hypothesis, over
`T^{λ'}(θ') ⊗ (R^{λ_ℓ}(β') ⊗ C)`. -/
local notation "Lθ" => TensorAct k (Tfam θ') ((Cyc β') ⊗[k] C)
  (BalancedTensor.endAction k (Tfam θ')
    (BlockLeftStandard Q (Λ ∘ Fin.castSucc) (initBlocks c) hb'₁ hα'₁)
    (AlgHom.comp (blockBlackIndEnd Q (Λ ∘ Fin.castSucc) i κ (b := initBlocks c)
      (b' := initBlocks b) h0 (initBlocks_rightBlock_of_ne κ hr) hκ (InitRestrict Q Λ b M))
      (inductionAction Q Λ b M (β' := β') hβ' C ρ)))

/-- **The standardized layer of the induction hypothesis is the layer `ₖFᵢ M ⊗_B S^L_{α_c}`
for `ℓ + 1` red strands**, over `T(i + ν) ⊗ C` through an identification of weights
`i + ν = θ' + β'`. -/
def fiInitLayerStandardEquiv :
    (ModuleCat.restrictScalars (TensorAct.firstFactorHom (C := C)
        (castTensorProductAlgebra Q Λ hcast))).obj
      (splitStandard Q Λ hQ θ' β' C (ModuleCat.of _ Lθ)) ≃ₗ[
        TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν) ⊗[k] C]
      fiLayer Q i Λ ν κ.castSucc h0 hr hκ hb' hα' C M ρ := by
  subst hθc hβc
  have hαc : RootNonViolated (ν := initWeight c + lastBlock c) (blockRoot c) := hcast ▸ hα'
  exact ((ModuleCat.restrictScalars _).mapIso
    (fiInitLayerStandardCore Q Λ hQ i κ h0 hr hκ M C ρ hα'₁ hαc).toModuleIso).toLinearEquiv.trans
    (fiLayerRestrictEquiv Q Λ i κ h0 hr hκ M C ρ hcast hb' hα' hαc)

end Standard

end StendhalAlgebra

end Categorification.Stendhal
