/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.EiInductionAction
import Categorification.WeightedKLR.RedStrands.EiCasts
import Categorification.Algebra.TensorActSplit

/-!
# `₁Eᵢ` of the two-piece input is the module of the induction hypothesis

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5. For a right module `M` over the block algebra of `ℓ + 1` red strands, with
`θ = i + θ₀` the weight of the first `ℓ` red strands, restricting the input
`X_M = M ⊗_{B'} S^L_{α'}` of the two-piece standardization along the last black strand of the
first factor gives `Eᵢ(M|_{B'} ⊗_{B'} S^L_{α'})`, the module to which the induction hypothesis
applies, with the last cyclotomic factor acting through `M` (`leftInputEquiv`). The isomorphism
is natural in endomorphisms of `M` (`leftInputEquiv_natural`).
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
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I)
  (b : Fin (ℓ + 2) → Multiset I)
  (M : Type) [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  {θ₀ β' : Multiset I} (hθ : initWeight b = ({i} : Multiset I) + θ₀) (hβ : lastBlock b = β')
  (hα₁ : RootNonViolated (ν := initWeight b) (blockRoot (initBlocks b)))

local notation "Cyc" β =>
  CycKLR k Q (fun i : I => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i) β
local notation "cc" h => CyclotomicAction.castCyc Q
  (fun i : I => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i) h
local notation "XL" => LeftStandardization Q (Λ ∘ Fin.castSucc) (initBlocks b) rfl hα₁
  (InitRestrict Q Λ b M)
local notation "X" => TwoPieceInput Q Λ b M hα₁
local notation "X₂" => FactorCast Q Λ (rfl : initWeight b = initWeight b) hβ X
local notation "N" => FactorCast Q Λ hθ (rfl : β' = β') X₂
local notation "ofX" => twoPieceInputOf Q Λ b M hα₁
local notation "Tfam" => TensorProductAlgebra k Q (Λ ∘ Fin.castSucc)
local notation "mR" => BalancedTensor.mapRight (k := k) (B := Tfam (initWeight b))
  (M := BlockLeftStandard Q (Λ ∘ Fin.castSucc) (initBlocks b) rfl hα₁)

/-- The factor algebra acting on the input transported along `θ = i + θ₀` and `β = β'`. -/
theorem factorCast_input_tmul_smul (t : Tfam (({i} : Multiset I) + θ₀)) (c : Cyc β') (x : XL) :
    ((t ⊗ₜ c : parabolicFactorAlgebra Q Λ (({i} : Multiset I) + θ₀) β') •
        (show N from (show X₂ from ofX x)) : N) =
      (show N from (show X₂ from ofX (castTensorProductAlgebra Q (Λ ∘ Fin.castSucc) hθ.symm t •
        mR (lastFactorEnd Q Λ b ((cc hβ.symm) c)) x))) := by
  rw [factorCast_smul Q Λ hθ rfl X₂, castFactor_symm_tmul Q Λ hθ rfl t c]
  change (show N from (show X₂ from (castFactor Q Λ rfl hβ).symm
    (castTensorProductAlgebra Q (Λ ∘ Fin.castSucc) hθ.symm t ⊗ₜ (cc rfl) c) • ofX x)) = _
  rw [castFactor_symm_tmul Q Λ rfl hβ, twoPieceInput_smul_def, twoPieceInputAction_tmul]
  rfl

theorem leftAppendHom_tmul (t : Tfam θ₀) (c : Cyc β') :
    leftAppendHom Q Λ i θ₀ β' (t ⊗ₜ c) = appendBlack Q (Λ ∘ Fin.castSucc) i θ₀ t ⊗ₜ c := rfl

variable (hα₁' : RootNonViolated (ν := ({i} : Multiset I) + θ₀) (blockRoot (initBlocks b)))
  (C : Type) [Ring C] [Algebra k C] (ρ : C →ₐ[k] Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M)

local notation "XLθ" => LeftStandardization Q (Λ ∘ Fin.castSucc) (initBlocks b) hθ hα₁'
  (InitRestrict Q Λ b M)
local notation "e₀" => leftStandardizationFamilyCast (Q := Q) (Λ := Λ ∘ Fin.castSucc)
  (InitRestrict Q Λ b M) hθ rfl hθ hα₁ hα₁'
local notation "ρ₁" => inductionAction Q Λ b M hβ C ρ
local notation "Y₁" => eiTop Q i (Λ ∘ Fin.castSucc) (initBlocks b) θ₀ hθ hα₁' ((Cyc β') ⊗[k] C)
  (InitRestrict Q Λ b M) ρ₁
local notation "SY" => SplitLeft k (Tfam θ₀) (Cyc β') C Y₁
local notation "El" => LeftResLeft Q Λ i θ₀ β' N
local notation "Bθ" => BlackRes (Q := Q) (Λ := Λ ∘ Fin.castSucc) i θ₀ XLθ

/-- The input as an element of the transported module. -/
def inputOfN : XL ≃+ N := AddEquiv.refl _

/-- The input as an element of the module over `T(i + θ₀)`. -/
def inputOfFC : XL ≃+ FamilyCast Tfam hθ XL := AddEquiv.refl _

theorem leftAppend_smul_inputOfN (t : Tfam θ₀) (c : Cyc β') (x : XL) :
    leftAppendHom Q Λ i θ₀ β' (t ⊗ₜ c) • inputOfN Q Λ i b M hθ hβ hα₁ x =
      inputOfN Q Λ i b M hθ hβ hα₁ (castTensorProductAlgebra Q (Λ ∘ Fin.castSucc) hθ.symm
        (appendBlack Q (Λ ∘ Fin.castSucc) i θ₀ t) • mR (lastFactorEnd Q Λ b ((cc hβ.symm) c)) x) :=
  factorCast_input_tmul_smul Q Λ i b M hθ hβ hα₁ _ c x

theorem smul_inputOfFC (t : Tfam (({i} : Multiset I) + θ₀)) (x : XL) :
    t • inputOfFC Q Λ i b M hθ hα₁ x =
      inputOfFC Q Λ i b M hθ hα₁ (castTensorProductAlgebra Q (Λ ∘ Fin.castSucc) hθ.symm t • x) :=
  familyCast_tensorProductAlgebra_smul hθ t x

theorem mR_lastFactorEnd_one (x : XL) : mR (lastFactorEnd Q Λ b ((cc hβ.symm) 1)) x = x := by
  rw [map_one, lastFactorEnd_one, BalancedTensor.mapRight_id, LinearMap.id_apply]

theorem leftAppend_one_smul_inputOfN (t : Tfam θ₀) (x : XL) :
    leftAppendHom Q Λ i θ₀ β' (t ⊗ₜ 1) • inputOfN Q Λ i b M hθ hβ hα₁ x =
      inputOfN Q Λ i b M hθ hβ hα₁ (castTensorProductAlgebra Q (Λ ∘ Fin.castSucc) hθ.symm
        (appendBlack Q (Λ ∘ Fin.castSucc) i θ₀ t) • x) :=
  (leftAppend_smul_inputOfN Q Λ i b M hθ hβ hα₁ t 1 x).trans (congrArg _ (congrArg _
    (mR_lastFactorEnd_one Q Λ b M hβ hα₁ x)))

theorem castAppendBlack_smul_of_mem (x : El) :
    castTensorProductAlgebra Q (Λ ∘ Fin.castSucc) hθ.symm
        (appendBlack Q (Λ ∘ Fin.castSucc) i θ₀ 1) • (inputOfN Q Λ i b M hθ hβ hα₁).symm x.val =
      (inputOfN Q Λ i b M hθ hβ hα₁).symm x.val := by
  have hx := x.prop
  have h1 : leftAppendHom Q Λ i θ₀ β' 1 = leftAppendHom Q Λ i θ₀ β' (1 ⊗ₜ 1) := rfl
  rw [← (inputOfN Q Λ i b M hθ hβ hα₁).apply_symm_apply x.val, h1,
    leftAppend_one_smul_inputOfN] at hx
  exact (inputOfN Q Λ i b M hθ hβ hα₁).injective hx

/-- The underlying map of `₁Eᵢ X_M ≅ Eᵢ(M|_{B'} ⊗ S^L_{α'})`. -/
def leftInputFun (x : El) : Bθ :=
  ⟨(e₀).symm (inputOfFC Q Λ i b M hθ hα₁ ((inputOfN Q Λ i b M hθ hβ hα₁).symm x.val)), by
    rw [mem_fixSub, ← map_smul, smul_inputOfFC, castAppendBlack_smul_of_mem]⟩

theorem leftInputFun_val (x : El) : (leftInputFun Q Λ i b M hθ hβ hα₁ hα₁' x).1 =
    (e₀).symm (inputOfFC Q Λ i b M hθ hα₁ ((inputOfN Q Λ i b M hθ hβ hα₁).symm x.val)) := rfl

theorem leftInputFun_add (x y : El) : leftInputFun Q Λ i b M hθ hβ hα₁ hα₁' (x + y) =
    leftInputFun Q Λ i b M hθ hβ hα₁ hα₁' x + leftInputFun Q Λ i b M hθ hβ hα₁ hα₁' y := by
  apply Subtype.ext
  rw [leftInputFun_val, Submodule.coe_add, leftInputFun_val, leftInputFun_val, Res.val_add,
    map_add, map_add, map_add]

theorem leftInputFun_tmul_one (t : Tfam θ₀) (x : El) :
    leftInputFun Q Λ i b M hθ hβ hα₁ hα₁' ((t ⊗ₜ 1 : parabolicFactorAlgebra Q Λ θ₀ β') • x) =
      t • leftInputFun Q Λ i b M hθ hβ hα₁ hα₁' x := by
  apply Subtype.ext
  obtain ⟨v, hv⟩ := (inputOfN Q Λ i b M hθ hβ hα₁).surjective x.val
  change (e₀).symm (inputOfFC Q Λ i b M hθ hα₁ ((inputOfN Q Λ i b M hθ hβ hα₁).symm
      (leftAppendHom Q Λ i θ₀ β' (t ⊗ₜ 1) • x.val))) =
    appendBlack Q (Λ ∘ Fin.castSucc) i θ₀ t •
      (e₀).symm (inputOfFC Q Λ i b M hθ hα₁ ((inputOfN Q Λ i b M hθ hβ hα₁).symm x.val))
  rw [← hv, leftAppend_one_smul_inputOfN, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply,
    ← smul_inputOfFC, map_smul]

local notation "mRθ" => BalancedTensor.mapRight (k := k)
  (B := Tfam ((Singleton.singleton i : Multiset I) + θ₀))
  (M := BlockLeftStandard Q (Λ ∘ Fin.castSucc) (initBlocks b) hθ hα₁')

theorem e₀_symm_inputOfFC_mapRight
    (g : Module.End (BlockAlgebra k Q (Λ ∘ Fin.castSucc) (initBlocks b))ᵐᵒᵖ
      (InitRestrict Q Λ b M)) (v : XL) :
    (e₀).symm (inputOfFC Q Λ i b M hθ hα₁ (mR g v)) =
      mRθ g ((e₀).symm (inputOfFC Q Λ i b M hθ hα₁ v)) :=
  leftStandardizationFamilyCast_symm_mapRight hθ rfl hθ hα₁ hα₁' g v

theorem leftInputFun_one_tmul (c : Cyc β') (x : El) :
    leftInputFun Q Λ i b M hθ hβ hα₁ hα₁' ((1 ⊗ₜ c : parabolicFactorAlgebra Q Λ θ₀ β') • x) =
      eiTopAction Q i (Λ ∘ Fin.castSucc) (initBlocks b) θ₀ hθ hα₁' ((Cyc β') ⊗[k] C)
        (InitRestrict Q Λ b M) ρ₁ (c ⊗ₜ 1) (leftInputFun Q Λ i b M hθ hβ hα₁ hα₁' x) := by
  apply Subtype.ext
  have hfix := (leftInputFun Q Λ i b M hθ hβ hα₁ hα₁' x).2
  rw [mem_fixSub, leftInputFun_val] at hfix
  obtain ⟨v, hv⟩ := (inputOfN Q Λ i b M hθ hβ hα₁).surjective x.val
  rw [eiTopAction_val, leftInputFun_val]
  change (e₀).symm (inputOfFC Q Λ i b M hθ hα₁ ((inputOfN Q Λ i b M hθ hβ hα₁).symm
      (leftAppendHom Q Λ i θ₀ β' (1 ⊗ₜ c) • x.val))) = mRθ (ρ₁ (c ⊗ₜ 1)) _
  rw [← hv] at hfix ⊢
  rw [leftAppend_smul_inputOfN, AddEquiv.symm_apply_apply, ← smul_inputOfFC, map_smul,
    e₀_symm_inputOfFC_mapRight, inductionAction_tmul_one]
  rw [leftInputFun_val, ← hv, AddEquiv.symm_apply_apply, ← LinearMap.map_smul]
  exact congrArg _ hfix

/-- The action of `C` on the transported input `N`. -/
abbrev inputAction (x : C) :
    Module.End (parabolicFactorAlgebra Q Λ (({i} : Multiset I) + θ₀) β') N :=
  factorCastMap Q Λ hθ rfl (factorCastMap Q Λ rfl hβ (twoPieceEnd Q Λ b hα₁ (ρ x)))

theorem leftInputFun_natural (x : C) (z : El) :
    leftInputFun Q Λ i b M hθ hβ hα₁ hα₁'
        (Res.map (inputAction Q Λ i b M hθ hβ hα₁ C ρ x) z) =
      eiTopAction Q i (Λ ∘ Fin.castSucc) (initBlocks b) θ₀ hθ hα₁' ((Cyc β') ⊗[k] C)
        (InitRestrict Q Λ b M) ρ₁ (1 ⊗ₜ x) (leftInputFun Q Λ i b M hθ hβ hα₁ hα₁' z) := by
  apply Subtype.ext
  obtain ⟨v, hv⟩ := (inputOfN Q Λ i b M hθ hβ hα₁).surjective z.val
  rw [eiTopAction_val, leftInputFun_val, leftInputFun_val]
  change (e₀).symm (inputOfFC Q Λ i b M hθ hα₁ ((inputOfN Q Λ i b M hθ hβ hα₁).symm
    (inputAction Q Λ i b M hθ hβ hα₁ C ρ x z.val))) = mRθ (ρ₁ (1 ⊗ₜ x)) _
  rw [← hv]
  change (e₀).symm (inputOfFC Q Λ i b M hθ hα₁ ((inputOfN Q Λ i b M hθ hβ hα₁).symm
    (inputOfN Q Λ i b M hθ hβ hα₁ (mR (initRestrictEnd Q Λ b (ρ x)) v)))) = _
  rw [AddEquiv.symm_apply_apply, e₀_symm_inputOfFC_mapRight, inductionAction_one_tmul,
    AddEquiv.symm_apply_apply]

theorem leftInputFun_injective : Function.Injective (leftInputFun Q Λ i b M hθ hβ hα₁ hα₁') := by
  intro x y h
  have h' := congrArg Subtype.val h
  rw [leftInputFun_val, leftInputFun_val] at h'
  exact Res.ext ((inputOfN Q Λ i b M hθ hβ hα₁).symm.injective
    ((inputOfFC Q Λ i b M hθ hα₁).injective ((e₀).symm.injective h')))

theorem leftInputFun_surjective :
    Function.Surjective (leftInputFun Q Λ i b M hθ hβ hα₁ hα₁') := by
  intro w
  have hw := w.2
  rw [mem_fixSub] at hw
  obtain ⟨v, hv⟩ := (inputOfFC Q Λ i b M hθ hα₁).surjective (e₀ w.1)
  have hv' : castTensorProductAlgebra Q (Λ ∘ Fin.castSucc) hθ.symm
      (appendBlack Q (Λ ∘ Fin.castSucc) i θ₀ 1) • v = v := by
    apply (inputOfFC Q Λ i b M hθ hα₁).injective
    rw [← smul_inputOfFC, hv, ← map_smul, hw]
  refine ⟨Res.mk (inputOfN Q Λ i b M hθ hβ hα₁ v) ?_, Subtype.ext ?_⟩
  · have h1 : leftAppendHom Q Λ i θ₀ β' 1 = leftAppendHom Q Λ i θ₀ β' (1 ⊗ₜ 1) := rfl
    rw [h1, leftAppend_one_smul_inputOfN, hv']
  · rw [leftInputFun_val, Res.val_mk, AddEquiv.symm_apply_apply, hv, LinearEquiv.symm_apply_apply]

/-- The underlying additive map of `₁Eᵢ X_M ≅ Eᵢ(M|_{B'} ⊗ S^L_{α'})`. -/
def leftInputHom : El →+ SY :=
  ((SplitLeft.of (k := k) (A₁ := Tfam θ₀) (A₂ := Cyc β') (C := C) (Y := Y₁)).toAddMonoidHom.comp
    (TensorAct.of (k := k) (A := Tfam θ₀) (C := (Cyc β') ⊗[k] C)
      (ρ := eiTopAction Q i (Λ ∘ Fin.castSucc) (initBlocks b) θ₀ hθ hα₁' ((Cyc β') ⊗[k] C)
        (InitRestrict Q Λ b M) ρ₁)).toAddMonoidHom).comp
    (AddMonoidHom.mk' (leftInputFun Q Λ i b M hθ hβ hα₁ hα₁')
      (leftInputFun_add Q Λ i b M hθ hβ hα₁ hα₁'))

theorem leftInputHom_apply (x : El) :
    leftInputHom Q Λ i b M hθ hβ hα₁ hα₁' C ρ x =
      SplitLeft.of (TensorAct.of (leftInputFun Q Λ i b M hθ hβ hα₁ hα₁' x)) := rfl

local notation "ρtop" => eiTopAction Q i (Λ ∘ Fin.castSucc) (initBlocks b) θ₀ hθ hα₁'
  ((Cyc β') ⊗[k] C) (InitRestrict Q Λ b M) ρ₁

theorem leftInputHom_tmul_one (t : Tfam θ₀) (x : El) :
    leftInputHom Q Λ i b M hθ hβ hα₁ hα₁' C ρ
        ((t ⊗ₜ 1 : parabolicFactorAlgebra Q Λ θ₀ β') • x) =
      (t ⊗ₜ 1 : parabolicFactorAlgebra Q Λ θ₀ β') •
        leftInputHom Q Λ i b M hθ hβ hα₁ hα₁' C ρ x :=
  (congrArg (fun u => SplitLeft.of (k := k) (A₁ := Tfam θ₀) (A₂ := Cyc β') (C := C)
      (TensorAct.of (ρ := ρtop) u)) (leftInputFun_tmul_one Q Λ i b M hθ hβ hα₁ hα₁' t x)).trans
    (SplitLeft.tmul_one_smul_of_of (C := C) ρtop t _).symm

theorem leftInputHom_one_tmul (c : Cyc β') (x : El) :
    leftInputHom Q Λ i b M hθ hβ hα₁ hα₁' C ρ
        ((1 ⊗ₜ c : parabolicFactorAlgebra Q Λ θ₀ β') • x) =
      (1 ⊗ₜ c : parabolicFactorAlgebra Q Λ θ₀ β') •
        leftInputHom Q Λ i b M hθ hβ hα₁ hα₁' C ρ x :=
  (congrArg (fun u => SplitLeft.of (k := k) (A₁ := Tfam θ₀) (A₂ := Cyc β') (C := C)
      (TensorAct.of (ρ := ρtop) u)) (leftInputFun_one_tmul Q Λ i b M hθ hβ hα₁ hα₁' C ρ c x)).trans
    (SplitLeft.one_tmul_smul_of_of (C := C) ρtop c _).symm

/-- **`₁Eᵢ X_M ≅ Eᵢ(M|_{B'} ⊗ S^L_{α'})` as modules over `T^{λ'}(θ₀) ⊗ R(β')`.** -/
def leftInputEquiv : El ≃ₗ[parabolicFactorAlgebra Q Λ θ₀ β'] SY :=
  LinearEquiv.ofBijective
    (tensorLinearOfGenerators (A := Tfam θ₀) (C := Cyc β')
      (leftInputHom Q Λ i b M hθ hβ hα₁ hα₁' C ρ)
      (leftInputHom_tmul_one Q Λ i b M hθ hβ hα₁ hα₁' C ρ)
      (leftInputHom_one_tmul Q Λ i b M hθ hβ hα₁ hα₁' C ρ))
    ⟨fun x y h => leftInputFun_injective Q Λ i b M hθ hβ hα₁ hα₁'
        ((TensorAct.of (ρ := ρtop)).injective (SplitLeft.of.injective h)),
      fun w => by
        obtain ⟨x, hx⟩ := leftInputFun_surjective Q Λ i b M hθ hβ hα₁ hα₁'
          ((TensorAct.of (ρ := ρtop)).symm (SplitLeft.of.symm w))
        refine ⟨x, ?_⟩
        rw [tensorLinearOfGenerators_apply, leftInputHom_apply Q Λ i b M hθ hβ hα₁ hα₁' C ρ, hx,
          LinearEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]⟩

theorem leftInputEquiv_apply (x : El) :
    leftInputEquiv Q Λ i b M hθ hβ hα₁ hα₁' C ρ x =
      SplitLeft.of (TensorAct.of (leftInputFun Q Λ i b M hθ hβ hα₁ hα₁' x)) := rfl

/-- The identification intertwines the actions of `C`. -/
theorem leftInputEquiv_natural (x : C) (z : El) :
    leftInputEquiv Q Λ i b M hθ hβ hα₁ hα₁' C ρ
        (Res.map (inputAction Q Λ i b M hθ hβ hα₁ C ρ x) z) =
      SplitLeft.action Y₁ x (leftInputEquiv Q Λ i b M hθ hβ hα₁ hα₁' C ρ z) :=
  (congrArg (fun u => SplitLeft.of (k := k) (A₁ := Tfam θ₀) (A₂ := Cyc β') (C := C)
      (TensorAct.of (ρ := ρtop) u)) (leftInputFun_natural Q Λ i b M hθ hβ hα₁ hα₁' C ρ x z)).trans
    (SplitLeft.action_of_of (A₂ := Cyc β') ρtop x _).symm

end StendhalAlgebra
