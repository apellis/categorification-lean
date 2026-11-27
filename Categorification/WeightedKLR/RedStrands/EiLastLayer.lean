/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.EiCaseBoth
import Categorification.WeightedKLR.RedStrands.TwoPieceLastBlackRes

/-!
# Naturality of `₂Eᵢ X_M ≅ X_{M e}`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5. The isomorphism `lastBlackInputEquiv` between the restriction of the two-piece
input `X_M` along the last black strand of the last factor and the input `X_{M e}` of
`ₗEᵢ M = M e` is natural in endomorphisms of `M` (`lastBlackInputEquiv_natural`).
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra MulOpposite InductionAlong
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

namespace StendhalAlgebra

section FactorCastCongr

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ)
  {θ θ' β β' : Multiset I} (hθ : θ = θ') (hβ : β = β')
  {N N' : Type} [AddCommGroup N] [Module k N] [Module (parabolicFactorAlgebra Q Λ θ β) N]
  [AddCommGroup N'] [Module k N'] [Module (parabolicFactorAlgebra Q Λ θ β) N']

/-- An isomorphism of `D(θ, β)`-modules as an isomorphism of the transported modules. -/
def factorCastCongr (e : N ≃ₗ[parabolicFactorAlgebra Q Λ θ β] N') :
    FactorCast Q Λ hθ hβ N ≃ₗ[parabolicFactorAlgebra Q Λ θ' β'] FactorCast Q Λ hθ hβ N' :=
  { factorCastMap Q Λ hθ hβ e.toLinearMap with
    invFun := factorCastMap Q Λ hθ hβ e.symm.toLinearMap
    left_inv := fun x => e.symm_apply_apply (show N from x)
    right_inv := fun x => e.apply_symm_apply (show N' from x) }

end FactorCastCongr

section CastAct

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (hQ : KLRSymm Q)
  (C : Type) [Ring C] [Algebra k C]

local notation "Tfam" => TensorProductAlgebra k Q Λ

section Family

variable {θ β ν : Multiset I} (h : θ + β = ν)
  {N N' : Type} [AddCommGroup N] [Module k N] [Module (parabolicFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N]
  [AddCommGroup N'] [Module k N'] [Module (parabolicFactorAlgebra Q Λ θ β) N']
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N']

/-- The transported standardization of an isomorphism. -/
def familyStandardEquiv (e : N ≃ₗ[parabolicFactorAlgebra Q Λ θ β] N') :
    FamilyCast Tfam h (ParabolicStandardT Q Λ θ β N hQ) ≃ₗ[Tfam ν]
      FamilyCast Tfam h (ParabolicStandardT Q Λ θ β N' hQ) :=
  { FamilyCast.map Tfam h (parabolicStandardEquiv Λ hQ e).toLinearMap with
    invFun := FamilyCast.map Tfam h (parabolicStandardEquiv Λ hQ e).symm.toLinearMap
    left_inv := fun x => (parabolicStandardEquiv Λ hQ e).symm_apply_apply
      (show ParabolicStandardT Q Λ θ β N hQ from x)
    right_inv := fun x => (parabolicStandardEquiv Λ hQ e).apply_symm_apply
      (show ParabolicStandardT Q Λ θ β N' hQ from x) }

variable {C}

/-- **The transported standardization of an isomorphism intertwining the actions of `C`**, as an
isomorphism of modules over `T(ν) ⊗ C`. -/
def familyStandardActEquiv {ρ : C →ₐ[k] Module.End (parabolicFactorAlgebra Q Λ θ β) N}
    {ρ' : C →ₐ[k] Module.End (parabolicFactorAlgebra Q Λ θ β) N'}
    (e : N ≃ₗ[parabolicFactorAlgebra Q Λ θ β] N') (he : ∀ c x, e (ρ c x) = ρ' c (e x)) :
    TensorAct k (Tfam ν) C ((FamilyCast.endHom Tfam h _).comp (standardActionT Q Λ hQ C ρ)) ≃ₗ[
      Tfam ν ⊗[k] C]
      TensorAct k (Tfam ν) C ((FamilyCast.endHom Tfam h _).comp (standardActionT Q Λ hQ C ρ')) :=
  TensorAct.equiv (familyStandardEquiv Q Λ hQ h e) fun c z => by
    change parabolicStandardMap Q Λ θ β e.toLinearMap (parabolicStandardMap Q Λ θ β (ρ c)
        (show ParabolicStandard Q Λ θ β N from z)) =
      parabolicStandardMap Q Λ θ β (ρ' c) (parabolicStandardMap Q Λ θ β e.toLinearMap
        (show ParabolicStandard Q Λ θ β N from z))
    rw [← LinearMap.comp_apply, ← parabolicStandardMap_comp, ← LinearMap.comp_apply,
      ← parabolicStandardMap_comp]
    exact LinearMap.congr_fun (congrArg (parabolicStandardMap Q Λ θ β)
      (LinearMap.ext fun x => he c x)) _

end Family

variable (b : Fin (ℓ + 2) → Multiset I)
  (M : Type) [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  {θ' β' : Multiset I} (hθ : initWeight b = θ') (hβ : lastBlock b = β')
  (hα₁ : RootNonViolated (ν := initWeight b) (blockRoot (initBlocks b)))
  {ν : Multiset I} (h : θ' + β' = ν) (hbν : blockPrefix b (ℓ + 2) = ν)
  (hαν : RootNonViolated (ν := ν) (blockRoot b))
  (ρ : C →ₐ[k] Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M)

/-- **`M ⊗_B S^L_α ≅ S(X_M)` over `T(ν) ⊗ C`**, with `S(X_M)` transported along
`θ' + β' = ν`. -/
def standardTwoPieceCastActEquiv :
    TensorAct k (Tfam ν) C (BalancedTensor.endAction k (Tfam ν) (BlockLeftStandard Q Λ b hbν hαν)
      ρ) ≃ₗ[Tfam ν ⊗[k] C]
      TensorAct k (Tfam ν) C ((FamilyCast.endHom Tfam h _).comp
        (standardActionT Q Λ hQ C (twoPieceCastAction Q Λ b M hθ hβ hα₁ C ρ))) :=
  TensorAct.equiv (standardTwoPieceCastEquiv Q Λ hQ b M hθ hβ hα₁ h hbν hαν) fun c y =>
    standardTwoPieceCastEquiv_mapRight Q Λ hQ b M hθ hβ hα₁ h hbν hαν (ρ c) y

end CastAct

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I)
  {b b' : Fin (ℓ + 2) → Multiset I} (h0 : leftBlock b' = leftBlock b)
  (hr : ∀ r, r ≠ Fin.last ℓ → rightBlock b' r = rightBlock b r)
  (hκ : {i} + rightBlock b' (Fin.last ℓ) = rightBlock b (Fin.last ℓ))
  (M : Type) [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  (hα' : RootNonViolated (ν := initWeight b) (blockRoot (initBlocks b)))
  (hα'' : RootNonViolated (ν := initWeight b') (blockRoot (initBlocks b')))

local notation "hinit" => initBlocks_eq_of_last h0 hr
local notation "M'" => BlockBlackRes Q Λ i (Fin.last ℓ) h0 hr hκ M
local notation "CM'" => CastBlockModule Q (Λ ∘ Fin.castSucc) hinit (InitRestrict Q Λ b' M')
local notation "hθ" => initWeight_eq_of_last h0 hr
local notation "Tfam" => TensorProductAlgebra k Q (Λ ∘ Fin.castSucc)
local notation "XL'" => LeftStandardization Q (Λ ∘ Fin.castSucc) (initBlocks b') rfl hα''
  (InitRestrict Q Λ b' M')
local notation "inc" => lastBlackInputIncl Q Λ i h0 hr hκ M hα' hα''
local notation "g'" => blockBlackResEnd Q Λ i (Fin.last ℓ) h0 hr hκ M

theorem lastBlackInputCast_mapRight_end
    (φ : Module.End (BlockAlgebra k Q (Λ ∘ Fin.castSucc) (initBlocks b'))ᵐᵒᵖ
      (InitRestrict Q Λ b' M')) (x : XL') :
    lastBlackInputCast Q Λ i h0 hr hκ M hα' hα''
        (show FamilyCast Tfam hθ XL' from
          (BalancedTensor.mapRight φ : XL' →ₗ[Tfam (initWeight b')] XL') x) =
      BalancedTensor.mapRight (castBlockModuleMap hinit φ)
        (lastBlackInputCast Q Λ i h0 hr hκ M hα' hα'' (show FamilyCast Tfam hθ XL' from x)) := by
  rw [lastBlackInputCast, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    leftStandardizationFamilyCast_symm_mapRight, leftStandardizationCast_mapRight]

theorem lastBlackIncl_comp_initRestrictEnd (g : Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M) :
    (lastBlackIncl Q Λ i h0 hr hκ M).comp
        (castBlockModuleMap hinit (initRestrictEnd Q Λ b' (g' g))) =
      (initRestrictEnd Q Λ b g).comp (lastBlackIncl Q Λ i h0 hr hκ M) :=
  LinearMap.ext fun _ => rfl

/-- **The inclusion `X_{M e} → X_M` is natural in `M`.** -/
theorem lastBlackInputIncl_initRestrictEnd (g : Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M)
    (x : XL') :
    inc (show FamilyCast Tfam hθ XL' from
        (BalancedTensor.mapRight (initRestrictEnd Q Λ b' (g' g)) :
          XL' →ₗ[Tfam (initWeight b')] XL') x) =
      BalancedTensor.mapRight (initRestrictEnd Q Λ b g) (inc (show FamilyCast Tfam hθ XL' from x))
      := by
  change lastBlackInclRight Q Λ i h0 hr hκ M hα' (lastBlackInputCast Q Λ i h0 hr hκ M hα' hα'' _) =
    BalancedTensor.mapRight (initRestrictEnd Q Λ b g)
      (lastBlackInclRight Q Λ i h0 hr hκ M hα' (lastBlackInputCast Q Λ i h0 hr hκ M hα' hα'' _))
  rw [lastBlackInputCast_mapRight_end, lastBlackInclRight, ← LinearMap.comp_apply,
    ← BalancedTensor.mapRight_comp, lastBlackIncl_comp_initRestrictEnd,
    BalancedTensor.mapRight_comp, LinearMap.comp_apply]

/-- **Naturality of `₂Eᵢ X_M ≅ X_{M e}`** in endomorphisms of `M`. -/
theorem lastBlackInputEquiv_natural (g : Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M)
    (x : FactorCast Q Λ (initWeight_eq_of_last h0 hr) (rfl : lastBlock b' = lastBlock b')
      (TwoPieceInput Q Λ b' M' hα'')) :
    lastBlackInputEquiv Q Λ i h0 hr hκ M hα' hα''
        (factorCastMap Q Λ (initWeight_eq_of_last h0 hr) rfl (twoPieceEnd Q Λ b' hα'' (g' g)) x) =
      Res.map (factorCastMap Q Λ rfl (lastBlock_eq_of_last i hκ) (twoPieceEnd Q Λ b hα' g))
        (lastBlackInputEquiv Q Λ i h0 hr hκ M hα' hα'' x) := by
  apply Res.ext
  rw [Res.val_map, lastBlackInputEquiv_val, lastBlackInputEquiv_val]
  change (twoPieceInputOf Q Λ b M hα') (inc (show FamilyCast Tfam hθ XL' from
    (BalancedTensor.mapRight (initRestrictEnd Q Λ b' (g' g)) : XL' →ₗ[Tfam (initWeight b')] XL')
      (show XL' from x))) = twoPieceEnd Q Λ b hα' g
        (twoPieceInputOf Q Λ b M hα' (inc (show FamilyCast Tfam hθ XL' from x)))
  rw [lastBlackInputIncl_initRestrictEnd, twoPieceEnd_of]

section LastInput

variable {θ' β₀ : Multiset I} (hθb : initWeight b = θ') (hθc : initWeight b' = θ')
  (hβb : lastBlock b = {i} + β₀) (hβc : lastBlock b' = β₀)

/-- **`₂Eᵢ X_M ≅ X_{M e}`** with both inputs transported to `D(θ', β₀)`. -/
def lastLayerInputEquiv :
    FactorCast Q Λ hθc (rfl : β₀ = β₀) (FactorCast Q Λ (rfl : initWeight b' = initWeight b') hβc
      (TwoPieceInput Q Λ b' M' hα'')) ≃ₗ[parabolicFactorAlgebra Q Λ θ' β₀]
      RightResRight Q Λ i θ' β₀ (FactorCast Q Λ hθb (rfl : ({i} : Multiset I) + β₀ = {i} + β₀)
        (FactorCast Q Λ (rfl : initWeight b = initWeight b) hβb (TwoPieceInput Q Λ b M hα'))) := by
  subst hθb hβc
  exact (factorCastCongr Q Λ hθc rfl (factorCastRfl Q Λ _).symm).trans
    ((lastBlackInputEquiv Q Λ i h0 hr hκ M hα' hα'').trans
      ((factorCastRfl Q Λ _).trans (rightResRightFactorCast Q Λ i (lastBlock b') rfl _).symm))

/-- **Naturality of `lastLayerInputEquiv`** in endomorphisms of `M`. -/
theorem lastLayerInputEquiv_natural (g : Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M)
    (x : FactorCast Q Λ hθc (rfl : β₀ = β₀) (FactorCast Q Λ (rfl : initWeight b' = initWeight b')
      hβc (TwoPieceInput Q Λ b' M' hα''))) :
    lastLayerInputEquiv Q Λ i h0 hr hκ M hα' hα'' hθb hθc hβb hβc
        (factorCastMap Q Λ hθc rfl (factorCastMap Q Λ rfl hβc (twoPieceEnd Q Λ b' hα'' (g' g))) x) =
      Res.map (factorCastMap Q Λ hθb rfl (factorCastMap Q Λ rfl hβb (twoPieceEnd Q Λ b hα' g)))
        (lastLayerInputEquiv Q Λ i h0 hr hκ M hα' hα'' hθb hθc hβb hβc x) := by
  subst hθb hβc
  exact lastBlackInputEquiv_natural Q Λ i h0 hr hκ M hα' hα'' g x

end LastInput

section LastLayer

variable (hQ : KLRSymm Q) (θ₀ β₀ : Multiset I) (hθb : initWeight b = {i} + θ₀)
  (hθc : initWeight b' = {i} + θ₀) (hβb : lastBlock b = {i} + β₀) (hβc : lastBlock b' = β₀)
  (hb' : blockPrefix b' (ℓ + 2) = θ₀ + (({i} : Multiset I) + β₀))
  (hαb' : RootNonViolated (ν := θ₀ + (({i} : Multiset I) + β₀)) (blockRoot b'))
  (C : Type) [Ring C] [Algebra k C] (ρ : C →ₐ[k] Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M)

/-- **The last layer**: `ₗEᵢ M ⊗ S^L_{α'} ≅ S(₂Eᵢ X_M)` over `T(θ₀ + i + β₀) ⊗ C`, the left
term of the last-strand sequence (`bothSeqTwo`). -/
def lastLayerEquiv :
    TensorAct k (TensorProductAlgebra k Q Λ (θ₀ + (({i} : Multiset I) + β₀))) C
        (BalancedTensor.endAction k (TensorProductAlgebra k Q Λ (θ₀ + (({i} : Multiset I) + β₀)))
          (BlockLeftStandard Q Λ b' hb' hαb') ((g').comp ρ)) ≃ₗ[
        TensorProductAlgebra k Q Λ (θ₀ + (({i} : Multiset I) + β₀)) ⊗[k] C]
      BothLeft Q Λ hQ i θ₀ β₀ C (twoPieceCastAction Q Λ b M hθb hβb hα' C ρ) :=
  (standardTwoPieceCastActEquiv Q Λ hQ C b' M' hθc hβc hα''
    (Eq.symm (lastBlackTwo_weight i θ₀ β₀)) hb' hαb' ((g').comp ρ)).trans
    (familyStandardActEquiv Q Λ hQ (Eq.symm (lastBlackTwo_weight i θ₀ β₀))
      (lastLayerInputEquiv Q Λ i h0 hr hκ M hα' hα'' hθb hθc hβb hβc)
      fun c x => lastLayerInputEquiv_natural Q Λ i h0 hr hκ M hα' hα'' hθb hθc hβb hβc (ρ c) x)

end LastLayer

end StendhalAlgebra

end Categorification.Stendhal
