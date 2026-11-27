/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.EiLeftInput

/-!
# The standardization of `ℓ + 1` red strands as a transported two-piece standardization

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5. For blocks `b` of `ℓ + 1` red strands whose first `ℓ` red strands have weight
`θ'` and whose last block is `β'`, the standardization `M ⊗_B S^L_α` is the standardization of the
two-piece input `X_M`, transported to `D(θ', β')` (`standardTwoPieceEquiv`), naturally in
endomorphisms of `M` (`standardTwoPieceEquiv_mapRight`). With an action of an algebra `C` on `M`
this is an isomorphism of modules over `T(θ' + β') ⊗ C` (`standardTwoPieceActEquiv`).

## Main definitions

* `standardActionT`: the action of `C` on `S N` induced by an action on `N`.
* `standardAct`: `S N` as a module over `T(θ + β) ⊗ C`.
* `standardActEquiv`: standardization of an isomorphism intertwining the actions of `C`.
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

section StandardAct

variable {θ β : Multiset I} (C : Type) [Ring C] [Algebra k C]
  {N : Type} [AddCommGroup N] [Module k N] [Module (parabolicFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N]
  {N' : Type} [AddCommGroup N'] [Module k N'] [Module (parabolicFactorAlgebra Q Λ θ β) N']
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N']

/-- The action of `C` on `S N` induced by an action on `N`. -/
abbrev standardActionT (ρ : C →ₐ[k] Module.End (parabolicFactorAlgebra Q Λ θ β) N) :
    C →ₐ[k] Module.End (TensorProductAlgebra k Q Λ (θ + β)) (ParabolicStandardT Q Λ θ β N hQ) :=
  (parabolicEndAlg Q Λ hQ).comp ρ

/-- **`S N` as a module over `T(θ + β) ⊗ C`.** -/
abbrev standardAct (ρ : C →ₐ[k] Module.End (parabolicFactorAlgebra Q Λ θ β) N) :
    ModuleCat.{0} (TensorProductAlgebra k Q Λ (θ + β) ⊗[k] C) :=
  ModuleCat.of _ (TensorAct k (TensorProductAlgebra k Q Λ (θ + β)) C
    (standardActionT Q Λ hQ C ρ))

theorem standardActionT_apply (ρ : C →ₐ[k] Module.End (parabolicFactorAlgebra Q Λ θ β) N)
    (c : C) (z : ParabolicStandardT Q Λ θ β N hQ) :
    standardActionT Q Λ hQ C ρ c z = parabolicStandardMap Q Λ θ β (ρ c) z := rfl

variable {C}

/-- **Standardization of an isomorphism intertwining the actions of `C`.** -/
def standardActEquiv {ρ : C →ₐ[k] Module.End (parabolicFactorAlgebra Q Λ θ β) N}
    {ρ' : C →ₐ[k] Module.End (parabolicFactorAlgebra Q Λ θ β) N'}
    (e : N ≃ₗ[parabolicFactorAlgebra Q Λ θ β] N') (he : ∀ c x, e (ρ c x) = ρ' c (e x)) :
    TensorAct k (TensorProductAlgebra k Q Λ (θ + β)) C (standardActionT Q Λ hQ C ρ) ≃ₗ[
      TensorProductAlgebra k Q Λ (θ + β) ⊗[k] C]
      TensorAct k (TensorProductAlgebra k Q Λ (θ + β)) C (standardActionT Q Λ hQ C ρ') :=
  TensorAct.equiv (parabolicStandardEquiv Λ hQ e) fun c z => by
    change parabolicStandardMap Q Λ θ β e.toLinearMap (parabolicStandardMap Q Λ θ β (ρ c) z) =
      parabolicStandardMap Q Λ θ β (ρ' c) (parabolicStandardMap Q Λ θ β e.toLinearMap z)
    rw [← LinearMap.comp_apply, ← parabolicStandardMap_comp, ← LinearMap.comp_apply,
      ← parabolicStandardMap_comp]
    exact LinearMap.congr_fun (congrArg (parabolicStandardMap Q Λ θ β)
      (LinearMap.ext fun x => he c x)) z

theorem standardActEquiv_of {ρ : C →ₐ[k] Module.End (parabolicFactorAlgebra Q Λ θ β) N}
    {ρ' : C →ₐ[k] Module.End (parabolicFactorAlgebra Q Λ θ β) N'}
    (e : N ≃ₗ[parabolicFactorAlgebra Q Λ θ β] N') (he : ∀ c x, e (ρ c x) = ρ' c (e x))
    (z : ParabolicStandardT Q Λ θ β N hQ) :
    standardActEquiv Q Λ hQ e he (TensorAct.of z) =
      TensorAct.of (parabolicStandardEquiv Λ hQ e z) := rfl

end StandardAct

section TwoPiece

variable (b : Fin (ℓ + 2) → Multiset I)
  (M : Type) [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  {θ' β' : Multiset I} (hθ : initWeight b = θ') (hβ : lastBlock b = β')
  (hα₁ : RootNonViolated (ν := initWeight b) (blockRoot (initBlocks b)))
  (hb : blockPrefix b (ℓ + 2) = θ' + β')
  (hα : RootNonViolated (ν := θ' + β') (blockRoot b))

local notation "X" => TwoPieceInput Q Λ b M hα₁
local notation "N" => FactorCast Q Λ hθ (rfl : β' = β')
  (FactorCast Q Λ (rfl : initWeight b = initWeight b) hβ X)
local notation "𝔹" => BlockAlgebra k Q Λ b

/-- The endomorphism of the transported two-piece input induced by one of `M`. -/
abbrev twoPieceCastEnd (g : Module.End 𝔹ᵐᵒᵖ M) : Module.End (parabolicFactorAlgebra Q Λ θ' β') N :=
  factorCastMap Q Λ hθ rfl (factorCastMap Q Λ rfl hβ (twoPieceEnd Q Λ b hα₁ g))

/-- **`M ⊗_B S^L_α ≅ S(X_M)`**, with `X_M` transported to `D(θ', β')`. -/
def standardTwoPieceEquiv :
    LeftStandardization Q Λ b hb hα M ≃ₗ[TensorProductAlgebra k Q Λ (θ' + β')]
      ParabolicStandardT Q Λ θ' β' N hQ := by
  subst hθ hβ
  exact (splitStandardEquiv Q Λ hQ b hα₁ hα M).trans (parabolicStandardEquiv Λ hQ
    ((factorCastRfl Q Λ X).trans (factorCastRfl Q Λ _)))

/-- **Naturality of `standardTwoPieceEquiv`** in endomorphisms of `M`. -/
theorem standardTwoPieceEquiv_mapRight (g : Module.End 𝔹ᵐᵒᵖ M)
    (y : LeftStandardization Q Λ b hb hα M) :
    standardTwoPieceEquiv Q Λ hQ b M hθ hβ hα₁ hb hα
        (BalancedTensor.mapRight (k := k) (B := TensorProductAlgebra k Q Λ (θ' + β'))
          (M := BlockLeftStandard Q Λ b hb hα) g y) =
      parabolicStandardMap Q Λ θ' β' (twoPieceCastEnd Q Λ b M hθ hβ hα₁ g)
        (standardTwoPieceEquiv Q Λ hQ b M hθ hβ hα₁ hb hα y) := by
  subst hθ hβ
  change parabolicStandardMap Q Λ _ _ _ (splitStandardEquiv Q Λ hQ b hα₁ hα M
    (BalancedTensor.mapRight (k := k) (B := TensorProductAlgebra k Q Λ
      (initWeight b + lastBlock b)) (M := BlockLeftStandard Q Λ b (blockPrefix_last b) hα) g y)) =
    parabolicStandardMap Q Λ _ _ _ (parabolicStandardMap Q Λ _ _ _
      (splitStandardEquiv Q Λ hQ b hα₁ hα M y))
  rw [splitStandardEquiv_mapRight, parabolicStandardMapT_apply, ← LinearMap.comp_apply,
    ← parabolicStandardMap_comp, ← LinearMap.comp_apply, ← parabolicStandardMap_comp]
  rfl

omit hb hα in
variable {ν : Multiset I} (h : θ' + β' = ν) (hbν : blockPrefix b (ℓ + 2) = ν)
  (hαν : RootNonViolated (ν := ν) (blockRoot b)) in
/-- **`M ⊗_B S^L_α ≅ S(X_M)`** over `T(ν)` for `θ' + β' = ν`, through the transport of `S(X_M)`
along `θ' + β' = ν`. -/
def standardTwoPieceCastEquiv :
    LeftStandardization Q Λ b hbν hαν M ≃ₗ[TensorProductAlgebra k Q Λ ν]
      FamilyCast (TensorProductAlgebra k Q Λ) h (ParabolicStandardT Q Λ θ' β' N hQ) := by
  subst h
  exact (standardTwoPieceEquiv Q Λ hQ b M hθ hβ hα₁ hbν hαν).trans
    (FamilyCast.rflEquiv _ _)

omit hb hα in
variable {ν : Multiset I} (h : θ' + β' = ν) (hbν : blockPrefix b (ℓ + 2) = ν)
  (hαν : RootNonViolated (ν := ν) (blockRoot b)) in
/-- **Naturality of `standardTwoPieceCastEquiv`** in endomorphisms of `M`. -/
theorem standardTwoPieceCastEquiv_mapRight (g : Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M)
    (y : LeftStandardization Q Λ b hbν hαν M) :
    (standardTwoPieceCastEquiv Q Λ hQ b M hθ hβ hα₁ h hbν hαν
        (BalancedTensor.mapRight (k := k) (B := TensorProductAlgebra k Q Λ ν)
          (M := BlockLeftStandard Q Λ b hbν hαν) g y) : ParabolicStandard Q Λ θ' β' N) =
      parabolicStandardMap Q Λ θ' β' (twoPieceCastEnd Q Λ b M hθ hβ hα₁ g)
        (standardTwoPieceCastEquiv Q Λ hQ b M hθ hβ hα₁ h hbν hαν y) := by
  subst h
  exact standardTwoPieceEquiv_mapRight Q Λ hQ b M hθ hβ hα₁ hbν hαν g y

variable (C : Type) [Ring C] [Algebra k C]
  (ρ : C →ₐ[k] Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M)

/-- The action of `C` on the transported two-piece input. -/
def twoPieceCastAction : C →ₐ[k] Module.End (parabolicFactorAlgebra Q Λ θ' β') N :=
  (factorCastEnd Q Λ hθ (rfl : β' = β')
    (FactorCast Q Λ (rfl : initWeight b = initWeight b) hβ X)).comp
    ((factorCastEnd Q Λ (rfl : initWeight b = initWeight b) hβ X).comp
      ((twoPieceEndAlg Q Λ b hα₁).comp ρ))

theorem twoPieceCastAction_apply (c : C) :
    twoPieceCastAction Q Λ b M hθ hβ hα₁ C ρ c = twoPieceCastEnd Q Λ b M hθ hβ hα₁ (ρ c) := rfl

/-- **`M ⊗_B S^L_α ≅ S(X_M)` over `T(θ' + β') ⊗ C`.** -/
def standardTwoPieceActEquiv :
    TensorAct k (TensorProductAlgebra k Q Λ (θ' + β')) C
        (BalancedTensor.endAction k (TensorProductAlgebra k Q Λ (θ' + β'))
          (BlockLeftStandard Q Λ b hb hα) ρ) ≃ₗ[TensorProductAlgebra k Q Λ (θ' + β') ⊗[k] C]
      TensorAct k (TensorProductAlgebra k Q Λ (θ' + β')) C
        (standardActionT Q Λ hQ C (twoPieceCastAction Q Λ b M hθ hβ hα₁ C ρ)) :=
  TensorAct.equiv (standardTwoPieceEquiv Q Λ hQ b M hθ hβ hα₁ hb hα) fun c y =>
    standardTwoPieceEquiv_mapRight Q Λ hQ b M hθ hβ hα₁ hb hα (ρ c) y

end TwoPiece

end StendhalAlgebra

end Categorification.Stendhal
