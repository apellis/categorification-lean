/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.EiStandardChain

/-!
# `Eᵢ` of the standardization as `Eᵢ` of a transported two-piece standardization

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5. An action of an algebra `C` on a module `P` over `T(i + ν)` induces one on
`Eᵢ P` (`blackResAction`), and isomorphisms intertwining the actions give isomorphisms of the
`T(ν) ⊗ C`-modules (`blackResActEquiv`). For blocks `b` of `ℓ + 1` red strands with first weight
`θ'` and last block `β'`, `θ' + β' = i + ν₀`, this identifies `Eᵢ(M ⊗_B S^L_α)` with `Eᵢ` of the
transported standardization `S(X_M)`, as modules over `T(ν₀) ⊗ C` (`eiTopEquiv`). This is the
middle term of the sequences of the induction step.
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

section BlackResAction

variable {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin (ℓ + 1) → I →₀ ℕ} (i : I) {ν : Multiset I}
  (C : Type) [Ring C] [Algebra k C]
  {P : Type} [AddCommGroup P] [Module k P]
  [Module (TensorProductAlgebra k Q Λ (({i} : Multiset I) + ν)) P]
  [IsScalarTower k (TensorProductAlgebra k Q Λ (({i} : Multiset I) + ν)) P]
  {P' : Type} [AddCommGroup P'] [Module k P']
  [Module (TensorProductAlgebra k Q Λ (({i} : Multiset I) + ν)) P']
  [IsScalarTower k (TensorProductAlgebra k Q Λ (({i} : Multiset I) + ν)) P']

/-- **The action of `C` on `Eᵢ P`** induced by an action on `P`. -/
def blackResAction
    (σ : C →ₐ[k] Module.End (TensorProductAlgebra k Q Λ (({i} : Multiset I) + ν)) P) :
    C →ₐ[k] Module.End (TensorProductAlgebra k Q Λ ν) (BlackRes (Q := Q) (Λ := Λ) i ν P) where
  toFun c := blackResMap i (σ c)
  map_one' := LinearMap.ext fun m => Subtype.ext (LinearMap.congr_fun (map_one σ) m.1)
  map_mul' c c' := LinearMap.ext fun m => Subtype.ext (LinearMap.congr_fun (map_mul σ c c') m.1)
  map_zero' := LinearMap.ext fun m => Subtype.ext (LinearMap.congr_fun (map_zero σ) m.1)
  map_add' c c' := LinearMap.ext fun m => Subtype.ext (LinearMap.congr_fun (map_add σ c c') m.1)
  commutes' c := LinearMap.ext fun m => Subtype.ext ((LinearMap.congr_fun (σ.commutes c) m.1).trans
    (by
      rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply]
      rfl))

theorem blackResAction_val
    (σ : C →ₐ[k] Module.End (TensorProductAlgebra k Q Λ (({i} : Multiset I) + ν)) P) (c : C)
    (m : BlackRes (Q := Q) (Λ := Λ) i ν P) : (blackResAction i C σ c m).1 = σ c m.1 := rfl

variable {C}

/-- **`Eᵢ` of an isomorphism intertwining the actions of `C`.** -/
def blackResActEquiv
    {σ : C →ₐ[k] Module.End (TensorProductAlgebra k Q Λ (({i} : Multiset I) + ν)) P}
    {σ' : C →ₐ[k] Module.End (TensorProductAlgebra k Q Λ (({i} : Multiset I) + ν)) P'}
    (e : P ≃ₗ[TensorProductAlgebra k Q Λ (({i} : Multiset I) + ν)] P')
    (he : ∀ c x, e (σ c x) = σ' c (e x)) :
    TensorAct k (TensorProductAlgebra k Q Λ ν) C (blackResAction i C σ) ≃ₗ[
      TensorProductAlgebra k Q Λ ν ⊗[k] C]
      TensorAct k (TensorProductAlgebra k Q Λ ν) C (blackResAction i C σ') :=
  TensorAct.equiv (blackResCongr i e) fun c m => Subtype.ext (he c m.1)

theorem blackResActEquiv_of
    {σ : C →ₐ[k] Module.End (TensorProductAlgebra k Q Λ (({i} : Multiset I) + ν)) P}
    {σ' : C →ₐ[k] Module.End (TensorProductAlgebra k Q Λ (({i} : Multiset I) + ν)) P'}
    (e : P ≃ₗ[TensorProductAlgebra k Q Λ (({i} : Multiset I) + ν)] P')
    (he : ∀ c x, e (σ c x) = σ' c (e x)) (m : BlackRes (Q := Q) (Λ := Λ) i ν P) :
    blackResActEquiv i e he (TensorAct.of m) = TensorAct.of (blackResCongr i e m) := rfl

end BlackResAction

section Top

variable (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (hQ : KLRSymm Q)
  (i : I) (b : Fin (ℓ + 2) → Multiset I)
  (M : Type) [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  {θ' β' : Multiset I} (hθ : initWeight b = θ') (hβ : lastBlock b = β')
  (hα₁ : RootNonViolated (ν := initWeight b) (blockRoot (initBlocks b)))
  {ν₀ : Multiset I} (h : θ' + β' = ({i} : Multiset I) + ν₀)
  (hb : blockPrefix b (ℓ + 2) = ({i} : Multiset I) + ν₀)
  (hα : RootNonViolated (ν := ({i} : Multiset I) + ν₀) (blockRoot b))
  (C : Type) [Ring C] [Algebra k C] (ρ : C →ₐ[k] Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M)

local notation "N" => FactorCast Q Λ hθ (rfl : β' = β')
  (FactorCast Q Λ (rfl : initWeight b = initWeight b) hβ (TwoPieceInput Q Λ b M hα₁))
local notation "SN" => FamilyCast (TensorProductAlgebra k Q Λ) h
  (ParabolicStandardT Q Λ θ' β' N hQ)

/-- The action of `C` on the transported standardization of the two-piece input. -/
abbrev topAction : C →ₐ[k] Module.End (TensorProductAlgebra k Q Λ (({i} : Multiset I) + ν₀)) SN :=
  (FamilyCast.endHom (TensorProductAlgebra k Q Λ) h _).comp
    (standardActionT Q Λ hQ C (twoPieceCastAction Q Λ b M hθ hβ hα₁ C ρ))

theorem topAction_apply (c : C) (z : ParabolicStandardT Q Λ θ' β' N hQ) :
    (topAction Q Λ hQ i b M hθ hβ hα₁ h C ρ c (show SN from z) : ParabolicStandard Q Λ θ' β' N) =
      parabolicStandardMap Q Λ θ' β' (twoPieceCastEnd Q Λ b M hθ hβ hα₁ (ρ c)) z := rfl

/-- **`Eᵢ(M ⊗_B S^L_α) ≅ Eᵢ S(X_M)` over `T(ν₀) ⊗ C`**, with `S(X_M)` transported along
`θ' + β' = i + ν₀`. -/
def eiTopEquiv :
    eiTop Q i Λ b ν₀ hb hα C M ρ ≃ₗ[TensorProductAlgebra k Q Λ ν₀ ⊗[k] C]
      TensorAct k (TensorProductAlgebra k Q Λ ν₀) C
        (blackResAction i C (topAction Q Λ hQ i b M hθ hβ hα₁ h C ρ)) :=
  blackResActEquiv i (standardTwoPieceCastEquiv Q Λ hQ b M hθ hβ hα₁ h hb hα) fun c y =>
    standardTwoPieceCastEquiv_mapRight Q Λ hQ b M hθ hβ hα₁ h hb hα (ρ c) y

theorem eiTopEquiv_of (m : BlackRes (Q := Q) (Λ := Λ) i ν₀ (LeftStandardization Q Λ b hb hα M)) :
    eiTopEquiv Q Λ hQ i b M hθ hβ hα₁ h hb hα C ρ
        (TensorAct.of (ρ := eiTopAction Q i Λ b ν₀ hb hα C M ρ) m) =
      TensorAct.of (blackResCongr i (standardTwoPieceCastEquiv Q Λ hQ b M hθ hβ hα₁ h hb hα) m) :=
  rfl

end Top

end StendhalAlgebra

end Categorification.Stendhal
