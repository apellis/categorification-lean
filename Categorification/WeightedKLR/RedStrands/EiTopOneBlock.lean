/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.EiTopChain
import Categorification.WeightedKLR.RedStrands.EiLeftInput
import Categorification.WeightedKLR.RedStrands.ParabolicStandardLastOneBlockNatural
import Categorification.Algebra.InductionAlongResEnd

/-!
# `Eᵢ S N` with a commuting action when `i` occurs in one piece

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5, `E`-part. For a module `N` over `T^{λ'}(θ) ⊗ R^{λ_ℓ}(β)` with an action `τ` of
an algebra `C`, the isomorphisms `Eᵢ(S N) ≅ S(₁Eᵢ N)` (`θ = i + θ₀`, `i ∉ β`) and
`Eᵢ(S N) ≅ S(₂Eᵢ N)` (`β = i + β₀`, `i ∉ θ`) are isomorphisms of modules over
`T(ν₀) ⊗ C` (`eiLeftOnlyEquiv`, `eiRightOnlyEquiv`), with `Eᵢ(S N)` in the transported form of
`eiTopEquiv`. For the two-piece input `X_M` with `i ∉ β`, `S(₁Eᵢ X_M)` is the standardization of
the module of the induction hypothesis (`leftTermEquiv`).
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
  (i : I) (C : Type) [Ring C] [Algebra k C]

local notation "Tfam" => TensorProductAlgebra k Q Λ

section LeftOnly

variable (θ₀ β : Multiset I) {N : Type} [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra Q Λ (({i} : Multiset I) + θ₀) β) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ (({i} : Multiset I) + θ₀) β) N]
  (τ : C →ₐ[k] Module.End (parabolicFactorAlgebra Q Λ (({i} : Multiset I) + θ₀) β) N)

/-- **`Eᵢ(S N) ≅ S(₁Eᵢ N)` over `T(θ₀ + β) ⊗ C`**, for `θ = i + θ₀` and `i ∉ β`. -/
def eiLeftOnlyEquiv (hi : i ∉ β) :
    TensorAct k (Tfam (θ₀ + β)) C (blackResAction i C
        ((FamilyCast.endHom Tfam (leftBlack_weight i θ₀ β).symm _).comp
          (standardActionT Q Λ hQ C τ))) ≃ₗ[Tfam (θ₀ + β) ⊗[k] C]
      TensorAct k (Tfam (θ₀ + β)) C (standardActionT Q Λ hQ C
        ((Res.endAlg (parabolicAppendLeft Q Λ i θ₀ β)).comp τ)) :=
  TensorAct.equiv ((blackResCongr i (leftStandardTEquiv Q Λ i hQ θ₀ β N).symm).trans
      (leftBlackResEquivT Q Λ i θ₀ β N hQ hi)) fun c _ =>
    leftBlackResEquiv_natural Q Λ i θ₀ β hQ (τ c) hi _ _ rfl

end LeftOnly

section RightOnly

variable (θ β₀ : Multiset I) {N : Type} [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra Q Λ θ (({i} : Multiset I) + β₀)) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ (({i} : Multiset I) + β₀)) N]
  (τ : C →ₐ[k] Module.End (parabolicFactorAlgebra Q Λ θ (({i} : Multiset I) + β₀)) N)

/-- **`Eᵢ(S N) ≅ S(₂Eᵢ N)` over `T(θ + β₀) ⊗ C`**, for `β = i + β₀` and `i ∉ θ`. -/
def eiRightOnlyEquiv (hi : i ∉ θ) :
    TensorAct k (Tfam (θ + β₀)) C (blackResAction i C
        ((FamilyCast.endHom Tfam (rightBlack_weight i θ β₀).symm _).comp
          (standardActionT Q Λ hQ C τ))) ≃ₗ[Tfam (θ + β₀) ⊗[k] C]
      TensorAct k (Tfam (θ + β₀)) C (standardActionT Q Λ hQ C
        ((Res.endAlg (parabolicAppendRight Q Λ i β₀ θ)).comp τ)) :=
  TensorAct.equiv ((blackResCongr i (rightStandardTEquiv Q Λ i hQ θ β₀ N).symm).trans
      (rightBlackResEquivT Q Λ i θ β₀ N hQ hi)) fun c _ =>
    rightBlackResEquiv_natural Q Λ i θ β₀ hQ (τ c) hi _ _ rfl

end RightOnly

section LeftTerm

variable {C} (b : Fin (ℓ + 2) → Multiset I)
  (M : Type) [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  {θ₀ β' : Multiset I} (hθ : initWeight b = ({i} : Multiset I) + θ₀) (hβ : lastBlock b = β')
  (hα₁ : RootNonViolated (ν := initWeight b) (blockRoot (initBlocks b)))
  (hα₁' : RootNonViolated (ν := ({i} : Multiset I) + θ₀) (blockRoot (initBlocks b)))
  (ρ : C →ₐ[k] Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M)

/-- **`S(₁Eᵢ X_M) ≅ S(Eᵢ(M|_{B'} ⊗_{B'} S^L_{α'}))` over `T(θ₀ + β) ⊗ C`.** -/
def leftTermEquiv :
    TensorAct k (Tfam (θ₀ + β')) C (standardActionT Q Λ hQ C
        ((Res.endAlg (parabolicAppendLeft Q Λ i θ₀ β')).comp
          (twoPieceCastAction Q Λ b M hθ hβ hα₁ C ρ))) ≃ₗ[Tfam (θ₀ + β') ⊗[k] C]
      TensorAct k (Tfam (θ₀ + β')) C
        (splitStandardAction Q Λ hQ (eiTop Q i (Λ ∘ Fin.castSucc) (initBlocks b) θ₀ hθ hα₁'
          ((CycKLR k Q (fun i : I => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i) β') ⊗[k] C)
          (InitRestrict Q Λ b M) (inductionAction Q Λ b M hβ C ρ))) :=
  standardActEquiv Q Λ hQ (leftInputEquiv Q Λ i b M hθ hβ hα₁ hα₁' C ρ)
    fun c z => leftInputEquiv_natural Q Λ i b M hθ hβ hα₁ hα₁' C ρ c z

end LeftTerm

end StendhalAlgebra

end Categorification.Stendhal
