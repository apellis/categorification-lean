/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongTensorFactorMackey
import Categorification.WeightedKLR.RedStrands.BlackModuleFactorCommutation
import Categorification.WeightedKLR.RedStrands.BlackModuleSecondFactorCommutation

/-!
# Commutation of functors on different factors of the factor algebra

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, (5.14), in
the proof of Proposition 5.5.

Over the tensor product `D = T^{λ₁}_θ ⊗ R^{λ_ℓ}_β` of the two factor algebras at the last red
strand, the functors `₁Eⱼ`, `₁Fᵢ` (restriction and induction along `appendBlack ⊗ 1`) commute
with the functors `₂Eⱼ`, `₂Fᵢ` (restriction and induction along `1 ⊗ cyclotomicLast`), since
they act on different tensor factors. These are instances of the Mackey-type isomorphisms
`InductionAlong.resIndCrossFactorEquiv` and `InductionAlong.resIndCrossFactorEquivRight`. No
hypothesis on the KLR polynomials `Q` is needed: the isomorphisms are purely algebraic.

## Main definitions

* `crossFactorEquiv`: `₂Eⱼ ₁Fᵢ N ≅ ₁Fᵢ ₂Eⱼ N`.
* `crossFactorEquivRight`: `₁Eⱼ ₂Fᵢ N ≅ ₂Fᵢ ₁Eⱼ N`.

## Main results

* `finrank_crossFactor_eq`, `finrank_crossFactorRight_eq`: the dimension forms.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open KLR InductionAlong
open scoped TensorProduct

open scoped Classical

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe u

variable {I : Type u} {k : Type u} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ)

local notation "Λ₀" => (Λ ∘ Fin.castSucc)
local notation "Λ₁" => (fun _ : Fin 1 => Λ (Fin.last ℓ))
local notation "D" => parabolicFactorAlgebra Q Λ

variable (i j : I) (θ ρ : Multiset I)

local notation "Sj" => (Singleton.singleton j : Multiset I)
local notation "Si" => (Singleton.singleton i : Multiset I)

section FirstInduction

-- Written out: notation is not hygienic inside `variable` binders.
variable (N : Type u) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra Q Λ θ ({j} + ρ)) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ ({j} + ρ)) N]

/-- **`₂Eⱼ ₁Fᵢ` against `₁Fᵢ ₂Eⱼ` over the factor algebra** (Webster, arXiv:1309.3796v3,
(5.14)): for every module `N` over `D_{θ, j+ρ}`, `₂Eⱼ ₁Fᵢ N ≅ ₁Fᵢ ₂Eⱼ N` over `D_{i+θ, ρ}`.
No condition on `i`, `j` or `Q` is needed. -/
def crossFactorEquiv :
    Res (parabolicRightHom Q Λ j (Si + θ) ρ) (IndK k N (leftAppendHom Q Λ i θ (Sj + ρ)))
      ≃ₗ[D (Si + θ) ρ]
      IndK k (Res (parabolicRightHom Q Λ j θ ρ) N) (leftAppendHom Q Λ i θ ρ) :=
  resIndCrossFactorEquiv
    (appendBlackNU (Q := Q) (Λ := Λ₀) i θ) (appendBlackNU_smul Q Λ i θ)
    (leftAppendHom Q Λ i θ ρ) (leftAppendHom_tmul Q Λ i θ ρ)
    (leftAppendHom Q Λ i θ (Sj + ρ)) (leftAppendHom_tmul Q Λ i θ (Sj + ρ))
    (cycLastHom Q Λ₁ j ρ)
    (parabolicRightHom Q Λ j θ ρ) (parabolicRightHom_tmul Q Λ j θ ρ)
    (parabolicRightHom Q Λ j (Si + θ) ρ) (parabolicRightHom_tmul Q Λ j (Si + θ) ρ) N

/-- **The dimension form of `crossFactorEquiv`** (Webster, arXiv:1309.3796v3, (5.14)):
`dim ₂Eⱼ ₁Fᵢ N = dim ₁Fᵢ ₂Eⱼ N` over `k`. -/
theorem finrank_crossFactor_eq :
    Module.finrank k (RestrictScalars k (D (Si + θ) ρ)
        (Res (parabolicRightHom Q Λ j (Si + θ) ρ)
          (IndK k N (leftAppendHom Q Λ i θ (Sj + ρ))))) =
      Module.finrank k (RestrictScalars k (D (Si + θ) ρ)
        (IndK k (Res (parabolicRightHom Q Λ j θ ρ) N) (leftAppendHom Q Λ i θ ρ))) :=
  finrank_restrictScalars_eq_of_equiv (crossFactorEquiv Q Λ i j θ ρ N)

end FirstInduction

section SecondInduction

-- Written out: notation is not hygienic inside `variable` binders.
variable (N : Type u) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra Q Λ ({j} + θ) ρ) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ ({j} + θ) ρ) N]

/-- **`₁Eⱼ ₂Fᵢ` against `₂Fᵢ ₁Eⱼ` over the factor algebra** (Webster, arXiv:1309.3796v3,
(5.14)): for every module `N` over `D_{j+θ, ρ}`, `₁Eⱼ ₂Fᵢ N ≅ ₂Fᵢ ₁Eⱼ N` over `D_{θ, i+ρ}`.
No condition on `i`, `j` or `Q` is needed. -/
def crossFactorEquivRight :
    Res (leftAppendHom Q Λ j θ (Si + ρ)) (IndK k N (parabolicRightHom Q Λ i (Sj + θ) ρ))
      ≃ₗ[D θ (Si + ρ)]
      IndK k (Res (leftAppendHom Q Λ j θ ρ) N) (parabolicRightHom Q Λ i θ ρ) :=
  resIndCrossFactorEquivRight
    (cycLastHom Q Λ₁ i ρ) (cycLastHom_smul Q Λ₁ i ρ)
    (parabolicRightHom Q Λ i θ ρ) (parabolicRightHom_tmul Q Λ i θ ρ)
    (parabolicRightHom Q Λ i (Sj + θ) ρ) (parabolicRightHom_tmul Q Λ i (Sj + θ) ρ)
    (appendBlackNU (Q := Q) (Λ := Λ₀) j θ)
    (leftAppendHom Q Λ j θ ρ) (leftAppendHom_tmul Q Λ j θ ρ)
    (leftAppendHom Q Λ j θ (Si + ρ)) (leftAppendHom_tmul Q Λ j θ (Si + ρ)) N

/-- **The dimension form of `crossFactorEquivRight`** (Webster, arXiv:1309.3796v3, (5.14)):
`dim ₁Eⱼ ₂Fᵢ N = dim ₂Fᵢ ₁Eⱼ N` over `k`. -/
theorem finrank_crossFactorRight_eq :
    Module.finrank k (RestrictScalars k (D θ (Si + ρ))
        (Res (leftAppendHom Q Λ j θ (Si + ρ))
          (IndK k N (parabolicRightHom Q Λ i (Sj + θ) ρ)))) =
      Module.finrank k (RestrictScalars k (D θ (Si + ρ))
        (IndK k (Res (leftAppendHom Q Λ j θ ρ) N) (parabolicRightHom Q Λ i θ ρ))) :=
  finrank_restrictScalars_eq_of_equiv (crossFactorEquivRight Q Λ i j θ ρ N)

end SecondInduction

end Categorification.Stendhal
