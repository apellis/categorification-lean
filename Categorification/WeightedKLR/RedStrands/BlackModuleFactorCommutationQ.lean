/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackModuleFactorCommutation
import Categorification.Algebra.InductionAlongTensorFactorLift
import Categorification.WeightedKLR.RedStrands.BlackModuleCrossNaturalityQ
import Categorification.WeightedKLR.RedStrands.BlackModuleEFLeftNaturalityQ
import Categorification.WeightedKLR.RedStrands.ParabolicStandardLastLeft

/-!
# Commutation of `₁Eⱼ` and `₁Fᵢ` on modules over the factor algebra

Over the tensor product `D = T^{λ₁}_θ ⊗ R^{λ_ℓ}_β` of the two factor algebras at the last red
strand, the functors `₁Eⱼ` (restriction along `appendBlack ⊗ 1`) and `₁Fᵢ` (induction along it)
satisfy the commutation relations of `Eⱼ` and `Fᵢ` on `T^{λ₁}`-modules (Webster,
arXiv:1309.3796v3, Theorem 4.31 on modules, for Rouquier parameters `Q`). They are
the lifts (`InductionAlong.liftResIndEquiv`, `liftResIndProdEquiv`, `liftIndResProdEquiv`) of
the natural isomorphisms `clLeftBlackModuleCrossEquivQ`, `clLeftBlackModuleEFEquivQ`,
`clLeftBlackModuleFEEquivQ`, and enter the dimension count in the proof of Proposition 5.5
there.

## Main definitions

* `factorCrossEquivQ`: `₁Eⱼ ₁Fᵢ N ≅ ₁Fᵢ ₁Eⱼ N` for `i ≠ j`.
* `factorEFEquivQ`: `₁Eᵢ ₁Fᵢ N ≅ ₁Fᵢ ₁Eᵢ N ⊕ N^{⊕ n}` when the weight pairing `n` is `≥ 0`.
* `factorFEEquivQ`: `₁Fᵢ ₁Eᵢ N ≅ ₁Eᵢ ₁Fᵢ N ⊕ N^{⊕ -n}` when it is `≤ 0`.

This is the version of `BlackModuleFactorCommutation` for every Rouquier parameter `Q`: the black
strands carry the relations of Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3, Definition 1.1, `r = 1`)
instead of the KL III relations. Each declaration carries the suffix `Q`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory CategoryTheory.Idempotents QuantumGroup QuantumGroup.UDot StringDiagrams
  KLR TwoRep CyclotomicAction DoubleDiagram KL3.Diagram InductionAlong MulOpposite
open scoped TensorProduct

open scoped Classical

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe u w

section CL

variable {I : Type u} {ℓ : ℕ} {Λ : Fin (ℓ + 1) → I →₀ ℕ} {C : CartanDatum I}
  {k : Type u} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {hQ : IsRouquierQ C Q}

local notation "Λ₀" => (Λ ∘ Fin.castSucc)
local notation "RDc" => coordinateDatum (Λ ∘ Fin.castSucc) C
local notation "D" => parabolicFactorAlgebra Q Λ

variable {P : Presentation.{u, u}
    (signature (coordinateDatum (Λ ∘ Fin.castSucc) C)
      (redWeight (cyclotomicCoverWeightDatum (Λ ∘ Fin.castSucc) C))) k}
  (hP : CoverRelsNegligible.{u, u, w} (Λ ∘ Fin.castSucc) C hQ
    (coverDotCentral (Λ ∘ Fin.castSucc) C hQ)
    (blockWeight (cyclotomicCoverWeightDatum (Λ ∘ Fin.castSucc) C)
      (cyclotomicCoverHighest (I := I) (ℓ := ℓ)) 0 : I ⊕ Fin ℓ → ℤ) P)
  (hwf : P.WFDom) (β : Multiset I)

section Cross

variable (i j : I) (ρ : Multiset I)

local notation "Sj" => (Singleton.singleton j : Multiset I)
local notation "Si" => (Singleton.singleton i : Multiset I)

/-- **`₁Eⱼ ₁Fᵢ` against `₁Fᵢ ₁Eⱼ` over the factor algebra**, `i ≠ j` (Webster,
arXiv:1309.3796v3, Theorem 4.31 on the first factor, in the proof of Proposition 5.5): for every
module `N` over `D_{j+ρ, β}`, `₁Eⱼ ₁Fᵢ N ≅ ₁Fᵢ ₁Eⱼ N` over `D_{i+ρ, β}`. -/
def factorCrossEquivQ (hji : j ≠ i) (N : Type u) [AddCommGroup N] [Module k N]
    [Module (D (Sj + ρ) β) N] [IsScalarTower k (D (Sj + ρ) β) N] :
    Res (leftAppendHomOfEq Q Λ j (cross_content i j ρ) β)
        (IndK k N (leftAppendHom Q Λ i (Sj + ρ) β)) ≃ₗ[D (Si + ρ) β]
      IndK k (Res (leftAppendHom Q Λ j ρ β) N)
        (leftAppendHom Q Λ i ρ β) :=
  liftResIndEquiv
    (appendBlackNUOfEq Q Λ₀ j (cross_content i j ρ))
    (leftAppendHomOfEq Q Λ j (cross_content i j ρ) β)
    (leftAppendHomOfEq_tmul Q Λ j (cross_content i j ρ) β)
    (appendBlackNU (Q := Q) (Λ := Λ₀) i (Sj + ρ))
    (appendBlackNU_smul Q Λ i (Sj + ρ))
    (leftAppendHom Q Λ i (Sj + ρ) β)
    (leftAppendHom_tmul Q Λ i (Sj + ρ) β)
    (appendBlackNU (Q := Q) (Λ := Λ₀) j ρ)
    (leftAppendHom Q Λ j ρ β)
    (leftAppendHom_tmul Q Λ j ρ β)
    (appendBlackNU (Q := Q) (Λ := Λ₀) i ρ)
    (appendBlackNU_smul Q Λ i ρ)
    (leftAppendHom Q Λ i ρ β)
    (leftAppendHom_tmul Q Λ i ρ β)
    (fun M _ _ => clLeftBlackModuleCrossEquivQ hP hwf i j ρ M hji)
    (fun _ _ _ _ _ _ f x => clLeftBlackModuleCrossEquiv_mapQ hP hwf i j ρ hji f x) N

end Cross

section EF

variable (i : I) (ν : Multiset I)

local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "nᵢ" => ip (RDc) i (downRightWeight (RDc) (coordinateRedWeights Λ₀ C) (Si + ν))

/-- **`₁Eᵢ ₁Fᵢ` against `₁Fᵢ ₁Eᵢ` over the factor algebra** (Webster, arXiv:1309.3796v3,
Theorem 4.31 on the first factor, in the proof of Proposition 5.5): for `n = ⟨i, λ⟩ ≥ 0`, with
`λ` the right weight of the first factor of content `i + ν`, `₁Eᵢ ₁Fᵢ N ≅ ₁Fᵢ ₁Eᵢ N ⊕ N^{⊕ n}`
for every module `N` over `D_{i+ν, β}`. -/
def factorEFEquivQ (hn : 0 ≤ nᵢ) (N : Type u) [AddCommGroup N] [Module k N]
    [Module (D (Si + ν) β) N] [IsScalarTower k (D (Si + ν) β) N] :=
  liftResIndProdEquiv _
    (appendBlackNU (Q := Q) (Λ := Λ₀) i (Si + ν))
    (leftAppendHom Q Λ i (Si + ν) β)
    (leftAppendHom_tmul Q Λ i (Si + ν) β)
    (appendBlackNU (Q := Q) (Λ := Λ₀) i (Si + ν))
    (appendBlackNU_smul Q Λ i (Si + ν))
    (leftAppendHom Q Λ i (Si + ν) β)
    (leftAppendHom_tmul Q Λ i (Si + ν) β)
    (appendBlackNU (Q := Q) (Λ := Λ₀) i ν)
    (leftAppendHom Q Λ i ν β)
    (leftAppendHom_tmul Q Λ i ν β)
    (appendBlackNU (Q := Q) (Λ := Λ₀) i ν)
    (appendBlackNU_smul Q Λ i ν)
    (leftAppendHom Q Λ i ν β)
    (leftAppendHom_tmul Q Λ i ν β)
    (fun M _ _ => clLeftBlackModuleEFEquivQ hP hwf i ν M hn)
    (fun _ _ _ _ _ _ f x => clLeftBlackModuleEFEquiv_mapQ hP hwf i ν f hn x) N

/-- **`₁Fᵢ ₁Eᵢ` against `₁Eᵢ ₁Fᵢ` over the factor algebra** (Webster, arXiv:1309.3796v3,
Theorem 4.31 on the first factor, in the proof of Proposition 5.5): for `n = ⟨i, λ⟩ ≤ 0`,
`₁Fᵢ ₁Eᵢ N ≅ ₁Eᵢ ₁Fᵢ N ⊕ N^{⊕ -n}` for every module `N` over `D_{i+ν, β}`. -/
def factorFEEquivQ (hn : nᵢ ≤ 0) (N : Type u) [AddCommGroup N] [Module k N]
    [Module (D (Si + ν) β) N] [IsScalarTower k (D (Si + ν) β) N] :=
  liftIndResProdEquiv _
    (appendBlackNU (Q := Q) (Λ := Λ₀) i (Si + ν))
    (leftAppendHom Q Λ i (Si + ν) β)
    (leftAppendHom_tmul Q Λ i (Si + ν) β)
    (appendBlackNU (Q := Q) (Λ := Λ₀) i (Si + ν))
    (appendBlackNU_smul Q Λ i (Si + ν))
    (leftAppendHom Q Λ i (Si + ν) β)
    (leftAppendHom_tmul Q Λ i (Si + ν) β)
    (appendBlackNU (Q := Q) (Λ := Λ₀) i ν)
    (leftAppendHom Q Λ i ν β)
    (leftAppendHom_tmul Q Λ i ν β)
    (appendBlackNU (Q := Q) (Λ := Λ₀) i ν)
    (appendBlackNU_smul Q Λ i ν)
    (leftAppendHom Q Λ i ν β)
    (leftAppendHom_tmul Q Λ i ν β)
    (fun M _ _ => clLeftBlackModuleFEEquivQ hP hwf i ν M hn)
    (fun _ _ _ _ _ _ f x => clLeftBlackModuleFEEquiv_mapQ hP hwf i ν f hn x) N

end EF

end CL

end Categorification.Stendhal
