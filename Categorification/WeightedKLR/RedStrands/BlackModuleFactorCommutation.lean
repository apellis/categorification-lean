/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongTensorFactorLift
import Categorification.WeightedKLR.RedStrands.BlackModuleCrossNaturality
import Categorification.WeightedKLR.RedStrands.BlackModuleEFLeftNaturality
import Categorification.WeightedKLR.RedStrands.ParabolicStandardLastLeft

/-!
# Commutation of `₁Eⱼ` and `₁Fᵢ` on modules over the factor algebra

Over the tensor product `D = T^{λ₁}_θ ⊗ R^{λ_ℓ}_β` of the two factor algebras at the last red
strand, the functors `₁Eⱼ` (restriction along `appendBlack ⊗ 1`) and `₁Fᵢ` (induction along it)
satisfy the commutation relations of `Eⱼ` and `Fᵢ` on `T^{λ₁}`-modules (Webster,
arXiv:1309.3796v3, Theorem 4.31 on modules, at standard Khovanov–Lauda black scalars). They are
the lifts (`InductionAlong.liftResIndEquiv`, `liftResIndProdEquiv`, `liftIndResProdEquiv`) of
the natural isomorphisms `clLeftBlackModuleCrossEquiv`, `clLeftBlackModuleEFEquiv`,
`clLeftBlackModuleFEEquiv`, and enter the dimension count in the proof of Proposition 5.5
there.

## Main definitions

* `factorCrossEquiv`: `₁Eⱼ ₁Fᵢ N ≅ ₁Fᵢ ₁Eⱼ N` for `i ≠ j`.
* `factorEFEquiv`: `₁Eᵢ ₁Fᵢ N ≅ ₁Fᵢ ₁Eᵢ N ⊕ N^{⊕ n}` when the weight pairing `n` is `≥ 0`.
* `factorFEEquiv`: `₁Fᵢ ₁Eᵢ N ≅ ₁Eᵢ ₁Fᵢ N ⊕ N^{⊕ -n}` when it is `≤ 0`.
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

section Cast

variable {I : Type u} [DecidableEq I] {k : Type u} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ)

/-- `leftAppendHom` with the content of the target given by an equality. -/
def leftAppendHomOfEq (j : I) {μ ν' : Multiset I} (hc : {j} + μ = ν') (β : Multiset I) :
    parabolicFactorAlgebra Q Λ μ β →ₙ+* parabolicFactorAlgebra Q Λ ν' β :=
  hc ▸ leftAppendHom Q Λ j μ β

theorem leftAppendHom_tmul (j : I) (μ β : Multiset I)
    (a : TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) μ)
    (c : CycKLR k Q (fun i => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i) β) :
    leftAppendHom Q Λ j μ β (a ⊗ₜ c) =
      appendBlackNU (Q := Q) (Λ := Λ ∘ Fin.castSucc) j μ a ⊗ₜ c := rfl

theorem leftAppendHomOfEq_tmul (j : I) {μ ν' : Multiset I} (hc : {j} + μ = ν')
    (β : Multiset I) (a : TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) μ)
    (c : CycKLR k Q (fun i => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i) β) :
    leftAppendHomOfEq Q Λ j hc β (a ⊗ₜ c) =
      appendBlackNUOfEq Q (Λ ∘ Fin.castSucc) j hc a ⊗ₜ c := by
  subst hc
  rfl

theorem appendBlackNU_smul (j : I) (μ : Multiset I) (c : k)
    (t : TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) μ) :
    appendBlackNU (Q := Q) (Λ := Λ ∘ Fin.castSucc) j μ (c • t) =
      c • appendBlackNU (Q := Q) (Λ := Λ ∘ Fin.castSucc) j μ t :=
  map_smul (appendBlack Q (Λ ∘ Fin.castSucc) j μ) c t

end Cast

section CL

variable {I : Type u} {ℓ : ℕ} {Λ : Fin (ℓ + 1) → I →₀ ℕ} {C : CartanDatum I}
  {k : Type u} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {hQ : IsRouquierQ C Q}

local notation "KL" => (CL.CLScalars.kl : CL.CLScalars C k)
local notation "Λ₀" => (Λ ∘ Fin.castSucc)
local notation "RDc" => coordinateDatum (Λ ∘ Fin.castSucc) C
local notation "D" => parabolicFactorAlgebra (CL.qCL KL) Λ

variable (hstd : ∀ i j, i ≠ j → Q i j = CL.qCL (CL.CLScalars.kl : CL.CLScalars C k) i j)
  {P : Presentation.{u, u}
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
def factorCrossEquiv (hji : j ≠ i) (N : Type u) [AddCommGroup N] [Module k N]
    [Module (D (Sj + ρ) β) N] [IsScalarTower k (D (Sj + ρ) β) N] :
    Res (leftAppendHomOfEq (CL.qCL KL) Λ j (cross_content i j ρ) β)
        (IndK k N (leftAppendHom (CL.qCL KL) Λ i (Sj + ρ) β)) ≃ₗ[D (Si + ρ) β]
      IndK k (Res (leftAppendHom (CL.qCL KL) Λ j ρ β) N)
        (leftAppendHom (CL.qCL KL) Λ i ρ β) :=
  liftResIndEquiv
    (appendBlackNUOfEq (CL.qCL KL) Λ₀ j (cross_content i j ρ))
    (leftAppendHomOfEq (CL.qCL KL) Λ j (cross_content i j ρ) β)
    (leftAppendHomOfEq_tmul (CL.qCL KL) Λ j (cross_content i j ρ) β)
    (appendBlackNU (Q := CL.qCL KL) (Λ := Λ₀) i (Sj + ρ))
    (appendBlackNU_smul (CL.qCL KL) Λ i (Sj + ρ))
    (leftAppendHom (CL.qCL KL) Λ i (Sj + ρ) β)
    (leftAppendHom_tmul (CL.qCL KL) Λ i (Sj + ρ) β)
    (appendBlackNU (Q := CL.qCL KL) (Λ := Λ₀) j ρ)
    (leftAppendHom (CL.qCL KL) Λ j ρ β)
    (leftAppendHom_tmul (CL.qCL KL) Λ j ρ β)
    (appendBlackNU (Q := CL.qCL KL) (Λ := Λ₀) i ρ)
    (appendBlackNU_smul (CL.qCL KL) Λ i ρ)
    (leftAppendHom (CL.qCL KL) Λ i ρ β)
    (leftAppendHom_tmul (CL.qCL KL) Λ i ρ β)
    (fun M _ _ => clLeftBlackModuleCrossEquiv hstd hP hwf i j ρ M hji)
    (fun _ _ _ _ _ _ f x => clLeftBlackModuleCrossEquiv_map hstd hP hwf i j ρ hji f x) N

end Cross

section EF

variable (i : I) (ν : Multiset I)

local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "nᵢ" => ip (RDc) i (downRightWeight (RDc) (coordinateRedWeights Λ₀ C) (Si + ν))

/-- **`₁Eᵢ ₁Fᵢ` against `₁Fᵢ ₁Eᵢ` over the factor algebra** (Webster, arXiv:1309.3796v3,
Theorem 4.31 on the first factor, in the proof of Proposition 5.5): for `n = ⟨i, λ⟩ ≥ 0`, with
`λ` the right weight of the first factor of content `i + ν`, `₁Eᵢ ₁Fᵢ N ≅ ₁Fᵢ ₁Eᵢ N ⊕ N^{⊕ n}`
for every module `N` over `D_{i+ν, β}`. -/
def factorEFEquiv (hn : 0 ≤ nᵢ) (N : Type u) [AddCommGroup N] [Module k N]
    [Module (D (Si + ν) β) N] [IsScalarTower k (D (Si + ν) β) N] :=
  liftResIndProdEquiv _
    (appendBlackNU (Q := CL.qCL KL) (Λ := Λ₀) i (Si + ν))
    (leftAppendHom (CL.qCL KL) Λ i (Si + ν) β)
    (leftAppendHom_tmul (CL.qCL KL) Λ i (Si + ν) β)
    (appendBlackNU (Q := CL.qCL KL) (Λ := Λ₀) i (Si + ν))
    (appendBlackNU_smul (CL.qCL KL) Λ i (Si + ν))
    (leftAppendHom (CL.qCL KL) Λ i (Si + ν) β)
    (leftAppendHom_tmul (CL.qCL KL) Λ i (Si + ν) β)
    (appendBlackNU (Q := CL.qCL KL) (Λ := Λ₀) i ν)
    (leftAppendHom (CL.qCL KL) Λ i ν β)
    (leftAppendHom_tmul (CL.qCL KL) Λ i ν β)
    (appendBlackNU (Q := CL.qCL KL) (Λ := Λ₀) i ν)
    (appendBlackNU_smul (CL.qCL KL) Λ i ν)
    (leftAppendHom (CL.qCL KL) Λ i ν β)
    (leftAppendHom_tmul (CL.qCL KL) Λ i ν β)
    (fun M _ _ => clLeftBlackModuleEFEquiv hstd hP hwf i ν M hn)
    (fun _ _ _ _ _ _ f x => clLeftBlackModuleEFEquiv_map hstd hP hwf i ν f hn x) N

/-- **`₁Fᵢ ₁Eᵢ` against `₁Eᵢ ₁Fᵢ` over the factor algebra** (Webster, arXiv:1309.3796v3,
Theorem 4.31 on the first factor, in the proof of Proposition 5.5): for `n = ⟨i, λ⟩ ≤ 0`,
`₁Fᵢ ₁Eᵢ N ≅ ₁Eᵢ ₁Fᵢ N ⊕ N^{⊕ -n}` for every module `N` over `D_{i+ν, β}`. -/
def factorFEEquiv (hn : nᵢ ≤ 0) (N : Type u) [AddCommGroup N] [Module k N]
    [Module (D (Si + ν) β) N] [IsScalarTower k (D (Si + ν) β) N] :=
  liftIndResProdEquiv _
    (appendBlackNU (Q := CL.qCL KL) (Λ := Λ₀) i (Si + ν))
    (leftAppendHom (CL.qCL KL) Λ i (Si + ν) β)
    (leftAppendHom_tmul (CL.qCL KL) Λ i (Si + ν) β)
    (appendBlackNU (Q := CL.qCL KL) (Λ := Λ₀) i (Si + ν))
    (appendBlackNU_smul (CL.qCL KL) Λ i (Si + ν))
    (leftAppendHom (CL.qCL KL) Λ i (Si + ν) β)
    (leftAppendHom_tmul (CL.qCL KL) Λ i (Si + ν) β)
    (appendBlackNU (Q := CL.qCL KL) (Λ := Λ₀) i ν)
    (leftAppendHom (CL.qCL KL) Λ i ν β)
    (leftAppendHom_tmul (CL.qCL KL) Λ i ν β)
    (appendBlackNU (Q := CL.qCL KL) (Λ := Λ₀) i ν)
    (appendBlackNU_smul (CL.qCL KL) Λ i ν)
    (leftAppendHom (CL.qCL KL) Λ i ν β)
    (leftAppendHom_tmul (CL.qCL KL) Λ i ν β)
    (fun M _ _ => clLeftBlackModuleFEEquiv hstd hP hwf i ν M hn)
    (fun _ _ _ _ _ _ f x => clLeftBlackModuleFEEquiv_map hstd hP hwf i ν f hn x) N

end EF

end CL

end Categorification.Stendhal
