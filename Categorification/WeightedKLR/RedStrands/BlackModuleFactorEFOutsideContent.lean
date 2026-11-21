/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackModuleEFOutsideContentCL
import Categorification.WeightedKLR.RedStrands.BlackModuleFactorCommutation
import Categorification.WeightedKLR.RedStrands.BlackModuleSecondFactorCommutation

/-!
# `Eᵢ Fᵢ` over the factor algebras for a colour outside the content

Over the tensor product `D = T^{λ₁}_θ ⊗ R^{λ_ℓ}_β` of the two factor algebras at the last red
strand, the case of the commutation relation of `Eᵢ` and `Fᵢ` (Webster, arXiv:1309.3796v3,
Theorem 4.31 on modules, at standard Khovanov–Lauda black scalars) in which `i` lies outside the
content of the factor reads `Eᵢ Fᵢ N ≅ N^{⊕ n}` with `n = ⟨i, λ⟩ ≥ 0`. It is the lift to the
tensor product (`InductionAlong.liftResIndPiEquiv`, `liftResIndPiEquivRight`) of the natural
isomorphism `clLeftBlackModuleEFEquivOfNotMem`, transported for the second factor through
Theorem 4.20 (`cycRingEquiv`). These are the inputs, for a colour outside the black content,
of the dimension count in the proof of Proposition 5.5 there.

## Main definitions

* `factorEFEquivOfNotMem`: `₁Eᵢ ₁Fᵢ N ≅ N^{⊕ n}` for `i ∉ θ`.
* `cycEFEquivOfNotMem`: `Eᵢ Fᵢ M ≅ M^{⊕ n}` on `R^λ_β`-modules for `i ∉ β`.
* `secondFactorEFEquivOfNotMem`: `₂Eᵢ ₂Fᵢ N ≅ N^{⊕ n}` for `i ∉ β`.

## Main results

* `finrank_factorEF_eq_of_notMem`, `finrank_secondFactorEF_eq_of_notMem`: the dimension forms
  `dim Eᵢ Fᵢ N = n dim N`.
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

section First

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
  (hwf : P.WFDom) (β : Multiset I) (i : I) (θ : Multiset I)

local notation "nᵢ" => ip (RDc) i (downRightWeight (RDc) (coordinateRedWeights Λ₀ C) θ)

/-- **`₁Eᵢ ₁Fᵢ` over the factor algebra for `i ∉ θ`** (Webster, arXiv:1309.3796v3, Theorem 4.31
on the first factor with `₁Eᵢ N = 0`, in the proof of Proposition 5.5): for `n = ⟨i, λ⟩`, with
`λ` the right weight of the first factor of content `θ`, `₁Eᵢ ₁Fᵢ N ≅ N^{⊕ n}` for every module
`N` over `D_{θ, β}`. -/
def factorEFEquivOfNotMem (hi : i ∉ θ) (N : Type u) [AddCommGroup N] [Module k N]
    [Module (D θ β) N] [IsScalarTower k (D θ β) N] :
    Res (leftAppendHom (CL.qCL KL) Λ i θ β) (IndK k N (leftAppendHom (CL.qCL KL) Λ i θ β))
      ≃ₗ[D θ β] (Fin (nᵢ).toNat → N) :=
  liftResIndPiEquiv _
    (appendBlackNU (Q := CL.qCL KL) (Λ := Λ₀) i θ)
    (leftAppendHom (CL.qCL KL) Λ i θ β)
    (leftAppendHom_tmul (CL.qCL KL) Λ i θ β)
    (appendBlackNU (Q := CL.qCL KL) (Λ := Λ₀) i θ)
    (appendBlackNU_smul (CL.qCL KL) Λ i θ)
    (leftAppendHom (CL.qCL KL) Λ i θ β)
    (leftAppendHom_tmul (CL.qCL KL) Λ i θ β)
    (fun M _ _ => clLeftBlackModuleEFEquivOfNotMem hstd hP hwf i θ M hi)
    (fun _ _ _ _ _ _ f x => clLeftBlackModuleEFEquivOfNotMem_map hstd hP hwf i θ f hi x) N

include hstd hP hwf in
/-- **The dimension form of `factorEFEquivOfNotMem`** (Webster, arXiv:1309.3796v3, in the
dimension count of the proof of Proposition 5.5): for `i ∉ θ`,
`dim ₁Eᵢ ₁Fᵢ N = n dim N` over `k`, with `n = ⟨i, λ⟩ ≥ 0`. -/
theorem finrank_factorEF_eq_of_notMem (hi : i ∉ θ) (N : Type u) [AddCommGroup N] [Module k N]
    [Module (D θ β) N] [IsScalarTower k (D θ β) N]
    [FiniteDimensional k (RestrictScalars k (D θ β) N)] :
    (Module.finrank k (RestrictScalars k (D θ β)
        (Res (leftAppendHom (CL.qCL KL) Λ i θ β)
          (IndK k N (leftAppendHom (CL.qCL KL) Λ i θ β)))) : ℤ) =
      nᵢ * Module.finrank k (RestrictScalars k (D θ β) N) := by
  have e := finrank_restrictScalars_eq_of_equiv_pi (k := k)
    (factorEFEquivOfNotMem hstd hP hwf β i θ hi N)
  rw [e, Fintype.card_fin]
  push_cast
  rw [Int.toNat_of_nonneg (ip_nonneg_of_notMem i θ hi)]

end First

section CycCL

variable {I : Type u} {Λ₁ : Fin 1 → I →₀ ℕ} {C : CartanDatum I}
  {k : Type u} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {hQ : IsRouquierQ C Q}

local notation "RD₁" => coordinateDatum Λ₁ C
local notation "KL" => (CL.CLScalars.kl : CL.CLScalars C k)
local notation "Cyc" => CycKLR k (CL.qCL KL) (fun j => (Polynomial.X : Polynomial k) ^ Λ₁ 0 j)
local notation "cR" => cycRingEquiv (CL.qCL KL) Λ₁
local notation "cL" => cycLastHom (CL.qCL KL) Λ₁

variable (hstd : ∀ i j, i ≠ j → Q i j = CL.qCL (CL.CLScalars.kl : CL.CLScalars C k) i j)
  {P : Presentation.{u, u}
    (signature (coordinateDatum Λ₁ C) (redWeight (cyclotomicCoverWeightDatum Λ₁ C))) k}
  (hP : CoverRelsNegligible.{u, u, w} Λ₁ C hQ (coverDotCentral Λ₁ C hQ)
    (blockWeight (cyclotomicCoverWeightDatum Λ₁ C) (cyclotomicCoverHighest (I := I) (ℓ := 1)) 0 :
      I ⊕ Fin 1 → ℤ) P)
  (hwf : P.WFDom) (i : I) (μ : Multiset I)

local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "n₂" => ip (RD₁) i (downRightWeight (RD₁) (coordinateRedWeights Λ₁ C) μ)

/-- **`Eᵢ Fᵢ` on modules over the cyclotomic KLR algebra for `i ∉ μ`** (Webster,
arXiv:1309.3796v3, Theorem 4.31 at one red strand with `Eᵢ M = 0`, through Theorem 4.20):
`Eᵢ Fᵢ M ≅ M^{⊕ n}` with `n = ⟨i, λ⟩`, for every module `M` over `R^λ_μ`, with `Fᵢ` induction
and `Eᵢ` restriction along the last-colour inclusion. -/
def cycEFEquivOfNotMem (hi : i ∉ μ) (M : Type u) [AddCommGroup M] [Module (Cyc μ) M] :
    Res (cL i μ) (Ind M (cL i μ)) ≃ₗ[Cyc μ] (Fin (n₂).toNat → M) :=
  resIndPiEquivTransport (cR μ) (cR (Si + μ)) (appendBlackNU_cycRingEquiv (CL.qCL KL) Λ₁ i μ)
    (toCycView (CL.qCL KL) Λ₁ μ M) (toCycView_smul (CL.qCL KL) Λ₁ μ M) _
    (clLeftBlackModuleEFEquivOfNotMem hstd hP hwf i μ (CycView (CL.qCL KL) Λ₁ μ M) hi)

variable {M M₂ : Type u} [AddCommGroup M] [AddCommGroup M₂]
  [Module (CycKLR k (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k))
    (fun j => (Polynomial.X : Polynomial k) ^ Λ₁ 0 j) μ) M]
  [Module (CycKLR k (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k))
    (fun j => (Polynomial.X : Polynomial k) ^ Λ₁ 0 j) μ) M₂]

/-- **Naturality of `cycEFEquivOfNotMem`**: it carries `Eᵢ Fᵢ f` to `f^n`. -/
theorem cycEFEquivOfNotMem_map (f : M →ₗ[Cyc μ] M₂) (hi : i ∉ μ)
    (x : Res (cL i μ) (Ind M (cL i μ))) :
    cycEFEquivOfNotMem hstd hP hwf i μ hi M₂ (Res.map (Ind.map f) x) =
      fun s => f (cycEFEquivOfNotMem hstd hP hwf i μ hi M x s) := by
  kernel_exact resIndPiEquivTransport_map (cR μ) (cR (Si + μ))
    (appendBlackNU_cycRingEquiv (CL.qCL KL) Λ₁ i μ)
    (toCycView (CL.qCL KL) Λ₁ μ M) (toCycView_smul (CL.qCL KL) Λ₁ μ M)
    (toCycView (CL.qCL KL) Λ₁ μ M₂) (toCycView_smul (CL.qCL KL) Λ₁ μ M₂)
    f (cycViewMap (CL.qCL KL) Λ₁ μ f) (fun _ => rfl) _
    (clLeftBlackModuleEFEquivOfNotMem hstd hP hwf i μ (CycView (CL.qCL KL) Λ₁ μ M) hi)
    (clLeftBlackModuleEFEquivOfNotMem hstd hP hwf i μ (CycView (CL.qCL KL) Λ₁ μ M₂) hi)
    (fun y => by
      kernel_exact clLeftBlackModuleEFEquivOfNotMem_map hstd hP hwf i μ
        (cycViewMap (CL.qCL KL) Λ₁ μ f) hi y) x

end CycCL

section Second

variable {I : Type u} {ℓ : ℕ} {Λ : Fin (ℓ + 1) → I →₀ ℕ} {C : CartanDatum I}
  {k : Type u} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {hQ : IsRouquierQ C Q}

local notation "KL" => (CL.CLScalars.kl : CL.CLScalars C k)
local notation "Λ₁" => (fun _ : Fin 1 => Λ (Fin.last ℓ))
local notation "RD₁" => coordinateDatum (fun _ : Fin 1 => Λ (Fin.last ℓ)) C
local notation "D" => parabolicFactorAlgebra (CL.qCL KL) Λ
local notation "cL" => cycLastHom (CL.qCL KL) (fun _ : Fin 1 => Λ (Fin.last ℓ))
local notation "ψ" => parabolicRightHom (CL.qCL KL) Λ

-- The weight `Λ₁` is written out: notation is not hygienic inside `variable` binders.
variable (hstd : ∀ i j, i ≠ j → Q i j = CL.qCL (CL.CLScalars.kl : CL.CLScalars C k) i j)
  {P : Presentation.{u, u}
    (signature (coordinateDatum (fun _ : Fin 1 => Λ (Fin.last ℓ)) C)
      (redWeight (cyclotomicCoverWeightDatum (fun _ : Fin 1 => Λ (Fin.last ℓ)) C))) k}
  (hP : CoverRelsNegligible.{u, u, w} (fun _ : Fin 1 => Λ (Fin.last ℓ)) C hQ
    (coverDotCentral (fun _ : Fin 1 => Λ (Fin.last ℓ)) C hQ)
    (blockWeight (cyclotomicCoverWeightDatum (fun _ : Fin 1 => Λ (Fin.last ℓ)) C)
      (cyclotomicCoverHighest (I := I) (ℓ := 1)) 0 : I ⊕ Fin 1 → ℤ) P)
  (hwf : P.WFDom) (θ : Multiset I) (i : I) (μ : Multiset I)

local notation "n₂" => ip (RD₁) i (downRightWeight (RD₁) (coordinateRedWeights Λ₁ C) μ)

/-- **`₂Eᵢ ₂Fᵢ` over the factor algebra for `i ∉ μ`** (Webster, arXiv:1309.3796v3,
Theorem 4.31 on the second factor with `₂Eᵢ N = 0`, in the proof of Proposition 5.5): for
`n = ⟨i, λ⟩`, with `λ` the right weight of content `μ` of the one-red-strand algebra of the
cyclotomic factor `R^{λ_ℓ}`, `₂Eᵢ ₂Fᵢ N ≅ N^{⊕ n}` for every module `N` over `D_{θ, μ}`. -/
def secondFactorEFEquivOfNotMem (hi : i ∉ μ) (N : Type u) [AddCommGroup N] [Module k N]
    [Module (D θ μ) N] [IsScalarTower k (D θ μ) N] :
    Res (ψ i θ μ) (IndK k N (ψ i θ μ)) ≃ₗ[D θ μ] (Fin (n₂).toNat → N) :=
  liftResIndPiEquivRight _
    (cL i μ) (ψ i θ μ) (parabolicRightHom_tmul (CL.qCL KL) Λ i θ μ)
    (cL i μ) (cycLastHom_smul (CL.qCL KL) Λ₁ i μ)
    (ψ i θ μ) (parabolicRightHom_tmul (CL.qCL KL) Λ i θ μ)
    (fun M _ _ => cycEFEquivOfNotMem hstd hP hwf i μ hi M)
    (fun _ _ _ _ _ _ f x => cycEFEquivOfNotMem_map hstd hP hwf i μ f hi x) N

include hstd hP hwf in
/-- **The dimension form of `secondFactorEFEquivOfNotMem`** (Webster, arXiv:1309.3796v3, in the
dimension count of the proof of Proposition 5.5): for `i ∉ μ`,
`dim ₂Eᵢ ₂Fᵢ N = n dim N` over `k`, with `n = ⟨i, λ⟩ ≥ 0`. -/
theorem finrank_secondFactorEF_eq_of_notMem (hi : i ∉ μ) (N : Type u) [AddCommGroup N]
    [Module k N] [Module (D θ μ) N] [IsScalarTower k (D θ μ) N]
    [FiniteDimensional k (RestrictScalars k (D θ μ) N)] :
    (Module.finrank k (RestrictScalars k (D θ μ) (Res (ψ i θ μ) (IndK k N (ψ i θ μ)))) : ℤ) =
      n₂ * Module.finrank k (RestrictScalars k (D θ μ) N) := by
  have e := finrank_restrictScalars_eq_of_equiv_pi (k := k)
    (secondFactorEFEquivOfNotMem hstd hP hwf θ i μ hi N)
  rw [e, Fintype.card_fin]
  push_cast
  rw [Int.toNat_of_nonneg (ip_nonneg_of_notMem i μ hi)]

end Second

end Categorification.Stendhal
