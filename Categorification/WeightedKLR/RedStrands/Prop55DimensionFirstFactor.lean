/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.Prop55CountRedEmpty
import Categorification.WeightedKLR.RedStrands.Prop55DimensionPieces
import Categorification.WeightedKLR.RedStrands.Prop55DimensionTransport
import Categorification.WeightedKLR.RedStrands.BlackModuleCrossFactorCommutation
import Categorification.WeightedKLR.RedStrands.BlackModuleFactorEFOutsideContent
import Categorification.Algebra.InductionAlongFinite

/-!
# Black-last pieces of `S(₁Fᵢ N)` in the dimension count of Proposition 5.5

Webster, arXiv:1309.3796v2, proof of Proposition 5.5, (5.13)–(5.14). For the parameters
`Q = CL.qCL KL` and a finite-dimensional module `N` over the parabolic factor algebra `D_{θ, β}`,
the piece of `S(₁Fᵢ N)` whose last strand is black of colour `j` is computed from the
restrictions `₁E_j ₁Fᵢ N` and `₂E_j ₁Fᵢ N` of the module `₁Fᵢ N` over `D_{i+θ, β}`. These are
rewritten by Theorem 4.31 on the first factor (`factorCrossEquiv`, `factorEFEquiv`,
`factorFEEquiv`, `factorEFEquivOfNotMem`) and by the commutation of the induction on the first
factor with the restriction on the second (`crossFactorEquiv`). The statements match those of
`Prop55DimensionColour` for `Fᵢ S(N)` term by term; for `j = i` the extra term is `n₁ dim S(N)`,
with `n₁ = ⟨i, λ₁⟩` computed in the first factor (weights `Λ ∘ Fin.castSucc`).

* `j ≠ i`: `finrank_fixSub_firstIndStandardT_cross_both` (`j` in both blocks),
  `finrank_fixSub_firstIndStandardT_cross_left` (first block only),
  `finrank_fixSub_firstIndStandardT_cross_right` (second block only);
* `j = i`: `finrank_fixSub_firstIndStandardT_self_both`, `_self_left`, `_self_right`, and
  `finrank_fixSub_firstIndStandardT_self_of_notMem` for `i ∉ θ + β`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory CategoryTheory.Idempotents QuantumGroup QuantumGroup.UDot StringDiagrams
  KLR TwoRep CyclotomicAction DoubleDiagram KL3.Diagram InductionAlong MulOpposite

open scoped Classical

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe w

section FactorFinite

variable {I k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin (ℓ + 1) → I →₀ ℕ}
  {C : CartanDatum I}

/-- The parabolic factor algebra `D_{θ, β}` is finite-dimensional for Rouquier parameters. -/
theorem module_finite_parabolicFactorAlgebra_of_rouquier (hR : IsRouquierQ C Q)
    (θ β : Multiset I) : Module.Finite k (parabolicFactorAlgebra Q Λ θ β) := by
  have := tensorProductAlgebra_finite (Λ ∘ Fin.castSucc) θ hR
  have := CycKLR.module_finite (ν := β) (Q := Q)
    (a := fun i => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i) (fun i j hij => by
      obtain ⟨c, hc, h⟩ := hR.polyInY_leading i j hij
      rw [h]
      exact hc.map Polynomial.C) (fun i => Polynomial.monic_X_pow (Λ (Fin.last ℓ) i))
  infer_instance

/-- Induction of a finite-dimensional module between parabolic factor algebras is
finite-dimensional, for Rouquier parameters. -/
theorem finiteDimensional_indK_parabolicFactor (hR : IsRouquierQ C Q)
    {θ β θ' β' : Multiset I}
    (φ : parabolicFactorAlgebra Q Λ θ β →ₙ+* parabolicFactorAlgebra Q Λ θ' β')
    (M : Type) [AddCommGroup M] [Module k M] [Module (parabolicFactorAlgebra Q Λ θ β) M]
    [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) M] [FiniteDimensional k M] :
    FiniteDimensional k (IndK k M φ) := by
  have := module_finite_parabolicFactorAlgebra_of_rouquier (Λ := Λ) hR θ' β'
  have : Module.Finite (parabolicFactorAlgebra Q Λ θ β) M :=
    Module.Finite.of_restrictScalars_finite k _ M
  exact IndK.finite_restrict k M φ

end FactorFinite

section GeneralProd

variable {I k : Type*} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (θ β : Multiset I)
  (hQ : KLRSymm Q)
  {X N : Type*}
  [AddCommGroup X] [Module k X] [Module (parabolicFactorAlgebra Q Λ θ β) X]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) X]
  [AddCommGroup N] [Module k N] [Module (parabolicFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N]

include hQ in
/-- `dim S(X ⊕ N^{⊕ n}) = dim S X + n dim S N`, with finiteness of `S X` derived from that of
`S(X ⊕ N^{⊕ n})` (Webster, arXiv:1309.3796v2, proof of Proposition 5.5). -/
theorem finrank_parabolicStandard_prod_pi_of_finiteDimensional {n : ℕ}
    (hXN : FiniteDimensional k (ParabolicStandard Q Λ θ β (X × (Fin n → N))))
    [FiniteDimensional k (ParabolicStandard Q Λ θ β N)] :
    Module.finrank k (ParabolicStandard Q Λ θ β (X × (Fin n → N))) =
      Module.finrank k (ParabolicStandard Q Λ θ β X) +
        n * Module.finrank k (ParabolicStandard Q Λ θ β N) := by
  have : FiniteDimensional k (ParabolicStandard Q Λ θ β X) :=
    FiniteDimensional.of_injective
      (parabolicStandardMap Q Λ θ β (LinearMap.inl (parabolicFactorAlgebra Q Λ θ β) X
        (Fin n → N)))
      (parabolicStandardMap_injective Q Λ θ β hQ _ LinearMap.inl_injective)
  have := finiteDimensional_parabolicStandard_pi Q Λ θ β hQ (N := N) n
  rw [finrank_parabolicStandard_prod Q Λ θ β hQ, finrank_parabolicStandard_pi Q Λ θ β hQ]

end GeneralProd

variable {I : Type} {ℓ : ℕ} {Λ : Fin (ℓ + 1) → I →₀ ℕ} {C : CartanDatum I}
  {k : Type} [Field k] {hR : IsRouquierQ C (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k))}

local notation "KL" => (CL.CLScalars.kl : CL.CLScalars C k)
local notation "QL" => CL.qCL KL
local notation "RD₀" => coordinateDatum (Λ ∘ Fin.castSucc) C
local notation "D" => parabolicFactorAlgebra (CL.qCL KL) Λ
local notation "Si" j => (Singleton.singleton j : Multiset I)
local notation "dw₀" => downRightWeight (coordinateDatum (Λ ∘ Fin.castSucc) C)
  (coordinateRedWeights (Λ ∘ Fin.castSucc) C)

-- The weight `Λ ∘ Fin.castSucc` is written out: notation is not hygienic inside binders.
variable {P : Presentation.{0, 0}
    (signature (coordinateDatum (Λ ∘ Fin.castSucc) C)
      (redWeight (cyclotomicCoverWeightDatum (Λ ∘ Fin.castSucc) C))) k}
  (hP : CoverRelsNegligible.{0, 0, w} (Λ ∘ Fin.castSucc) C hR
    (coverDotCentral (Λ ∘ Fin.castSucc) C hR)
    (blockWeight (cyclotomicCoverWeightDatum (Λ ∘ Fin.castSucc) C)
      (cyclotomicCoverHighest (I := I) (ℓ := ℓ)) 0 : I ⊕ Fin ℓ → ℤ) P)
  (hwf : P.WFDom)
  (hQs : KLRSymm (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)))

attribute [local instance] resFactorModuleK resFactor_isScalarTower

section Transport

variable (i : I) (θ β : Multiset I) (N : Type) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ θ β) N]
  [IsScalarTower k (parabolicFactorAlgebra (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ
    θ β) N]

omit [Module k N] [IsScalarTower k
  (parabolicFactorAlgebra (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ θ β) N] in
/-- `S(₁Fᵢ N)` over `T(i + (θ + β))` and over `T((i + θ) + β)` have the same black-last
pieces. -/
theorem finrank_fixSub_firstIndStandardT_eq_parabolicStandardT (b : Option I) :
    Module.finrank k (fixSub k (FirstIndStandardT QL Λ i θ β N hQs)
        (lastStrandIdem QL Λ ((Si i) + (θ + β)) b)) =
      Module.finrank k (fixSub k
          (ParabolicStandardT QL Λ ((Si i) + θ) β (FirstIndLeft QL Λ i θ β N) hQs)
        (lastStrandIdem QL Λ (((Si i) + θ) + β) b)) :=
  (finrank_fixSub_lastStrandIdem_transport (firstInd_blackWeight i θ β)
    (FirstIndStandardT QL Λ i θ β N hQs)
    (ParabolicStandardT QL Λ ((Si i) + θ) β (FirstIndLeft QL Λ i θ β N) hQs)
    (LinearEquiv.refl k (ParabolicStandard QL Λ ((Si i) + θ) β (FirstIndLeft QL Λ i θ β N)))
    (fun _ _ => rfl) b).symm

end Transport

section CrossBoth

variable (i j : I) (θ₀ β₀ : Multiset I) (N : Type) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ
    (({j} : Multiset I) + θ₀) (({j} : Multiset I) + β₀)) N]
  [IsScalarTower k (parabolicFactorAlgebra (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ
    (({j} : Multiset I) + θ₀) (({j} : Multiset I) + β₀)) N]

include hP hwf hQs in
/-- **The black-last piece of `S(₁Fᵢ N)` of colour `j ≠ i`, `j` in both blocks** (Webster,
arXiv:1309.3796v2, proof of Proposition 5.5): it has dimension
`dim S(₁Fᵢ ₁E_j N) + dim S(₁Fᵢ ₂E_j N)`. -/
theorem finrank_fixSub_firstIndStandardT_cross_both (hji : j ≠ i) [FiniteDimensional k N] :
    Module.finrank k (fixSub k (FirstIndStandardT QL Λ i ((Si j) + θ₀) ((Si j) + β₀) N hQs)
        (lastStrandIdem QL Λ ((Si i) + (((Si j) + θ₀) + ((Si j) + β₀))) (some j))) =
      Module.finrank k
          (FirstIndStandardT QL Λ i θ₀ ((Si j) + β₀) (LastResLeft QL Λ j θ₀ β₀ N) hQs) +
        Module.finrank k
          (FirstIndStandardT QL Λ i ((Si j) + θ₀) β₀ (LastResRight QL Λ j θ₀ β₀ N) hQs) := by
  have := finiteDimensional_indK_parabolicFactor (Λ := Λ) hR
    (leftAppendHom QL Λ i ((Si j) + θ₀) ((Si j) + β₀)) N
  rw [finrank_fixSub_firstIndStandardT_eq_parabolicStandardT,
    finrank_fixSub_lastStrandIdem_parabolicStandardT_of_eq (Λ := Λ) hR hQs j
      (cross_content i j θ₀) (rfl : (Si j) + β₀ = (Si j) + β₀)]
  congr 1
  · exact finrank_parabolicStandard_congr QL Λ _ _ hQs
      (factorCrossEquiv (fun _ _ _ => rfl) hP hwf ((Si j) + β₀) i j θ₀ hji N)
  · exact finrank_parabolicStandard_congr QL Λ _ _ hQs
      (crossFactorEquiv QL Λ i j ((Si j) + θ₀) β₀ N)

end CrossBoth

section Left

variable (i j : I) (θ₀ β : Multiset I) (N : Type) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ
    (({j} : Multiset I) + θ₀) β) N]
  [IsScalarTower k (parabolicFactorAlgebra (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ
    (({j} : Multiset I) + θ₀) β) N]

include hP hwf hQs in
/-- **The black-last piece of `S(₁Fᵢ N)` of colour `j ≠ i`, `j` in the first block only**
(Webster, arXiv:1309.3796v2, proof of Proposition 5.5): it has dimension
`dim S(₁Fᵢ ₁E_j N)`. -/
theorem finrank_fixSub_firstIndStandardT_cross_left (hji : j ≠ i) (hj : j ∉ β) :
    Module.finrank k (fixSub k (FirstIndStandardT QL Λ i ((Si j) + θ₀) β N hQs)
        (lastStrandIdem QL Λ ((Si i) + (((Si j) + θ₀) + β)) (some j))) =
      Module.finrank k (FirstIndStandardT QL Λ i θ₀ β (LeftResLeft QL Λ j θ₀ β N) hQs) := by
  rw [finrank_fixSub_firstIndStandardT_eq_parabolicStandardT,
    finrank_fixSub_lastStrandIdem_parabolicStandardT_left_of_eq (Λ := Λ) hQs j
      (cross_content i j θ₀) hj]
  exact finrank_parabolicStandard_congr QL Λ _ _ hQs
    (factorCrossEquiv (fun _ _ _ => rfl) hP hwf β i j θ₀ hji N)

end Left

section Right

variable (i j : I) (θ β₀ : Multiset I) (N : Type) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ
    θ (({j} : Multiset I) + β₀)) N]
  [IsScalarTower k (parabolicFactorAlgebra (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ
    θ (({j} : Multiset I) + β₀)) N]

/-- **The black-last piece of `S(₁Fᵢ N)` of colour `j ≠ i`, `j` in the second block only**
(Webster, arXiv:1309.3796v2, proof of Proposition 5.5): it has dimension
`dim S(₁Fᵢ ₂E_j N)`. -/
theorem finrank_fixSub_firstIndStandardT_cross_right (hji : j ≠ i) (hj : j ∉ θ) :
    Module.finrank k (fixSub k (FirstIndStandardT QL Λ i θ ((Si j) + β₀) N hQs)
        (lastStrandIdem QL Λ ((Si i) + (θ + ((Si j) + β₀))) (some j))) =
      Module.finrank k (FirstIndStandardT QL Λ i θ β₀ (RightResRight QL Λ j θ β₀ N) hQs) := by
  have hj' : j ∉ (Si i) + θ := by
    rw [Multiset.mem_add, Multiset.mem_singleton]
    exact fun h => h.elim hji hj
  rw [finrank_fixSub_firstIndStandardT_eq_parabolicStandardT,
    finrank_fixSub_lastStrandIdem_parabolicStandardT_right_of_eq (Λ := Λ) hQs j
      (rfl : (Si j) + β₀ = (Si j) + β₀) hj']
  exact finrank_parabolicStandard_congr QL Λ _ _ hQs (crossFactorEquiv QL Λ i j θ β₀ N)

end Right

section FactorEF

variable (i : I) (ν β : Multiset I) (N : Type) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ
    (({i} : Multiset I) + ν) β) N]
  [IsScalarTower k (parabolicFactorAlgebra (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ
    (({i} : Multiset I) + ν) β) N]

include hP hwf hQs in
/-- **Standardization of `₁Eᵢ ₁Fᵢ N`** (Webster, arXiv:1309.3796v2, Theorem 4.31 on the first
factor, in the proof of Proposition 5.5): `dim S(₁Eᵢ ₁Fᵢ N) = dim S(₁Fᵢ ₁Eᵢ N) + n₁ dim S(N)`,
`n₁ = ⟨i, λ₁⟩` for the first factor of content `i + ν`, in both signs of `n₁`. -/
theorem finrank_parabolicStandard_factorEF [FiniteDimensional k N] :
    (Module.finrank k (ParabolicStandard QL Λ ((Si i) + ν) β
        (Res (leftAppendHom QL Λ i ((Si i) + ν) β)
          (IndK k N (leftAppendHom QL Λ i ((Si i) + ν) β)))) : ℤ) =
      Module.finrank k (ParabolicStandard QL Λ ((Si i) + ν) β
          (IndK k (Res (leftAppendHom QL Λ i ν β) N) (leftAppendHom QL Λ i ν β))) +
        ip (RD₀) i (dw₀ ((Si i) + ν)) *
          Module.finrank k (ParabolicStandard QL Λ ((Si i) + ν) β N) := by
  have hN : FiniteDimensional k (ParabolicStandard QL Λ ((Si i) + ν) β N) :=
    finiteDimensional_parabolicStandard_of_finiteDimensional (Λ := Λ) hR hQs ((Si i) + ν) β N
  have hFE : FiniteDimensional k (ParabolicStandard QL Λ ((Si i) + ν) β
      (IndK k (Res (leftAppendHom QL Λ i ν β) N) (leftAppendHom QL Λ i ν β))) := by
    have := finiteDimensional_res_of_isScalarTower (parabolicAppendLeft QL Λ i ν β) N
    have := finiteDimensional_indK_parabolicFactor (Λ := Λ) hR (leftAppendHom QL Λ i ν β)
      (Res (leftAppendHom QL Λ i ν β) N)
    exact finiteDimensional_parabolicStandard_of_finiteDimensional (Λ := Λ) hR hQs _ _ _
  rcases le_total 0 (ip (RD₀) i (dw₀ ((Si i) + ν))) with h | h
  · have e := finrank_parabolicStandard_of_equiv_prod_pi QL Λ ((Si i) + ν) β hQs
      (factorEFEquiv (fun _ _ _ => rfl) hP hwf β i ν h N)
    rw [e]
    push_cast
    rw [Int.toNat_of_nonneg h]
  · have e0 := factorFEEquiv (fun _ _ _ => rfl) hP hwf β i ν h N
    have e1 := finrank_parabolicStandard_congr QL Λ ((Si i) + ν) β hQs e0
    have hXN := LinearEquiv.finiteDimensional (LinearEquiv.ofBijective
      (parabolicStandardMap QL Λ ((Si i) + ν) β e0.toLinearMap)
      ⟨parabolicStandardMap_injective QL Λ ((Si i) + ν) β hQs _ e0.injective,
        parabolicStandardMap_surjective QL Λ ((Si i) + ν) β hQs _ e0.surjective⟩)
    have e := congrArg (Nat.cast : ℕ → ℤ) (e1.trans
      (finrank_parabolicStandard_prod_pi_of_finiteDimensional QL Λ ((Si i) + ν) β hQs hXN))
    push_cast at e
    have ht : (((-ip (RD₀) i (dw₀ ((Si i) + ν))).toNat : ℕ) : ℤ) =
        -ip (RD₀) i (dw₀ ((Si i) + ν)) := Int.toNat_of_nonneg (neg_nonneg.mpr h)
    linear_combination -e -
      (Module.finrank k (ParabolicStandard QL Λ ((Si i) + ν) β N) : ℤ) * ht

end FactorEF

section FactorEFNotMem

variable (i : I) (θ β : Multiset I) (N : Type) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ θ β) N]
  [IsScalarTower k (parabolicFactorAlgebra (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ
    θ β) N]

include hP hwf hQs in
/-- **Standardization of `₁Eᵢ ₁Fᵢ N` for `i ∉ θ`** (Webster, arXiv:1309.3796v2, Theorem 4.31
on the first factor with `₁Eᵢ N = 0`, in the proof of Proposition 5.5):
`dim S(₁Eᵢ ₁Fᵢ N) = n₁ dim S(N)`, `n₁ = ⟨i, λ₁⟩` for the first factor of content `θ`. -/
theorem finrank_parabolicStandard_factorEF_of_notMem (hi : i ∉ θ) [FiniteDimensional k N] :
    (Module.finrank k (ParabolicStandard QL Λ θ β
        (Res (leftAppendHom QL Λ i θ β) (IndK k N (leftAppendHom QL Λ i θ β)))) : ℤ) =
      ip (RD₀) i (dw₀ θ) * Module.finrank k (ParabolicStandard QL Λ θ β N) := by
  have := finiteDimensional_parabolicStandard_of_finiteDimensional (Λ := Λ) hR hQs θ β N
  rw [finrank_parabolicStandard_congr QL Λ _ _ hQs
      (factorEFEquivOfNotMem (fun _ _ _ => rfl) hP hwf β i θ hi N),
    finrank_parabolicStandard_pi QL Λ _ _ hQs]
  push_cast
  rw [Int.toNat_of_nonneg (ip_nonneg_of_notMem i θ hi)]

end FactorEFNotMem

section BothSelf

variable (i : I) (θ₀ β₀ : Multiset I) (N : Type) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ
    (({i} : Multiset I) + θ₀) (({i} : Multiset I) + β₀)) N]
  [IsScalarTower k (parabolicFactorAlgebra (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ
    (({i} : Multiset I) + θ₀) (({i} : Multiset I) + β₀)) N]

include hP hwf hQs in
/-- **The black-last piece of `S(₁Fᵢ N)` of colour `i`, `i` in both blocks** (Webster,
arXiv:1309.3796v2, proof of Proposition 5.5): it has dimension
`dim S(₁Fᵢ ₁Eᵢ N) + dim S(₁Fᵢ ₂Eᵢ N) + n₁ dim S(N)`, `n₁ = ⟨i, λ₁⟩` for the first factor of
content `i + θ₀`. -/
theorem finrank_fixSub_firstIndStandardT_self_both [FiniteDimensional k N] :
    (Module.finrank k (fixSub k (FirstIndStandardT QL Λ i ((Si i) + θ₀) ((Si i) + β₀) N hQs)
        (lastStrandIdem QL Λ ((Si i) + (((Si i) + θ₀) + ((Si i) + β₀))) (some i))) : ℤ) =
      Module.finrank k
          (FirstIndStandardT QL Λ i θ₀ ((Si i) + β₀) (LastResLeft QL Λ i θ₀ β₀ N) hQs) +
        Module.finrank k
          (FirstIndStandardT QL Λ i ((Si i) + θ₀) β₀ (LastResRight QL Λ i θ₀ β₀ N) hQs) +
        ip (RD₀) i (dw₀ ((Si i) + θ₀)) *
          Module.finrank k (ParabolicStandard QL Λ ((Si i) + θ₀) ((Si i) + β₀) N) := by
  have := finiteDimensional_indK_parabolicFactor (Λ := Λ) hR
    (leftAppendHom QL Λ i ((Si i) + θ₀) ((Si i) + β₀)) N
  have hp := finrank_fixSub_lastStrandIdem_parabolicStandardT_of_eq (Λ := Λ) hR hQs i
    (rfl : (Si i) + ((Si i) + θ₀) = (Si i) + ((Si i) + θ₀))
    (rfl : (Si i) + β₀ = (Si i) + β₀) (FirstIndLeft QL Λ i ((Si i) + θ₀) ((Si i) + β₀) N)
  have h1 := finrank_parabolicStandard_factorEF hP hwf hQs i θ₀ ((Si i) + β₀) N
  have h1' : (Module.finrank k (ParabolicStandard QL Λ ((Si i) + θ₀) ((Si i) + β₀)
      (Res (leftAppendHomOfEq QL Λ i (rfl : (Si i) + ((Si i) + θ₀) = (Si i) + ((Si i) + θ₀))
        ((Si i) + β₀)) (FirstIndLeft QL Λ i ((Si i) + θ₀) ((Si i) + β₀) N))) : ℤ) =
      Module.finrank k
          (FirstIndStandardT QL Λ i θ₀ ((Si i) + β₀) (LastResLeft QL Λ i θ₀ β₀ N) hQs) +
        ip (RD₀) i (dw₀ ((Si i) + θ₀)) *
          Module.finrank k (ParabolicStandard QL Λ ((Si i) + θ₀) ((Si i) + β₀) N) := h1
  have h2 : Module.finrank k (ParabolicStandard QL Λ ((Si i) + ((Si i) + θ₀)) β₀
      (Res (parabolicRightHomOfEq QL Λ i (rfl : (Si i) + β₀ = (Si i) + β₀)
        ((Si i) + ((Si i) + θ₀))) (FirstIndLeft QL Λ i ((Si i) + θ₀) ((Si i) + β₀) N))) =
      Module.finrank k
        (FirstIndStandardT QL Λ i ((Si i) + θ₀) β₀ (LastResRight QL Λ i θ₀ β₀ N) hQs) :=
    finrank_parabolicStandard_congr QL Λ _ _ hQs
      (crossFactorEquiv QL Λ i i ((Si i) + θ₀) β₀ N)
  rw [finrank_fixSub_firstIndStandardT_eq_parabolicStandardT, hp]
  push_cast
  rw [h1', h2]
  ring

end BothSelf

section LeftSelf

variable (i : I) (θ₀ β : Multiset I) (N : Type) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ
    (({i} : Multiset I) + θ₀) β) N]
  [IsScalarTower k (parabolicFactorAlgebra (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ
    (({i} : Multiset I) + θ₀) β) N]

include hP hwf hQs in
/-- **The black-last piece of `S(₁Fᵢ N)` of colour `i`, `i` in the first block only**
(Webster, arXiv:1309.3796v2, proof of Proposition 5.5): it has dimension
`dim S(₁Fᵢ ₁Eᵢ N) + n₁ dim S(N)`, `n₁ = ⟨i, λ₁⟩` for the first factor of content `i + θ₀`. -/
theorem finrank_fixSub_firstIndStandardT_self_left (hi : i ∉ β) [FiniteDimensional k N] :
    (Module.finrank k (fixSub k (FirstIndStandardT QL Λ i ((Si i) + θ₀) β N hQs)
        (lastStrandIdem QL Λ ((Si i) + (((Si i) + θ₀) + β)) (some i))) : ℤ) =
      Module.finrank k (FirstIndStandardT QL Λ i θ₀ β (LeftResLeft QL Λ i θ₀ β N) hQs) +
        ip (RD₀) i (dw₀ ((Si i) + θ₀)) *
          Module.finrank k (ParabolicStandard QL Λ ((Si i) + θ₀) β N) := by
  have hp := finrank_fixSub_lastStrandIdem_parabolicStandardT_left QL Λ i ((Si i) + θ₀) β
    (FirstIndLeft QL Λ i ((Si i) + θ₀) β N) hQs hi
  have h1 := finrank_parabolicStandard_factorEF hP hwf hQs i θ₀ β N
  rw [finrank_fixSub_firstIndStandardT_eq_parabolicStandardT, hp]
  exact h1

end LeftSelf

section RightSelf

variable (i : I) (θ β₀ : Multiset I) (N : Type) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ
    θ (({i} : Multiset I) + β₀)) N]
  [IsScalarTower k (parabolicFactorAlgebra (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ
    θ (({i} : Multiset I) + β₀)) N]

include hP hwf hQs in
/-- **The black-last piece of `S(₁Fᵢ N)` of colour `i`, `i` in the second block only**
(Webster, arXiv:1309.3796v2, proof of Proposition 5.5): it has dimension
`dim S(₁Fᵢ ₂Eᵢ N) + n₁ dim S(N)`, `n₁ = ⟨i, λ₁⟩` for the first factor of content `θ`. -/
theorem finrank_fixSub_firstIndStandardT_self_right (hi : i ∉ θ) [FiniteDimensional k N] :
    (Module.finrank k (fixSub k (FirstIndStandardT QL Λ i θ ((Si i) + β₀) N hQs)
        (lastStrandIdem QL Λ ((Si i) + (θ + ((Si i) + β₀))) (some i))) : ℤ) =
      Module.finrank k (FirstIndStandardT QL Λ i θ β₀ (RightResRight QL Λ i θ β₀ N) hQs) +
        ip (RD₀) i (dw₀ θ) * Module.finrank k (ParabolicStandard QL Λ θ ((Si i) + β₀) N) := by
  have := finiteDimensional_indK_parabolicFactor (Λ := Λ) hR
    (leftAppendHom QL Λ i θ ((Si i) + β₀)) N
  have hp := finrank_fixSub_lastStrandIdem_parabolicStandardT_of_eq (Λ := Λ) hR hQs i
    (rfl : (Si i) + θ = (Si i) + θ)
    (rfl : (Si i) + β₀ = (Si i) + β₀) (FirstIndLeft QL Λ i θ ((Si i) + β₀) N)
  have h1 := finrank_parabolicStandard_factorEF_of_notMem hP hwf hQs i θ ((Si i) + β₀) N hi
  have h1' : (Module.finrank k (ParabolicStandard QL Λ θ ((Si i) + β₀)
      (Res (leftAppendHomOfEq QL Λ i (rfl : (Si i) + θ = (Si i) + θ) ((Si i) + β₀))
        (FirstIndLeft QL Λ i θ ((Si i) + β₀) N))) : ℤ) =
      ip (RD₀) i (dw₀ θ) * Module.finrank k (ParabolicStandard QL Λ θ ((Si i) + β₀) N) := h1
  have h2 : Module.finrank k (ParabolicStandard QL Λ ((Si i) + θ) β₀
      (Res (parabolicRightHomOfEq QL Λ i (rfl : (Si i) + β₀ = (Si i) + β₀) ((Si i) + θ))
        (FirstIndLeft QL Λ i θ ((Si i) + β₀) N))) =
      Module.finrank k
        (FirstIndStandardT QL Λ i θ β₀ (RightResRight QL Λ i θ β₀ N) hQs) :=
    finrank_parabolicStandard_congr QL Λ _ _ hQs (crossFactorEquiv QL Λ i i θ β₀ N)
  rw [finrank_fixSub_firstIndStandardT_eq_parabolicStandardT, hp]
  push_cast
  rw [h1', h2]
  ring

end RightSelf

section NotMemSelf

variable (i : I) (θ β : Multiset I) (N : Type) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ θ β) N]
  [IsScalarTower k (parabolicFactorAlgebra (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ
    θ β) N]

include hP hwf hQs in
/-- **The black-last piece of `S(₁Fᵢ N)` of colour `i ∉ θ + β`** (Webster,
arXiv:1309.3796v2, proof of Proposition 5.5): it has dimension `n₁ dim S(N)`,
`n₁ = ⟨i, λ₁⟩` for the first factor of content `θ`. -/
theorem finrank_fixSub_firstIndStandardT_self_of_notMem (hi : i ∉ θ + β)
    [FiniteDimensional k N] :
    (Module.finrank k (fixSub k (FirstIndStandardT QL Λ i θ β N hQs)
        (lastStrandIdem QL Λ ((Si i) + (θ + β)) (some i))) : ℤ) =
      ip (RD₀) i (dw₀ θ) * Module.finrank k (ParabolicStandard QL Λ θ β N) := by
  have hiθ : i ∉ θ := fun h => hi (Multiset.mem_add.mpr (Or.inl h))
  have hiβ : i ∉ β := fun h => hi (Multiset.mem_add.mpr (Or.inr h))
  have hp := finrank_fixSub_lastStrandIdem_parabolicStandardT_left_of_eq (Λ := Λ) hQs i
    (rfl : (Si i) + θ = (Si i) + θ) hiβ (FirstIndLeft QL Λ i θ β N)
  have h1 := finrank_parabolicStandard_factorEF_of_notMem hP hwf hQs i θ β N hiθ
  rw [finrank_fixSub_firstIndStandardT_eq_parabolicStandardT, hp]
  exact h1

end NotMemSelf

end Categorification.Stendhal
