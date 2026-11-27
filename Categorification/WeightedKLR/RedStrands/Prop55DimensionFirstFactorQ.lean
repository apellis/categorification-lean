/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.Prop55DimensionFirstFactor
import Categorification.WeightedKLR.RedStrands.Prop55CountRedEmpty
import Categorification.WeightedKLR.RedStrands.Prop55DimensionPieces
import Categorification.WeightedKLR.RedStrands.Prop55DimensionTransport
import Categorification.WeightedKLR.RedStrands.BlackModuleCrossFactorCommutationQ
import Categorification.WeightedKLR.RedStrands.BlackModuleFactorEFOutsideContentQ
import Categorification.Algebra.InductionAlongFinite

/-!
# Black-last pieces of `S(₁Fᵢ N)` in the dimension count of Proposition 5.5

Webster, arXiv:1309.3796v2, proof of Proposition 5.5, (5.13)–(5.14). For Rouquier
parameters `Q` and a finite-dimensional module `N` over the parabolic factor algebra `D_{θ, β}`,
the piece of `S(₁Fᵢ N)` whose last strand is black of colour `j` is computed from the
restrictions `₁E_j ₁Fᵢ N` and `₂E_j ₁Fᵢ N` of the module `₁Fᵢ N` over `D_{i+θ, β}`. These are
rewritten by Theorem 4.31 on the first factor (`factorCrossEquivQ`, `factorEFEquivQ`,
`factorFEEquivQ`, `factorEFEquivOfNotMemQ`) and by the commutation of the induction on the first
factor with the restriction on the second (`crossFactorEquivQ`). The statements match those of
`Prop55DimensionColour` for `Fᵢ S(N)` term by term; for `j = i` the extra term is `n₁ dim S(N)`,
with `n₁ = ⟨i, λ₁⟩` computed in the first factor (weights `Λ ∘ Fin.castSucc`).

* `j ≠ i`: `finrank_fixSub_firstIndStandardT_cross_bothQ` (`j` in both blocks),
  `finrank_fixSub_firstIndStandardT_cross_leftQ` (first block only),
  `finrank_fixSub_firstIndStandardT_cross_rightQ` (second block only);
* `j = i`: `finrank_fixSub_firstIndStandardT_self_bothQ`, `_self_left`, `_self_right`, and
  `finrank_fixSub_firstIndStandardT_self_of_notMemQ` for `i ∉ θ + β`.

This is the version of `Prop55DimensionFirstFactor` for every Rouquier parameter `Q`: the black
strands carry the relations of Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3, Definition 1.1, `r = 1`)
instead of the KL III relations. Each declaration carries the suffix `Q`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory CategoryTheory.Idempotents QuantumGroup QuantumGroup.UDot StringDiagrams
  KLR TwoRep CyclotomicAction DoubleDiagram KL3.Diagram InductionAlong MulOpposite

open scoped Classical

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe w

variable {I : Type} {ℓ : ℕ} {Λ : Fin (ℓ + 1) → I →₀ ℕ} {C : CartanDatum I}
  {k : Type} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {hR : IsRouquierQ C Q}

local notation "QL" => Q
local notation "RD₀" => coordinateDatum (Λ ∘ Fin.castSucc) C
local notation "D" => parabolicFactorAlgebra Q Λ
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
  (hQs : KLRSymm Q)

attribute [local instance] resFactorModuleK resFactor_isScalarTower

section Transport

variable (i : I) (θ β : Multiset I) (N : Type) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ
    θ β) N]

omit [Module k N] [IsScalarTower k
  (parabolicFactorAlgebra Q Λ θ β) N] in
/-- `S(₁Fᵢ N)` over `T(i + (θ + β))` and over `T((i + θ) + β)` have the same black-last
pieces. -/
theorem finrank_fixSub_firstIndStandardT_eq_parabolicStandardTQ (b : Option I) :
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
  [Module (parabolicFactorAlgebra Q Λ
    (({j} : Multiset I) + θ₀) (({j} : Multiset I) + β₀)) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ
    (({j} : Multiset I) + θ₀) (({j} : Multiset I) + β₀)) N]

include hP hwf hQs in
/-- **The black-last piece of `S(₁Fᵢ N)` of colour `j ≠ i`, `j` in both blocks** (Webster,
arXiv:1309.3796v2, proof of Proposition 5.5): it has dimension
`dim S(₁Fᵢ ₁E_j N) + dim S(₁Fᵢ ₂E_j N)`. -/
theorem finrank_fixSub_firstIndStandardT_cross_bothQ (hji : j ≠ i) [FiniteDimensional k N] :
    Module.finrank k (fixSub k (FirstIndStandardT QL Λ i ((Si j) + θ₀) ((Si j) + β₀) N hQs)
        (lastStrandIdem QL Λ ((Si i) + (((Si j) + θ₀) + ((Si j) + β₀))) (some j))) =
      Module.finrank k
          (FirstIndStandardT QL Λ i θ₀ ((Si j) + β₀) (LastResLeft QL Λ j θ₀ β₀ N) hQs) +
        Module.finrank k
          (FirstIndStandardT QL Λ i ((Si j) + θ₀) β₀ (LastResRight QL Λ j θ₀ β₀ N) hQs) := by
  have := finiteDimensional_indK_parabolicFactor (Λ := Λ) hR
    (leftAppendHom QL Λ i ((Si j) + θ₀) ((Si j) + β₀)) N
  rw [finrank_fixSub_firstIndStandardT_eq_parabolicStandardTQ,
    finrank_fixSub_lastStrandIdem_parabolicStandardT_of_eq (Λ := Λ) hR hQs j
      (cross_content i j θ₀) (rfl : (Si j) + β₀ = (Si j) + β₀)]
  congr 1
  · exact finrank_parabolicStandard_congr QL Λ _ _ hQs
      (factorCrossEquivQ hP hwf ((Si j) + β₀) i j θ₀ hji N)
  · exact finrank_parabolicStandard_congr QL Λ _ _ hQs
      (crossFactorEquivQ QL Λ i j ((Si j) + θ₀) β₀ N)

end CrossBoth

section Left

variable (i j : I) (θ₀ β : Multiset I) (N : Type) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra Q Λ
    (({j} : Multiset I) + θ₀) β) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ
    (({j} : Multiset I) + θ₀) β) N]

include hP hwf hQs in
/-- **The black-last piece of `S(₁Fᵢ N)` of colour `j ≠ i`, `j` in the first block only**
(Webster, arXiv:1309.3796v2, proof of Proposition 5.5): it has dimension
`dim S(₁Fᵢ ₁E_j N)`. -/
theorem finrank_fixSub_firstIndStandardT_cross_leftQ (hji : j ≠ i) (hj : j ∉ β) :
    Module.finrank k (fixSub k (FirstIndStandardT QL Λ i ((Si j) + θ₀) β N hQs)
        (lastStrandIdem QL Λ ((Si i) + (((Si j) + θ₀) + β)) (some j))) =
      Module.finrank k (FirstIndStandardT QL Λ i θ₀ β (LeftResLeft QL Λ j θ₀ β N) hQs) := by
  rw [finrank_fixSub_firstIndStandardT_eq_parabolicStandardTQ,
    finrank_fixSub_lastStrandIdem_parabolicStandardT_left_of_eq (Λ := Λ) hQs j
      (cross_content i j θ₀) hj]
  exact finrank_parabolicStandard_congr QL Λ _ _ hQs
    (factorCrossEquivQ hP hwf β i j θ₀ hji N)

end Left

section Right

variable (i j : I) (θ β₀ : Multiset I) (N : Type) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra Q Λ
    θ (({j} : Multiset I) + β₀)) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ
    θ (({j} : Multiset I) + β₀)) N]

/-- **The black-last piece of `S(₁Fᵢ N)` of colour `j ≠ i`, `j` in the second block only**
(Webster, arXiv:1309.3796v2, proof of Proposition 5.5): it has dimension
`dim S(₁Fᵢ ₂E_j N)`. -/
theorem finrank_fixSub_firstIndStandardT_cross_rightQ (hji : j ≠ i) (hj : j ∉ θ) :
    Module.finrank k (fixSub k (FirstIndStandardT QL Λ i θ ((Si j) + β₀) N hQs)
        (lastStrandIdem QL Λ ((Si i) + (θ + ((Si j) + β₀))) (some j))) =
      Module.finrank k (FirstIndStandardT QL Λ i θ β₀ (RightResRight QL Λ j θ β₀ N) hQs) := by
  have hj' : j ∉ (Si i) + θ := by
    rw [Multiset.mem_add, Multiset.mem_singleton]
    exact fun h => h.elim hji hj
  rw [finrank_fixSub_firstIndStandardT_eq_parabolicStandardTQ,
    finrank_fixSub_lastStrandIdem_parabolicStandardT_right_of_eq (Λ := Λ) hQs j
      (rfl : (Si j) + β₀ = (Si j) + β₀) hj']
  exact finrank_parabolicStandard_congr QL Λ _ _ hQs (crossFactorEquivQ QL Λ i j θ β₀ N)

end Right

section FactorEF

variable (i : I) (ν β : Multiset I) (N : Type) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra Q Λ
    (({i} : Multiset I) + ν) β) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ
    (({i} : Multiset I) + ν) β) N]

include hP hwf hQs in
/-- **Standardization of `₁Eᵢ ₁Fᵢ N`** (Webster, arXiv:1309.3796v2, Theorem 4.31 on the first
factor, in the proof of Proposition 5.5): `dim S(₁Eᵢ ₁Fᵢ N) = dim S(₁Fᵢ ₁Eᵢ N) + n₁ dim S(N)`,
`n₁ = ⟨i, λ₁⟩` for the first factor of content `i + ν`, in both signs of `n₁`. -/
theorem finrank_parabolicStandard_factorEFQ [FiniteDimensional k N] :
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
      (factorEFEquivQ hP hwf β i ν h N)
    rw [e]
    push_cast
    rw [Int.toNat_of_nonneg h]
  · have e0 := factorFEEquivQ hP hwf β i ν h N
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
  [Module (parabolicFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ
    θ β) N]

include hP hwf hQs in
/-- **Standardization of `₁Eᵢ ₁Fᵢ N` for `i ∉ θ`** (Webster, arXiv:1309.3796v2, Theorem 4.31
on the first factor with `₁Eᵢ N = 0`, in the proof of Proposition 5.5):
`dim S(₁Eᵢ ₁Fᵢ N) = n₁ dim S(N)`, `n₁ = ⟨i, λ₁⟩` for the first factor of content `θ`. -/
theorem finrank_parabolicStandard_factorEF_of_notMemQ (hi : i ∉ θ) [FiniteDimensional k N] :
    (Module.finrank k (ParabolicStandard QL Λ θ β
        (Res (leftAppendHom QL Λ i θ β) (IndK k N (leftAppendHom QL Λ i θ β)))) : ℤ) =
      ip (RD₀) i (dw₀ θ) * Module.finrank k (ParabolicStandard QL Λ θ β N) := by
  have := finiteDimensional_parabolicStandard_of_finiteDimensional (Λ := Λ) hR hQs θ β N
  rw [finrank_parabolicStandard_congr QL Λ _ _ hQs
      (factorEFEquivOfNotMemQ hP hwf β i θ hi N),
    finrank_parabolicStandard_pi QL Λ _ _ hQs]
  push_cast
  rw [Int.toNat_of_nonneg (ip_nonneg_of_notMem i θ hi)]

end FactorEFNotMem

section BothSelf

variable (i : I) (θ₀ β₀ : Multiset I) (N : Type) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra Q Λ
    (({i} : Multiset I) + θ₀) (({i} : Multiset I) + β₀)) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ
    (({i} : Multiset I) + θ₀) (({i} : Multiset I) + β₀)) N]

include hP hwf hQs in
/-- **The black-last piece of `S(₁Fᵢ N)` of colour `i`, `i` in both blocks** (Webster,
arXiv:1309.3796v2, proof of Proposition 5.5): it has dimension
`dim S(₁Fᵢ ₁Eᵢ N) + dim S(₁Fᵢ ₂Eᵢ N) + n₁ dim S(N)`, `n₁ = ⟨i, λ₁⟩` for the first factor of
content `i + θ₀`. -/
theorem finrank_fixSub_firstIndStandardT_self_bothQ [FiniteDimensional k N] :
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
  have h1 := finrank_parabolicStandard_factorEFQ hP hwf hQs i θ₀ ((Si i) + β₀) N
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
      (crossFactorEquivQ QL Λ i i ((Si i) + θ₀) β₀ N)
  rw [finrank_fixSub_firstIndStandardT_eq_parabolicStandardTQ, hp]
  push_cast
  rw [h1', h2]
  ring

end BothSelf

section LeftSelf

variable (i : I) (θ₀ β : Multiset I) (N : Type) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra Q Λ
    (({i} : Multiset I) + θ₀) β) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ
    (({i} : Multiset I) + θ₀) β) N]

include hP hwf hQs in
/-- **The black-last piece of `S(₁Fᵢ N)` of colour `i`, `i` in the first block only**
(Webster, arXiv:1309.3796v2, proof of Proposition 5.5): it has dimension
`dim S(₁Fᵢ ₁Eᵢ N) + n₁ dim S(N)`, `n₁ = ⟨i, λ₁⟩` for the first factor of content `i + θ₀`. -/
theorem finrank_fixSub_firstIndStandardT_self_leftQ (hi : i ∉ β) [FiniteDimensional k N] :
    (Module.finrank k (fixSub k (FirstIndStandardT QL Λ i ((Si i) + θ₀) β N hQs)
        (lastStrandIdem QL Λ ((Si i) + (((Si i) + θ₀) + β)) (some i))) : ℤ) =
      Module.finrank k (FirstIndStandardT QL Λ i θ₀ β (LeftResLeft QL Λ i θ₀ β N) hQs) +
        ip (RD₀) i (dw₀ ((Si i) + θ₀)) *
          Module.finrank k (ParabolicStandard QL Λ ((Si i) + θ₀) β N) := by
  have hp := finrank_fixSub_lastStrandIdem_parabolicStandardT_left QL Λ i ((Si i) + θ₀) β
    (FirstIndLeft QL Λ i ((Si i) + θ₀) β N) hQs hi
  have h1 := finrank_parabolicStandard_factorEFQ hP hwf hQs i θ₀ β N
  rw [finrank_fixSub_firstIndStandardT_eq_parabolicStandardTQ, hp]
  exact h1

end LeftSelf

section RightSelf

variable (i : I) (θ β₀ : Multiset I) (N : Type) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra Q Λ
    θ (({i} : Multiset I) + β₀)) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ
    θ (({i} : Multiset I) + β₀)) N]

include hP hwf hQs in
/-- **The black-last piece of `S(₁Fᵢ N)` of colour `i`, `i` in the second block only**
(Webster, arXiv:1309.3796v2, proof of Proposition 5.5): it has dimension
`dim S(₁Fᵢ ₂Eᵢ N) + n₁ dim S(N)`, `n₁ = ⟨i, λ₁⟩` for the first factor of content `θ`. -/
theorem finrank_fixSub_firstIndStandardT_self_rightQ (hi : i ∉ θ) [FiniteDimensional k N] :
    (Module.finrank k (fixSub k (FirstIndStandardT QL Λ i θ ((Si i) + β₀) N hQs)
        (lastStrandIdem QL Λ ((Si i) + (θ + ((Si i) + β₀))) (some i))) : ℤ) =
      Module.finrank k (FirstIndStandardT QL Λ i θ β₀ (RightResRight QL Λ i θ β₀ N) hQs) +
        ip (RD₀) i (dw₀ θ) * Module.finrank k (ParabolicStandard QL Λ θ ((Si i) + β₀) N) := by
  have := finiteDimensional_indK_parabolicFactor (Λ := Λ) hR
    (leftAppendHom QL Λ i θ ((Si i) + β₀)) N
  have hp := finrank_fixSub_lastStrandIdem_parabolicStandardT_of_eq (Λ := Λ) hR hQs i
    (rfl : (Si i) + θ = (Si i) + θ)
    (rfl : (Si i) + β₀ = (Si i) + β₀) (FirstIndLeft QL Λ i θ ((Si i) + β₀) N)
  have h1 := finrank_parabolicStandard_factorEF_of_notMemQ hP hwf hQs i θ ((Si i) + β₀) N hi
  have h1' : (Module.finrank k (ParabolicStandard QL Λ θ ((Si i) + β₀)
      (Res (leftAppendHomOfEq QL Λ i (rfl : (Si i) + θ = (Si i) + θ) ((Si i) + β₀))
        (FirstIndLeft QL Λ i θ ((Si i) + β₀) N))) : ℤ) =
      ip (RD₀) i (dw₀ θ) * Module.finrank k (ParabolicStandard QL Λ θ ((Si i) + β₀) N) := h1
  have h2 : Module.finrank k (ParabolicStandard QL Λ ((Si i) + θ) β₀
      (Res (parabolicRightHomOfEq QL Λ i (rfl : (Si i) + β₀ = (Si i) + β₀) ((Si i) + θ))
        (FirstIndLeft QL Λ i θ ((Si i) + β₀) N))) =
      Module.finrank k
        (FirstIndStandardT QL Λ i θ β₀ (RightResRight QL Λ i θ β₀ N) hQs) :=
    finrank_parabolicStandard_congr QL Λ _ _ hQs (crossFactorEquivQ QL Λ i i θ β₀ N)
  rw [finrank_fixSub_firstIndStandardT_eq_parabolicStandardTQ, hp]
  push_cast
  rw [h1', h2]
  ring

end RightSelf

section NotMemSelf

variable (i : I) (θ β : Multiset I) (N : Type) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ
    θ β) N]

include hP hwf hQs in
/-- **The black-last piece of `S(₁Fᵢ N)` of colour `i ∉ θ + β`** (Webster,
arXiv:1309.3796v2, proof of Proposition 5.5): it has dimension `n₁ dim S(N)`,
`n₁ = ⟨i, λ₁⟩` for the first factor of content `θ`. -/
theorem finrank_fixSub_firstIndStandardT_self_of_notMemQ (hi : i ∉ θ + β)
    [FiniteDimensional k N] :
    (Module.finrank k (fixSub k (FirstIndStandardT QL Λ i θ β N hQs)
        (lastStrandIdem QL Λ ((Si i) + (θ + β)) (some i))) : ℤ) =
      ip (RD₀) i (dw₀ θ) * Module.finrank k (ParabolicStandard QL Λ θ β N) := by
  have hiθ : i ∉ θ := fun h => hi (Multiset.mem_add.mpr (Or.inl h))
  have hiβ : i ∉ β := fun h => hi (Multiset.mem_add.mpr (Or.inr h))
  have hp := finrank_fixSub_lastStrandIdem_parabolicStandardT_left_of_eq (Λ := Λ) hQs i
    (rfl : (Si i) + θ = (Si i) + θ) hiβ (FirstIndLeft QL Λ i θ β N)
  have h1 := finrank_parabolicStandard_factorEF_of_notMemQ hP hwf hQs i θ β N hiθ
  rw [finrank_fixSub_firstIndStandardT_eq_parabolicStandardTQ, hp]
  exact h1

end NotMemSelf

end Categorification.Stendhal
