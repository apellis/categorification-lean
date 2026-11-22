/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.Prop55DimensionFirstFactor
import Categorification.WeightedKLR.RedStrands.Prop55DimensionRed
import Categorification.WeightedKLR.RedStrands.BlackModuleSecondFactorCommutation

/-!
# Black-last pieces of `S(₂Fᵢ N)` in the dimension count of Proposition 5.5

Webster, arXiv:1309.3796v2, proof of Proposition 5.5, (5.13)–(5.14). For the parameters
`Q = CL.qCL KL` and a finite-dimensional module `N` over the parabolic factor algebra `D_{θ, β}`,
the piece of `S(₂Fᵢ N)` whose last strand is black of colour `j` is computed from the
restrictions `₁E_j ₂Fᵢ N` and `₂E_j ₂Fᵢ N` of the module `₂Fᵢ N` over `D_{θ, i+β}`. These are
rewritten by the commutation of the induction on the second factor with the restriction on the
first (`crossFactorEquivRight`) and by Theorem 4.31 on the second factor
(`secondFactorCrossEquiv`, `secondFactorEFEquiv`, `secondFactorFEEquiv`,
`secondFactorEFEquivOfNotMem`). The statements match those of `Prop55DimensionColour` for
`Fᵢ S(N)` term by term; for `j = i` the extra term is `n₂ dim S(N)`, with `n₂ = ⟨i, λ₂⟩`
computed in the cyclotomic second factor (the one-colour weight `Λ (Fin.last ℓ)`).

* `j ≠ i`: `finrank_fixSub_lastIndStandardT_cross_both` (`j` in both blocks),
  `finrank_fixSub_lastIndStandardT_cross_left` (first block only),
  `finrank_fixSub_lastIndStandardT_cross_right` (second block only);
* `j = i`: `finrank_fixSub_lastIndStandardT_self_both`, `_self_left`, `_self_right`, and
  `finrank_fixSub_lastIndStandardT_self_of_notMem` for `i ∉ θ + β`.
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
  {k : Type} [Field k] {hR : IsRouquierQ C (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k))}

local notation "KL" => (CL.CLScalars.kl : CL.CLScalars C k)
local notation "QL" => CL.qCL KL
local notation "RD₁" => coordinateDatum (fun _ : Fin 1 => Λ (Fin.last ℓ)) C
local notation "Si" j => (Singleton.singleton j : Multiset I)
local notation "dw₁" => downRightWeight (coordinateDatum (fun _ : Fin 1 => Λ (Fin.last ℓ)) C)
  (coordinateRedWeights (fun _ : Fin 1 => Λ (Fin.last ℓ)) C)

-- The weight `Λ (Fin.last ℓ)` is written out: notation is not hygienic inside binders.
variable {P : Presentation.{0, 0}
    (signature (coordinateDatum (fun _ : Fin 1 => Λ (Fin.last ℓ)) C)
      (redWeight (cyclotomicCoverWeightDatum (fun _ : Fin 1 => Λ (Fin.last ℓ)) C))) k}
  (hP : CoverRelsNegligible.{0, 0, w} (fun _ : Fin 1 => Λ (Fin.last ℓ)) C hR
    (coverDotCentral (fun _ : Fin 1 => Λ (Fin.last ℓ)) C hR)
    (blockWeight (cyclotomicCoverWeightDatum (fun _ : Fin 1 => Λ (Fin.last ℓ)) C)
      (cyclotomicCoverHighest (I := I) (ℓ := 1)) 0 : I ⊕ Fin 1 → ℤ) P)
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
/-- `S(₂Fᵢ N)` over `T(i + (θ + β))` and over `T(θ + (i + β))` have the same black-last
pieces. -/
theorem finrank_fixSub_lastIndStandardT_eq_parabolicStandardT (b : Option I) :
    Module.finrank k (fixSub k (LastIndStandardT QL Λ i θ β N hQs)
        (lastStrandIdem QL Λ ((Si i) + (θ + β)) b)) =
      Module.finrank k (fixSub k
          (ParabolicStandardT QL Λ θ ((Si i) + β) (LastIndRight QL Λ i θ β N) hQs)
        (lastStrandIdem QL Λ (θ + ((Si i) + β)) b)) :=
  (finrank_fixSub_lastStrandIdem_transport (Q := QL) (Λ := Λ) (lastInd_blackWeight i θ β)
    (LastIndStandardT QL Λ i θ β N hQs)
    (ParabolicStandardT QL Λ θ ((Si i) + β) (LastIndRight QL Λ i θ β N) hQs)
    (LinearEquiv.refl k (ParabolicStandard QL Λ θ ((Si i) + β) (LastIndRight QL Λ i θ β N)))
    (fun _ _ => rfl) b).symm

end Transport

section CrossBoth

variable (i j : I) (θ₀ β₀ : Multiset I) (N : Type) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ
    (({j} : Multiset I) + θ₀) (({j} : Multiset I) + β₀)) N]
  [IsScalarTower k (parabolicFactorAlgebra (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ
    (({j} : Multiset I) + θ₀) (({j} : Multiset I) + β₀)) N]

include hP hwf hQs in
/-- **The black-last piece of `S(₂Fᵢ N)` of colour `j ≠ i`, `j` in both blocks** (Webster,
arXiv:1309.3796v2, proof of Proposition 5.5): it has dimension
`dim S(₂Fᵢ ₁E_j N) + dim S(₂Fᵢ ₂E_j N)`. -/
theorem finrank_fixSub_lastIndStandardT_cross_both (hji : j ≠ i) [FiniteDimensional k N] :
    Module.finrank k (fixSub k (LastIndStandardT QL Λ i ((Si j) + θ₀) ((Si j) + β₀) N hQs)
        (lastStrandIdem QL Λ ((Si i) + (((Si j) + θ₀) + ((Si j) + β₀))) (some j))) =
      Module.finrank k
          (LastIndStandardT QL Λ i θ₀ ((Si j) + β₀) (LastResLeft QL Λ j θ₀ β₀ N) hQs) +
        Module.finrank k
          (LastIndStandardT QL Λ i ((Si j) + θ₀) β₀ (LastResRight QL Λ j θ₀ β₀ N) hQs) := by
  have := finiteDimensional_indK_parabolicFactor (Λ := Λ) hR
    (parabolicRightHom QL Λ i ((Si j) + θ₀) ((Si j) + β₀)) N
  rw [finrank_fixSub_lastIndStandardT_eq_parabolicStandardT,
    finrank_fixSub_lastStrandIdem_parabolicStandardT_of_eq (Λ := Λ) hR hQs j
      (rfl : (Si j) + θ₀ = (Si j) + θ₀) (cross_content i j β₀)]
  congr 1
  · exact finrank_parabolicStandard_congr QL Λ _ _ hQs
      (crossFactorEquivRight QL Λ i j θ₀ ((Si j) + β₀) N)
  · exact finrank_parabolicStandard_congr QL Λ _ _ hQs
      (secondFactorCrossEquiv (fun _ _ _ => rfl) hP hwf ((Si j) + θ₀) i j β₀ hji N)

end CrossBoth

section Left

variable (i j : I) (θ₀ β : Multiset I) (N : Type) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ
    (({j} : Multiset I) + θ₀) β) N]
  [IsScalarTower k (parabolicFactorAlgebra (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ
    (({j} : Multiset I) + θ₀) β) N]

/-- **The black-last piece of `S(₂Fᵢ N)` of colour `j ≠ i`, `j` in the first block only**
(Webster, arXiv:1309.3796v2, proof of Proposition 5.5): it has dimension
`dim S(₂Fᵢ ₁E_j N)`. -/
theorem finrank_fixSub_lastIndStandardT_cross_left (hji : j ≠ i) (hj : j ∉ β) :
    Module.finrank k (fixSub k (LastIndStandardT QL Λ i ((Si j) + θ₀) β N hQs)
        (lastStrandIdem QL Λ ((Si i) + (((Si j) + θ₀) + β)) (some j))) =
      Module.finrank k (LastIndStandardT QL Λ i θ₀ β (LeftResLeft QL Λ j θ₀ β N) hQs) := by
  have hj' : j ∉ (Si i) + β := by
    rw [Multiset.mem_add, Multiset.mem_singleton]
    exact fun h => h.elim hji hj
  rw [finrank_fixSub_lastIndStandardT_eq_parabolicStandardT,
    finrank_fixSub_lastStrandIdem_parabolicStandardT_left_of_eq (Λ := Λ) hQs j
      (rfl : (Si j) + θ₀ = (Si j) + θ₀) hj']
  exact finrank_parabolicStandard_congr QL Λ _ _ hQs (crossFactorEquivRight QL Λ i j θ₀ β N)

end Left

section Right

variable (i j : I) (θ β₀ : Multiset I) (N : Type) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ
    θ (({j} : Multiset I) + β₀)) N]
  [IsScalarTower k (parabolicFactorAlgebra (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ
    θ (({j} : Multiset I) + β₀)) N]

include hP hwf hQs in
/-- **The black-last piece of `S(₂Fᵢ N)` of colour `j ≠ i`, `j` in the second block only**
(Webster, arXiv:1309.3796v2, proof of Proposition 5.5): it has dimension
`dim S(₂Fᵢ ₂E_j N)`. -/
theorem finrank_fixSub_lastIndStandardT_cross_right (hji : j ≠ i) (hj : j ∉ θ) :
    Module.finrank k (fixSub k (LastIndStandardT QL Λ i θ ((Si j) + β₀) N hQs)
        (lastStrandIdem QL Λ ((Si i) + (θ + ((Si j) + β₀))) (some j))) =
      Module.finrank k (LastIndStandardT QL Λ i θ β₀ (RightResRight QL Λ j θ β₀ N) hQs) := by
  rw [finrank_fixSub_lastIndStandardT_eq_parabolicStandardT,
    finrank_fixSub_lastStrandIdem_parabolicStandardT_right_of_eq (Λ := Λ) hQs j
      (cross_content i j β₀) hj]
  exact finrank_parabolicStandard_congr QL Λ _ _ hQs
    (secondFactorCrossEquiv (fun _ _ _ => rfl) hP hwf θ i j β₀ hji N)

end Right

section SecondFactorEF

variable (i : I) (θ ν : Multiset I) (N : Type) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ
    θ (({i} : Multiset I) + ν)) N]
  [IsScalarTower k (parabolicFactorAlgebra (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ
    θ (({i} : Multiset I) + ν)) N]

include hP hwf hQs in
/-- **Standardization of `₂Eᵢ ₂Fᵢ N`** (Webster, arXiv:1309.3796v2, Theorem 4.31 on the second
factor, in the proof of Proposition 5.5): `dim S(₂Eᵢ ₂Fᵢ N) = dim S(₂Fᵢ ₂Eᵢ N) + n₂ dim S(N)`,
`n₂ = ⟨i, λ₂⟩` for the cyclotomic second factor of content `i + ν`, in both signs of `n₂`. -/
theorem finrank_parabolicStandard_secondFactorEF [FiniteDimensional k N] :
    (Module.finrank k (ParabolicStandard QL Λ θ ((Si i) + ν)
        (Res (parabolicRightHom QL Λ i θ ((Si i) + ν))
          (IndK k N (parabolicRightHom QL Λ i θ ((Si i) + ν))))) : ℤ) =
      Module.finrank k (ParabolicStandard QL Λ θ ((Si i) + ν)
          (IndK k (Res (parabolicRightHom QL Λ i θ ν) N) (parabolicRightHom QL Λ i θ ν))) +
        ip (RD₁) i (dw₁ ((Si i) + ν)) *
          Module.finrank k (ParabolicStandard QL Λ θ ((Si i) + ν) N) := by
  have hN : FiniteDimensional k (ParabolicStandard QL Λ θ ((Si i) + ν) N) :=
    finiteDimensional_parabolicStandard_of_finiteDimensional (Λ := Λ) hR hQs θ ((Si i) + ν) N
  have hFE : FiniteDimensional k (ParabolicStandard QL Λ θ ((Si i) + ν)
      (IndK k (Res (parabolicRightHom QL Λ i θ ν) N) (parabolicRightHom QL Λ i θ ν))) := by
    have := finiteDimensional_res_of_isScalarTower (parabolicAppendRight QL Λ i ν θ) N
    have := finiteDimensional_indK_parabolicFactor (Λ := Λ) hR (parabolicRightHom QL Λ i θ ν)
      (Res (parabolicRightHom QL Λ i θ ν) N)
    exact finiteDimensional_parabolicStandard_of_finiteDimensional (Λ := Λ) hR hQs _ _ _
  rcases le_total 0 (ip (RD₁) i (dw₁ ((Si i) + ν))) with h | h
  · have e := finrank_parabolicStandard_of_equiv_prod_pi QL Λ θ ((Si i) + ν) hQs
      (secondFactorEFEquiv (fun _ _ _ => rfl) hP hwf θ i ν h N)
    rw [e]
    push_cast
    rw [Int.toNat_of_nonneg h]
  · have e0 := secondFactorFEEquiv (fun _ _ _ => rfl) hP hwf θ i ν h N
    have e1 := finrank_parabolicStandard_congr QL Λ θ ((Si i) + ν) hQs e0
    have hXN := LinearEquiv.finiteDimensional (LinearEquiv.ofBijective
      (parabolicStandardMap QL Λ θ ((Si i) + ν) e0.toLinearMap)
      ⟨parabolicStandardMap_injective QL Λ θ ((Si i) + ν) hQs _ e0.injective,
        parabolicStandardMap_surjective QL Λ θ ((Si i) + ν) hQs _ e0.surjective⟩)
    have e := congrArg (Nat.cast : ℕ → ℤ) (e1.trans
      (finrank_parabolicStandard_prod_pi_of_finiteDimensional QL Λ θ ((Si i) + ν) hQs hXN))
    push_cast at e
    have ht : (((-ip (RD₁) i (dw₁ ((Si i) + ν))).toNat : ℕ) : ℤ) =
        -ip (RD₁) i (dw₁ ((Si i) + ν)) := Int.toNat_of_nonneg (neg_nonneg.mpr h)
    linear_combination -e -
      (Module.finrank k (ParabolicStandard QL Λ θ ((Si i) + ν) N) : ℤ) * ht

end SecondFactorEF

section SecondFactorEFNotMem

variable (i : I) (θ β : Multiset I) (N : Type) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ θ β) N]
  [IsScalarTower k (parabolicFactorAlgebra (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ
    θ β) N]

include hP hwf hQs in
/-- **Standardization of `₂Eᵢ ₂Fᵢ N` for `i ∉ β`** (Webster, arXiv:1309.3796v2, Theorem 4.31
on the second factor with `₂Eᵢ N = 0`, in the proof of Proposition 5.5):
`dim S(₂Eᵢ ₂Fᵢ N) = n₂ dim S(N)`, `n₂ = ⟨i, λ₂⟩` for the cyclotomic second factor of
content `β`. -/
theorem finrank_parabolicStandard_secondFactorEF_of_notMem (hi : i ∉ β)
    [FiniteDimensional k N] :
    (Module.finrank k (ParabolicStandard QL Λ θ β
        (Res (parabolicRightHom QL Λ i θ β) (IndK k N (parabolicRightHom QL Λ i θ β)))) : ℤ) =
      ip (RD₁) i (dw₁ β) * Module.finrank k (ParabolicStandard QL Λ θ β N) := by
  have := finiteDimensional_parabolicStandard_of_finiteDimensional (Λ := Λ) hR hQs θ β N
  rw [finrank_parabolicStandard_congr QL Λ _ _ hQs
      (secondFactorEFEquivOfNotMem (fun _ _ _ => rfl) hP hwf θ i β hi N),
    finrank_parabolicStandard_pi QL Λ _ _ hQs]
  push_cast
  rw [Int.toNat_of_nonneg (ip_nonneg_of_notMem i β hi)]

end SecondFactorEFNotMem

section BothSelf

variable (i : I) (θ₀ β₀ : Multiset I) (N : Type) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ
    (({i} : Multiset I) + θ₀) (({i} : Multiset I) + β₀)) N]
  [IsScalarTower k (parabolicFactorAlgebra (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ
    (({i} : Multiset I) + θ₀) (({i} : Multiset I) + β₀)) N]

include hP hwf hQs in
/-- **The black-last piece of `S(₂Fᵢ N)` of colour `i`, `i` in both blocks** (Webster,
arXiv:1309.3796v2, proof of Proposition 5.5): it has dimension
`dim S(₂Fᵢ ₁Eᵢ N) + dim S(₂Fᵢ ₂Eᵢ N) + n₂ dim S(N)`, `n₂ = ⟨i, λ₂⟩` for the cyclotomic second
factor of content `i + β₀`. -/
theorem finrank_fixSub_lastIndStandardT_self_both [FiniteDimensional k N] :
    (Module.finrank k (fixSub k (LastIndStandardT QL Λ i ((Si i) + θ₀) ((Si i) + β₀) N hQs)
        (lastStrandIdem QL Λ ((Si i) + (((Si i) + θ₀) + ((Si i) + β₀))) (some i))) : ℤ) =
      Module.finrank k
          (LastIndStandardT QL Λ i θ₀ ((Si i) + β₀) (LastResLeft QL Λ i θ₀ β₀ N) hQs) +
        Module.finrank k
          (LastIndStandardT QL Λ i ((Si i) + θ₀) β₀ (LastResRight QL Λ i θ₀ β₀ N) hQs) +
        ip (RD₁) i (dw₁ ((Si i) + β₀)) *
          Module.finrank k (ParabolicStandard QL Λ ((Si i) + θ₀) ((Si i) + β₀) N) := by
  have := finiteDimensional_indK_parabolicFactor (Λ := Λ) hR
    (parabolicRightHom QL Λ i ((Si i) + θ₀) ((Si i) + β₀)) N
  have hp := finrank_fixSub_lastStrandIdem_parabolicStandardT_of_eq (Λ := Λ) hR hQs i
    (rfl : (Si i) + θ₀ = (Si i) + θ₀)
    (rfl : (Si i) + ((Si i) + β₀) = (Si i) + ((Si i) + β₀))
    (LastIndRight QL Λ i ((Si i) + θ₀) ((Si i) + β₀) N)
  have h1 : Module.finrank k (ParabolicStandard QL Λ θ₀ ((Si i) + ((Si i) + β₀))
      (Res (leftAppendHomOfEq QL Λ i (rfl : (Si i) + θ₀ = (Si i) + θ₀)
        ((Si i) + ((Si i) + β₀))) (LastIndRight QL Λ i ((Si i) + θ₀) ((Si i) + β₀) N))) =
      Module.finrank k
        (LastIndStandardT QL Λ i θ₀ ((Si i) + β₀) (LastResLeft QL Λ i θ₀ β₀ N) hQs) :=
    finrank_parabolicStandard_congr QL Λ _ _ hQs
      (crossFactorEquivRight QL Λ i i θ₀ ((Si i) + β₀) N)
  have h2 := finrank_parabolicStandard_secondFactorEF hP hwf hQs i ((Si i) + θ₀) β₀ N
  have h2' : (Module.finrank k (ParabolicStandard QL Λ ((Si i) + θ₀) ((Si i) + β₀)
      (Res (parabolicRightHomOfEq QL Λ i
        (rfl : (Si i) + ((Si i) + β₀) = (Si i) + ((Si i) + β₀)) ((Si i) + θ₀))
        (LastIndRight QL Λ i ((Si i) + θ₀) ((Si i) + β₀) N))) : ℤ) =
      Module.finrank k
          (LastIndStandardT QL Λ i ((Si i) + θ₀) β₀ (LastResRight QL Λ i θ₀ β₀ N) hQs) +
        ip (RD₁) i (dw₁ ((Si i) + β₀)) *
          Module.finrank k (ParabolicStandard QL Λ ((Si i) + θ₀) ((Si i) + β₀) N) := h2
  rw [finrank_fixSub_lastIndStandardT_eq_parabolicStandardT, hp]
  push_cast
  rw [h1, h2']
  ring

end BothSelf

section LeftSelf

variable (i : I) (θ₀ β : Multiset I) (N : Type) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ
    (({i} : Multiset I) + θ₀) β) N]
  [IsScalarTower k (parabolicFactorAlgebra (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ
    (({i} : Multiset I) + θ₀) β) N]

include hP hwf hQs in
/-- **The black-last piece of `S(₂Fᵢ N)` of colour `i`, `i` in the first block only**
(Webster, arXiv:1309.3796v2, proof of Proposition 5.5): it has dimension
`dim S(₂Fᵢ ₁Eᵢ N) + n₂ dim S(N)`, `n₂ = ⟨i, λ₂⟩` for the cyclotomic second factor of
content `β`. -/
theorem finrank_fixSub_lastIndStandardT_self_left (hi : i ∉ β) [FiniteDimensional k N] :
    (Module.finrank k (fixSub k (LastIndStandardT QL Λ i ((Si i) + θ₀) β N hQs)
        (lastStrandIdem QL Λ ((Si i) + (((Si i) + θ₀) + β)) (some i))) : ℤ) =
      Module.finrank k (LastIndStandardT QL Λ i θ₀ β (LeftResLeft QL Λ i θ₀ β N) hQs) +
        ip (RD₁) i (dw₁ β) * Module.finrank k (ParabolicStandard QL Λ ((Si i) + θ₀) β N) := by
  have := finiteDimensional_indK_parabolicFactor (Λ := Λ) hR
    (parabolicRightHom QL Λ i ((Si i) + θ₀) β) N
  have hp := finrank_fixSub_lastStrandIdem_parabolicStandardT_of_eq (Λ := Λ) hR hQs i
    (rfl : (Si i) + θ₀ = (Si i) + θ₀) (rfl : (Si i) + β = (Si i) + β)
    (LastIndRight QL Λ i ((Si i) + θ₀) β N)
  have h1 : Module.finrank k (ParabolicStandard QL Λ θ₀ ((Si i) + β)
      (Res (leftAppendHomOfEq QL Λ i (rfl : (Si i) + θ₀ = (Si i) + θ₀) ((Si i) + β))
        (LastIndRight QL Λ i ((Si i) + θ₀) β N))) =
      Module.finrank k (LastIndStandardT QL Λ i θ₀ β (LeftResLeft QL Λ i θ₀ β N) hQs) :=
    finrank_parabolicStandard_congr QL Λ _ _ hQs (crossFactorEquivRight QL Λ i i θ₀ β N)
  have h2 := finrank_parabolicStandard_secondFactorEF_of_notMem hP hwf hQs i ((Si i) + θ₀) β
    N hi
  have h2' : (Module.finrank k (ParabolicStandard QL Λ ((Si i) + θ₀) β
      (Res (parabolicRightHomOfEq QL Λ i (rfl : (Si i) + β = (Si i) + β) ((Si i) + θ₀))
        (LastIndRight QL Λ i ((Si i) + θ₀) β N))) : ℤ) =
      ip (RD₁) i (dw₁ β) * Module.finrank k (ParabolicStandard QL Λ ((Si i) + θ₀) β N) := h2
  rw [finrank_fixSub_lastIndStandardT_eq_parabolicStandardT, hp]
  push_cast
  rw [h1, h2']

end LeftSelf

section RightSelf

variable (i : I) (θ β₀ : Multiset I) (N : Type) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ
    θ (({i} : Multiset I) + β₀)) N]
  [IsScalarTower k (parabolicFactorAlgebra (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ
    θ (({i} : Multiset I) + β₀)) N]

include hP hwf hQs in
/-- **The black-last piece of `S(₂Fᵢ N)` of colour `i`, `i` in the second block only**
(Webster, arXiv:1309.3796v2, proof of Proposition 5.5): it has dimension
`dim S(₂Fᵢ ₂Eᵢ N) + n₂ dim S(N)`, `n₂ = ⟨i, λ₂⟩` for the cyclotomic second factor of
content `i + β₀`. -/
theorem finrank_fixSub_lastIndStandardT_self_right (hi : i ∉ θ) [FiniteDimensional k N] :
    (Module.finrank k (fixSub k (LastIndStandardT QL Λ i θ ((Si i) + β₀) N hQs)
        (lastStrandIdem QL Λ ((Si i) + (θ + ((Si i) + β₀))) (some i))) : ℤ) =
      Module.finrank k (LastIndStandardT QL Λ i θ β₀ (RightResRight QL Λ i θ β₀ N) hQs) +
        ip (RD₁) i (dw₁ ((Si i) + β₀)) *
          Module.finrank k (ParabolicStandard QL Λ θ ((Si i) + β₀) N) := by
  have hp := finrank_fixSub_lastStrandIdem_parabolicStandardT_right_of_eq (Λ := Λ) hQs i
    (rfl : (Si i) + ((Si i) + β₀) = (Si i) + ((Si i) + β₀)) hi
    (LastIndRight QL Λ i θ ((Si i) + β₀) N)
  have h2 := finrank_parabolicStandard_secondFactorEF hP hwf hQs i θ β₀ N
  rw [finrank_fixSub_lastIndStandardT_eq_parabolicStandardT, hp]
  exact h2

end RightSelf

section NotMemSelf

variable (i : I) (θ β : Multiset I) (N : Type) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ θ β) N]
  [IsScalarTower k (parabolicFactorAlgebra (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ
    θ β) N]

include hP hwf hQs in
/-- **The black-last piece of `S(₂Fᵢ N)` of colour `i ∉ θ + β`** (Webster,
arXiv:1309.3796v2, proof of Proposition 5.5): it has dimension `n₂ dim S(N)`,
`n₂ = ⟨i, λ₂⟩` for the cyclotomic second factor of content `β`. -/
theorem finrank_fixSub_lastIndStandardT_self_of_notMem (hi : i ∉ θ + β)
    [FiniteDimensional k N] :
    (Module.finrank k (fixSub k (LastIndStandardT QL Λ i θ β N hQs)
        (lastStrandIdem QL Λ ((Si i) + (θ + β)) (some i))) : ℤ) =
      ip (RD₁) i (dw₁ β) * Module.finrank k (ParabolicStandard QL Λ θ β N) := by
  have hiθ : i ∉ θ := fun h => hi (Multiset.mem_add.mpr (Or.inl h))
  have hiβ : i ∉ β := fun h => hi (Multiset.mem_add.mpr (Or.inr h))
  have hp := finrank_fixSub_lastStrandIdem_parabolicStandardT_right_of_eq (Λ := Λ) hQs i
    (rfl : (Si i) + β = (Si i) + β) hiθ (LastIndRight QL Λ i θ β N)
  have h2 := finrank_parabolicStandard_secondFactorEF_of_notMem hP hwf hQs i θ β N hiβ
  rw [finrank_fixSub_lastIndStandardT_eq_parabolicStandardT, hp]
  exact h2

end NotMemSelf

end Categorification.Stendhal
