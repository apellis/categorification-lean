/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.Prop55DimensionCount
import Categorification.WeightedKLR.RedStrands.Prop55DimensionColourQ
import Categorification.WeightedKLR.RedStrands.Prop55DimensionSecondFactorQ
import Categorification.WeightedKLR.RedStrands.CoordinateWeightPairing
import Categorification.WeightedKLR.RedStrands.ParabolicStandardFiniteFiltration

/-!
# The dimension count of Proposition 5.5

Webster, arXiv:1309.3796v2, proof of Proposition 5.5, (5.13)–(5.14). For Rouquier
parameters `Q` and a finite-dimensional module `N` over the parabolic
factor algebra `D_{θ, β}`,
`dim Fᵢ S(N) = dim S(₁Fᵢ N) + dim S(₂Fᵢ N)`.
The proof is Webster's induction on the number of black strands: split each side according to the
last strand; the last-red pieces agree (`finrank_lastRed_firstIndF_eq_add`), and the piece of
colour `j` of `Fᵢ S(N)` is a sum of `dim Fᵢ S(N')` over restrictions `N'` of `N` with one black
strand fewer (plus `n dim S(N)` for `j = i`), matched term by term by the pieces of `S(₁Fᵢ N)` and
`S(₂Fᵢ N)` (plus `n₁ dim S(N)` and `n₂ dim S(N)`), with `n = n₁ + n₂`
(`ip_downRightWeight_split`).

## Main results

* `finrank_firstIndF_eq_addQ`: the dimension count.
* `firstIndDeltaInjective_of_rouquier`: injectivity of `δ₁ : S(₁Fᵢ N) → Fᵢ S(N)` for
  finite-dimensional `N`.
* `allFiniteDeltaInjective_of_rouquier`: the route hypothesis `AllFiniteDeltaInjective` holds.
* `hasFiltration_loadingProj_of_rouquier`: Webster's Proposition 5.20 filtration of
  `T^λ e(s, λ_ℓ, w)` by standardizations, without route hypothesis.

## Hypotheses

The intermediate lemmas take, for each of the three cyclotomic data that occur (the weights `Λ`,
the first factor `Λ ∘ Fin.castSucc` and the one-colour datum `Λ (Fin.last ℓ)`), a base
presentation `P` of the cyclotomic cover with `CoverRelsNegligible` and well-founded domain
(`P.WFDom`), to which the relation families of Theorem 4.31 are adjoined. The presentation with
no base relations (`noRelations`) satisfies both conditions vacuously, so the main results take
no such hypothesis: besides the standard scalars they assume only the Rouquier condition `hR`
and the symmetry `hQs : KLRSymm QL`.

This is the version of `Prop55DimensionCount` for every Rouquier parameter `Q`: the black strands
carry the relations of Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3, Definition 1.1, `r = 1`) instead
of the KL III relations. Each declaration carries the suffix `Q`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory CategoryTheory.Idempotents QuantumGroup QuantumGroup.UDot StringDiagrams
  KLR KLRAlgebra TwoRep CyclotomicAction DoubleDiagram KL3.Diagram InductionAlong MulOpposite
  ModuleFiltration

open scoped Classical

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe w₀ w₁ w₂

variable {I : Type} {ℓ : ℕ} {Λ : Fin (ℓ + 1) → I →₀ ℕ} {C : CartanDatum I}
  {k : Type} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {hR : IsRouquierQ C Q}

local notation "QL" => Q
local notation "D" => parabolicFactorAlgebra Q Λ
local notation "Si" j => (Singleton.singleton j : Multiset I)
local notation "TA" => TensorProductAlgebra k Q Λ

variable (Λ) in
/-- The dimension count of Proposition 5.5 for all finite-dimensional modules over `D_{θ, β}`:
`dim Fᵢ S(N) = dim S(₁Fᵢ N) + dim S(₂Fᵢ N)` for every colour `i`. -/
def FirstIndFinrankSplitQ (hQs : KLRSymm Q)
    (θ β : Multiset I) : Prop :=
  ∀ (i : I) (N : Type) [AddCommGroup N] [Module k N]
    [Module (parabolicFactorAlgebra Q Λ θ β) N]
    [IsScalarTower k (parabolicFactorAlgebra Q Λ
      θ β) N],
    FiniteDimensional k N →
      Module.finrank k (FirstIndF Q Λ i θ β N hQs) =
        Module.finrank k
            (FirstIndStandardT Q Λ i θ β N hQs) +
          Module.finrank k
            (LastIndStandardT Q Λ i θ β N hQs)

-- The weights are written out: notation is not hygienic inside binders.
variable {P : Presentation.{0, 0}
    (signature (coordinateDatum Λ C) (redWeight (cyclotomicCoverWeightDatum Λ C))) k}
  (hP : CoverRelsNegligible.{0, 0, w₀} Λ C hR (coverDotCentral Λ C hR)
    (blockWeight (cyclotomicCoverWeightDatum Λ C) (cyclotomicCoverHighest (I := I)
      (ℓ := ℓ + 1)) 0 : I ⊕ Fin (ℓ + 1) → ℤ) P)
  (hwf : P.WFDom)
  {P₁ : Presentation.{0, 0}
    (signature (coordinateDatum (Λ ∘ Fin.castSucc) C)
      (redWeight (cyclotomicCoverWeightDatum (Λ ∘ Fin.castSucc) C))) k}
  (hP₁ : CoverRelsNegligible.{0, 0, w₁} (Λ ∘ Fin.castSucc) C hR
    (coverDotCentral (Λ ∘ Fin.castSucc) C hR)
    (blockWeight (cyclotomicCoverWeightDatum (Λ ∘ Fin.castSucc) C)
      (cyclotomicCoverHighest (I := I) (ℓ := ℓ)) 0 : I ⊕ Fin ℓ → ℤ) P₁)
  (hwf₁ : P₁.WFDom)
  {P₂ : Presentation.{0, 0}
    (signature (coordinateDatum (fun _ : Fin 1 => Λ (Fin.last ℓ)) C)
      (redWeight (cyclotomicCoverWeightDatum (fun _ : Fin 1 => Λ (Fin.last ℓ)) C))) k}
  (hP₂ : CoverRelsNegligible.{0, 0, w₂} (fun _ : Fin 1 => Λ (Fin.last ℓ)) C hR
    (coverDotCentral (fun _ : Fin 1 => Λ (Fin.last ℓ)) C hR)
    (blockWeight (cyclotomicCoverWeightDatum (fun _ : Fin 1 => Λ (Fin.last ℓ)) C)
      (cyclotomicCoverHighest (I := I) (ℓ := 1)) 0 : I ⊕ Fin 1 → ℤ) P₂)
  (hwf₂ : P₂.WFDom)
  (hQs : KLRSymm Q)

section Colour

variable (i : I) (θ β : Multiset I) (N : Type) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ
    θ β) N]

include hP hwf hP₁ hwf₁ hP₂ hwf₂ in
/-- **The colour-`j` step of the dimension count, `j ≠ i`** (Webster, arXiv:1309.3796v2, proof
of Proposition 5.5): given the dimension count for fewer black strands, the black-last pieces of
colour `j` of `Fᵢ S(N)`, `S(₁Fᵢ N)` and `S(₂Fᵢ N)` satisfy the dimension count. -/
theorem finrank_fixSub_firstIndF_split_of_neQ (j : I) (hji : j ≠ i) (hj : j ∈ θ + β)
    [FiniteDimensional k N]
    (IH : ∀ θ' β' : Multiset I, Multiset.card θ' + Multiset.card β' <
      Multiset.card θ + Multiset.card β → FirstIndFinrankSplitQ Λ hQs θ' β') :
    Module.finrank k (fixSub k (FirstIndF QL Λ i θ β N hQs)
        (lastStrandIdem QL Λ ((Si i) + (θ + β)) (some j))) =
      Module.finrank k (fixSub k (FirstIndStandardT QL Λ i θ β N hQs)
          (lastStrandIdem QL Λ ((Si i) + (θ + β)) (some j))) +
        Module.finrank k (fixSub k (LastIndStandardT QL Λ i θ β N hQs)
          (lastStrandIdem QL Λ ((Si i) + (θ + β)) (some j))) := by
  by_cases hθ : j ∈ θ <;> by_cases hβ : j ∈ β
  · obtain ⟨θ₀, rfl⟩ := exists_eq_singleton_add_of_mem hθ
    obtain ⟨β₀, rfl⟩ := exists_eq_singleton_add_of_mem hβ
    have hF := finrank_fixSub_firstIndF_cross_bothQ hP hwf hQs i j θ₀ β₀ N hji
    have h1 := finrank_fixSub_firstIndStandardT_cross_bothQ hP₁ hwf₁ hQs i j θ₀ β₀ N hji
    have h2 := finrank_fixSub_lastIndStandardT_cross_bothQ hP₂ hwf₂ hQs i j θ₀ β₀ N hji
    have ha := IH θ₀ ((Si j) + β₀)
      (by simp only [Multiset.card_add, Multiset.card_singleton]; omega) i
      (LastResLeft QL Λ j θ₀ β₀ N)
      (finiteDimensional_res_of_isScalarTower (parabolicAppendLeft QL Λ j θ₀ ((Si j) + β₀)) N)
    have hb := IH ((Si j) + θ₀) β₀
      (by simp only [Multiset.card_add, Multiset.card_singleton]; omega) i
      (LastResRight QL Λ j θ₀ β₀ N)
      (finiteDimensional_res_of_isScalarTower (parabolicAppendRight QL Λ j β₀ ((Si j) + θ₀)) N)
    omega
  · obtain ⟨θ₀, rfl⟩ := exists_eq_singleton_add_of_mem hθ
    have hF := finrank_fixSub_firstIndF_cross_leftQ hP hwf hQs i j θ₀ β N hji hβ
    have h1 := finrank_fixSub_firstIndStandardT_cross_leftQ hP₁ hwf₁ hQs i j θ₀ β N hji hβ
    have h2 := finrank_fixSub_lastIndStandardT_cross_leftQ (Λ := Λ) hQs i j θ₀ β N hji hβ
    have ha := IH θ₀ β
      (by simp only [Multiset.card_add, Multiset.card_singleton]; omega) i
      (LeftResLeft QL Λ j θ₀ β N)
      (finiteDimensional_res_of_isScalarTower (parabolicAppendLeft QL Λ j θ₀ β) N)
    omega
  · obtain ⟨β₀, rfl⟩ := exists_eq_singleton_add_of_mem hβ
    have hF := finrank_fixSub_firstIndF_cross_rightQ hP hwf hQs i j θ β₀ N hji hθ
    have h1 := finrank_fixSub_firstIndStandardT_cross_rightQ (Λ := Λ) hQs i j θ β₀ N hji hθ
    have h2 := finrank_fixSub_lastIndStandardT_cross_rightQ hP₂ hwf₂ hQs i j θ β₀ N hji hθ
    have ha := IH θ β₀
      (by simp only [Multiset.card_add, Multiset.card_singleton]; omega) i
      (RightResRight QL Λ j θ β₀ N)
      (finiteDimensional_res_of_isScalarTower (parabolicAppendRight QL Λ j β₀ θ) N)
    omega
  · exact absurd hj (by rw [Multiset.mem_add]; tauto)

include hP hwf hP₁ hwf₁ hP₂ hwf₂ in
/-- **The colour-`i` step of the dimension count** (Webster, arXiv:1309.3796v2, proof of
Proposition 5.5): given the dimension count for fewer black strands, the black-last pieces of
colour `i` of `Fᵢ S(N)`, `S(₁Fᵢ N)` and `S(₂Fᵢ N)` satisfy the dimension count; the extra
terms `n dim S(N)`, `n₁ dim S(N)` and `n₂ dim S(N)` match by `n = n₁ + n₂`. -/
theorem finrank_fixSub_firstIndF_split_selfQ [FiniteDimensional k N]
    (IH : ∀ θ' β' : Multiset I, Multiset.card θ' + Multiset.card β' <
      Multiset.card θ + Multiset.card β → FirstIndFinrankSplitQ Λ hQs θ' β') :
    Module.finrank k (fixSub k (FirstIndF QL Λ i θ β N hQs)
        (lastStrandIdem QL Λ ((Si i) + (θ + β)) (some i))) =
      Module.finrank k (fixSub k (FirstIndStandardT QL Λ i θ β N hQs)
          (lastStrandIdem QL Λ ((Si i) + (θ + β)) (some i))) +
        Module.finrank k (fixSub k (LastIndStandardT QL Λ i θ β N hQs)
          (lastStrandIdem QL Λ ((Si i) + (θ + β)) (some i))) := by
  have hs := ip_downRightWeight_split C i Λ θ β
  by_cases hθ : i ∈ θ <;> by_cases hβ : i ∈ β
  · obtain ⟨θ₀, rfl⟩ := exists_eq_singleton_add_of_mem hθ
    obtain ⟨β₀, rfl⟩ := exists_eq_singleton_add_of_mem hβ
    have hF := finrank_fixSub_firstIndF_self_bothQ hP hwf hQs i θ₀ β₀ N
    have h1 := finrank_fixSub_firstIndStandardT_self_bothQ hP₁ hwf₁ hQs i θ₀ β₀ N
    have h2 := finrank_fixSub_lastIndStandardT_self_bothQ hP₂ hwf₂ hQs i θ₀ β₀ N
    have ha := IH θ₀ ((Si i) + β₀)
      (by simp only [Multiset.card_add, Multiset.card_singleton]; omega) i
      (LastResLeft QL Λ i θ₀ β₀ N)
      (finiteDimensional_res_of_isScalarTower (parabolicAppendLeft QL Λ i θ₀ ((Si i) + β₀)) N)
    have hb := IH ((Si i) + θ₀) β₀
      (by simp only [Multiset.card_add, Multiset.card_singleton]; omega) i
      (LastResRight QL Λ i θ₀ β₀ N)
      (finiteDimensional_res_of_isScalarTower (parabolicAppendRight QL Λ i β₀ ((Si i) + θ₀)) N)
    have haz : (_ : ℤ) = _ := congrArg (Nat.cast (R := ℤ)) ha
    have hbz : (_ : ℤ) = _ := congrArg (Nat.cast (R := ℤ)) hb
    push_cast at haz hbz
    have key : (Module.finrank k (fixSub k (FirstIndF QL Λ i ((Si i) + θ₀) ((Si i) + β₀) N hQs)
        (lastStrandIdem QL Λ ((Si i) + (((Si i) + θ₀) + ((Si i) + β₀))) (some i))) : ℤ) =
        Module.finrank k (fixSub k (FirstIndStandardT QL Λ i ((Si i) + θ₀) ((Si i) + β₀) N hQs)
          (lastStrandIdem QL Λ ((Si i) + (((Si i) + θ₀) + ((Si i) + β₀))) (some i))) +
        Module.finrank k (fixSub k (LastIndStandardT QL Λ i ((Si i) + θ₀) ((Si i) + β₀) N hQs)
          (lastStrandIdem QL Λ ((Si i) + (((Si i) + θ₀) + ((Si i) + β₀))) (some i))) := by
      linear_combination hF - h1 - h2 + haz + hbz +
        (Module.finrank k (ParabolicStandard QL Λ ((Si i) + θ₀) ((Si i) + β₀) N) : ℤ) * hs
    exact_mod_cast key
  · obtain ⟨θ₀, rfl⟩ := exists_eq_singleton_add_of_mem hθ
    have hF := finrank_fixSub_firstIndF_self_leftQ hP hwf hQs i θ₀ β N hβ
    have h1 := finrank_fixSub_firstIndStandardT_self_leftQ hP₁ hwf₁ hQs i θ₀ β N hβ
    have h2 := finrank_fixSub_lastIndStandardT_self_leftQ hP₂ hwf₂ hQs i θ₀ β N hβ
    have ha := IH θ₀ β
      (by simp only [Multiset.card_add, Multiset.card_singleton]; omega) i
      (LeftResLeft QL Λ i θ₀ β N)
      (finiteDimensional_res_of_isScalarTower (parabolicAppendLeft QL Λ i θ₀ β) N)
    have haz : (_ : ℤ) = _ := congrArg (Nat.cast (R := ℤ)) ha
    push_cast at haz
    have key : (Module.finrank k (fixSub k (FirstIndF QL Λ i ((Si i) + θ₀) β N hQs)
        (lastStrandIdem QL Λ ((Si i) + (((Si i) + θ₀) + β)) (some i))) : ℤ) =
        Module.finrank k (fixSub k (FirstIndStandardT QL Λ i ((Si i) + θ₀) β N hQs)
          (lastStrandIdem QL Λ ((Si i) + (((Si i) + θ₀) + β)) (some i))) +
        Module.finrank k (fixSub k (LastIndStandardT QL Λ i ((Si i) + θ₀) β N hQs)
          (lastStrandIdem QL Λ ((Si i) + (((Si i) + θ₀) + β)) (some i))) := by
      linear_combination hF - h1 - h2 + haz +
        (Module.finrank k (ParabolicStandard QL Λ ((Si i) + θ₀) β N) : ℤ) * hs
    exact_mod_cast key
  · obtain ⟨β₀, rfl⟩ := exists_eq_singleton_add_of_mem hβ
    have hF := finrank_fixSub_firstIndF_self_rightQ hP hwf hQs i θ β₀ N hθ
    have h1 := finrank_fixSub_firstIndStandardT_self_rightQ hP₁ hwf₁ hQs i θ β₀ N hθ
    have h2 := finrank_fixSub_lastIndStandardT_self_rightQ hP₂ hwf₂ hQs i θ β₀ N hθ
    have ha := IH θ β₀
      (by simp only [Multiset.card_add, Multiset.card_singleton]; omega) i
      (RightResRight QL Λ i θ β₀ N)
      (finiteDimensional_res_of_isScalarTower (parabolicAppendRight QL Λ i β₀ θ) N)
    have haz : (_ : ℤ) = _ := congrArg (Nat.cast (R := ℤ)) ha
    push_cast at haz
    have key : (Module.finrank k (fixSub k (FirstIndF QL Λ i θ ((Si i) + β₀) N hQs)
        (lastStrandIdem QL Λ ((Si i) + (θ + ((Si i) + β₀))) (some i))) : ℤ) =
        Module.finrank k (fixSub k (FirstIndStandardT QL Λ i θ ((Si i) + β₀) N hQs)
          (lastStrandIdem QL Λ ((Si i) + (θ + ((Si i) + β₀))) (some i))) +
        Module.finrank k (fixSub k (LastIndStandardT QL Λ i θ ((Si i) + β₀) N hQs)
          (lastStrandIdem QL Λ ((Si i) + (θ + ((Si i) + β₀))) (some i))) := by
      linear_combination hF - h1 - h2 + haz +
        (Module.finrank k (ParabolicStandard QL Λ θ ((Si i) + β₀) N) : ℤ) * hs
    exact_mod_cast key
  · have hi : i ∉ θ + β := by rw [Multiset.mem_add]; tauto
    have hF := finrank_fixSub_firstIndF_self_of_notMemQ hP hwf hQs i θ β N hi
    have h1 := finrank_fixSub_firstIndStandardT_self_of_notMemQ hP₁ hwf₁ hQs i θ β N hi
    have h2 := finrank_fixSub_lastIndStandardT_self_of_notMemQ hP₂ hwf₂ hQs i θ β N hi
    have key : (Module.finrank k (fixSub k (FirstIndF QL Λ i θ β N hQs)
        (lastStrandIdem QL Λ ((Si i) + (θ + β)) (some i))) : ℤ) =
        Module.finrank k (fixSub k (FirstIndStandardT QL Λ i θ β N hQs)
          (lastStrandIdem QL Λ ((Si i) + (θ + β)) (some i))) +
        Module.finrank k (fixSub k (LastIndStandardT QL Λ i θ β N hQs)
          (lastStrandIdem QL Λ ((Si i) + (θ + β)) (some i))) := by
      linear_combination hF - h1 - h2 +
        (Module.finrank k (ParabolicStandard QL Λ θ β N) : ℤ) * hs
    exact_mod_cast key

end Colour

/-- `finrank_eq_lastRed_add_sum` with the `k`-algebra structure on corners used in this folder
(`IsIdempotentElem.instAlgebraCorner_categorification`), which is not definitionally the one of
`KLR.cornerAlgebra` at instance transparency. The proof is the same. -/
private theorem finrank_eq_lastRed_add_sum_cornerQ {K : Type} [Field K]
    {Q : I → I → MvPolynomial (Fin 2) K} (Λ : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I)
    (Y : Type*) [AddCommGroup Y] [Module K Y] [Module (TensorProductAlgebra K Q Λ ν) Y]
    [IsScalarTower K (TensorProductAlgebra K Q Λ ν) Y] [FiniteDimensional K Y] :
    Module.finrank K Y = Module.finrank K (fixSub K Y (TensorProductAlgebra.lastRedIdem Q Λ ν)) +
      ∑ j ∈ ν.toFinset, Module.finrank K (fixSub K Y (lastStrandIdem Q Λ ν (some j))) := by
  have e := fixSubSumEquiv (isOrthFamily_lastStrandIdem Q Λ ν) K Y
  rw [sum_lastStrandIdem, fixSub_one] at e
  rw [← finrank_top K Y, e.finrank_eq, Module.finrank_pi_fintype,
    Finset.sum_coe_sort (insert none (ν.toFinset.image some))
      (fun a => Module.finrank K (fixSub K Y (lastStrandIdem Q Λ ν a))),
    Finset.sum_insert (by simp), Finset.sum_image (by simp), lastStrandIdem_none]

section Count

variable (i : I) (θ β : Multiset I) (N : Type) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ
    θ β) N]

include hP hwf hP₁ hwf₁ hP₂ hwf₂ in
/-- **The induction step of the dimension count** (Webster, arXiv:1309.3796v2, proof of
Proposition 5.5, (5.13)–(5.14)): given the dimension count for fewer black strands, it holds
for `N`. Both sides are split by the last strand (`finrank_eq_lastRed_add_sum`). -/
theorem finrank_firstIndF_eq_add_of_ltQ [FiniteDimensional k N]
    (IH : ∀ θ' β' : Multiset I, Multiset.card θ' + Multiset.card β' <
      Multiset.card θ + Multiset.card β → FirstIndFinrankSplitQ Λ hQs θ' β') :
    Module.finrank k (FirstIndF QL Λ i θ β N hQs) =
      Module.finrank k (FirstIndStandardT QL Λ i θ β N hQs) +
        Module.finrank k (LastIndStandardT QL Λ i θ β N hQs) := by
  have : Module.Finite (D θ β) N := Module.Finite.of_restrictScalars_finite k _ N
  have : FiniteDimensional k (FirstIndF QL Λ i θ β N hQs) :=
    have := firstIndF_restrict_finite QL Λ i θ β N hQs hR
    Module.Finite.equiv (restrictScalarsEquivOfTower k (TA ((Si i) + (θ + β))) _)
  have : FiniteDimensional k (FirstIndStandardT QL Λ i θ β N hQs) :=
    have := firstIndStandardT_restrict_finite QL Λ i θ β N hQs hR
    Module.Finite.equiv (restrictScalarsEquivOfTower k (TA ((Si i) + (θ + β))) _)
  have : FiniteDimensional k (LastIndStandardT QL Λ i θ β N hQs) :=
    have := lastIndStandardT_restrict_finite QL Λ i θ β N hQs hR
    Module.Finite.equiv (restrictScalarsEquivOfTower k (TA ((Si i) + (θ + β))) _)
  have hsum : ∑ j ∈ ((Si i) + (θ + β)).toFinset,
      Module.finrank k (fixSub k (FirstIndF QL Λ i θ β N hQs)
        (lastStrandIdem QL Λ ((Si i) + (θ + β)) (some j))) =
      ∑ j ∈ ((Si i) + (θ + β)).toFinset,
        (Module.finrank k (fixSub k (FirstIndStandardT QL Λ i θ β N hQs)
          (lastStrandIdem QL Λ ((Si i) + (θ + β)) (some j))) +
        Module.finrank k (fixSub k (LastIndStandardT QL Λ i θ β N hQs)
          (lastStrandIdem QL Λ ((Si i) + (θ + β)) (some j)))) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    by_cases hji : j = i
    · subst hji
      exact finrank_fixSub_firstIndF_split_selfQ hP hwf hP₁ hwf₁ hP₂ hwf₂ hQs _ θ β N IH
    · have hj' : j ∈ θ + β := by
        have := Multiset.mem_toFinset.mp hj
        rw [Multiset.mem_add, Multiset.mem_singleton] at this
        exact this.resolve_left hji
      exact finrank_fixSub_firstIndF_split_of_neQ hP hwf hP₁ hwf₁ hP₂ hwf₂ hQs i θ β N j hji hj'
        IH
  let ν := (Si i) + (θ + β)
  rw [finrank_eq_lastRed_add_sum_cornerQ (Q := QL) Λ ν (FirstIndF QL Λ i θ β N hQs),
    finrank_eq_lastRed_add_sum_cornerQ (Q := QL) Λ ν (FirstIndStandardT QL Λ i θ β N hQs),
    finrank_eq_lastRed_add_sum_cornerQ (Q := QL) Λ ν (LastIndStandardT QL Λ i θ β N hQs),
    finrank_lastRed_firstIndF_eq_add QL Λ i θ β N hQs hR, hsum, Finset.sum_add_distrib]
  ring

variable (hR) in
include hR in
/-- **The dimension count of Proposition 5.5** (Webster, arXiv:1309.3796v2, proof of
Proposition 5.5, (5.13)–(5.14)): for Rouquier parameters `Q` and a finite-dimensional
module `N` over `D_{θ, β}`,
`dim Fᵢ S(N) = dim S(₁Fᵢ N) + dim S(₂Fᵢ N)`. Proved by strong induction on `|θ| + |β|`, with
the presentation of the cyclotomic cover having no base relations (`noRelations`). -/
theorem finrank_firstIndF_eq_addQ [FiniteDimensional k N] :
    Module.finrank k (FirstIndF QL Λ i θ β N hQs) =
      Module.finrank k (FirstIndStandardT QL Λ i θ β N hQs) +
        Module.finrank k (LastIndStandardT QL Λ i θ β N hQs) := by
  suffices h : ∀ (n : ℕ) (θ β : Multiset I), Multiset.card θ + Multiset.card β = n →
      FirstIndFinrankSplitQ Λ hQs θ β from h _ θ β rfl i N inferInstance
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro θ β hn i N _ _ _ _ _
    exact finrank_firstIndF_eq_add_of_ltQ.{0, 0, 0} (hR := hR)
      (P := noRelations _ k) (P₁ := noRelations _ k) (P₂ := noRelations _ k)
      (fun r => PEmpty.elim r) (fun r => PEmpty.elim r) (fun r => PEmpty.elim r)
      (fun r => PEmpty.elim r) (fun r => PEmpty.elim r) (fun r => PEmpty.elim r) hQs i θ β N
      (fun θ' β' h => ih _ (hn ▸ h) θ' β' rfl)

variable (hR) in
include hR in
/-- **Injectivity of `δ₁ : S(₁Fᵢ N) → Fᵢ S(N)` for finite-dimensional `N`** (Webster,
arXiv:1309.3796v2, proof of Proposition 5.5), for Rouquier parameters `Q`, from the
dimension count `finrank_firstIndF_eq_addQ`. -/
theorem firstIndDeltaInjective_of_rouquier [FiniteDimensional k N] :
    FirstIndDeltaInjective QL Λ i θ β N hQs := by
  rw [firstIndDeltaInjective_iff_finrank_of_finite QL Λ i θ β N hQs hR,
    finrank_restrictScalars_of_tower, finrank_restrictScalars_of_tower,
    finrank_restrictScalars_of_tower]
  exact finrank_firstIndF_eq_addQ hR hQs i θ β N

end Count

variable (hR) in
include hR in
/-- **The route hypothesis of Proposition 5.5 holds for every Rouquier
parameter `Q`** (Webster, arXiv:1309.3796v2, proof of Proposition 5.5): `δ₁` is injective for
every finite-dimensional module. -/
theorem allFiniteDeltaInjective_of_rouquier : AllFiniteDeltaInjective QL Λ hQs :=
  fun i θ β M _ => firstIndDeltaInjective_of_rouquier hR hQs i θ β M.carrier

variable (hR) in
include hR in
/-- **Filtration of `T^λ e(s, λ_ℓ, w)` by standardizations for Rouquier
parameters `Q`** (Webster, arXiv:1309.3796v2, Proposition 5.20, recursion in its proof), with
no route hypothesis: `hasFiltration_loadingProj_of_finite` with
`allFiniteDeltaInjective_of_rouquier`. -/
theorem hasFiltration_loadingProj_of_rouquier (w : List I) {θ : Multiset I}
    (s : Seq (stendhalWeight ℓ (θ + 0))) (hs : IsRedOrdered s) :
    HasFiltration (stdLayerModule QL Λ hQs) ((redLayer QL Λ θ s hs).wordLayers QL Λ w)
      (loadingProj QL Λ (blackWordLoading w (appendRedLoading s))
        (blackWordLoading_ordered w _ ((appendRedLoading_ordered_iff s).2 hs))) :=
  hasFiltration_loadingProj_of_finite hR (allFiniteDeltaInjective_of_rouquier hR hQs) w s hs

end Categorification.Stendhal
