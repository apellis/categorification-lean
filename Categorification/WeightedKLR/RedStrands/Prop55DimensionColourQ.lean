/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.Prop55DimensionColour
import Categorification.WeightedKLR.RedStrands.Prop55DimensionAmbientQ
import Categorification.WeightedKLR.RedStrands.Prop55DimensionPieces
import Categorification.WeightedKLR.RedStrands.ParabolicStandardLastOneBlockLinear

/-!
# Black-last pieces of `Fᵢ S(N)` in the dimension count of Proposition 5.5

Webster, arXiv:1309.3796v2, proof of Proposition 5.5, (5.13)–(5.14). For Rouquier
parameters `Q` and a finite-dimensional module `N` over the parabolic factor algebra, the piece of
`Fᵢ S(N)` whose last strand is black of colour `j` is computed from `Fᵢ E_j S(N)` (Theorem 4.31)
and the description of `E_j S(N)` by the restrictions of `N`:

* `j ≠ i`: `finrank_fixSub_firstIndF_cross_bothQ` (`j` in both blocks),
  `finrank_fixSub_firstIndF_cross_leftQ` (first block only),
  `finrank_fixSub_firstIndF_cross_rightQ` (second block only);
* `j = i`: the same with the extra term `n dim S(N)`, `n = ⟨i, λ⟩`
  (`finrank_fixSub_firstIndF_self_bothQ`, `_self_left`, `_self_right`), and
  `finrank_fixSub_firstIndF_self_of_notMemQ` for `i ∉ θ + β`.

This is the version of `Prop55DimensionColour` for every Rouquier parameter `Q`: the black strands
carry the relations of Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3, Definition 1.1, `r = 1`) instead
of the KL III relations. Each declaration carries the suffix `Q`.
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
local notation "RDc" => coordinateDatum Λ C
local notation "TA" => TensorProductAlgebra k Q Λ
local notation "Φ" => appendBlackNU (Q := Q) (Λ := Λ)
local notation "D" => parabolicFactorAlgebra Q Λ
local notation "Si" j => (Singleton.singleton j : Multiset I)
local notation "dw" => downRightWeight (coordinateDatum Λ C) (coordinateRedWeights Λ C)

variable {P : Presentation.{0, 0}
    (signature (coordinateDatum Λ C) (redWeight (cyclotomicCoverWeightDatum Λ C))) k}
  (hP : CoverRelsNegligible.{0, 0, w} Λ C hR (coverDotCentral Λ C hR)
    (blockWeight (cyclotomicCoverWeightDatum Λ C) (cyclotomicCoverHighest (I := I)
      (ℓ := ℓ + 1)) 0 : I ⊕ Fin (ℓ + 1) → ℤ) P)
  (hwf : P.WFDom)
  (hQs : KLRSymm Q)

section Both

variable (i j : I) (θ₀ β₀ : Multiset I) (N : Type) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra Q Λ
    (({j} : Multiset I) + θ₀) (({j} : Multiset I) + β₀)) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ
    (({j} : Multiset I) + θ₀) (({j} : Multiset I) + β₀)) N]

/-- `Fᵢ S(N)` and `Fᵢ` of `S(N)` over `T(j + (θ₀ + β))` have the same black-last pieces. -/
theorem finrank_fixSub_firstIndF_lastStandardTQ (b : Option I) :
    Module.finrank k (fixSub k (FirstIndF QL Λ i ((Si j) + θ₀) ((Si j) + β₀) N hQs)
        (lastStrandIdem QL Λ ((Si i) + (((Si j) + θ₀) + ((Si j) + β₀))) b)) =
      Module.finrank k (fixSub k (IndK k (LastStandardT QL Λ j θ₀ β₀ N hQs)
          (Φ i ((Si j) + (θ₀ + ((Si j) + β₀)))))
        (lastStrandIdem QL Λ ((Si i) + ((Si j) + (θ₀ + ((Si j) + β₀)))) b)) := by
  have h := finrank_fixSub_indK_transport (Q := QL) (Λ := Λ) i
    (add_assoc (Si j) θ₀ ((Si j) + β₀))
    (ParabolicStandardT QL Λ ((Si j) + θ₀) ((Si j) + β₀) N hQs)
    (LastStandardT QL Λ j θ₀ β₀ N hQs)
    (LinearEquiv.refl k (ParabolicStandard QL Λ ((Si j) + θ₀) ((Si j) + β₀) N))
    (fun t x => (congrArg (fun s => parabolicStandardAction QL Λ ((Si j) + θ₀) ((Si j) + β₀)
      N hQs s x) (castTensorProductAlgebra_cast_back _ (add_assoc _ _ _).symm t)).symm) b
  exact h.symm

include hP hwf in
/-- **The black-last piece of `Fᵢ S(N)` of colour `j ≠ i`, `j` in both blocks** (Webster,
arXiv:1309.3796v2, proof of Proposition 5.5): it has dimension
`dim Fᵢ S(₁E_j N) + dim Fᵢ S(₂E_j N)`. -/
theorem finrank_fixSub_firstIndF_cross_bothQ (hji : j ≠ i) [FiniteDimensional k N] :
    Module.finrank k (fixSub k (FirstIndF QL Λ i ((Si j) + θ₀) ((Si j) + β₀) N hQs)
        (lastStrandIdem QL Λ ((Si i) + (((Si j) + θ₀) + ((Si j) + β₀))) (some j))) =
      Module.finrank k (FirstIndF QL Λ i θ₀ ((Si j) + β₀) (LastResLeft QL Λ j θ₀ β₀ N) hQs) +
        Module.finrank k
          (FirstIndF QL Λ i ((Si j) + θ₀) β₀ (LastResRight QL Λ j θ₀ β₀ N) hQs) := by
  have ht := finrank_fixSub_firstIndF_lastStandardTQ (Λ := Λ) hQs i j θ₀ β₀ N (some j)
  have hc := finrank_fixSub_lastStrandIdem_indK_crossQ hP hwf i j (θ₀ + ((Si j) + β₀)) hji
    (LastStandardT QL Λ j θ₀ β₀ N hQs)
  have hp := finrank_indK_blackRes_lastStandardT (Λ := Λ) hR hQs i j θ₀ β₀ N
  omega

end Both

section BothSelf

variable (i : I) (θ₀ β₀ : Multiset I) (N : Type) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra Q Λ
    (({i} : Multiset I) + θ₀) (({i} : Multiset I) + β₀)) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ
    (({i} : Multiset I) + θ₀) (({i} : Multiset I) + β₀)) N]

include hP hwf in
/-- **The black-last piece of `Fᵢ S(N)` of colour `i`, `i` in both blocks** (Webster,
arXiv:1309.3796v2, proof of Proposition 5.5): it has dimension
`dim Fᵢ S(₁Eᵢ N) + dim Fᵢ S(₂Eᵢ N) + n dim S(N)`, `n = ⟨i, λ⟩`. -/
theorem finrank_fixSub_firstIndF_self_bothQ [FiniteDimensional k N] :
    (Module.finrank k (fixSub k (FirstIndF QL Λ i ((Si i) + θ₀) ((Si i) + β₀) N hQs)
        (lastStrandIdem QL Λ ((Si i) + (((Si i) + θ₀) + ((Si i) + β₀))) (some i))) : ℤ) =
      Module.finrank k (FirstIndF QL Λ i θ₀ ((Si i) + β₀) (LastResLeft QL Λ i θ₀ β₀ N) hQs) +
        Module.finrank k
          (FirstIndF QL Λ i ((Si i) + θ₀) β₀ (LastResRight QL Λ i θ₀ β₀ N) hQs) +
        ip (RDc) i (dw (((Si i) + θ₀) + ((Si i) + β₀))) *
          Module.finrank k (ParabolicStandard QL Λ ((Si i) + θ₀) ((Si i) + β₀) N) := by
  have : FiniteDimensional k (LastStandardT QL Λ i θ₀ β₀ N hQs) :=
    finiteDimensional_parabolicStandard_of_finiteDimensional (Λ := Λ) hR hQs _ _ N
  have ht := finrank_fixSub_firstIndF_lastStandardTQ (Λ := Λ) hQs i i θ₀ β₀ N (some i)
  have hs := finrank_fixSub_lastStrandIdem_indK_selfQ hP hwf i (θ₀ + ((Si i) + β₀))
    (LastStandardT QL Λ i θ₀ β₀ N hQs)
  have hs' : (Module.finrank k (fixSub k (IndK k (LastStandardT QL Λ i θ₀ β₀ N hQs)
          (Φ i ((Si i) + (θ₀ + ((Si i) + β₀)))))
        (lastStrandIdem QL Λ ((Si i) + ((Si i) + (θ₀ + ((Si i) + β₀)))) (some i))) : ℤ) =
      Module.finrank k (IndK k (BlackRes (Q := QL) (Λ := Λ) i (θ₀ + ((Si i) + β₀))
        (LastStandardT QL Λ i θ₀ β₀ N hQs)) (Φ i (θ₀ + ((Si i) + β₀)))) +
        ip (RDc) i (dw ((Si i) + (θ₀ + ((Si i) + β₀)))) *
          Module.finrank k (ParabolicStandard QL Λ ((Si i) + θ₀) ((Si i) + β₀) N) := hs
  have hp := finrank_indK_blackRes_lastStandardT (Λ := Λ) hR hQs i i θ₀ β₀ N
  have hw : dw ((Si i) + (θ₀ + ((Si i) + β₀))) = dw (((Si i) + θ₀) + ((Si i) + β₀)) :=
    congrArg _ (add_assoc _ _ _).symm
  have h4 := congrArg (fun w => ip (RDc) i w *
    (Module.finrank k (ParabolicStandard QL Λ ((Si i) + θ₀) ((Si i) + β₀) N) : ℤ)) hw
  have htz : (_ : ℤ) = _ := congrArg (Nat.cast (R := ℤ)) ht
  have hpz : (_ : ℤ) = _ := congrArg (Nat.cast (R := ℤ)) hp
  linarith

end BothSelf

section Left

variable (i j : I) (θ₀ β : Multiset I) (N : Type) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra Q Λ
    (({j} : Multiset I) + θ₀) β) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ
    (({j} : Multiset I) + θ₀) β) N]

/-- `Fᵢ S(N)` and `Fᵢ` of `S(N)` over `T(j + (θ₀ + β))` have the same black-last pieces. -/
theorem finrank_fixSub_firstIndF_leftStandardTQ (b : Option I) :
    Module.finrank k (fixSub k (FirstIndF QL Λ i ((Si j) + θ₀) β N hQs)
        (lastStrandIdem QL Λ ((Si i) + (((Si j) + θ₀) + β)) b)) =
      Module.finrank k (fixSub k (IndK k (LeftStandardT QL Λ j θ₀ β N hQs)
          (Φ i ((Si j) + (θ₀ + β))))
        (lastStrandIdem QL Λ ((Si i) + ((Si j) + (θ₀ + β))) b)) := by
  have h := finrank_fixSub_indK_transport (Q := QL) (Λ := Λ) i
    (add_assoc (Si j) θ₀ β)
    (ParabolicStandardT QL Λ ((Si j) + θ₀) β N hQs)
    (LeftStandardT QL Λ j θ₀ β N hQs)
    (LinearEquiv.refl k (ParabolicStandard QL Λ ((Si j) + θ₀) β N))
    (fun t x => (congrArg (fun s => parabolicStandardAction QL Λ ((Si j) + θ₀) β
      N hQs s x) (castTensorProductAlgebra_cast_back _ (add_assoc _ _ _).symm t)).symm) b
  exact h.symm

include hP hwf in
/-- **The black-last piece of `Fᵢ S(N)` of colour `j ≠ i`, `j` in the first block only**
(Webster, arXiv:1309.3796v2, proof of Proposition 5.5): it has dimension `dim Fᵢ S(₁E_j N)`. -/
theorem finrank_fixSub_firstIndF_cross_leftQ (hji : j ≠ i) (hj : j ∉ β) :
    Module.finrank k (fixSub k (FirstIndF QL Λ i ((Si j) + θ₀) β N hQs)
        (lastStrandIdem QL Λ ((Si i) + (((Si j) + θ₀) + β)) (some j))) =
      Module.finrank k (FirstIndF QL Λ i θ₀ β (LeftResLeft QL Λ j θ₀ β N) hQs) := by
  have ht := finrank_fixSub_firstIndF_leftStandardTQ (Λ := Λ) hQs i j θ₀ β N (some j)
  have hc := finrank_fixSub_lastStrandIdem_indK_crossQ hP hwf i j (θ₀ + β) hji
    (LeftStandardT QL Λ j θ₀ β N hQs)
  let E : IndK k (BlackRes (Q := QL) (Λ := Λ) j (θ₀ + β) (LeftStandardT QL Λ j θ₀ β N hQs))
      (Φ i (θ₀ + β)) ≃ₗ[TA ((Si i) + (θ₀ + β))]
      IndK k (ParabolicStandardT QL Λ θ₀ β (LeftResLeft QL Λ j θ₀ β N) hQs) (Φ i (θ₀ + β)) :=
    Ind.mapEquiv (leftBlackResEquivT QL Λ j θ₀ β N hQs hj)
  have h1 := (E.restrictScalars k).finrank_eq
  have h1' : Module.finrank k (IndK k (BlackRes (Q := QL) (Λ := Λ) j (θ₀ + β)
      (LeftStandardT QL Λ j θ₀ β N hQs)) (Φ i (θ₀ + β))) =
      Module.finrank k (FirstIndF QL Λ i θ₀ β (LeftResLeft QL Λ j θ₀ β N) hQs) := h1
  omega

end Left

section LeftSelf

variable (i : I) (θ₀ β : Multiset I) (N : Type) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra Q Λ
    (({i} : Multiset I) + θ₀) β) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ
    (({i} : Multiset I) + θ₀) β) N]

include hP hwf in
/-- **The black-last piece of `Fᵢ S(N)` of colour `i`, `i` in the first block only** (Webster,
arXiv:1309.3796v2, proof of Proposition 5.5): it has dimension `dim Fᵢ S(₁Eᵢ N) + n dim S(N)`,
`n = ⟨i, λ⟩`. -/
theorem finrank_fixSub_firstIndF_self_leftQ (hi : i ∉ β) [FiniteDimensional k N] :
    (Module.finrank k (fixSub k (FirstIndF QL Λ i ((Si i) + θ₀) β N hQs)
        (lastStrandIdem QL Λ ((Si i) + (((Si i) + θ₀) + β)) (some i))) : ℤ) =
      Module.finrank k (FirstIndF QL Λ i θ₀ β (LeftResLeft QL Λ i θ₀ β N) hQs) +
        ip (RDc) i (dw (((Si i) + θ₀) + β)) *
          Module.finrank k (ParabolicStandard QL Λ ((Si i) + θ₀) β N) := by
  have : FiniteDimensional k (LeftStandardT QL Λ i θ₀ β N hQs) :=
    finiteDimensional_parabolicStandard_of_finiteDimensional (Λ := Λ) hR hQs _ _ N
  have ht := finrank_fixSub_firstIndF_leftStandardTQ (Λ := Λ) hQs i i θ₀ β N (some i)
  have hs := finrank_fixSub_lastStrandIdem_indK_selfQ hP hwf i (θ₀ + β)
    (LeftStandardT QL Λ i θ₀ β N hQs)
  have hs' : (Module.finrank k (fixSub k (IndK k (LeftStandardT QL Λ i θ₀ β N hQs)
          (Φ i ((Si i) + (θ₀ + β))))
        (lastStrandIdem QL Λ ((Si i) + ((Si i) + (θ₀ + β))) (some i))) : ℤ) =
      Module.finrank k (IndK k (BlackRes (Q := QL) (Λ := Λ) i (θ₀ + β)
        (LeftStandardT QL Λ i θ₀ β N hQs)) (Φ i (θ₀ + β))) +
        ip (RDc) i (dw ((Si i) + (θ₀ + β))) *
          Module.finrank k (ParabolicStandard QL Λ ((Si i) + θ₀) β N) := hs
  let E : IndK k (BlackRes (Q := QL) (Λ := Λ) i (θ₀ + β) (LeftStandardT QL Λ i θ₀ β N hQs))
      (Φ i (θ₀ + β)) ≃ₗ[TA ((Si i) + (θ₀ + β))]
      IndK k (ParabolicStandardT QL Λ θ₀ β (LeftResLeft QL Λ i θ₀ β N) hQs) (Φ i (θ₀ + β)) :=
    Ind.mapEquiv (leftBlackResEquivT QL Λ i θ₀ β N hQs hi)
  have h1 := (E.restrictScalars k).finrank_eq
  have h1' : Module.finrank k (IndK k (BlackRes (Q := QL) (Λ := Λ) i (θ₀ + β)
      (LeftStandardT QL Λ i θ₀ β N hQs)) (Φ i (θ₀ + β))) =
      Module.finrank k (FirstIndF QL Λ i θ₀ β (LeftResLeft QL Λ i θ₀ β N) hQs) := h1
  have hw : dw ((Si i) + (θ₀ + β)) = dw (((Si i) + θ₀) + β) := congrArg _ (add_assoc _ _ _).symm
  have h4 := congrArg (fun w => ip (RDc) i w *
    (Module.finrank k (ParabolicStandard QL Λ ((Si i) + θ₀) β N) : ℤ)) hw
  have htz : (_ : ℤ) = _ := congrArg (Nat.cast (R := ℤ)) ht
  have h1z : (_ : ℤ) = _ := congrArg (Nat.cast (R := ℤ)) h1'
  linarith

end LeftSelf

section Right

variable (i j : I) (θ β₀ : Multiset I) (N : Type) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra Q Λ
    θ (({j} : Multiset I) + β₀)) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ
    θ (({j} : Multiset I) + β₀)) N]

/-- `Fᵢ S(N)` and `Fᵢ` of `S(N)` over `T(j + (θ + β₀))` have the same black-last pieces. -/
theorem finrank_fixSub_firstIndF_rightStandardTQ (b : Option I) :
    Module.finrank k (fixSub k (FirstIndF QL Λ i θ ((Si j) + β₀) N hQs)
        (lastStrandIdem QL Λ ((Si i) + (θ + ((Si j) + β₀))) b)) =
      Module.finrank k (fixSub k (IndK k (RightStandardT QL Λ j θ β₀ N hQs)
          (Φ i ((Si j) + (θ + β₀))))
        (lastStrandIdem QL Λ ((Si i) + ((Si j) + (θ + β₀))) b)) := by
  have h := finrank_fixSub_indK_transport (Q := QL) (Λ := Λ) i
    (add_left_comm θ (Si j) β₀)
    (ParabolicStandardT QL Λ θ ((Si j) + β₀) N hQs)
    (RightStandardT QL Λ j θ β₀ N hQs)
    (LinearEquiv.refl k (ParabolicStandard QL Λ θ ((Si j) + β₀) N))
    (fun t x => (congrArg (fun s => parabolicStandardAction QL Λ θ ((Si j) + β₀)
      N hQs s x) (castTensorProductAlgebra_cast_back _ (add_left_comm _ _ _) t)).symm) b
  exact h.symm

include hP hwf in
/-- **The black-last piece of `Fᵢ S(N)` of colour `j ≠ i`, `j` in the second block only**
(Webster, arXiv:1309.3796v2, proof of Proposition 5.5): it has dimension `dim Fᵢ S(₂E_j N)`. -/
theorem finrank_fixSub_firstIndF_cross_rightQ (hji : j ≠ i) (hj : j ∉ θ) :
    Module.finrank k (fixSub k (FirstIndF QL Λ i θ ((Si j) + β₀) N hQs)
        (lastStrandIdem QL Λ ((Si i) + (θ + ((Si j) + β₀))) (some j))) =
      Module.finrank k (FirstIndF QL Λ i θ β₀ (RightResRight QL Λ j θ β₀ N) hQs) := by
  have ht := finrank_fixSub_firstIndF_rightStandardTQ (Λ := Λ) hQs i j θ β₀ N (some j)
  have hc := finrank_fixSub_lastStrandIdem_indK_crossQ hP hwf i j (θ + β₀) hji
    (RightStandardT QL Λ j θ β₀ N hQs)
  let E : IndK k (BlackRes (Q := QL) (Λ := Λ) j (θ + β₀) (RightStandardT QL Λ j θ β₀ N hQs))
      (Φ i (θ + β₀)) ≃ₗ[TA ((Si i) + (θ + β₀))]
      IndK k (ParabolicStandardT QL Λ θ β₀ (RightResRight QL Λ j θ β₀ N) hQs) (Φ i (θ + β₀)) :=
    Ind.mapEquiv (rightBlackResEquivT QL Λ j θ β₀ N hQs hj)
  have h1 := (E.restrictScalars k).finrank_eq
  have h1' : Module.finrank k (IndK k (BlackRes (Q := QL) (Λ := Λ) j (θ + β₀)
      (RightStandardT QL Λ j θ β₀ N hQs)) (Φ i (θ + β₀))) =
      Module.finrank k (FirstIndF QL Λ i θ β₀ (RightResRight QL Λ j θ β₀ N) hQs) := h1
  omega

end Right

section RightSelf

variable (i : I) (θ β₀ : Multiset I) (N : Type) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra Q Λ
    θ (({i} : Multiset I) + β₀)) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ
    θ (({i} : Multiset I) + β₀)) N]

include hP hwf in
/-- **The black-last piece of `Fᵢ S(N)` of colour `i`, `i` in the second block only** (Webster,
arXiv:1309.3796v2, proof of Proposition 5.5): it has dimension `dim Fᵢ S(₂Eᵢ N) + n dim S(N)`,
`n = ⟨i, λ⟩`. -/
theorem finrank_fixSub_firstIndF_self_rightQ (hi : i ∉ θ) [FiniteDimensional k N] :
    (Module.finrank k (fixSub k (FirstIndF QL Λ i θ ((Si i) + β₀) N hQs)
        (lastStrandIdem QL Λ ((Si i) + (θ + ((Si i) + β₀))) (some i))) : ℤ) =
      Module.finrank k (FirstIndF QL Λ i θ β₀ (RightResRight QL Λ i θ β₀ N) hQs) +
        ip (RDc) i (dw (θ + ((Si i) + β₀))) *
          Module.finrank k (ParabolicStandard QL Λ θ ((Si i) + β₀) N) := by
  have : FiniteDimensional k (RightStandardT QL Λ i θ β₀ N hQs) :=
    finiteDimensional_parabolicStandard_of_finiteDimensional (Λ := Λ) hR hQs _ _ N
  have ht := finrank_fixSub_firstIndF_rightStandardTQ (Λ := Λ) hQs i i θ β₀ N (some i)
  have hs := finrank_fixSub_lastStrandIdem_indK_selfQ hP hwf i (θ + β₀)
    (RightStandardT QL Λ i θ β₀ N hQs)
  have hs' : (Module.finrank k (fixSub k (IndK k (RightStandardT QL Λ i θ β₀ N hQs)
          (Φ i ((Si i) + (θ + β₀))))
        (lastStrandIdem QL Λ ((Si i) + ((Si i) + (θ + β₀))) (some i))) : ℤ) =
      Module.finrank k (IndK k (BlackRes (Q := QL) (Λ := Λ) i (θ + β₀)
        (RightStandardT QL Λ i θ β₀ N hQs)) (Φ i (θ + β₀))) +
        ip (RDc) i (dw ((Si i) + (θ + β₀))) *
          Module.finrank k (ParabolicStandard QL Λ θ ((Si i) + β₀) N) := hs
  let E : IndK k (BlackRes (Q := QL) (Λ := Λ) i (θ + β₀) (RightStandardT QL Λ i θ β₀ N hQs))
      (Φ i (θ + β₀)) ≃ₗ[TA ((Si i) + (θ + β₀))]
      IndK k (ParabolicStandardT QL Λ θ β₀ (RightResRight QL Λ i θ β₀ N) hQs) (Φ i (θ + β₀)) :=
    Ind.mapEquiv (rightBlackResEquivT QL Λ i θ β₀ N hQs hi)
  have h1 := (E.restrictScalars k).finrank_eq
  have h1' : Module.finrank k (IndK k (BlackRes (Q := QL) (Λ := Λ) i (θ + β₀)
      (RightStandardT QL Λ i θ β₀ N hQs)) (Φ i (θ + β₀))) =
      Module.finrank k (FirstIndF QL Λ i θ β₀ (RightResRight QL Λ i θ β₀ N) hQs) := h1
  have hw : dw ((Si i) + (θ + β₀)) = dw (θ + ((Si i) + β₀)) :=
    congrArg _ (add_left_comm _ _ _).symm
  have h4 := congrArg (fun w => ip (RDc) i w *
    (Module.finrank k (ParabolicStandard QL Λ θ ((Si i) + β₀) N) : ℤ)) hw
  have htz : (_ : ℤ) = _ := congrArg (Nat.cast (R := ℤ)) ht
  have h1z : (_ : ℤ) = _ := congrArg (Nat.cast (R := ℤ)) h1'
  linarith

end RightSelf

section NotMem

variable (i : I) (θ β : Multiset I) (N : Type) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra Q Λ
    θ β) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ
    θ β) N]

include hP hwf in
/-- **The black-last piece of `Fᵢ S(N)` of colour `i ∉ θ + β`** (Webster, arXiv:1309.3796v2,
proof of Proposition 5.5): it has dimension `n dim S(N)`, `n = ⟨i, λ⟩`. -/
theorem finrank_fixSub_firstIndF_self_of_notMemQ (hi : i ∉ θ + β) [FiniteDimensional k N] :
    (Module.finrank k (fixSub k (FirstIndF QL Λ i θ β N hQs)
        (lastStrandIdem QL Λ ((Si i) + (θ + β)) (some i))) : ℤ) =
      ip (RDc) i (dw (θ + β)) * Module.finrank k (ParabolicStandard QL Λ θ β N) := by
  have : FiniteDimensional k (ParabolicStandardT QL Λ θ β N hQs) :=
    finiteDimensional_parabolicStandard_of_finiteDimensional (Λ := Λ) hR hQs _ _ N
  have hs := finrank_fixSub_lastStrandIdem_indK_self_of_notMemQ hP hwf i (θ + β) hi
    (ParabolicStandardT QL Λ θ β N hQs)
  exact hs

end NotMem

end Categorification.Stendhal
