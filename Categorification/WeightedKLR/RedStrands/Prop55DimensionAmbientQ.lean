/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.Prop55DimensionAmbient
import Categorification.WeightedKLR.RedStrands.Prop55DimensionFinite
import Categorification.WeightedKLR.RedStrands.BlackModuleEFOutsideContentCLQ
import Categorification.WeightedKLR.RedStrands.BlackModuleSecondFactorCommutationQ

/-!
# Black-last pieces of `Fᵢ` in the dimension count of Proposition 5.5

Webster, arXiv:1309.3796v2, proof of Proposition 5.5. In the dimension count (5.13)–(5.14) the
module `Fᵢ S(N)` over `T(i + ν)` is split according to the last strand. This file computes the
piece whose last strand is black of colour `j`, for Rouquier parameters `Q`, in terms of
`Fᵢ E_j`:

* `finrank_fixSub_lastStrandIdem_indK_crossQ`: for `j ≠ i`, the piece of `Fᵢ X` is `Fᵢ E_j X`
  (Webster, Theorem 4.31, `E_j Fᵢ ≅ Fᵢ E_j`).
* `finrank_fixSub_lastStrandIdem_indK_selfQ`: the piece of `Fᵢ X` of colour `i` has dimension
  `dim Fᵢ Eᵢ X + n dim X`, `n = ⟨i, λ⟩` (Webster, Theorem 4.31, `Eᵢ Fᵢ ≅ Fᵢ Eᵢ ⊕ id^n`).
* `finrank_fixSub_lastStrandIdem_indK_self_of_notMemQ`: for `i ∉ ν`, it has dimension `n dim X`.

This is the version of `Prop55DimensionAmbient` for every Rouquier parameter `Q`: the black strands
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

section CL

variable {I : Type} {ℓ : ℕ} {Λ : Fin (ℓ + 1) → I →₀ ℕ} {C : CartanDatum I}
  {k : Type} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {hQ : IsRouquierQ C Q}

local notation "RDc" => coordinateDatum Λ C
local notation "TA" => TensorProductAlgebra k Q Λ
local notation "Φ" => appendBlackNU (Q := Q) (Λ := Λ)

variable {P : Presentation.{0, 0}
    (signature (coordinateDatum Λ C) (redWeight (cyclotomicCoverWeightDatum Λ C))) k}
  (hP : CoverRelsNegligible.{0, 0, w} Λ C hQ (coverDotCentral Λ C hQ)
    (blockWeight (cyclotomicCoverWeightDatum Λ C) (cyclotomicCoverHighest (I := I)
      (ℓ := ℓ + 1)) 0 : I ⊕ Fin (ℓ + 1) → ℤ) P)
  (hwf : P.WFDom)

include hP hwf in
/-- **The black-last piece of `Fᵢ X` of colour `j ≠ i`** (Webster, arXiv:1309.3796v2, Theorem
4.31, in the proof of Proposition 5.5): for a `T(j + ρ)`-module `X`, the piece of `Fᵢ X` whose
last strand is black of colour `j` has the dimension of `Fᵢ E_j X`. -/
theorem finrank_fixSub_lastStrandIdem_indK_crossQ (i j : I) (ρ : Multiset I) (hji : j ≠ i)
    (X : Type) [AddCommGroup X] [Module k X] [Module (TA (({j} : Multiset I) + ρ)) X]
    [IsScalarTower k (TA (({j} : Multiset I) + ρ)) X] :
    Module.finrank k (fixSub k (IndK k X (Φ i (({j} : Multiset I) + ρ)))
        (lastStrandIdem Q Λ (({i} : Multiset I) + (({j} : Multiset I) + ρ)) (some j))) =
      Module.finrank k (IndK k (BlackRes (Q := Q) (Λ := Λ) j ρ X) (Φ i ρ)) := by
  have h0 := finrank_fixSub_lastStrandIdem_eq_res (Q := Q) (Λ := Λ) j
    (cross_content i j ρ)
    (IndK k X (Φ i (({j} : Multiset I) + ρ)))
  have hc := finrank_restrictScalars_eq_of_equiv (k := k)
    (clLeftBlackModuleCrossEquivQ hP hwf i j ρ X hji)
  have hc' : Module.finrank k (RestrictScalars k (TA (({i} : Multiset I) + ρ))
      (Res (appendBlackNUOfEq Q Λ j (cross_content i j ρ))
        (IndK k X (Φ i (({j} : Multiset I) + ρ))))) =
      Module.finrank k (RestrictScalars k (TA (({i} : Multiset I) + ρ))
        (IndK k (Res (Φ j ρ) X) (Φ i ρ))) := hc
  let E : IndK k (BlackRes (Q := Q) (Λ := Λ) j ρ X) (Φ i ρ)
      ≃ₗ[TA (({i} : Multiset I) + ρ)] IndK k (Res (Φ j ρ) X) (Φ i ρ) :=
    Ind.mapEquiv (blackResEquivRes Q Λ j ρ X)
  have h1 := (E.restrictScalars k).finrank_eq
  have h2 := finrank_restrictScalars_of_tower (k := k)
    (T := TensorProductAlgebra k Q Λ (({i} : Multiset I) + ρ))
    (X := IndK k (Res (Φ j ρ) X) (Φ i ρ))
  omega

set_option hygiene false in
local notation "iρ" => (({i} : Multiset I) + ρ)

include hP hwf in
/-- **The black-last piece of `Fᵢ X` of colour `i`** (Webster, arXiv:1309.3796v2, Theorem
4.31, in the proof of Proposition 5.5): for a finite-dimensional `T(i + ρ)`-module `X`, the piece
of `Fᵢ X` whose last strand is black of colour `i` has dimension `dim Fᵢ Eᵢ X + n dim X`, with
`n = ⟨i, λ⟩` for the right weight `λ` of content `i + ρ`. -/
theorem finrank_fixSub_lastStrandIdem_indK_selfQ (i : I) (ρ : Multiset I)
    (X : Type) [AddCommGroup X] [Module k X] [Module (TA iρ) X]
    [IsScalarTower k (TA iρ) X] [FiniteDimensional k X] :
    (Module.finrank k (fixSub k (IndK k X (Φ i iρ))
        (lastStrandIdem Q Λ (({i} : Multiset I) + iρ)
          (some i))) : ℤ) =
      Module.finrank k (IndK k (BlackRes (Q := Q) (Λ := Λ) i ρ X) (Φ i ρ)) +
        ip (RDc) i (downRightWeight (RDc) (coordinateRedWeights Λ C) iρ) *
          Module.finrank k X := by
  have := tensorProductAlgebra_finite Λ iρ hQ
  have := tensorProductAlgebra_finite Λ
    (({i} : Multiset I) + iρ) hQ
  have : Module.Finite (TA iρ) X :=
    Module.Finite.of_restrictScalars_finite k _ X
  have : FiniteDimensional k (IndK k X (Φ i iρ)) :=
    IndK.finite_restrict k _ _
  let := Res.moduleK k (Φ i iρ) (IndK k X (Φ i iρ))
  have := Res.isScalarTowerK k (Φ i iρ) (IndK k X (Φ i iρ))
  have : FiniteDimensional k (Res (Φ i iρ) (IndK k X (Φ i iρ))) :=
    finiteDimensional_res_of_nonUnitalAlgHom (appendBlack Q Λ i iρ) _
  have : FiniteDimensional k (RestrictScalars k (TA iρ)
      (Res (Φ i iρ) (Ind X (Φ i iρ)))) :=
    finiteDimensional_restrictScalars_of_tower (X := Res (Φ i iρ) (IndK k X _))
  let := Res.moduleK k (Φ i ρ) X
  have := Res.isScalarTowerK k (Φ i ρ) X
  have : FiniteDimensional k (Res (Φ i ρ) X) :=
    finiteDimensional_res_of_nonUnitalAlgHom (appendBlack Q Λ i ρ) X
  have := tensorProductAlgebra_finite Λ ρ hQ
  have : Module.Finite (TA ρ) (Res (Φ i ρ) X) := Module.Finite.of_restrictScalars_finite k _ _
  have : FiniteDimensional k (IndK k (Res (Φ i ρ) X) (Φ i ρ)) := IndK.finite_restrict k _ _
  have : FiniteDimensional k (RestrictScalars k (TA iρ)
      (Ind (Res (Φ i ρ) X) (Φ i ρ))) :=
    finiteDimensional_restrictScalars_of_tower (X := IndK k (Res (Φ i ρ) X) (Φ i ρ))
  have : FiniteDimensional k (RestrictScalars k (TA iρ) X) :=
    finiteDimensional_restrictScalars_of_tower
  have h := finrank_clLeftEF_eqQ hP hwf i ρ X
  have h' : (Module.finrank k (RestrictScalars k (TA iρ)
      (Res (Φ i iρ) (IndK k X (Φ i iρ)))) : ℤ) =
      Module.finrank k (RestrictScalars k (TA iρ) (IndK k (Res (Φ i ρ) X) (Φ i ρ))) +
        ip (RDc) i (downRightWeight (RDc) (coordinateRedWeights Λ C) iρ) *
          Module.finrank k (RestrictScalars k (TA iρ) X) := h
  have h0 := finrank_fixSub_lastStrandIdem_eq_res_self (Q := Q) (Λ := Λ) i iρ
    (IndK k X (Φ i iρ))
  have h0z : (_ : ℤ) = _ := congrArg (Nat.cast (R := ℤ)) h0
  let E : IndK k (BlackRes (Q := Q) (Λ := Λ) i ρ X) (Φ i ρ)
      ≃ₗ[TA iρ]       IndK k (Res (Φ i ρ) X) (Φ i ρ) :=
    Ind.mapEquiv (blackResEquivRes Q Λ i ρ X)
  have h1 := (E.restrictScalars k).finrank_eq
  have h2 := finrank_restrictScalars_of_tower (k := k)
    (T := TensorProductAlgebra k Q Λ iρ) (X := IndK k (Res (Φ i ρ) X) (Φ i ρ))
  have h3 := finrank_restrictScalars_of_tower (k := k)
    (T := TensorProductAlgebra k Q Λ iρ) (X := X)
  have h1z : (_ : ℤ) = _ := congrArg (Nat.cast (R := ℤ)) h1
  have h2z : (_ : ℤ) = _ := congrArg (Nat.cast (R := ℤ)) h2
  have h3z : (_ : ℤ) = _ := congrArg (Nat.cast (R := ℤ)) h3
  have h4 := congrArg
    (fun t : ℤ => ip (RDc) i (downRightWeight (RDc) (coordinateRedWeights Λ C) iρ) * t) h3z
  linarith

include hP hwf in
/-- **The black-last piece of `Fᵢ X` of colour `i ∉ ν`** (Webster, arXiv:1309.3796v2, Theorem
4.31 with `Eᵢ X = 0`, in the proof of Proposition 5.5): for a finite-dimensional `T(ν)`-module
`X`, the piece of `Fᵢ X` whose last strand is black of colour `i` has dimension `n dim X`, with
`n = ⟨i, λ⟩` for the right weight `λ` of content `ν`. -/
theorem finrank_fixSub_lastStrandIdem_indK_self_of_notMemQ (i : I) (ν : Multiset I) (hi : i ∉ ν)
    (X : Type) [AddCommGroup X] [Module k X] [Module (TA ν) X]
    [IsScalarTower k (TA ν) X] [FiniteDimensional k X] :
    (Module.finrank k (fixSub k (IndK k X (Φ i ν))
        (lastStrandIdem Q Λ (({i} : Multiset I) + ν) (some i))) : ℤ) =
      ip (RDc) i (downRightWeight (RDc) (coordinateRedWeights Λ C) ν) *
          Module.finrank k X := by
  have : FiniteDimensional k (RestrictScalars k (TA ν) X) :=
    finiteDimensional_restrictScalars_of_tower
  have h := finrank_clLeftEF_eq_of_notMemQ hP hwf i ν X hi
  rw [finrank_fixSub_lastStrandIdem_eq_res i rfl,
    ← finrank_restrictScalars_of_tower (T := TensorProductAlgebra k Q Λ ν) (X := X)]
  exact h

end CL

end Categorification.Stendhal
