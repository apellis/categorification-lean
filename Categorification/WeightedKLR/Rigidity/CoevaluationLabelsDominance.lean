/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapGradedCoefficient
import Categorification.WeightedKLR.Rigidity.ReducedDividedNorm
import Categorification.WeightedKLR.Rigidity.CoevaluationDualWord

/-!
# The dual red label of the coevaluation word of `w₀` is not truncated

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.1,
Definition 7.1 and Lemma 7.3, and §7.3, Definition 7.18. For the divided coevaluation word `d`
of a dominant weight `λ` along a reduced expression `w` of an element `g` of the Weyl group, the
weight `λ - ν` of the coevaluation standard module (`ν` the black content of `d`) is `gλ`
(`rootSum_coevaluationWord_of_reduced`). At a left descent `i` of `g` the pairing
`⟨α_i^∨, gλ⟩` is nonpositive (`apply_coroot_nonpos_of_isLeftDescent`). If every simple
reflection is a left descent (`g = w₀`), the second red label `λ* = -w₀λ`
(`CycKLR.dualRedLabel`) is therefore read without truncation: this is the hypothesis `hdom` of
`CupCap.capBalanced_coevaluationLabels` and `CupCap.gradedCoevaluationHeadFunctor`.

The pairing of the weight datum `RD` (`⟨i, j_X⟩ = a_{ij}`) is compared with the realization `P`
of `C.toLusztig.cartanMatrix` through the root datum `projectiveRootDatum RD` (coroots `RD.iY`,
roots `⟨-, j_X⟩`) and the matching hypothesis `weight(α_j^∨) = ⟨j, λ⟩`, as in
`CycKLR.subsingleton_of_isLeftDescent_coevaluationWord`; both sides use `⟨α_i^∨, α_j⟩ = a_{ij}`
(`coevaluation_endpoint_pairing`), so no transpose enters.

* `pair_sub_multisetSum_iX`: `⟨i, λ - Σ_{j ∈ ν} j_X⟩` is the root-datum pairing
  `(λ - Σ ν)(i)` of `projectiveRootDatum RD`.
* `pair_sub_coevaluationWord_eq`: it equals `⟨α_i^∨, gλ⟩` in the realization.
* `pair_sub_coevaluationWord_nonpos`: the hypothesis `hdom` for the coevaluation word of `w₀`.
* `gradedCoevaluationLongestFunctor`, `gradedCoevaluationLongestFunctorForgetIso`: the graded
  coevaluation functor at `L_μ` for the divided coevaluation word of `w₀`, with `hdom`
  discharged.
-/

noncomputable section

open Module

namespace Categorification.Stendhal

open KLR KLR.CycKLR KLR.KLRAlgebra QuantumGroup QuantumGroup.UDot

variable {I : Type} [Fintype I] [DecidableEq I] {C : CartanDatum I}
  {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (highest : X)

omit [Fintype I] [DecidableEq I] in
/-- The pairing `⟨i, λ - Σ_{j ∈ ν} j_X⟩` of the weight datum is the pairing of the root datum
`projectiveRootDatum RD` of `λ - Σ_j ν_j j'` with the coroot `i`. -/
theorem pair_sub_multisetSum_iX [DecidableEq I] (ν : Multiset I) (i : I) :
    RD.pair (RD.iY i) (highest - (ν.map RD.iX).sum) =
      (RD.pair.flip highest - (projectiveRootDatum RD).rootSum ν.toFinsupp)
        ((projectiveRootDatum RD).coroot i) := by
  induction ν using Multiset.induction_on with
  | empty => simp [projectiveRootDatum]
  | cons a s ih =>
    rw [← Multiset.singleton_add, Multiset.toFinsupp_add, Multiset.toFinsupp_singleton,
      LusztigCartanDatum.RootDatum.rootSum_add,
      LusztigCartanDatum.RootDatum.rootSum_single, Multiset.map_add, Multiset.map_singleton,
      Multiset.sum_add, Multiset.sum_singleton]
    have h1 : RD.pair (RD.iY i) (highest - (RD.iX a + (s.map RD.iX).sum)) =
        RD.pair (RD.iY i) (highest - (s.map RD.iX).sum) - RD.pair (RD.iY i) (RD.iX a) := by
      rw [show highest - (RD.iX a + (s.map RD.iX).sum) =
        (highest - (s.map RD.iX).sum) - RD.iX a by abel, map_sub]
    rw [h1, ih]
    simp [projectiveRootDatum]
    abel

variable {K H : Type*} [Field K] [ConditionallyCompleteLinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup H] [Module K H]
  (P : Matrix.Realization C.toLusztig.cartanMatrix K H) (weight : P.integralWeights)
  (match_weight : ∀ i, (weight : Dual K H) (P.coroot i) = (RD.pair (RD.iY i) highest : K))

local notation "hCartan" => C.toLusztig.isGeneralizedCartan_cartanMatrix
local notation "Dc" => P.cartanDatum hCartan
local notation "cs" => P.coxeterSystem hCartan

include match_weight in
/-- **The weight of the coevaluation standard module is `gλ`**: for a nonnegative reflection
path `w` (e.g. a reduced expression, `nonnegativeReflectionPath_of_reduced`), the pairing
`⟨i, λ - ν⟩` with `ν` the content of the coevaluation word is the coroot pairing of the endpoint
`s_{w_k} ⋯ s_{w_1} λ` of the path. -/
theorem pair_sub_coevaluationWord_eq (w : List I) (hw : NonnegativeReflectionPath Dc weight w)
    (i : I) :
    RD.pair (RD.iY i) (highest - ((coevaluationWord Dc weight w : Multiset I).map RD.iX).sum) =
      (Dc).coroot i (w.foldl (fun μ j => (Dc).reflection j μ) weight) := by
  rw [pair_sub_multisetSum_iX]
  exact coevaluation_endpoint_pairing (projectiveRootDatum RD) P (RD.pair.flip highest) weight
    match_weight w hw i

include match_weight in
/-- **The hypothesis `hdom` for the coevaluation word of a reduced expression**: at a left
descent `i` of the Weyl element `g` of `w.reverse`, `⟨i, λ - ν⟩ = ⟨α_i^∨, gλ⟩ ≤ 0`. -/
theorem pair_sub_coevaluationWord_nonpos_of_isLeftDescent
    (hweight : P.IsDominantIntegral (weight : Dual K H)) (w : List I)
    (hw : (cs).IsReduced w.reverse) (i : I) (hi : (cs).IsLeftDescent ((cs).wordProd w.reverse) i) :
    RD.pair (RD.iY i)
      (highest - ((expandDiv (coevaluationDividedWord Dc weight w) : Multiset I).map RD.iX).sum)
        ≤ 0 := by
  rw [expand_coevaluationDividedWord, pair_sub_coevaluationWord_eq RD highest P weight
    match_weight w (nonnegativeReflectionPath_of_reduced P hCartan weight hweight w hw)]
  have h := apply_coroot_nonpos_of_isLeftDescent hweight hi
  rw [← coe_foldl_reflection_cartanDatum P hCartan, ← P.coroot_cartanDatum_cast hCartan] at h
  exact_mod_cast h

include match_weight in
/-- **The dual red label of the coevaluation word of `w₀` is not truncated** (the hypothesis
`hdom` of `CupCap.gradedCoevaluationHeadFunctor`): if every simple reflection is a left descent
of the Weyl element of `w.reverse`, then `⟨i, λ - ν⟩ ≤ 0` for every `i`. -/
theorem pair_sub_coevaluationWord_nonpos
    (hweight : P.IsDominantIntegral (weight : Dual K H)) (w : List I)
    (hw : (cs).IsReduced w.reverse)
    (hlong : ∀ i, (cs).IsLeftDescent ((cs).wordProd w.reverse) i) (i : I) :
    RD.pair (RD.iY i)
      (highest - ((expandDiv (coevaluationDividedWord Dc weight w) : Multiset I).map RD.iX).sum)
        ≤ 0 :=
  pair_sub_coevaluationWord_nonpos_of_isLeftDescent RD highest P weight match_weight hweight w hw
    i (hlong i)

namespace CupCap

open CategoryTheory DG Categorification.Graded CycKLR KLRAlgebra
open scoped DG.DegreeZero

universe v w

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [Fintype I] [DecidableEq I] {k : Type} [Field k] {C : CartanDatum I}
  {Q : I → I → MvPolynomial (Fin 2) k} (hP : IsRouquierQ C Q) (Λ : I → ℕ)
  {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (highest : X)
  (hΛ : ∀ i, (Λ i : ℤ) = RD.pair (RD.iY i) highest)
  {K H : Type*} [Field K] [ConditionallyCompleteLinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup H] [Module K H]
  (P : Matrix.Realization C.toLusztig.cartanMatrix K H) (weight : P.integralWeights)
  (match_weight : ∀ i, (weight : Dual K H) (P.coroot i) = (RD.pair (RD.iY i) highest : K))
  (hweight : P.IsDominantIntegral (weight : Dual K H)) (w : List I)
  (hw : (P.coxeterSystem C.toLusztig.isGeneralizedCartan_cartanMatrix).IsReduced w.reverse)
  (hlong : ∀ i, (P.coxeterSystem C.toLusztig.isGeneralizedCartan_cartanMatrix).IsLeftDescent
    ((P.coxeterSystem C.toLusztig.isGeneralizedCartan_cartanMatrix).wordProd w.reverse) i)

set_option hygiene false in
local notation "dw" => coevaluationDividedWord
  (P.cartanDatum C.toLusztig.isGeneralizedCartan_cartanMatrix) weight w
set_option hygiene false in
local notation "ν₂" => (expandDiv (dw) : Multiset I)
set_option hygiene false in
local notation "Λ₂" => coevaluationLabels Λ RD highest ν₂
set_option hygiene false in
local notation "dC" => (fun i => C.dot i i / 2 : I → ℤ)

variable {ℓ : ℕ} {Λt : Fin ℓ → I →₀ ℕ} {j : ℕ} {hj : j ≤ ℓ} {ν : Multiset I}

set_option hygiene false in
local notation "SB" => oppositeGrade (tensorProductGrade
  (stendhalGradingDatum (plusLabels Λt (Λ₂) j hj) hP.gradingDatum dC (dotDegree C hP)) (ν + ν₂))
set_option hygiene false in
local notation "ST" => oppositeGrade (tensorProductGrade
  (stendhalGradingDatum Λt hP.gradingDatum dC (dotDegree C hP)) ν)
set_option hygiene false in
local notation "At" => TensorProductAlgebra k Q Λt ν
set_option hygiene false in
local notation "Ab" => TensorProductAlgebra k Q (plusLabels Λt (Λ₂) j hj) (ν + ν₂)
set_option hygiene false in
local notation "Lμ" => ViaQuotient k Q (Λ₂) ν₂ (coevaluationHead Q Λ RD highest (dw))

/-- **The graded coevaluation functor at `L_μ` for the coevaluation word of `w₀`**
(arXiv:1309.3796v3, Definition 7.18 with Definition 7.1): `gradedCoevaluationHeadFunctor` for
the divided coevaluation word of a reduced expression `w` of the longest element (every simple
reflection a left descent), with the hypothesis `hdom` discharged by
`pair_sub_coevaluationWord_nonpos`. The realization `P` and the integral weight `weight`
matching `highest` (`match_weight`) carry the Weyl group. -/
def gradedCoevaluationLongestFunctor (s : ℤ) :
    letI := gradedAlgebraInternalGrading (SB)
    letI := gradedAlgebraInternalGrading (ST)
    letI := gradedAlgebraBigradedDGRing (SB)
    letI := gradedAlgebraBigradedDGRing (ST)
    [CatModule.HasDerivedCategory.{v,0} (WeightCategory Abᵐᵒᵖ)] →
    [CatModule.HasDerivedCategory.{v,0} (WeightCategory Atᵐᵒᵖ)] →
    CatModule.DerivedCategory.{v,0} (WeightCategory Atᵐᵒᵖ) ⥤
      CatModule.DerivedCategory.{v,0} (WeightCategory Abᵐᵒᵖ) :=
  gradedCoevaluationHeadFunctor (Λt := Λt) (j := j) (hj := hj) (ν := ν) hP Λ RD highest (dw) hΛ
    (Stendhal.pair_sub_coevaluationWord_nonpos RD highest P weight match_weight hweight w hw
      hlong) s

/-- **The graded coevaluation functor of `w₀` forgets to the ungraded one**
(arXiv:1309.3796v3, Definition 7.18): `gradedCoevaluationHeadFunctorForgetIso` with `hdom`
discharged. -/
def gradedCoevaluationLongestFunctorForgetIso (s : ℤ) :
    letI := gradedAlgebraInternalGrading (SB)
    letI := gradedAlgebraInternalGrading (ST)
    letI := gradedAlgebraBigradedDGRing (SB)
    letI := gradedAlgebraBigradedDGRing (ST)
    [CatModule.HasDerivedCategory.{v,0} (WeightCategory Abᵐᵒᵖ)] →
    [CatModule.HasDerivedCategory.{v,0} (WeightCategory Atᵐᵒᵖ)] →
    [DG.HasDerivedCategory.{w,0} Abᵐᵒᵖ] → [DG.HasDerivedCategory.{w,0} Atᵐᵒᵖ] →
    (gradedCoevaluationLongestFunctor hP Λ RD highest hΛ P weight match_weight hweight w hw
        hlong s ⋙ CatModule.weightForgetDerived Abᵐᵒᵖ ≅
      CatModule.weightForgetDerived Atᵐᵒᵖ ⋙
        coevaluationFunctor.{0, w} k Q Λt (Λ₂) j hj ν ν₂ Lμ) :=
  gradedCoevaluationHeadFunctorForgetIso (Λt := Λt) (j := j) (hj := hj) (ν := ν) hP Λ RD
    highest (dw) hΛ
    (Stendhal.pair_sub_coevaluationWord_nonpos RD highest P weight match_weight hweight w hw
      hlong) s

end CupCap

end Categorification.Stendhal
