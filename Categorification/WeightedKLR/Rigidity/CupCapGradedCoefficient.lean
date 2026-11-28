/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapGradedFunctor
import Categorification.WeightedKLR.Rigidity.CupCapGradedHead
import Categorification.WeightedKLR.Rigidity.CupCapCoevaluation
import Categorification.WeightedKLR.RedStrands.SingleRedGrading
import Categorification.WeightedKLR.RedStrands.DividedProjectives

/-!
# The graded coefficient module `L_μ` of the cap bimodule

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.1,
Lemma 7.3, and §7.3, Definitions 7.15 and 7.18. Webster's coefficient module `L_μ` of the cap
bimodule `K^{λ⁺}_λ` is the simple head of the coevaluation projective
(`Stendhal.coevaluationHead`): the quotient of the right projective `e T` of the wrap idempotent
`e = wrapIdem z₀` of the divided-power idempotent `z₀`, by the images of the cut projectives.
Its grading is the diagram grading (Definitions 4.4–4.7) with the KL degrees of the Rouquier
grading datum, `d_i = (α_i, α_i) / 2`.

* The wrap idempotent has degree zero (`wrapIdem_mem_tensorProductGrade`): the cyclotomic
  projection inserting the first red strand and the appending of the second red strand preserve
  degrees, once the grading datum of the first red strand is identified with the restriction of
  the grading datum of both (`restrictRedGrading_stendhalGradingDatum`).
* Hence `L_μ` is a graded right module over `T̃^{(μ, μ*)}` (`isGradedCoeff_coevaluationHead`,
  the hypothesis `CupCap.IsGradedCoeff` of the grading of `K̃^{λ⁺}_λ`).
* The strands at the maximum have weight `μ - w₀μ = μ + μ*`, so a black strand crossing all of
  them has degree zero (`capBalanced_coevaluationLabels`, the hypothesis `CupCap.CapBalanced`).
  The input is that the second red label `⟨α_i^∨, λ*⟩ = -⟨α_i^∨, λ - ν⟩` is not truncated
  (`hdom : ⟨α_i^∨, λ - ν⟩ ≤ 0`, the hypothesis of `CycKLR.dualHighest_pair`), which holds for the
  coevaluation word of the longest element, where `λ - ν = w₀λ`.

The graded coevaluation functor with `L = L_μ` (`gradedCoevaluationHeadFunctor`) and its
comparison with the ungraded coevaluation functor (`gradedCoevaluationHeadFunctorForgetIso`)
then carry no grading hypothesis beyond `hdom`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR

section Restrict

variable {I k : Type*} [CommRing k] {ℓ : ℕ} {Q : I → I → MvPolynomial (Fin 2) k}
  (Λ : Fin (ℓ + 1) → I →₀ ℕ) (G : KLR.GradingDatum Q) (d : I → ℤ)
  (hd : ∀ i, G.degX i = 2 * d i)

/-- **Omitting the last red strand from Webster's grading datum** gives Webster's grading
datum of the earlier red labels (arXiv:1309.3796v3, Definition 4.4). -/
theorem restrictRedGrading_stendhalGradingDatum :
    restrictRedGrading Q Λ (stendhalGradingDatum Λ G d hd) =
      stendhalGradingDatum (Λ ∘ Fin.castSucc) G d hd := by
  unfold restrictRedGrading stendhalGradingDatum
  congr 1
  · funext a
    cases a <;> rfl
  · funext a b
    cases a <;> cases b <;> rfl

end Restrict

namespace TwoRedErase

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin 2 → I →₀ ℕ) (ν : Multiset I)
  (G : KLR.GradingDatum Q) (d : I → ℤ) (hd : ∀ i, G.degX i = 2 * d i)

/-- **The wrap idempotent preserves degrees**: for `z` of degree `n` in the cyclotomic quotient
at the first red strand, `wrapIdem z` (the first red strand on the left, the second on the
right) has degree `n` in `T^{(λ₁, λ₂)}` (arXiv:1309.3796v3, Definitions 4.4–4.7). -/
theorem wrapIdem_mem_tensorProductGrade {n : ℤ}
    {z : CycKLR k Q (fun i => Polynomial.X ^ Λ 0 i) ν}
    (hz : z ∈ CycKLR.grade G (Λ 0) ν n) :
    wrapIdem Q Λ ν z ∈ tensorProductGrade (stendhalGradingDatum Λ G d hd) ν n := by
  have h1 := SingleRed.cyclotomicEquiv_mem_grade (Λ ∘ Fin.castSucc) G d hd ν hz
  rw [← restrictRedGrading_stendhalGradingDatum Λ G d hd] at h1
  exact appendRed_mem_grade (ℓ := 1) Q Λ ν (stendhalGradingDatum Λ G d hd) h1

end TwoRedErase

namespace CupCap

open CycKLR KLRAlgebra QuantumGroup QuantumGroup.UDot MulOpposite DirectSum KL2

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [Fintype I] [DecidableEq I] {k : Type} [Field k] {C : CartanDatum I}
  {Q : I → I → MvPolynomial (Fin 2) k} (hP : IsRouquierQ C Q) (Λ : I → ℕ)
  {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y)
  (highest : X) (dw : List (I × ℕ))

set_option hygiene false in
local notation "ν₂" => (expandDiv dw : Multiset I)
set_option hygiene false in
local notation "Λ₂" => coevaluationLabels Λ RD highest ν₂
set_option hygiene false in
local notation "dC" => (fun i => C.dot i i / 2 : I → ℤ)
set_option hygiene false in
local notation "Gc" => stendhalGradingDatum (Λ₂) hP.gradingDatum dC (dotDegree C hP)
set_option hygiene false in
local notation "Tc" => TensorProductAlgebra k Q (Λ₂) ν₂
set_option hygiene false in
local notation "eW" => TwoRedErase.wrapIdem Q (Λ₂) ν₂ (dividedIdem Λ (Q := Q) dw)
set_option hygiene false in
local notation "cutC" => TwoRedErase.cutIdem Q (Λ₂) ν₂

omit [Fintype I] in
/-- The divided-power idempotent of a divided word has degree zero in the cyclotomic quotient
(KL I §2.5). -/
theorem dividedIdem_mem_grade :
    dividedIdem Λ (Q := Q) dw ∈ CycKLR.grade hP.gradingDatum Λ ν₂ 0 :=
  Graded.mem_map_of_mem _ (CycKLR.mk k Q _ _).toLinearMap
    (hP.gradingDatum.hflip_mem_grade (fun i j => congrArg Neg.neg (C.symm i j))
      (divIdem_mem_grade hP.gradingDatum (isBlocks_ofList dw rfl)))

/-- **The coevaluation wrap idempotent has degree zero** for Webster's grading of
`T^{(μ, μ*)}`. -/
theorem wrapIdem_dividedIdem_mem_grade : eW ∈ tensorProductGrade (Gc) ν₂ 0 :=
  TwoRedErase.wrapIdem_mem_tensorProductGrade (Λ₂) ν₂ hP.gradingDatum dC (dotDegree C hP)
    (dividedIdem_mem_grade hP Λ dw)

/-- The cut idempotents have degree zero. -/
theorem cutIdem_mem_grade (s : TwoRedErase.CutLoading ν₂) :
    cutC s ∈ tensorProductGrade (Gc) ν₂ 0 :=
  mk_e_mem_tensorProductGrade (Gc) ν₂ s.1.1 s.1.2

/-- **The grading of Webster's `L_μ`**: the diagram grading of the head of the coevaluation
projective (`Stendhal.headGrade`), on `L_μ` viewed as a module over `T̃^{(μ, μ*)}`. -/
def coevaluationHeadGrade (q : ℤ) :
    AddSubgroup (ViaQuotient k Q (Λ₂) ν₂ (coevaluationHead Q Λ RD highest dw)) :=
  headGrade (tensorProductGrade (Gc) ν₂) (wrapIdem_dividedIdem_mem_grade hP Λ RD highest dw)
    cutC (cutIdem_mem_grade hP Λ RD highest dw) q

theorem isInternal_coevaluationHeadGrade :
    IsInternal (coevaluationHeadGrade hP Λ RD highest dw) :=
  isInternal_headGrade (tensorProductGrade (Gc) ν₂)
    (wrapIdem_dividedIdem_mem_grade hP Λ RD highest dw) cutC
    (cutIdem_mem_grade hP Λ RD highest dw)

noncomputable instance coevaluationHeadDecomposition :
    Decomposition (coevaluationHeadGrade hP Λ RD highest dw) :=
  (isInternal_coevaluationHeadGrade hP Λ RD highest dw).chooseDecomposition _

/-- **`L_μ` is a graded right module over `T̃^{(μ, μ*)}`** (the hypothesis `IsGradedCoeff` of
the grading of the cap bimodule), for Webster's grading with the KL degrees. -/
theorem isGradedCoeff_coevaluationHead :
    IsGradedCoeff (Λc := Λ₂) (ν₀ := ν₂) hP.gradingDatum dC (dotDegree C hP)
      (coevaluationHeadGrade hP Λ RD highest dw) := by
  intro r p x hx v hv
  rw [ViaQuotient.smul_def]
  exact op_smul_mem_headGrade (tensorProductGrade (Gc) ν₂)
    (wrapIdem_dividedIdem_mem_grade hP Λ RD highest dw) cutC
    (cutIdem_mem_grade hP Λ RD highest dw) (Graded.mem_map_of_mem _ _ hx) hv

omit [Fintype I] [DecidableEq I] in
/-- `d_i ⟨α_i^∨, α_j⟩ = (α_i, α_j)` for `d_i = (α_i, α_i) / 2`. -/
theorem halfDot_mul_pair_iY_iX (i j : I) :
    C.dot i i / 2 * RD.pair (RD.iY i) (RD.iX j) = C.dot i j := by
  rw [RD.pair_iY_iX]
  obtain ⟨e, he⟩ := C.dot_self_even i
  obtain ⟨t, ht⟩ := C.dvd_two_mul i j
  have hne : C.dot i i ≠ 0 := (C.dot_self_pos i).ne'
  rw [ht, Int.mul_ediv_cancel_left _ hne, he, show e + e = 2 * e by ring,
    Int.mul_ediv_cancel_left _ two_ne_zero]
  have h2 : 2 * C.dot i j = 2 * (e * t) := by rw [ht, he]; ring
  omega

omit [DecidableEq I] in
/-- **The balance condition at the maximum of `L_μ`** (the hypothesis `CapBalanced` of the
grading of the cap bimodule): for the KL degrees, a black strand crossing all the strands at the
maximum (the red labels `λ, λ*` and the black weight `ν`) has degree
`-(ν, α_i) + d_i ⟨α_i^∨, λ + λ*⟩ = -(ν, α_i) + d_i ⟨α_i^∨, ν⟩ = 0`. The hypothesis `hdom`
(`⟨α_i^∨, λ - ν⟩ ≤ 0`) says that the second red label `λ*` is not truncated; it holds for the
coevaluation word of the longest element (`λ - ν = w₀λ`). -/
theorem capBalanced_coevaluationLabels (hΛ : ∀ i, (Λ i : ℤ) = RD.pair (RD.iY i) highest)
    (ν : Multiset I) (hdom : ∀ i, RD.pair (RD.iY i) (highest - (ν.map RD.iX).sum) ≤ 0) :
    CapBalanced (coevaluationLabels Λ RD highest ν) ν hP.gradingDatum dC := by
  have hsum : ∀ i, C.dot i i / 2 *
      ((coevaluationLabels Λ RD highest ν 0 i : ℤ) + coevaluationLabels Λ RD highest ν 1 i) =
      (ν.map fun i' => C.dot i i').sum := by
    intro i
    have h0 : (coevaluationLabels Λ RD highest ν 0 i : ℤ) = Λ i := rfl
    have h1 : (coevaluationLabels Λ RD highest ν 1 i : ℤ) =
        -(RD.pair (RD.iY i) (highest - (ν.map RD.iX).sum)) := by
      change ((-(RD.pair (RD.iY i) (highest - (ν.map RD.iX).sum))).toNat : ℤ) = _
      exact Int.toNat_of_nonneg (by linarith [hdom i])
    have hp : RD.pair (RD.iY i) (ν.map RD.iX).sum =
        (ν.map fun i' => RD.pair (RD.iY i) (RD.iX i')).sum := by
      rw [map_multiset_sum, Multiset.map_map]
      rfl
    rw [h0, h1, hΛ i, map_sub, neg_sub, add_sub_cancel, hp, ← Multiset.sum_map_mul_left]
    exact congrArg Multiset.sum (Multiset.map_congr rfl fun i' _ =>
      halfDot_mul_pair_iY_iX RD i i')
  intro i
  constructor
  · simp only [IsRouquierQ.gradingDatum_degΨ]
    rw [hsum i, Multiset.sum_map_neg, neg_add_eq_zero]
    exact congrArg Multiset.sum (Multiset.map_congr rfl fun i' _ => C.symm i' i)
  · simp only [IsRouquierQ.gradingDatum_degΨ]
    rw [hsum i, Multiset.sum_map_neg, neg_add_cancel]

variable (C) in
/-- **The grading shift of the coevaluation functor at `L_μ`**, in the grading
`coevaluationHeadGrade` (wrap generator in degree `0`): `2⟨μ, ρ⟩ + ⟨d⟩`, where
`2⟨μ, ρ⟩ = Σ_{i ∈ ν} d_i` is the `ρ`-degree of the black word of the coevaluation word
(`ν = μ - w₀μ`) and `⟨d⟩ = Σ_{(i, n) ∈ d} d_i n(n-1)/2` (`KL2.divAngle2`) moves the wrap generator
to the degree of the normalized divided-power projective (`KL2.dividedProjective`).

Webster, arXiv:1309.3796v3, proof of Proposition 7.20, prints the shift `(2⟨λ, ρ⟩)` (and
`[-2ρ^∨(λ)]`); for the categorification of `coev_μ` the index must be the inserted weight `μ`, as
in Definition 7.4 at `λ = ∅`: `coev_μ(1) = a⁻¹ [L_μ]` with
`a = (-1)^{2ρ^∨(μ)} q^{-2⟨μ,ρ⟩}` (proof of Proposition 7.5; `QuantumDual.dualLowestScalar_eq`).
With Webster's convention `M(s)_n = M_{n+s}`, `[M(s)] = q^s [M]` (the library's identification
inverts the grading variable, `FirstWeight.tensorModuleEquiv`), the shift is `+2⟨μ, ρ⟩` on
Webster's `L_μ`, and `+(2⟨μ, ρ⟩ + ⟨d⟩)` on `L_μ` with the grading used here. -/
def coevaluationHeadShift : ℤ :=
  ((expandDiv dw).map fun i => C.dot i i / 2).sum + divAngle2 C dw

section Functor

open CategoryTheory DG Categorification.Graded
open scoped DG.DegreeZero

universe v w

variable {ℓ : ℕ} {Λt : Fin ℓ → I →₀ ℕ} {j : ℕ} {hj : j ≤ ℓ} {ν : Multiset I}
  (hΛ : ∀ i, (Λ i : ℤ) = RD.pair (RD.iY i) highest)
  (hdom : ∀ i, RD.pair (RD.iY i) (highest - ((expandDiv dw : Multiset I).map RD.iX).sum) ≤ 0)

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
local notation "Lμ" => ViaQuotient k Q (Λ₂) ν₂ (coevaluationHead Q Λ RD highest dw)

/-- **The graded coevaluation functor at Webster's `L_μ`** (arXiv:1309.3796v3, Definition 7.18,
with Lemma 7.3): `gradedCoevaluationFunctor` for the coefficient module `L = L_μ` with its
diagram grading (`coevaluationHeadGrade`) and the KL degrees, translated by `s`. The grading
hypotheses `CapBalanced` and `IsGradedCoeff` are discharged by `capBalanced_coevaluationLabels`
(from `hΛ` and `hdom`) and `isGradedCoeff_coevaluationHead`. -/
def gradedCoevaluationHeadFunctor (s : ℤ) :
    letI := gradedAlgebraInternalGrading (SB)
    letI := gradedAlgebraInternalGrading (ST)
    letI := gradedAlgebraBigradedDGRing (SB)
    letI := gradedAlgebraBigradedDGRing (ST)
    [CatModule.HasDerivedCategory.{v,0} (WeightCategory Abᵐᵒᵖ)] →
    [CatModule.HasDerivedCategory.{v,0} (WeightCategory Atᵐᵒᵖ)] →
    CatModule.DerivedCategory.{v,0} (WeightCategory Atᵐᵒᵖ) ⥤
      CatModule.DerivedCategory.{v,0} (WeightCategory Abᵐᵒᵖ) :=
  gradedCoevaluationFunctor (Λ := Λt) (j := j) (hj := hj) (ν := ν) hP.gradingDatum dC
    (dotDegree C hP) (coevaluationHeadGrade hP Λ RD highest dw)
    (capBalanced_coevaluationLabels hP Λ RD highest hΛ _ hdom)
    (isGradedCoeff_coevaluationHead hP Λ RD highest dw) s

/-- **The graded coevaluation functor at `L_μ` forgets to the ungraded one**: forgetting the
weights after `gradedCoevaluationHeadFunctor` is `coevaluationFunctor` with `L = L_μ` after
forgetting the weights (arXiv:1309.3796v3, Definition 7.18). -/
def gradedCoevaluationHeadFunctorForgetIso (s : ℤ) :
    letI := gradedAlgebraInternalGrading (SB)
    letI := gradedAlgebraInternalGrading (ST)
    letI := gradedAlgebraBigradedDGRing (SB)
    letI := gradedAlgebraBigradedDGRing (ST)
    [CatModule.HasDerivedCategory.{v,0} (WeightCategory Abᵐᵒᵖ)] →
    [CatModule.HasDerivedCategory.{v,0} (WeightCategory Atᵐᵒᵖ)] →
    [DG.HasDerivedCategory.{w,0} Abᵐᵒᵖ] → [DG.HasDerivedCategory.{w,0} Atᵐᵒᵖ] →
    (gradedCoevaluationHeadFunctor hP Λ RD highest dw hΛ hdom s ⋙
        CatModule.weightForgetDerived Abᵐᵒᵖ ≅
      CatModule.weightForgetDerived Atᵐᵒᵖ ⋙
        coevaluationFunctor.{0, w} k Q Λt (Λ₂) j hj ν ν₂ Lμ) :=
  gradedCoevaluationFunctorForgetIso (Λ := Λt) (j := j) (hj := hj) (ν := ν) hP.gradingDatum dC
    (dotDegree C hP) (coevaluationHeadGrade hP Λ RD highest dw)
    (capBalanced_coevaluationLabels hP Λ RD highest hΛ _ hdom)
    (isGradedCoeff_coevaluationHead hP Λ RD highest dw) s

end Functor

end CupCap

end Categorification.Stendhal
