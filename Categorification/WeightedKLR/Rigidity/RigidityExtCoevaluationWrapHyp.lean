/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.RigidityExtDualBlock
import Categorification.WeightedKLR.Rigidity.SMoveDualLabels
import LieLean.GroupTheory.Coxeter.Longest

/-!
# The hypotheses of Lemma 7.3 for the coevaluation word and for its dual

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.1,
Lemma 7.3, and §7.3, proof of Proposition 7.22 (gap (c)). For the divided coevaluation word `d`
of a reduced expression `w` of the longest element, the reflected divided-power idempotent
`z₀ = 1_d` of `R^λ(ν)` satisfies the four properties used for the head of the wrap projective:
the cyclotomic relation of the second red strand on the last black strand, `z₀ ≠ 0`, every
nonzero element of `z₀ R^λ(ν)` generates `z₀`, and `z₀ R^λ(ν) z₀ = k z₀`
(`Stendhal.wrapHeadHypotheses_coevaluation`; these are the steps of
`Stendhal.finrank_ext_standard_coevaluationHead`, stated separately).

The X side of the S-move is the coevaluation head at the dual weight `λ* = -w₀λ`, with the
divided word `d̄ = d.reverse` of the reversed expression
(`Stendhal.coevaluationDividedWord_reverse`). `Stendhal.wrapHeadHypotheses_dualCoevaluation`
gives the four properties there. Lemma 7.3 at `λ*` uses that every simple reflection is a left
descent of the element of the reversed expression, `w₀⁻¹ = w₀`; this is where the Weyl group is
assumed finite (Webster's setting of §7, in which `w₀` exists).

## Main results

* `Stendhal.wrapHeadHypotheses_coevaluation`.
* `Stendhal.isLeftDescent_wordProd_of_reverse`.
* `Stendhal.wrapHeadHypotheses_dualCoevaluation`.
-/

noncomputable section

open Module

namespace Categorification.Stendhal

/-- In a finite Coxeter group, if every simple reflection is a left descent of `π(w.reverse)`,
then every simple reflection is a left descent of `π(w)`: both are the longest element. -/
theorem isLeftDescent_wordProd_of_reverse {B W : Type*} [Group W] {M : CoxeterMatrix B}
    (cs : CoxeterSystem M W) [Finite W] (w : List B)
    (hlong : ∀ i, cs.IsLeftDescent (cs.wordProd w.reverse) i) (i : B) :
    cs.IsLeftDescent (cs.wordProd w) i := by
  have h : (cs.wordProd w.reverse)⁻¹ = cs.longestElement :=
    cs.eq_longestElement_iff_forall_isRightDescent.2 fun j =>
      cs.isRightDescent_inv_iff.2 (hlong j)
  have hw : cs.wordProd w = cs.longestElement := by
    rw [← h, CoxeterSystem.wordProd_reverse, inv_inv]
  rw [hw]
  exact cs.isLeftDescent_longestElement i

end Categorification.Stendhal

namespace Categorification.KLR.CycKLR

open KLRAlgebra Categorification.Graded QuantumGroup QuantumGroup.UDot _root_.Module KL2

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} {k : Type} [Fintype I] [DecidableEq I] [Field k] {C : CartanDatum I}
    {Q : I → I → MvPolynomial (Fin 2) k} (hP : IsRouquierQ C Q) (Λ : I → ℕ)
    {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y)
    (highest : X) (hΛ : ∀ i, (Λ i : ℤ) = RD.pair (RD.iY i) highest)
    (hR : (projectiveRootDatum RD).IsXRegular)
    {K H : Type*} [Field K] [ConditionallyCompleteLinearOrder K] [IsStrictOrderedRing K]
    [AddCommGroup H] [Module K H] (P : Matrix.Realization C.toLusztig.cartanMatrix K H)

local notation "aΛ" => (fun j => (Polynomial.X : Polynomial k) ^ Λ j)
local notation "G" => hP.gradingDatum
local notation "dp" =>
  dividedProjective hP.gradingDatum (fun i j => congrArg Neg.neg (C.symm i j)) C Λ
local notation "Dc" => P.cartanDatum C.toLusztig.isGeneralizedCartan_cartanMatrix
local notation "cs" => P.coxeterSystem C.toLusztig.isGeneralizedCartan_cartanMatrix

omit [Fintype I] in
private local instance finiteBlockWrapHyp (ν : Multiset I) : HasGdim (grade G Λ ν) := by
  let := module_finite (Q := Q) (ν := ν) (fun i j hij => by
    obtain ⟨c, hc, h⟩ := hP.polyInY_leading i j hij
    rw [h]
    exact hc.map Polynomial.C) (fun i => Polynomial.monic_X_pow (R := k) (Λ i))
  exact HasGdim.of_finiteDimensional _

include hP hΛ hR in
/-- **The hypotheses of Lemma 7.3 for the coevaluation word** (Webster, arXiv:1309.3796v3, §7.1,
Lemma 7.3, from Proposition 7.2 and Theorem 5.2). For a reduced expression `w` of the longest
element and its divided coevaluation word `d`, `z₀ = 1_d ∈ R^λ(d̂)` satisfies: the cyclotomic
relation of the second red label `λ*` on the last black strand (`LastDotRelation`), `z₀ ≠ 0`,
every nonzero element of `z₀ R^λ` generates `z₀`, and `z₀ R^λ z₀ = k z₀`. -/
theorem _root_.Categorification.Stendhal.wrapHeadHypotheses_coevaluation
    [FiniteDimensional K H] (weight : P.integralWeights)
    (hweight : P.IsDominantIntegral (weight : Module.Dual K H))
    (match_weight : ∀ i, (weight : Module.Dual K H) (P.coroot i) =
      (RD.pair.flip highest ((projectiveRootDatum RD).coroot i) : K))
    (w : List I) (hw : (cs).IsReduced w.reverse)
    (hlong : ∀ i, (cs).IsLeftDescent ((cs).wordProd w.reverse) i) :
    Stendhal.TwoRedErase.LastDotRelation Q (coevaluationLabels Λ RD highest
        (expandDiv (Stendhal.coevaluationDividedWord Dc weight w)))
      (expandDiv (Stendhal.coevaluationDividedWord Dc weight w) : Multiset I) ∧
    dividedIdem Λ (Q := Q) (Stendhal.coevaluationDividedWord Dc weight w) ≠ 0 ∧
    (∀ y : CycKLR k Q aΛ (expandDiv (Stendhal.coevaluationDividedWord Dc weight w)),
      dividedIdem Λ (Q := Q) (Stendhal.coevaluationDividedWord Dc weight w) * y = y → y ≠ 0 →
      ∃ c, y * c = dividedIdem Λ (Q := Q) (Stendhal.coevaluationDividedWord Dc weight w)) ∧
    (∀ x : CycKLR k Q aΛ (expandDiv (Stendhal.coevaluationDividedWord Dc weight w)),
      dividedIdem Λ (Q := Q) (Stendhal.coevaluationDividedWord Dc weight w) * x *
        dividedIdem Λ (Q := Q) (Stendhal.coevaluationDividedWord Dc weight w) = x →
      ∃ c : k, x = c • dividedIdem Λ (Q := Q) (Stendhal.coevaluationDividedWord Dc weight w)) := by
  let d := Stendhal.coevaluationDividedWord Dc weight w
  let ν : Multiset I := expandDiv d
  let z₀ := dividedIdem Λ (Q := Q) d
  have hz₀ : IsIdempotentElem z₀ := isIdempotentElem_dividedIdem Λ d
  have hz₀0 : z₀ ∈ grade G Λ ν 0 :=
    Graded.mem_map_of_mem _ (mk k Q aΛ ν).toLinearMap
      (hP.gradingDatum.hflip_mem_grade (fun i j => congrArg Neg.neg (C.symm i j))
        (divIdem_mem_grade G (isBlocks_ofList d rfl)))
  have hdp : dp ν d rfl = (GProj.ofIdempotent z₀ hz₀ hz₀0).shift (-divAngle2 C d) := rfl
  have hrank : finrank (LaurentPolynomial ℤ) (K0 (grade G Λ ν)) = 1 := by
    change finrank (LaurentPolynomial ℤ) (K0 (grade G Λ (expandDiv d : Multiset I))) = 1
    dsimp only [d]
    rw [Stendhal.expand_coevaluationDividedWord]
    exact finrank_coevaluation_projectiveBlock hP Λ RD highest hΛ hR P weight hweight
      match_weight w hw
  have hn : GProj.homGdim (dp ν d rfl) (dp ν d rfl) = 1 :=
    homGdim_dividedWord_of_websterNorm hP Λ RD highest hΛ hR d
      (Stendhal.websterForm_coevaluationDividedWord P (dominantWeight Λ RD highest hΛ) hR weight
        hweight match_weight w hw)
  have hsimple := isSimple_coevaluationProjective hP Λ RD highest hΛ hR P weight hweight
    match_weight w hw
  have hne : z₀ ≠ 0 := by
    intro h0
    have := IsSimpleModule.nontrivial (CycKLR k Q aΛ ν) (dp ν d rfl).carrier
    obtain ⟨y, hy⟩ := exists_ne (0 : (dp ν d rfl).carrier)
    let y' : leftIdeal z₀ := y
    have hy' : (y' : CycKLR k Q aΛ ν) * z₀ = y' := y'.2
    apply hy
    change y' = 0
    apply Subtype.ext
    have hz : ∀ a : CycKLR k Q aΛ ν, a * z₀ = a → a = 0 := fun a ha => by
      rw [← ha, h0, mul_zero]
    exact hz _ hy'
  have hnt : Nontrivial (CycKLR k Q aΛ ν) := ⟨⟨z₀, 0, hne⟩⟩
  have hcen : ∀ z : CycKLR k Q aΛ ν, (∀ y, z * y = y * z) → ∃ c : k, z = algebraMap k _ c :=
    fun z hz => GProj.exists_algebraMap_of_commute (dp ν d rfl) hrank hn z hz
  have hgen : ∀ y : CycKLR k Q aΛ ν, z₀ * y = y → y ≠ 0 → ∃ c, y * c = z₀ :=
    fun y hy hy0 => GProj.exists_mul_eq_of_homGdim_eq_one hz₀ hz₀0 _ hrank (hdp ▸ hn) y hy hy0
  have hscalar : ∀ x : CycKLR k Q aΛ ν, z₀ * x * z₀ = x → ∃ c : k, x = c • z₀ :=
    fun x hx => GProj.exists_smul_eq_of_homGdim_eq_one hz₀ hz₀0 _ (hdp ▸ hn) x hx
  have hvan : ∀ i, Subsingleton (CycKLR k Q aΛ ({i} + ν)) := by
    intro i
    have h := subsingleton_of_isLeftDescent_coevaluationWord hP Λ RD highest hΛ hR P weight
      hweight match_weight w hw i (hlong i)
    change Subsingleton (CycKLR k Q aΛ ({i} + (expandDiv d : Multiset I)))
    dsimp only [d]
    rw [Stendhal.expand_coevaluationDividedWord]
    exact h
  exact ⟨fun t h => dot_pow_mul_e_eq_zero_of_lowest hP Λ RD highest hΛ ν hvan hcen t h,
    hne, hgen, hscalar⟩

include hP hR in
/-- **The hypotheses of Lemma 7.3 at the dual weight** (Webster, arXiv:1309.3796v3, §7.1,
Lemma 7.3 at `λ* = -w₀λ`; §7.3, the X side of the S-move in Proposition 7.22). Let `w` be a
reduced expression of the longest element, `d` the divided coevaluation word of `λ`,
`λ* = (Σ d̂) - λ` (`dualHighest`) with labels `⟨α_i^∨, λ*⟩` (the second coevaluation label
of `λ`), `-wλ` the corresponding dominant weight and `d̄` its divided coevaluation word along
the reversed expression (equal to `d.reverse`, `coevaluationDividedWord_reverse`). Then the
four hypotheses of `wrapHeadHypotheses_coevaluation` hold for `d̄` at `λ*`. The Weyl group is
assumed finite. -/
theorem _root_.Categorification.Stendhal.wrapHeadHypotheses_dualCoevaluation
    [FiniteDimensional K H] [Finite (P.weylGroup C.toLusztig.isGeneralizedCartan_cartanMatrix)]
    (weight : P.integralWeights)
    (hweight : P.IsDominantIntegral (weight : Module.Dual K H))
    (match_weight : ∀ i, (weight : Module.Dual K H) (P.coroot i) =
      (RD.pair.flip highest ((projectiveRootDatum RD).coroot i) : K))
    (w : List I) (hw : (cs).IsReduced w.reverse)
    (hlong : ∀ i, (cs).IsLeftDescent ((cs).wordProd w.reverse) i) :
    Stendhal.TwoRedErase.LastDotRelation Q (coevaluationLabels
        (fun j => coevaluationLabels Λ RD highest
          (expandDiv (Stendhal.coevaluationDividedWord Dc weight w)) (Fin.last 1) j) RD
        (dualHighest RD highest (expandDiv (Stendhal.coevaluationDividedWord Dc weight w)))
        (expandDiv (Stendhal.coevaluationDividedWord Dc
          (-(w.foldl (fun μ j => (Dc).reflection j μ) weight)) w.reverse)))
      (expandDiv (Stendhal.coevaluationDividedWord Dc
          (-(w.foldl (fun μ j => (Dc).reflection j μ) weight)) w.reverse) : Multiset I) ∧
    dividedIdem (fun j => coevaluationLabels Λ RD highest
          (expandDiv (Stendhal.coevaluationDividedWord Dc weight w)) (Fin.last 1) j) (Q := Q)
        (Stendhal.coevaluationDividedWord Dc
          (-(w.foldl (fun μ j => (Dc).reflection j μ) weight)) w.reverse) ≠ 0 ∧
    (∀ y : CycKLR k Q (fun j => (Polynomial.X : Polynomial k) ^ coevaluationLabels Λ RD highest
          (expandDiv (Stendhal.coevaluationDividedWord Dc weight w)) (Fin.last 1) j)
        (expandDiv (Stendhal.coevaluationDividedWord Dc
          (-(w.foldl (fun μ j => (Dc).reflection j μ) weight)) w.reverse)),
      dividedIdem (fun j => coevaluationLabels Λ RD highest
          (expandDiv (Stendhal.coevaluationDividedWord Dc weight w)) (Fin.last 1) j) (Q := Q)
        (Stendhal.coevaluationDividedWord Dc
          (-(w.foldl (fun μ j => (Dc).reflection j μ) weight)) w.reverse) * y = y → y ≠ 0 →
      ∃ c, y * c = dividedIdem (fun j => coevaluationLabels Λ RD highest
          (expandDiv (Stendhal.coevaluationDividedWord Dc weight w)) (Fin.last 1) j) (Q := Q)
        (Stendhal.coevaluationDividedWord Dc
          (-(w.foldl (fun μ j => (Dc).reflection j μ) weight)) w.reverse)) ∧
    (∀ x : CycKLR k Q (fun j => (Polynomial.X : Polynomial k) ^ coevaluationLabels Λ RD highest
          (expandDiv (Stendhal.coevaluationDividedWord Dc weight w)) (Fin.last 1) j)
        (expandDiv (Stendhal.coevaluationDividedWord Dc
          (-(w.foldl (fun μ j => (Dc).reflection j μ) weight)) w.reverse)),
      dividedIdem (fun j => coevaluationLabels Λ RD highest
          (expandDiv (Stendhal.coevaluationDividedWord Dc weight w)) (Fin.last 1) j) (Q := Q)
        (Stendhal.coevaluationDividedWord Dc
          (-(w.foldl (fun μ j => (Dc).reflection j μ) weight)) w.reverse) * x *
      dividedIdem (fun j => coevaluationLabels Λ RD highest
          (expandDiv (Stendhal.coevaluationDividedWord Dc weight w)) (Fin.last 1) j) (Q := Q)
        (Stendhal.coevaluationDividedWord Dc
          (-(w.foldl (fun μ j => (Dc).reflection j μ) weight)) w.reverse) = x →
      ∃ c : k, x = c • dividedIdem (fun j => coevaluationLabels Λ RD highest
          (expandDiv (Stendhal.coevaluationDividedWord Dc weight w)) (Fin.last 1) j) (Q := Q)
        (Stendhal.coevaluationDividedWord Dc
          (-(w.foldl (fun μ j => (Dc).reflection j μ) weight)) w.reverse)) := by
  let d := Stendhal.coevaluationDividedWord Dc weight w
  let highest' : X := ((expandDiv d : Multiset I).map RD.iX).sum - highest
  let weight' : P.integralWeights := -(w.foldl (fun μ j => (Dc).reflection j μ) weight)
  let Λ' : I → ℕ := fun j => coevaluationLabels Λ RD highest (expandDiv d) (Fin.last 1) j
  have hpair := pair_dualHighest_coevaluation RD highest P weight hweight match_weight w hw
  have hweight' : P.IsDominantIntegral (weight' : Module.Dual K H) :=
    Stendhal.isDominantIntegral_neg_foldl P _ weight w hweight hlong
  have match_weight' : ∀ i, (weight' : Module.Dual K H) (P.coroot i) =
      (RD.pair.flip highest' ((projectiveRootDatum RD).coroot i) : K) := by
    intro i
    change _ = ((RD.pair (RD.iY i) highest' : ℤ) : K)
    rw [hpair, ← P.coroot_cartanDatum_cast, map_neg]
  have hΛ' : ∀ i, (Λ' i : ℤ) = RD.pair (RD.iY i) highest' := by
    intro i
    obtain ⟨n, hn⟩ := hweight' i
    have h0 : (0 : ℤ) ≤ RD.pair (RD.iY i) highest' := by
      have := (match_weight' i).symm.trans hn
      have : ((RD.pair (RD.iY i) highest' : ℤ) : K) = ((n : ℤ) : K) := by
        rw [Int.cast_natCast]; exact this
      have := Int.cast_injective this
      omega
    change ((-(RD.pair (RD.iY i) (highest - _))).toNat : ℤ) = _
    rw [show -(RD.pair (RD.iY i) (highest - ((expandDiv d : Multiset I).map RD.iX).sum)) =
      RD.pair (RD.iY i) highest' by simp only [highest', map_sub]; abel]
    exact Int.toNat_of_nonneg h0
  have hw' : (cs).IsReduced w.reverse.reverse := by
    rw [List.reverse_reverse]; exact ((cs).isReduced_reverse_iff w).mp hw
  have hlong' : ∀ i, (cs).IsLeftDescent ((cs).wordProd w.reverse.reverse) i := by
    rw [List.reverse_reverse]
    exact Stendhal.isLeftDescent_wordProd_of_reverse cs w hlong
  exact Stendhal.wrapHeadHypotheses_coevaluation hP Λ' RD highest' hΛ' hR P weight' hweight'
    match_weight' w.reverse hw' hlong'

end Categorification.KLR.CycKLR
