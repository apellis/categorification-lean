/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.ExtremalBlockRank
import Categorification.WeightedKLR.Rigidity.ExtremalNorm
import Categorification.WeightedKLR.RedStrands.SingleRedEulerForm

/-!
# The coevaluation divided powers in the cyclotomic algebra

Webster, arXiv:1309.3796v2, Definition 7.1 and Proposition 7.2.
The nilHecke blocks of the coevaluation word define an actual normalized
cyclotomic projective. Its rational Shapovalov norm computes its graded endomorphisms.
-/

noncomputable section
namespace Categorification.Stendhal
open KLR.KLRAlgebra
variable {I X : Type*} [AddCommGroup X] (D : CartanDatum I X)

/-- The divided blocks in order of induction in Definition 7.1. -/
def coevaluationDividedWord (weight : X) : List I → List (I × ℕ)
  | [] => []
  | i :: w => (i, (D.coroot i weight).toNat) :: coevaluationDividedWord (D.reflection i weight) w

/-- Expanding the nilHecke blocks gives the original black-strand word. -/
theorem expand_coevaluationDividedWord (weight : X) (w : List I) :
    expandDiv (coevaluationDividedWord D weight w) = coevaluationWord D weight w := by
  induction w generalizing weight with
  | nil => rfl
  | cons i w ih =>
    change _ ++ expandDiv (coevaluationDividedWord D (D.reflection i weight) w) = _
    rw [ih]
    rfl

/-- The final block uses the coroot pairing of the endpoint of the preceding path. -/
theorem coevaluationDividedWord_snoc (weight : X) (w : List I) (i : I) :
    coevaluationDividedWord D weight (w ++ [i]) = coevaluationDividedWord D weight w ++
      [(i, (D.coroot i (w.foldl (fun μ j => D.reflection j μ) weight)).toNat)] := by
  induction w generalizing weight with
  | nil => rfl
  | cons j w ih => simp only [List.cons_append, coevaluationDividedWord, List.foldl_cons, ih]

end Categorification.Stendhal

namespace Categorification.KLR.CycKLR
open KLRAlgebra Categorification.Graded QuantumGroup QuantumGroup.UDot KLGamma LieLean
open LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop
open scoped RatFunc
attribute [local instance] KLGamma.qToVAlgebra

variable {I k : Type*} [Fintype I] [DecidableEq I] [Field k] {C : CartanDatum I}
    {Q : I → I → MvPolynomial (Fin 2) k} (hP : IsRouquierQ C Q) (Λ : I → ℕ)
    {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y)
    (highest : X) (hΛ : ∀ i, (Λ i : ℤ) = RD.pair (RD.iY i) highest)
    (hR : (projectiveRootDatum RD).IsXRegular)

local notation "G" => hP.gradingDatum
local notation "wt" => dominantWeight Λ RD highest hΛ
local notation "dp" => dividedProjective G (fun i j => congrArg Neg.neg (C.symm i j)) C Λ

omit [Fintype I] in
private local instance finiteBlock (β : Multiset I) : HasGdim (grade G Λ β) := by
  let := module_finite (Q := Q) (ν := β) (fun i j hij => by
    obtain ⟨c, hc, h⟩ := hP.polyInY_leading i j hij
    rw [h]
    exact hc.map Polynomial.C) (fun i => Polynomial.monic_X_pow (R := k) (Λ i))
  exact HasGdim.of_finiteDimensional _

/-- A norm-one divided lowering word has graded endomorphism series one on its
actual normalized cyclotomic projective. -/
theorem homGdim_dividedWord_of_websterNorm (d : List (I × ℕ))
    (hn : Stendhal.SingleBlack.websterForm wt hR (dividedLoweringWord wt d) (dividedLoweringWord wt d) = 1) :
    GProj.homGdim (dp (expandDiv d : Multiset I) d rfl) (dp (expandDiv d : Multiset I) d rfl) = 1 := by
  let β : Multiset I := expandDiv d
  let p := dp β d rfl
  have h := homForm_eq_websterForm hP Λ RD highest hΛ hR β (K0.of p) (K0.of p)
  change lsCast (K0.homForm (grade G Λ β) (K0.of p) (K0.of p)) = algebraMap (RatFunc ℚ) (LaurentSeries ℚ)
    (Stendhal.SingleBlack.websterForm wt hR
      (projectiveIntegralEquiv hP Λ RD highest hΛ hR (dividedWordClass hP Λ d)).val
      (projectiveIntegralEquiv hP Λ RD highest hΛ hR (dividedWordClass hP Λ d)).val) at h
  rw [K0.homForm_of, projectiveIntegralEquiv_dividedWordClass, hn, map_one] at h
  change GProj.homGdim p p = 1
  ext n
  have hc := congrArg (fun f : LaurentSeries ℚ => f.coeff n) (h.trans (map_one lsCast).symm)
  change ((GProj.homGdim p p).coeff n : ℚ) = (((1 : LaurentSeries ℤ).coeff n : ℤ) : ℚ) at hc
  exact_mod_cast hc

/-- For a reduced path, the normalized divided-word projective is simple when its
quantum vector has norm one. -/
theorem isSimple_coevaluationProjective_of_websterNorm
    {K H : Type*} [Field K] [ConditionallyCompleteLinearOrder K] [IsStrictOrderedRing K]
    [AddCommGroup H] [Module K H] [Module.Finite K H]
    (P : Matrix.Realization C.toLusztig.cartanMatrix K H) (weight : P.integralWeights)
    (hweight : P.IsDominantIntegral (weight : Module.Dual K H))
    (match_weight : ∀ i, (weight : Module.Dual K H) (P.coroot i) =
        (RD.pair.flip highest ((projectiveRootDatum RD).coroot i) : K))
    (w : List I) (hw : (P.coxeterSystem C.toLusztig.isGeneralizedCartan_cartanMatrix).IsReduced w.reverse)
    (hn : let d := Stendhal.coevaluationDividedWord (P.cartanDatum C.toLusztig.isGeneralizedCartan_cartanMatrix) weight w
          Stendhal.SingleBlack.websterForm wt hR (dividedLoweringWord wt d) (dividedLoweringWord wt d) = 1) :
    let d := Stendhal.coevaluationDividedWord (P.cartanDatum C.toLusztig.isGeneralizedCartan_cartanMatrix) weight w
    IsSimpleModule (CycKLR k Q (fun i => (Polynomial.X : Polynomial k) ^ Λ i) (expandDiv d : Multiset I))
      (dp (expandDiv d : Multiset I) d rfl).carrier := by
  let d := Stendhal.coevaluationDividedWord (P.cartanDatum C.toLusztig.isGeneralizedCartan_cartanMatrix) weight w
  let β : Multiset I := expandDiv d
  change IsSimpleModule (CycKLR k Q (fun i => (Polynomial.X : Polynomial k) ^ Λ i) β) (dp β d rfl).carrier
  apply GProj.isSimpleModule_of_homGdim_eq_one
  · change Module.finrank (LaurentPolynomial ℤ) (K0 (grade G Λ (expandDiv d : Multiset I))) = 1
    dsimp only [d]
    rw [Stendhal.expand_coevaluationDividedWord]
    exact finrank_coevaluation_projectiveBlock hP Λ RD highest hΛ hR P weight hweight match_weight w hw
  · exact homGdim_dividedWord_of_websterNorm hP Λ RD highest hΛ hR d hn

end Categorification.KLR.CycKLR
