/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.ReducedDividedNorm

/-!
# Independence of the extremal divided-power projective

Webster, arXiv:1309.3796v2, Proposition 7.2. Indecomposability in a rank-one
block identifies two expressions up to shift. The bar involution on their
nonzero divided lowering vectors determines the shift exactly.
-/

noncomputable section
namespace Categorification.Graded.GProj
open Module
variable {k A : Type*} [Field k] [Ring A] [Algebra k A]
    {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [HasGdim 𝒜]
/-- Indecomposable projectives in a Laurent-rank-one block differ by a grading shift. -/
theorem exists_iso_shift_of_rank_one {P Q : GProj 𝒜} (hP : P.IsIndec A) (hQ : Q.IsIndec A)
    (hrank : finrank (LaurentPolynomial ℤ) (K0 𝒜) = 1) :
    ∃ n : ℤ, Nonempty (P.Iso (Q.shift n)) := by
  have hcard : Nat.card (IndecClass 𝒜) = 1 :=
    (Module.finrank_eq_nat_card_basis (K0.indecBasis 𝒜)).symm.trans hrank
  have := (Nat.card_eq_one_iff_unique.mp hcard).1
  exact Quotient.exact (Subsingleton.elim (α := IndecClass 𝒜)
    (Quotient.mk (indecSetoid 𝒜) ⟨P, hP⟩) (Quotient.mk (indecSetoid 𝒜) ⟨Q, hQ⟩))
end Categorification.Graded.GProj

namespace Categorification.KLR.CycKLR
open KLRAlgebra Categorification.Graded QuantumGroup QuantumGroup.UDot KLGamma LieLean
open LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop
open scoped TensorProduct

variable {I k : Type*} [Fintype I] [DecidableEq I] [Field k] {C : CartanDatum I}
    {Q : I → I → MvPolynomial (Fin 2) k} (hP : IsRouquierQ C Q) (Λ : I → ℕ)
    {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y)
    (highest : X) (hΛ : ∀ i, (Λ i : ℤ) = RD.pair (RD.iY i) highest)
    (hR : (projectiveRootDatum RD).IsXRegular)

local notation "G" => hP.gradingDatum
local notation "LP" => LaurentPolynomial ℤ
local notation "v" => (RatFunc.X : RatFunc ℚ)
local notation "wt" => dominantWeight Λ RD highest hΛ
local notation "dp" => dividedProjective G (fun i j => congrArg Neg.neg (C.symm i j)) C Λ
local notation "η" => projectiveIntegralEquiv hP Λ RD highest hΛ hR
local notation "ι" => DirectSum.lof LP _ (fun ν => K0 (grade G Λ ν))

private theorem dividedWord_image (β : Multiset I) (d : List (I × ℕ)) (hd : (expandDiv d : Multiset I) = β) :
    (η (ι β (K0.of (dp β d hd)))).val = dividedLoweringWord wt d := by
  subst β
  exact projectiveIntegralEquiv_dividedWordClass hP Λ RD highest hΛ hR d

/-- In a rank-one cyclotomic block, norm-one divided words give isomorphic projectives
with their normalized gradings. -/
theorem dividedWord_iso_of_websterNorm (β : Multiset I) (d d' : List (I × ℕ))
    (hd : (expandDiv d : Multiset I) = β) (hd' : (expandDiv d' : Multiset I) = β)
    (rank_one : Module.finrank LP (K0 (grade G Λ β)) = 1)
    (hn : Stendhal.SingleBlack.websterForm wt hR (dividedLoweringWord wt d) (dividedLoweringWord wt d) = 1)
    (hn' : Stendhal.SingleBlack.websterForm wt hR (dividedLoweringWord wt d') (dividedLoweringWord wt d') = 1) :
    Nonempty ((dp β d hd).Iso (dp β d' hd')) := by
  let := module_finite (Q := Q) (ν := β) (fun i j hij => by
    obtain ⟨c, hc, h⟩ := hP.polyInY_leading i j hij
    rw [h]
    exact hc.map Polynomial.C) (fun i => Polynomial.monic_X_pow (R := k) (Λ i))
  let := HasGdim.of_finiteDimensional (grade G Λ β)
  have indec (b : List (I × ℕ)) (hb : (expandDiv b : Multiset I) = β)
      (h : Stendhal.SingleBlack.websterForm wt hR (dividedLoweringWord wt b) (dividedLoweringWord wt b) = 1) :
      (dp β b hb).IsIndec _ := by
    subst β
    apply GProj.isIndec_of_norm_one
    exact homGdim_dividedWord_of_websterNorm hP Λ RD highest hΛ hR b h
  obtain ⟨a, ⟨e⟩⟩ := GProj.exists_iso_shift_of_rank_one (indec d hd hn) (indec d' hd' hn') rank_one
  have heq := K0.of_eq_of_iso e
  rw [← K0.T_smul_of] at heq
  have he : dividedLoweringWord wt d = v ^ (-a) • dividedLoweringWord wt d' := by
    rw [← dividedWord_image hP Λ RD highest hΛ hR β d hd,
      ← dividedWord_image hP Λ RD highest hΛ hR β d' hd', heq, map_smul, projectiveIntegralEquiv_T]
  have hb := congrArg (hwBar hR wt) he
  rw [Stendhal.bar_dividedLoweringWord, hwBar_smul, bar_X_zpow, neg_neg, Stendhal.bar_dividedLoweringWord] at hb
  have hx : dividedLoweringWord wt d' ≠ 0 := by
    intro hz
    simp [hz, Stendhal.SingleBlack.websterForm] at hn'
  have hs := (smul_left_injective (RatFunc ℚ) hx) (he.symm.trans hb)
  have ha := zpow_injective_of_not_root RatFunc.X_ne_zero hvn_ratFunc hs
  obtain rfl : a = 0 := by omega
  exact ⟨e.trans (GMod.shiftZeroIso (dp β d' hd').toGMod)⟩

/-- Webster, Proposition 7.2. Two reduced expressions for the same Weyl element
give isomorphic normalized graded cyclotomic projectives at the common content. -/
theorem coevaluationProjective_iso_of_same_weyl
    {K H : Type*} [Field K] [ConditionallyCompleteLinearOrder K] [IsStrictOrderedRing K]
    [AddCommGroup H] [Module K H] [Module.Finite K H]
    (P : Matrix.Realization C.toLusztig.cartanMatrix K H) (weight : P.integralWeights)
    (hweight : P.IsDominantIntegral (weight : Module.Dual K H))
    (match_weight : ∀ i, (weight : Module.Dual K H) (P.coroot i) =
        (RD.pair.flip highest ((projectiveRootDatum RD).coroot i) : K))
    (u w : List I) (hu : (P.coxeterSystem C.toLusztig.isGeneralizedCartan_cartanMatrix).IsReduced u.reverse)
    (hw : (P.coxeterSystem C.toLusztig.isGeneralizedCartan_cartanMatrix).IsReduced w.reverse)
    (same : (P.coxeterSystem C.toLusztig.isGeneralizedCartan_cartanMatrix).wordProd u.reverse =
      (P.coxeterSystem C.toLusztig.isGeneralizedCartan_cartanMatrix).wordProd w.reverse) :
    let d := Stendhal.coevaluationDividedWord (P.cartanDatum C.toLusztig.isGeneralizedCartan_cartanMatrix) weight
    let β := (expandDiv (d u) : Multiset I)
    ∃ h : (expandDiv (d w) : Multiset I) = β, Nonempty ((dp β (d u) rfl).Iso (dp β (d w) h)) := by
  let D := P.cartanDatum C.toLusztig.isGeneralizedCartan_cartanMatrix
  let d := Stendhal.coevaluationDividedWord D weight
  let β := (expandDiv (d u) : Multiset I)
  have h : (expandDiv (d w) : Multiset I) = β := by
    dsimp only [β, d]
    rw [Stendhal.expand_coevaluationDividedWord, Stendhal.expand_coevaluationDividedWord]
    exact (Stendhal.coevaluationWord_multiplicities_eq_of_reduced P _ weight hweight u w hu hw same).symm
  refine ⟨h, dividedWord_iso_of_websterNorm hP Λ RD highest hΛ hR β (d u) (d w) rfl h ?_ ?_ ?_⟩
  · dsimp only [β, d]
    rw [Stendhal.expand_coevaluationDividedWord]
    exact finrank_coevaluation_projectiveBlock hP Λ RD highest hΛ hR P weight hweight match_weight u hu
  · exact Stendhal.websterForm_coevaluationDividedWord P wt hR weight hweight match_weight u hu
  · exact Stendhal.websterForm_coevaluationDividedWord P wt hR weight hweight match_weight w hw

end Categorification.KLR.CycKLR
