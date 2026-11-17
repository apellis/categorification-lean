/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TensorWordProjectives
import Categorification.WeightedKLR.RedStrands.BlackSerre

/-!
# Divided black induction on tensor word projectives

Webster, arXiv:1309.3796v2, §4.6 and the tensor word identification in Theorem
4.38. Appending a divided black block to an indexing word gives intrinsic
divided black induction on its graded projective class.
-/

noncomputable section
namespace Categorification.Stendhal.FirstWeight
open KLR KLRAlgebra Categorification.Graded QuantumGroup KL2
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
variable {I k : Type*} {ℓ : ℕ} [DecidableEq I] [Field k]
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin ℓ → I →₀ ℕ)
  (C : CartanDatum I) (hQ : IsRouquierQ C Q)

local notation "di" => fun i => C.dot i i / 2
local notation "H" => affineCoverGrading Λ hQ.gradingDatum di (dotDegree C hQ)
local notation "G" => stendhalGradingDatum Λ hQ.gradingDatum di (dotDegree C hQ)
local notation "LP" => LaurentPolynomial ℤ
local notation "fam" => fun β : Multiset I => K0 (tensorProductGrade G β)
local notation "lift" => totalProjectionK0 Λ C hQ

/-- The total graded class of the shifted tensor-word projective in its black weight. -/
def tensorWordProjectiveClass (w : TensorWord I ℓ) : DirectSum (Multiset I) fam :=
  DirectSum.lof LP _ fam w.content.toMultiset (K0.of (tensorWordProjective Λ C hQ w))

private theorem projection_word_factorial (w : TensorWord I ℓ) :
    lift ((H).clsW (expandDiv w.blocks)) =
      divQFact2 C w.blackBlocks • tensorWordProjectiveClass Λ C hQ w := by
  have hs := affineCoverGrading_cross_symm Λ hQ.gradingDatum di (dotDegree C hQ)
    (fun i j => congrArg Neg.neg (C.symm i j))
  have hX := affineCoverGrading_dot Λ hQ.gradingDatum di (dotDegree C hQ) C (fun _ => rfl)
  rw [(H).clsW_eq _ w.blocks_weight]
  change lift (DirectSum.lof LP _ (H).K0fam _ _) = _
  rw [totalProjectionK0_lof, show K0.of ((H).projP (Seq.ofList _ w.blocks_weight)) = _ from
    (H).of_expanded_eq_factorial hs (affineCoverCartan C ℓ) hX w.blocks w.blocks_weight,
    map_smul, map_smul, projectionK0_dividedProjective, w.blocks_factorial C]
  rfl

/-- Intrinsic divided lowering appends a divided black block to the shared tensor
word, including multiplicity zero (Webster, arXiv:1309.3796v2, Theorem 4.38). -/
theorem blackDividedLower_tensorWordProjectiveClass (w : TensorWord I ℓ) (i : I) (n : ℕ) :
    blackDividedLower Λ C hQ i n (tensorWordProjectiveClass Λ C hQ w) =
      tensorWordProjectiveClass Λ C hQ (w.black i n) := by
  let v := tUnit (C.dot i i / 2)
  let f := divQFact2 C w.blackBlocks
  have he : expandDiv (w.black i n).blocks = expandDiv w.blocks ++ List.replicate n (.inl i) := by
    rw [TensorWord.blocks, expandDiv_append]
    simp [expandDiv]
  have hf : divQFact2 C (w.black i n).blackBlocks = f * qfact v n := by
    rw [TensorWord.blackBlocks, divQFact2_append]
    simp [f, v, divQFact2]
  have h := blackLower_pow_totalProjectionK0_word Λ C hQ i n _ _ w.blocks_weight
  rw [← he, projection_word_factorial, projection_word_factorial, map_smul,
    blackLower_pow_eq_qfact_smul, LinearMap.smul_apply, hf] at h
  have hn : f * qfact v n ≠ 0 := by
    rw [← hf]
    intro hzero
    exact KL2Gamma.qToV_divQFact2_ne_zero C _ (by rw [hzero, map_zero])
  apply totalK0_smul_injective Λ C hQ hn
  simpa only [smul_smul] using h

end Categorification.Stendhal.FirstWeight
