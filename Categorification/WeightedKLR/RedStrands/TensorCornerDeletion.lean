/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Prop31G0
import Categorification.WeightedKLR.RedStrands.BlackHomAdjunction
import Categorification.WeightedKLR.RedStrands.CyclotomicCoverSequenceRaising
import Categorification.WeightedKLR.RedStrands.CyclotomicRestrictionWords
import Categorification.WeightedKLR.RedStrands.TensorCornerEndpoints
import Categorification.WeightedKLR.RedStrands.TensorWordInduction

/-!
# Black deletion for the graded dimensions of ordinary Stendhal corners

Webster, arXiv:1309.3796v2, §4.6 and Lemma 4.36. Frobenius reciprocity
moves a terminal black strand from the source to raw restriction on the target.
Undoing the normalization of restriction gives the common Laurent monomial.
-/

noncomputable section
namespace Categorification.Stendhal

open KLR KLRAlgebra CycKLR QuantumGroup QuantumGroup.UDot Categorification.Graded
open LieLean.QuantumGroup

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} {k : Type*} [DecidableEq I] [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k}
  (Λ : Fin ℓ → I →₀ ℕ) (C : CartanDatum I) (hQ : IsRouquierQ C Q) (ν : Multiset I)
  (i : I)

local notation "D" => I ⊕ Fin ℓ
local notation "μ" => stendhalWeight ℓ ν
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "γ" => ((Singleton.singleton (Sum.inl i) : Multiset D) + μ)
local notation "G" => stendhalGradingDatum Λ hQ.gradingDatum
  (fun j => C.dot j j / 2) (dotDegree C hQ)
local notation "C₀" => extendedCartanDatum C Λ
local notation "m" => cyclotomicCoverExponent (I := I) (ℓ := ℓ)
local notation "σ" => raiseShift (fun j => ∑ r, Λ r j) i ν C

/-- Deleting a marked occurrence of a black colour preserves the order of all red labels. -/
theorem markedBlackDeletionOrdered {i : I} {w : List D}
    (hw : (w : Multiset D) = {Sum.inl i} + μ)
    (ho : IsRedOrdered (Seq.ofList w (hw.trans (stendhalWeight_black_cons i ν))))
    {t : List D × D × List D} (ht : t ∈ markedWords w) (hi : Sum.inl i = t.2.1) :
    IsRedOrdered (Seq.ofList (t.1 ++ t.2.2) (markedBlackDeletionContent ν hw ht hi)) := by
  let del : WordDeletion (Sum.inl i) w :=
    ⟨(t.1, t.2.2), (markedWord_split ht).trans (by rw [hi])⟩
  exact (isRedOrdered_delete_black del _ (markedBlackDeletionContent ν hw ht hi)).mpr ho

private theorem homForm_blackInd_blackRaise [HasGdim (tensorProductGrade G ν)]
    [HasGdim (tensorProductGrade G νᵢ)] (x : K0 (tensorProductGrade G ν))
    (y : K0 (tensorProductGrade G νᵢ)) :
    K0.homForm _ (blackIndK0 G i ν x) y =
      toLaurentSeries (LaurentPolynomial.T (-σ)) *
        K0.homForm _ x (blackRaiseK0 G i ν C hQ y) := by
  rw [homForm_blackInd_blackRes G i ν C hQ, blackRaiseK0, LinearMap.smul_apply,
    K0.homForm_T_smul_right, K0.toLaurentSeries_T, ← mul_assoc, HahnSeries.single_mul_single,
    neg_add_cancel, one_mul, HahnSeries.single_zero_one, one_mul]

/-- The graded dimension of the corner with source ending in black `i` is a
Laurent-polynomial sum over all occurrences of `i` in the target word. Each
term uses the quantum integer for the weight of the prefix before that occurrence. -/
theorem sequenceCornerPoly_appendBlack (s : Seq μ) (hs : IsRedOrdered s)
    (w : List D) (hw : (w : Multiset D) = γ)
    (ho : IsRedOrdered (Seq.ofList w (hw.trans (stendhalWeight_black_cons i ν)))) :
    sequenceCornerPoly G (appendBlackLoading i ν s) (appendBlackLoading_ordered i ν s hs)
      (Seq.ofList w (hw.trans (stendhalWeight_black_cons i ν))) ho =
    LaurentPolynomial.T (-σ) * ((markedWords w).attach.map fun t =>
      if hi : Sum.inl i = t.1.2.1 then
        qIntU (qUnitLP ^ di C₀ (Sum.inl i)) (prefixPair C₀ m (Sum.inl i) t.1.1) *
          sequenceCornerPoly G s hs
            (Seq.ofList (t.1.1 ++ t.1.2.2) (markedBlackDeletionContent ν hw t.2 hi))
            (markedBlackDeletionOrdered ν hw ho t.2 hi)
      else 0).sum := by
  let := tensorProductAlgebra_finite Λ ν hQ
  let := tensorProductAlgebra_finite Λ νᵢ hQ
  let := HasGdim.of_finiteDimensional (tensorProductGrade G ν)
  let := HasGdim.of_finiteDimensional (tensorProductGrade G νᵢ)
  apply toLaurentSeries_injective
  rw [toLaurentSeries_sequenceCornerPoly C hQ Λ, ← K0.homForm_of,
    ← FirstWeight.blackIndK0_sequenceProj G i s hs,
    ← projectedSequenceClass_ordered Λ C hQ νᵢ _ ho, homForm_blackInd_blackRaise,
    blackRaiseK0_projectedSequenceClass Λ C hQ ν i w hw ho, toLaurentSeries_mul,
    map_list_sum, map_list_sum]
  apply congrArg (_ * ·)
  apply congrArg List.sum
  simp only [List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro t _
  split_ifs with hi
  · rw [K0.map_smul_of_T (F := K0.homForm _ _) (fun d x => K0.homForm_T_smul_right d _ x),
      projectedSequenceClass_ordered Λ C hQ ν _ (markedBlackDeletionOrdered ν hw ho t.2 hi),
      toLaurentSeries_mul, toLaurentSeries_sequenceCornerPoly C hQ Λ, K0.homForm_of]
  · rw [map_zero, map_zero]

end Categorification.Stendhal
