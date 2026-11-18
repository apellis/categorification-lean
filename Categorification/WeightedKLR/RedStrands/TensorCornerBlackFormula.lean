/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TensorCornerPolynomial
import Categorification.WeightedKLR.RedStrands.TensorCornerWords
import Categorification.WeightedKLR.RedStrands.TensorCornerDeletion

/-!
# The marked black deletion after relabeling the red strands

Webster, arXiv:1309.3796v2, §4.7, Lemma 4.36. Replacing red indices by their
dominant weights preserves the sum over marked black positions, including when
several red indices carry the same weight.
-/

noncomputable section
namespace Categorification.Stendhal

open KLR KLRAlgebra CycKLR QuantumGroup
open LieLean.QuantumGroup
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type*} [Field k]
    {Q : I → I → MvPolynomial (Fin 2) k} (C : CartanDatum I) (hQ : IsRouquierQ C Q)

local notation:max "grade(" L ")" => stendhalGradingDatum L hQ.gradingDatum (fun i => C.dot i i / 2) (dotDegree C hQ)
local notation:max "word(" L "," s ")" => List.map (Sum.map id L) (List.ofFn (KLR.Seq.lbl s))

/-- If all smaller corners agree with the word calculation, so does a corner whose
source loading ends in a black strand. -/
theorem sequenceCornerPoly_eq_wordCornerPoly_appendBlack {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) (ν : Multiset I)
    (ih : ∀ (a : Seq (stendhalWeight ℓ ν)) (ha : IsRedOrdered a)
      (b : Seq (stendhalWeight ℓ ν)) (hb : IsRedOrdered b),
      sequenceCornerPoly grade(Λ) a ha b hb = cornerPolynomial C word(Λ, a) word(Λ, b))
    (i : I) (s : Seq (stendhalWeight ℓ ν)) (hs : IsRedOrdered s)
    (t : Seq (stendhalWeight ℓ ({i} + ν))) (ht : IsRedOrdered t) :
    sequenceCornerPoly grade(Λ) (appendBlackLoading i ν s) (appendBlackLoading_ordered i ν s hs) t ht =
      cornerPolynomial C word(Λ, appendBlackLoading i ν s) word(Λ, t) := by
  classical
  let w := List.ofFn t.lbl
  have hw : (w : Multiset (I ⊕ Fin ℓ)) = {Sum.inl i} + stendhalWeight ℓ ν :=
    (Seq.coe_ofFn t).trans (stendhalWeight_black_cons i ν).symm
  have he := Seq.ofList_ofFn t (hw.trans (stendhalWeight_black_cons i ν))
  have ho : IsRedOrdered (Seq.ofList w (hw.trans (stendhalWeight_black_cons i ν))) := by
    rw [he]; exact ht
  have hd := sequenceCornerPoly_appendBlack Λ C hQ ν i s hs w hw ho
  have hcongr (a b : Seq (stendhalWeight ℓ ({i} + ν))) (ha : IsRedOrdered a) (hb : IsRedOrdered b)
      (hab : a = b) :
      sequenceCornerPoly grade(Λ) (appendBlackLoading i ν s) (appendBlackLoading_ordered i ν s hs) a ha =
      sequenceCornerPoly grade(Λ) (appendBlackLoading i ν s) (appendBlackLoading_ordered i ν s hs) b hb := by
    subst b
    rfl
  rw [← hcongr _ t ho ht he, hd, weightedWord_appendBlackLoading, cornerPolynomial_terminalBlack]
  let relabel := Sum.map (id : I → I) Λ
  let term (z : List (I ⊕ (I →₀ ℕ)) × (I ⊕ (I →₀ ℕ)) × List (I ⊕ (I →₀ ℕ))) :=
    if Sum.inl i = z.2.1 then
      cornerDeletionCoeff C i word(Λ, s) z.1 * cornerPolynomial C word(Λ, s) (z.1 ++ z.2.2)
    else 0
  change _ = ((markedWords (w.map relabel)).attach.map (fun z => term z.val)).sum
  rw [List.attach_map_val (f := term), markedWords_map, List.map_map, ← List.sum_map_mul_left]
  apply congrArg List.sum
  rw [← List.attach_map_val (l := markedWords w)
    (f := term ∘ (fun z => (z.1.map relabel, relabel z.2.1, z.2.2.map relabel)))]
  apply List.map_congr_left
  intro a _
  have hblack : (Sum.inl i : I ⊕ (I →₀ ℕ)) = Sum.map id Λ a.val.2.1 ↔ Sum.inl i = a.val.2.1 := by
    cases a.val.2.1 <;> simp
  simp only [Function.comp_apply, term, relabel, hblack]
  split_ifs with h
  · rw [ih, weightedWord_markedBlackDeletion Λ ν hw a.property h, ← mul_assoc]
    congr 1
    rw [cornerDeletionCoeff, cornerPrefixPair_eq_content C Λ i (Seq.coe_ofFn s), cornerPrefixPair_map]
    congr 2
    simp [raiseShift, Nat.cast_sum, mul_sub]
  · simp

end Categorification.Stendhal
