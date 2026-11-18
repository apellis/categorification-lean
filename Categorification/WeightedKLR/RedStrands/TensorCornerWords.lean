/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Prop320
import Categorification.WeightedKLR.RedStrands.AddRed
import Categorification.WeightedKLR.RedStrands.BlackInduction
import Categorification.WeightedKLR.RedStrands.CyclotomicCoverSequenceClass
import Categorification.WeightedKLR.RedStrands.Vacuum

/-!
# Words of tensor product boundary loadings

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
§4.6 and §4.7, Lemma 4.36. The terminal black and red operations on loadings
append the corresponding letter to the boundary word. Deleting a marked
black occurrence is concatenation of its prefix and suffix. These are the
word operations in the recursion for the graded corner dimensions.
-/

namespace Categorification.Stendhal

open KLR KLRAlgebra CycKLR

variable {I : Type*} {ℓ : ℕ} {ν : Multiset I}

private theorem ofFn_seq_cast {J : Type*} {a b : Multiset J} (h : a = b) (s : Seq a) :
    List.ofFn (KLR.Seq.cast h s).lbl = List.ofFn s.lbl := by
  subst b
  rfl

private theorem ofFn_seq_map {J K : Type*} (f : J → K) {a : Multiset J} (s : Seq a) :
    List.ofFn (KLR.Seq.map f s).lbl = (List.ofFn s.lbl).map f := by
  rw [List.map_ofFn]
  exact (List.ofFn_congr (Multiset.card_map f a).symm (f ∘ s.lbl)).symm

private theorem ofFn_seq_singleton {J : Type*} {a : J} (s : Seq ({a} : Multiset J)) :
    List.ofFn s.lbl = [a] := by
  have hl : s.lbl = fun _ => a := funext fun j => Multiset.mem_singleton.mp (s.mem j)
  rw [hl]
  simp

/-- Appending a black strand appends its label in the ordinary boundary word. -/
@[simp] theorem word_appendBlackLoading (i : I) (ν : Multiset I)
    (s : Seq (stendhalWeight ℓ ν)) :
    List.ofFn (appendBlackLoading i ν s).lbl = List.ofFn s.lbl ++ [.inl i] := by
  rw [appendBlackLoading, ofFn_seq_cast, KLR.ofFn_append, ofFn_seq_singleton]

/-- Appending a red strand embeds the old indices and puts the new red index last. -/
@[simp] theorem word_appendRedLoading (s : Seq (stendhalWeight ℓ ν)) :
    List.ofFn (appendRedLoading s).lbl =
      (List.ofFn s.lbl).map (addRedColor ℓ) ++ [.inr (Fin.last ℓ)] := by
  rw [appendRedLoading, ofFn_seq_cast, KLR.ofFn_append, ofFn_seq_map, ofFn_seq_singleton]

/-- The vacuum loading reads as the prescribed list of red strands. -/
@[simp] theorem word_vacuumSeq :
    List.ofFn (vacuumSeq (I := I) (ℓ := ℓ)).lbl = (List.finRange ℓ).map Sum.inr := by
  have hc : (stendhalWeight ℓ (0 : Multiset I)).card = ℓ := by simp [stendhalWeight]
  rw [← List.ofFn_id, List.map_ofFn, List.ofFn_congr hc]
  rfl

/-- A smaller loading from a marked deletion reads as the remaining prefix and suffix. -/
theorem word_markedBlackDeletion (ν : Multiset I) {i : I} {w : List (I ⊕ Fin ℓ)}
    (hw : (w : Multiset _) = ({Sum.inl i} : Multiset (I ⊕ Fin ℓ)) + stendhalWeight ℓ ν)
    {t : List (I ⊕ Fin ℓ) × (I ⊕ Fin ℓ) × List (I ⊕ Fin ℓ)}
    (ht : t ∈ markedWords w) (hi : Sum.inl i = t.2.1) :
    List.ofFn (Seq.ofList (t.1 ++ t.2.2) (markedBlackDeletionContent ν hw ht hi)).lbl =
      t.1 ++ t.2.2 :=
  Seq.ofFn_ofList _ _

/-- Relabelling a word relabels each marked position, retaining its multiplicity. -/
theorem markedWords_map {J K : Type*} (f : J → K) (w : List J) :
    markedWords (w.map f) = (markedWords w).map (fun t => (t.1.map f, f t.2.1, t.2.2.map f)) := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [markedWords, ih, List.map_map, Function.comp_def]

section RedWeights

variable {J : Type*}

/-- Appending a black strand also appends its label after replacing red indices by weights. -/
theorem weightedWord_appendBlackLoading (labels : Fin ℓ → J) (i : I) (ν : Multiset I)
    (s : Seq (stendhalWeight ℓ ν)) :
    (List.ofFn (appendBlackLoading i ν s).lbl).map (Sum.map id labels) =
      (List.ofFn s.lbl).map (Sum.map id labels) ++ [.inl i] := by
  rw [word_appendBlackLoading, List.map_append]
  rfl

/-- Appending a red strand extends the weighted boundary word by its new weight. -/
theorem weightedWord_appendRedLoading (labels : Fin (ℓ + 1) → J) (s : Seq (stendhalWeight ℓ ν)) :
    (List.ofFn (appendRedLoading s).lbl).map (Sum.map id labels) =
      (List.ofFn s.lbl).map (Sum.map id (labels ∘ Fin.castSucc)) ++ [.inr (labels (Fin.last ℓ))] := by
  have hf : (Sum.map (id : I → I) labels) ∘ addRedColor ℓ =
      Sum.map id (labels ∘ Fin.castSucc) := by
    funext x
    cases x <;> rfl
  rw [word_appendRedLoading, List.map_append, List.map_map, hf]
  rfl

/-- Relabelling a marked deletion concatenates the relabelled prefix and suffix. -/
theorem weightedWord_markedBlackDeletion (labels : Fin ℓ → J) (ν : Multiset I)
    {i : I} {w : List (I ⊕ Fin ℓ)}
    (hw : (w : Multiset _) = ({Sum.inl i} : Multiset (I ⊕ Fin ℓ)) + stendhalWeight ℓ ν)
    {t : List (I ⊕ Fin ℓ) × (I ⊕ Fin ℓ) × List (I ⊕ Fin ℓ)}
    (ht : t ∈ markedWords w) (hi : Sum.inl i = t.2.1) :
    (List.ofFn (Seq.ofList (t.1 ++ t.2.2) (markedBlackDeletionContent ν hw ht hi)).lbl).map
      (Sum.map id labels) = t.1.map (Sum.map id labels) ++ t.2.2.map (Sum.map id labels) := by
  rw [word_markedBlackDeletion ν hw ht hi, List.map_append]

end RedWeights

end Categorification.Stendhal
