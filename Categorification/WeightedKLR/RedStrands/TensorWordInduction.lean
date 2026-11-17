/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TensorWordProjectives
import Categorification.WeightedKLR.RedStrands.LastRedInduction
import Categorification.WeightedKLR.RedStrands.BlackPrincipal

/-!
# Right induction on common word generators

Webster, arXiv:1309.3796v2, §4.7, Lemma 4.37. Terminal-red
induction and ordinary right-black induction extend the expanded
projective at the very same boundary as the corresponding tensor word.
-/

noncomputable section
namespace Categorification.Stendhal.FirstWeight
open KLR KLRAlgebra Categorification.Graded
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
variable {I : Type*} {ℓ : ℕ}

/-- A single black strand adds one occurrence of its colour to the loading. -/
theorem TensorWord.content_black_one (w : TensorWord I ℓ) (i : I) :
    (w.black i 1).content.toMultiset = {i} + w.content.toMultiset := by
  simp [TensorWord.content, Finsupp.toMultiset_single, add_comm]

theorem TensorWord.loading_black_one (w : TensorWord I ℓ) (i : I) :
    Seq.cast (congrArg (stendhalWeight ℓ) (w.content_black_one i)) (w.black i 1).loading =
      appendBlackLoading i w.content.toMultiset w.loading := by
  let μ := stendhalWeight ℓ w.content.toMultiset
  let σ : Multiset (I ⊕ Fin ℓ) := {.inl i}
  have he : expandDiv (w.black i 1).blocks = expandDiv w.blocks ++ [.inl i] := by
    rw [TensorWord.blocks, expandDiv_append]
    rfl
  have hn : (expandDiv w.blocks).length = μ.card := congrArg Multiset.card w.blocks_weight
  apply Subtype.ext
  funext a
  change (Seq.cast _ (w.black i 1).loading).1 a = (Seq.cast _ (w.loading.append (default : Seq σ))).1 a
  rw [Seq.cast_apply, Seq.cast_apply]
  change (Seq.ofList _ (w.black i 1).blocks_weight).lbl _ = _
  rw [Seq.ofList_lbl]
  simp only [getElem_congr_coll he, Fin.val_cast]
  by_cases h : a.val < μ.card
  · rw [Seq.append_apply_lt _ _ _ h, List.getElem_append_left (by simpa [hn] using h)]
    exact (Seq.ofList_lbl _ w.blocks_weight ⟨a.val, h⟩).symm
  · rw [Seq.append_apply_ge _ _ _ (le_of_not_gt h), List.getElem_append_right (by simpa [hn] using le_of_not_gt h)]
    exact (List.getElem_singleton _).trans (Multiset.mem_singleton.mp ((default : Seq σ).mem _)).symm

variable {k : Type*} [DecidableEq I] [Field k] {Q : I → I → MvPolynomial (Fin 2) k}

private theorem class_congr {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I} (G : GradingDatum (stendhalQ Q Λ))
    {s t : Seq (stendhalWeight ℓ ν)} (hs : IsRedOrdered s) (ht : IsRedOrdered t) (h : s = t) :
    K0.of (sequenceProj G s hs) = K0.of (sequenceProj G t ht) := by cases h; rfl

theorem tensorWordSequenceProj_red {Λ : Fin (ℓ+1) → I →₀ ℕ}
    (G : GradingDatum (stendhalQ Q Λ)) (w : TensorWord I ℓ) :
    lastRedIndK0 G w.content.toMultiset (K0.of (sequenceProj (restrictRedGrading Q Λ G)
      w.loading w.blocks_redOrdered)) =
      K0.of (sequenceProj G w.red.loading w.red.blocks_redOrdered) := by
  refine Eq.trans ?_ (class_congr G ((appendRedLoading_ordered_iff _).2 w.blocks_redOrdered)
    w.red.blocks_redOrdered w.loading_red.symm)
  unfold sequenceProj
  refine (lastRedIndK0_ofIdempotent G w.content.toMultiset _ _).trans ?_
  exact K0.of_ofIdempotent_congr (𝒜 := tensorProductGrade G w.content.toMultiset)
    (appendRed_mk_e Q Λ _ w.loading w.blocks_redOrdered) _ _ _ _

/-- Right-black induction of an ordinary loading appends the black strand at the boundary. -/
theorem blackIndK0_sequenceProj {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
    (G : GradingDatum (stendhalQ Q Λ)) (i : I) (s : Seq (stendhalWeight ℓ ν)) (hs : IsRedOrdered s) :
    blackIndK0 G i ν (K0.of (sequenceProj G s hs)) =
      K0.of (sequenceProj G (appendBlackLoading i ν s) (appendBlackLoading_ordered i ν s hs)) := by
  unfold sequenceProj
  refine (blackIndK0_ofIdempotent G i ν _ _).trans ?_
  apply K0.of_ofIdempotent_congr
  exact appendBlack_mk_e Q Λ i ν s hs

theorem tensorWordSequenceProj_black {Λ : Fin ℓ → I →₀ ℕ}
    (G : GradingDatum (stendhalQ Q Λ)) (w : TensorWord I ℓ) (i : I) :
    blackIndK0 G i w.content.toMultiset (K0.of (sequenceProj G w.loading w.blocks_redOrdered)) =
      K0.of (sequenceProj G (Seq.cast (congrArg (stendhalWeight ℓ) (w.content_black_one i)) (w.black i 1).loading)
        (by rw [w.loading_black_one]; exact appendBlackLoading_ordered i _ _ w.blocks_redOrdered)) := by
  refine Eq.trans ?_ (class_congr G (appendBlackLoading_ordered i _ _ w.blocks_redOrdered)
    _ (w.loading_black_one i).symm)
  exact blackIndK0_sequenceProj G i w.loading w.blocks_redOrdered
end Categorification.Stendhal.FirstWeight
