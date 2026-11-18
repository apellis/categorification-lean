/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleAllDownBoundary
import Categorification.WeightedKLR.RedStrands.DoubleSingleRedReduction

/-!
# Nonviolated all-down loadings with one red strand

For the single-red case of Webster, arXiv:1309.3796v2, §4.5, Lemma 4.28,
the ordinary all-down loadings which survive Definition 4.27 have the red
strand on the far left. Their black suffix gives a word in KL order when
read from right to left.
-/

namespace Categorification.Stendhal.DoubleDiagram

open QuantumGroup QuantumGroup.UDot KLR KL3.Diagram

universe u v

variable {I : Type u}

private theorem downward_black_suffix (w : List (DoubleStrand I 1))
    (hr : w.filterMap DoubleStrand.redLabel = []) (hd : ∀ i : I, Sum.inl (true, i) ∉ w) :
    ∃ z : List I, w = (z.map dn).map Sum.inl := by
  induction w with
  | nil => exact ⟨[], rfl⟩
  | cons x w ih =>
    cases x with
    | inr r => simp at hr
    | inl p =>
      obtain ⟨ε, i⟩ := p
      cases ε with
      | true => exact False.elim (hd i (by simp))
      | false =>
        obtain ⟨z, hz⟩ := ih hr
          (fun j hj => hd j (List.mem_cons_of_mem _ hj))
        exact ⟨i :: z, congrArg (Sum.inl (false, i) :: ·) hz⟩

private theorem single_red_down_word (b : DoubleBoundary I 1) (hd : b.AllDown) (hv : ¬ b.IsViolated) :
    ∃ z : List I, b.word = [.inr 0] ++ blackWord (z.map dn) ++ [] := by
  have hr : b.word.filterMap DoubleStrand.redLabel = [0] := b.redOrder
  cases hw : b.word with
  | nil => simp [hw] at hr
  | cons a w =>
    cases a with
    | inl c => exact False.elim (hv ⟨c, by simp [hw]⟩)
    | inr r =>
      have hr0 : r = 0 := Subsingleton.elim _ _
      subst r
      have ht : w.filterMap DoubleStrand.redLabel = [] := by
        simpa [hw, List.filterMap_cons] using hr
      obtain ⟨z,hz⟩ := downward_black_suffix w ht (fun i hi => hd i (by rw [hw]; exact List.mem_cons_of_mem _ hi))
      exact ⟨z.reverse, by simp only [blackWord, ← List.map_reverse, List.reverse_reverse, List.append_nil,
        List.singleton_append]; rw [hz]⟩

variable {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (Λ : Fin 1 → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}) {ν : Multiset I}

/-- Every nonviolated one-red all-down matrix index is the corresponding
single-red KL triple, including the right-weight constraint. -/
theorem downTriple_eq_singleRedTriple (s : {s : Seq (stendhalWeight 1 ν) // IsRedOrdered s})
    (hv : ¬ IsViolated s.val) :
    ∃ (z : List I) (h : endWeight RD (Subtype.val ∘ Λ) 0
        ([.inr 0] ++ blackWord (z.map dn) ++ []) = downRightWeight RD Λ ν),
      downTriple RD Λ s = singleRedTriple RD (z.map dn) h := by
  let b := downTriple RD Λ s
  obtain ⟨z,hz⟩ := single_red_down_word b.val (DoubleBoundary.allDown_ofDown s.val s.property)
    (fun e => hv ((DoubleBoundary.isViolated_ofDown_iff s.val s.property).mp e))
  have h : endWeight RD (Subtype.val ∘ Λ) 0 ([.inr 0] ++ blackWord (z.map dn) ++ []) =
      downRightWeight RD Λ ν := by
    rw [← hz]
    exact b.property
  exact ⟨z, h, Subtype.ext (DoubleBoundary.ext hz)⟩

end Categorification.Stendhal.DoubleDiagram
