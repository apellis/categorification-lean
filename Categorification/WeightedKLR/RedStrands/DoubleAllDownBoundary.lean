/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleViolatingQuotient
import Categorification.Diagrams.KLR.MatEnd
import Categorification.WeightedKLR.RedStrands.DoubleDiagramCut
import StringDiagrams.Generation

/-!
# The all-down block of the signed diagram category

Webster, arXiv:1309.3796v2, §4.5, Lemma 4.28. Fixing the multiset of black
strands makes the all-down boundary family finite, independently of the
number of signed words in the weight fibre. Matrices of morphisms between
these boundaries form the target algebra for the ordinary diagram map.
-/

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open KLR QuantumGroup QuantumGroup.UDot CategoryTheory StringDiagrams
open scoped Classical

variable {I X Y : Type*} {C : CartanDatum I} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) {ℓ : ℕ}
  (Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x})

/-- The common right weight of the all-down words with black content ν. -/
def downRightWeight (ν : Multiset I) : X := (List.ofFn (Subtype.val ∘ Λ)).sum - (ν.map RD.iX).sum

private theorem down_weight (w : List (I ⊕ Fin ℓ)) :
    RD.wX ((w.map DoubleStrand.down).filterMap Sum.getLeft?) =
      -((w.filterMap Sum.getLeft?).map RD.iX).sum := by
  induction w with
  | nil => simp
  | cons a w ih => cases a <;> simpa [DoubleStrand.down, List.filterMap_cons, add_comm] using ih

/-- The signed triple obtained by assigning the downward orientation to every ordinary
black strand. Its right weight depends only on the black multiset and red family. -/
def downTriple {ν : Multiset I} (s : {s : Seq (stendhalWeight ℓ ν) // IsRedOrdered s}) :
    DoubleStendhalTriple RD Λ 0 (downRightWeight RD Λ ν) :=
  ⟨DoubleBoundary.ofDown s.val s.property, by
    rw [DoubleBoundary.rightWeight_eq, zero_add]
    have hc := DoubleBoundary.blackContent_ofDown s.val s.property
    have h : ((List.ofFn s.val.lbl).filterMap Sum.getLeft? : Multiset I) = ν := by
      have eq : DoubleStrand.blackLabel ∘ DoubleStrand.down (I := I) (ℓ := ℓ) = Sum.getLeft? :=
        funext fun x => by cases x <;> rfl
      change (((List.ofFn s.val.lbl).map DoubleStrand.down).filterMap DoubleStrand.blackLabel :
        Multiset I) = ν at hc
      simpa only [List.filterMap_map, eq] using hc
    change _ + RD.wX (((List.ofFn s.val.lbl).map DoubleStrand.down).filterMap Sum.getLeft?) = _
    have hi := congrArg (fun n : Multiset I => (n.map RD.iX).sum) h
    rw [down_weight, downRightWeight, sub_eq_add_neg]
    exact congrArg (fun t => (List.ofFn (Subtype.val ∘ Λ)).sum + -t) hi⟩

variable {RD Λ} {k : Type*} [CommRing k]
    (P : Presentation (signature RD (Subtype.val ∘ Λ)) k)
    {ν : Multiset I}

/-- An all-down boundary object in the quotient by violated cuts. -/
abbrev downObj (s : {s : Seq (stendhalWeight ℓ ν) // IsRedOrdered s}) :=
  (violatingFunctor P _).obj (downTriple RD Λ s)

/-- The finite all-down matrix algebra at a single black content. -/
abbrev downwardMatrix (ν : Multiset I) := KLR.Diagram.MatEnd (downObj P (ν := ν))

/-- A violated ordinary sequence has zero identity in the all-down block. -/
theorem downObj_id_eq_zero (s : {s : Seq (stendhalWeight ℓ ν) // IsRedOrdered s})
    (h : IsViolated s.val) : 𝟙 (downObj P s) = 0 :=
  DoubleViolatingQuotient.id_eq_zero k (tripleObj P) (x := downTriple RD Λ s)
    ((DoubleBoundary.isViolated_ofDown_iff s.val s.property).mpr h)

/-- There are no morphisms from an ordered all-down sequence to an unordered
one in any presentation of the signed signature. This permits restriction
to the ordered principal submatrix in the all-down diagram map. -/
theorem hom_eq_zero_of_ordered_unordered
    {s t : Seq (stendhalWeight ℓ ν)} (hs : IsRedOrdered s) (ht : ¬IsRedOrdered t)
    (f : P.obj (obj RD (Subtype.val ∘ Λ) 0 ((List.ofFn s.lbl).map DoubleStrand.down)) ⟶
      P.obj (obj RD (Subtype.val ∘ Λ) 0 ((List.ofFn t.lbl).map DoubleStrand.down))) : f = 0 := by
  induction f using P.hom_induction with
  | diag d =>
    exfalso
    apply ht
    have h := redList_eq_of_diagram RD (Subtype.val ∘ Λ) d
    have hred (w : List (I ⊕ Fin ℓ)) :
        (w.map DoubleStrand.down).filterMap DoubleStrand.redLabel = w.filterMap Sum.getRight? := by
      simp only [List.filterMap_map, Function.comp_def, DoubleStrand.redLabel_down]
    rw [hred, hred] at h
    apply (DoubleBoundary.pairwise_red_iff _).mp
    rw [h]
    exact (DoubleBoundary.pairwise_red_iff _).mpr hs
  | zero => rfl
  | add f g hf hg => simp [hf, hg]
  | smul r f hf => simp [hf]

end Categorification.Stendhal.DoubleDiagram
