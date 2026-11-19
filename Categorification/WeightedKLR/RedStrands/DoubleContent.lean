/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleAllDownIdeal
import Categorification.WeightedKLR.RedStrands.DoubleDiagramCut
import StringDiagrams.Generation

/-!
# Signed black multiplicities of double Stendhal boundaries

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
§4.5, Definitions 4.22–4.24 and proof of Theorem 4.29. For each colour, every
horizontal cut has the same number of downward strands minus upward strands.
Thus the factorization of a boundary identity through all-down boundaries can
use only the ordinary black multiset specified by these signed multiplicities.
-/

noncomputable section

namespace Categorification.Stendhal

open QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams CategoryTheory

variable {I : Type*} {ℓ : ℕ}

private def DoubleStrand.multiplicity : DoubleStrand I ℓ → I →₀ ℤ
  | .inl (false, i) => Finsupp.single i 1
  | .inl (true, i) => -Finsupp.single i 1
  | .inr _ => 0

/-- Signed black multiplicities, with a downward strand contributing one and an upward
strand contributing minus one to its colour. -/
def DoubleBoundary.signedContent (b : DoubleBoundary I ℓ) : I →₀ ℤ :=
  (b.word.map DoubleStrand.multiplicity).sum

/-- Signed black multiplicities of a word of strands. -/
def wordContent (w : List (DoubleStrand I ℓ)) : I →₀ ℤ := (w.map DoubleStrand.multiplicity).sum

theorem DoubleBoundary.signedContent_eq_wordContent (b : DoubleBoundary I ℓ) :
    b.signedContent = wordContent b.word := rfl

@[simp] theorem wordContent_red (r : Fin ℓ) : wordContent [(Sum.inr r : DoubleStrand I ℓ)] = 0 := by
  simp [wordContent, DoubleStrand.multiplicity]

@[simp] theorem wordContent_append (v w : List (DoubleStrand I ℓ)) :
    wordContent (v ++ w) = wordContent v + wordContent w := by
  simp [wordContent]

@[simp] theorem wordContent_reverse (w : List (DoubleStrand I ℓ)) :
    wordContent w.reverse = wordContent w := by
  simp [wordContent, List.sum_reverse]

/-- Reversing the orientations of black strands negates their signed multiplicities. -/
theorem wordContent_map_dual (s : List (KL3.Diagram.Letter I)) :
    wordContent ((s.map KL3.Diagram.Letter.dual).map (Sum.inl (β := Fin ℓ))) =
      -wordContent (s.map (Sum.inl (β := Fin ℓ))) := by
  induction s with
  | nil => simp [wordContent]
  | cons l s ih =>
    obtain ⟨d, i⟩ := l
    simp only [wordContent, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, neg_add]
    cases d <;> simp [KL3.Diagram.Letter.dual, DoubleStrand.multiplicity]

/-- The integral multiplicities of an ordinary black multiset. -/
def contentVector (ν : Multiset I) : I →₀ ℤ := (ν.map (fun i => Finsupp.single i (1 : ℤ))).sum

private theorem contentVector_apply [DecidableEq I] (ν : Multiset I) (i : I) :
    contentVector ν i = ν.count i := by
  induction ν using Multiset.induction_on with
  | empty => simp [contentVector]
  | cons j ν ih =>
    by_cases h : i = j
    · subst j; simp [contentVector, ← ih, add_comm]
    · simp [contentVector, Multiset.count_cons_of_ne h, Finsupp.single_eq_of_ne h, ← ih]

private theorem contentVector_injective : Function.Injective (contentVector (I := I)) := by
  classical
  intro ν μ h
  apply Multiset.ext.mpr
  intro i
  exact_mod_cast (by simpa only [contentVector_apply] using congrArg (fun f : I →₀ ℤ => f i) h :
    (ν.count i : ℤ) = μ.count i)

/-- On an all-down boundary the signed multiplicities are those of its ordinary black multiset. -/
theorem DoubleBoundary.signedContent_of_allDown (b : DoubleBoundary I ℓ) (h : b.AllDown) :
    b.signedContent = contentVector b.blackContent := by
  have aux (w : List (DoubleStrand I ℓ)) (hw : ∀ i, Sum.inl (true, i) ∉ w) :
      (w.map DoubleStrand.multiplicity).sum = contentVector (w.filterMap DoubleStrand.blackLabel) := by
    induction w with
    | nil => simp [contentVector]
    | cons x w ih =>
      have ht := ih fun i hi => hw i (.tail _ hi)
      cases x with
      | inr r =>
        change 0 + (w.map DoubleStrand.multiplicity).sum = contentVector (w.filterMap DoubleStrand.blackLabel)
        rw [zero_add]
        exact ht
      | inl s =>
        obtain ⟨d,i⟩ := s
        cases d with
        | true => exact (hw i (.head _)).elim
        | false =>
          simpa [DoubleStrand.multiplicity, DoubleStrand.blackLabel, DoubleStrand.erase, contentVector] using ht
  exact aux b.word h

namespace DoubleDiagram

private theorem Move.top_multiplicity (g : Move I ℓ) :
    (g.top.map DoubleStrand.multiplicity).sum = (g.bottom.map DoubleStrand.multiplicity).sum := by
  cases g with
  | black g =>
    cases g with
    | dot => rfl
    | cross d i j => simp [Move.top, Move.bottom, add_comm]
    | cup l | cap l =>
      obtain ⟨d, i⟩ := l
      cases d <;> simp [Move.top, Move.bottom, Letter.dual, DoubleStrand.multiplicity]
  | blackRed | redBlack => simp [Move.top, Move.bottom, DoubleStrand.multiplicity]

universe w u v
variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {ℓ : ℕ} {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}}
  {k : Type w} [CommRing k] (P : Presentation.{w, max u v} (signature RD (fun r => (Λ r).val)) k)
  {right : X}

local notation "T" => DoubleStendhalTriple RD Λ 0 right
local notation "labels" => (Subtype.val ∘ Λ)

/-- Signed black content is constant along a raw diagram (Webster, arXiv:1309.3796v2,
§4.5, Definitions 4.22–4.24). In particular a raw diagram cannot change the signed
multiplicities even when two different multiplicity vectors have the same weight. -/
theorem signedContent_eq_of_diagram {a b : T}
    (d : obj RD labels 0 a.val.word ⟶ obj RD labels 0 b.val.word) :
    b.val.signedContent = a.val.signedContent := by
  simpa only [DoubleBoundary.signedContent, obj, forget_colours] using
    chain_wordInvariant RD labels (fun w => (w.map DoubleStrand.multiplicity).sum)
      (fun u g v => by simp only [List.map_append, List.sum_append, Move.top_multiplicity]) (Diagram.chain d)

/-- All morphisms between different signed-content blocks vanish in the violating quotient
(Webster, arXiv:1309.3796v2, §4.5, Definitions 4.22–4.24 and 4.27). -/
theorem hom_eq_zero_of_signedContent_ne {a b : T} (h : a.val.signedContent ≠ b.val.signedContent)
    (f : (violatingFunctor P right).obj a ⟶ (violatingFunctor P right).obj b) : f = 0 := by
  let π := violatingFunctor P right
  obtain ⟨⟨g⟩, rfl⟩ := π.map_surjective f
  change P.obj (obj RD labels 0 a.val.word) ⟶ P.obj (obj RD labels 0 b.val.word) at g
  have hg : g = 0 := by
    induction g using P.hom_induction with
    | diag d => exact (h (signedContent_eq_of_diagram (a := a) (b := b) d).symm).elim
    | zero => rfl
    | add f g hf hg => simp [hf, hg]
    | smul r f hf => simp [hf]
  subst g
  exact π.map_zero a b

variable (t : I → I → kˣ)
local notation "Q" => addRedUpRelations RD labels k (addMixedBlackRelations RD labels k t P)

/-- Every boundary identity factors through all-down words of matching signed content,
including in weight data where the right weight does not determine the multiplicities
(Webster, arXiv:1309.3796v2, §4.5, proof of Theorem 4.29). -/
theorem id_mem_matchingContentFactorSpan (b : T) :
    let π := violatingFunctor Q right
    𝟙 (π.obj b) ∈ factorSpan k π.obj
      (fun d => d.val.AllDown ∧ contentVector d.val.blackContent = b.val.signedContent) b b := by
  refine (Submodule.span_le.mpr ?_) (id_mem_allDownFactorSpan P t b)
  rintro _ ⟨d, hd, u, v, rfl⟩
  by_cases h : b.val.signedContent = d.val.signedContent
  · exact Submodule.subset_span ⟨d, ⟨hd, ((d.val.signedContent_of_allDown hd).symm.trans h.symm)⟩,
      u, v, rfl⟩
  · rw [hom_eq_zero_of_signedContent_ne Q h u, Limits.zero_comp]
    exact Submodule.zero_mem _

/-- At signed content `ν`, the all-down identities in the proof of Theorem 4.29 can be
restricted to the ordinary black multiset `ν` (Webster, arXiv:1309.3796v2, §4.5). -/
theorem id_mem_allDownContentFactorSpan (b : T) (ν : Multiset I)
    (hb : b.val.signedContent = contentVector ν) :
    let π := violatingFunctor Q right
    𝟙 (π.obj b) ∈ factorSpan k π.obj (fun d => d.val.AllDown ∧ d.val.blackContent = ν) b b := by
  simpa only [hb, contentVector_injective.eq_iff] using id_mem_matchingContentFactorSpan P t b

end DoubleDiagram
end Categorification.Stendhal
