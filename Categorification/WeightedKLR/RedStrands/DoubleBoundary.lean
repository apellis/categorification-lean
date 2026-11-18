/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.Basic
import Categorification.KLR.DividedPowerIdempotents
import Categorification.WeightedKLR.RedStrands.Stendhal

/-!
# Double Stendhal boundaries

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
§4.5, Definitions 4.22–4.24 and 4.27. A signed boundary is a left-to-right word
in oriented black letters and the ordered red labels. The word records both the
signed black list and the positions of the red strands from Definition 4.23.
Once the left weight is chosen, the right weight is determined by the reds and
the signed black roots. The all-down words are the ordinary Stendhal boundary
sequences of Definitions 4.1 and 4.7.
-/

namespace Categorification.Stendhal

open KLR QuantumGroup QuantumGroup.UDot

variable {I : Type*} {ℓ : ℕ}

/-- A black letter carries a colour and an orientation, with `true` for upward
and `false` for downward. A red letter records its index in the red family. -/
abbrev DoubleStrand (I : Type*) (ℓ : ℕ) := KL3.Diagram.Letter I ⊕ Fin ℓ

namespace DoubleStrand

/-- Forget the orientation of a black strand. -/
def erase : DoubleStrand I ℓ → I ⊕ Fin ℓ
  | .inl s => .inl s.2
  | .inr r => .inr r

/-- Put the downward orientation on an ordinary Stendhal strand. -/
def down : I ⊕ Fin ℓ → DoubleStrand I ℓ
  | .inl i => .inl (false, i)
  | .inr r => .inr r

/-- Read the red index of a strand. -/
abbrev redLabel : DoubleStrand I ℓ → Option (Fin ℓ) := Sum.getRight?

/-- Read the black colour of a strand. -/
def blackLabel : DoubleStrand I ℓ → Option I := Sum.getLeft? ∘ erase

/-- The change in region weight from left to right across a strand of Webster,
arXiv:1309.3796v2, §4.5, Definitions 4.22 and 4.23. -/
def weight {C : CartanDatum I} {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (RD : WeightDatum C X Y) (Λ : Fin ℓ → X) : DoubleStrand I ℓ → X
  | .inl s => sgn s.1 • RD.iX s.2
  | .inr r => Λ r

@[simp] theorem erase_down (x : I ⊕ Fin ℓ) : erase (down x) = x := by
  cases x <;> rfl

@[simp] theorem redLabel_down (x : I ⊕ Fin ℓ) : redLabel (down x) = x.getRight? := by
  cases x <;> rfl

@[simp] theorem getRight?_erase (x : DoubleStrand I ℓ) : (erase x).getRight? = redLabel x := by
  cases x <;> rfl

end DoubleStrand

/-- The word of a double Stendhal triple for a fixed family of red labels,
as in Webster, arXiv:1309.3796v2, §4.5, Definition 4.23. -/
@[ext] structure DoubleBoundary (I : Type*) (ℓ : ℕ) where
  /-- The strands in left-to-right order. -/
  word : List (DoubleStrand I ℓ)
  /-- The red strands occur once each, in the order of the red family. -/
  redOrder : word.filterMap DoubleStrand.redLabel = List.finRange ℓ

namespace DoubleBoundary

/-- A boundary belongs to the all-down sector if every black strand points downward. -/
def AllDown (b : DoubleBoundary I ℓ) : Prop := ∀ i : I, Sum.inl (true, i) ∉ b.word

/-- A boundary violates the condition in Webster, arXiv:1309.3796v2, §4.5,
preceding Definition 4.27, if its leftmost strand is black in either orientation. -/
def IsViolated (b : DoubleBoundary I ℓ) : Prop :=
  ∃ s : KL3.Diagram.Letter I, b.word.head? = some (.inl s)

/-- The left-to-right list of boundary labels, ignoring black orientations. -/
def eraseWord (b : DoubleBoundary I ℓ) : List (I ⊕ Fin ℓ) := b.word.map DoubleStrand.erase

/-- The multiset of black colours, ignoring orientations. -/
def blackContent (b : DoubleBoundary I ℓ) : Multiset I := b.word.filterMap DoubleStrand.blackLabel

/-- The right weight of a double Stendhal triple in Webster, arXiv:1309.3796v2,
§4.5, Definition 4.23. Set the left weight to zero for Definition 4.27. -/
def rightWeight {C : CartanDatum I} {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (RD : WeightDatum C X Y) (Λ : Fin ℓ → X) (left : X) (b : DoubleBoundary I ℓ) : X :=
  left + (b.word.map (DoubleStrand.weight RD Λ)).sum

/-- The weight equation of Webster, arXiv:1309.3796v2, Definition 4.23, with
the red and signed black sums written separately. -/
theorem rightWeight_eq {C : CartanDatum I} {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (RD : WeightDatum C X Y) (Λ : Fin ℓ → X) (left : X) (b : DoubleBoundary I ℓ) :
    b.rightWeight RD Λ left = left + (List.ofFn Λ).sum + RD.wX (b.word.filterMap Sum.getLeft?) := by
  have h (w : List (DoubleStrand I ℓ)) : (w.map (DoubleStrand.weight RD Λ)).sum =
      ((w.filterMap DoubleStrand.redLabel).map Λ).sum + RD.wX (w.filterMap Sum.getLeft?) := by
    induction w with
    | nil => simp
    | cons s w ih =>
      cases s <;> simp [DoubleStrand.weight, List.filterMap_cons, ih, add_assoc, add_left_comm]
  rw [rightWeight, h, b.redOrder]
  simp [List.ofFn_eq_map, add_assoc]

private theorem pairwise_red_iff {μ : Multiset (I ⊕ Fin ℓ)} (s : Seq μ) :
    ((List.ofFn s.lbl).filterMap Sum.getRight?).Pairwise (· < ·) ↔ IsRedOrdered s := by
  rw [List.pairwise_filterMap, List.pairwise_iff_getElem]
  simp only [List.length_ofFn, List.getElem_ofFn, Sum.getRight?_eq_some_iff]
  constructor
  · intro h a b r r' hab ha hb
    exact h a b a.isLt b.isLt hab r ha r' hb
  · intro h a b ha hb hab r hr r' hr'
    exact h ⟨a, ha⟩ ⟨b, hb⟩ r r' hab hr hr'

private theorem filterMap_none {α β : Type*} (m : Multiset α) :
    Multiset.filterMap (fun _ : α => (none : Option β)) m = 0 := by
  induction m using Multiset.induction_on with
  | empty => rfl
  | cons a m ih => rw [Multiset.filterMap_cons_none a m rfl, ih]

private theorem rightContent_stendhalWeight (ν : Multiset I) :
    (stendhalWeight ℓ ν).filterMap Sum.getRight? = (List.finRange ℓ : Multiset (Fin ℓ)) := by
  rw [stendhalWeight, Multiset.filterMap_add, Multiset.filterMap_map, Multiset.filterMap_map]
  simp [Function.comp_def, filterMap_none, ← List.ofFn_id, ← Fin.univ_val_map]

private theorem leftContent_stendhalWeight (ν : Multiset I) :
    (stendhalWeight ℓ ν).filterMap Sum.getLeft? = ν := by
  rw [stendhalWeight, Multiset.filterMap_add, Multiset.filterMap_map, Multiset.filterMap_map]
  simp [Function.comp_def, filterMap_none]

private theorem red_order_of_seq {ν : Multiset I} (s : Seq (stendhalWeight ℓ ν))
    (hs : IsRedOrdered s) : (List.ofFn s.lbl).filterMap Sum.getRight? = List.finRange ℓ := by
  have hc : (List.ofFn s.lbl : Multiset (I ⊕ Fin ℓ)) = stendhalWeight ℓ ν := by
    rw [← Fin.univ_val_map]
    exact s.property
  have hp : List.Perm ((List.ofFn s.lbl).filterMap Sum.getRight?) (List.finRange ℓ) := by
    apply Multiset.coe_eq_coe.mp
    rw [← Multiset.filterMap_coe, hc, rightContent_stendhalWeight]
  exact List.Perm.eq_of_sortedLE ((pairwise_red_iff s).mpr hs).sortedLT.sortedLE
    (List.sortedLT_finRange ℓ).sortedLE hp

/-- The boundary inclusion in Webster, arXiv:1309.3796v2, §4.5, Definition 4.27.
The orientation of every black strand of an ordinary sequence is downward. -/
def ofDown {ν : Multiset I} (s : Seq (stendhalWeight ℓ ν)) (hs : IsRedOrdered s) :
    DoubleBoundary I ℓ where
  word := (List.ofFn s.lbl).map DoubleStrand.down
  redOrder := by
    rw [List.filterMap_map]
    simpa only [Function.comp_def, DoubleStrand.redLabel_down] using red_order_of_seq s hs

@[simp] theorem eraseWord_ofDown {ν : Multiset I} (s : Seq (stendhalWeight ℓ ν))
    (hs : IsRedOrdered s) : (ofDown s hs).eraseWord = List.ofFn s.lbl := by
  simp [eraseWord, ofDown, Function.comp_def]

@[simp] theorem allDown_ofDown {ν : Multiset I} (s : Seq (stendhalWeight ℓ ν))
    (hs : IsRedOrdered s) : (ofDown s hs).AllDown := by
  intro i hi
  obtain ⟨x, _, hx⟩ := List.mem_map.mp hi
  cases x <;> simp [DoubleStrand.down] at hx

/-- The all-down inclusion preserves and reflects the violating boundary condition
of Webster, arXiv:1309.3796v2, Definitions 4.3 and 4.27. -/
@[simp] theorem isViolated_ofDown_iff {ν : Multiset I} (s : Seq (stendhalWeight ℓ ν))
    (hs : IsRedOrdered s) : (ofDown s hs).IsViolated ↔ Stendhal.IsViolated s := by
  simp only [IsViolated, Stendhal.IsViolated, ofDown, List.head?_eq_getElem?]
  by_cases h : 0 < (stendhalWeight ℓ ν).card
  · cases hz : s.lbl ⟨0, h⟩ <;> simp [h, hz, DoubleStrand.down]
  · simp [h]

private theorem blackContent_eq (b : DoubleBoundary I ℓ) :
    b.blackContent = (b.eraseWord : Multiset (I ⊕ Fin ℓ)).filterMap Sum.getLeft? := by
  rw [blackContent, eraseWord, ← Multiset.filterMap_coe, ← Multiset.map_coe,
    Multiset.filterMap_map]
  rfl

@[simp] theorem blackContent_ofDown {ν : Multiset I} (s : Seq (stendhalWeight ℓ ν))
    (hs : IsRedOrdered s) : (ofDown s hs).blackContent = ν := by
  rw [blackContent_eq, eraseWord_ofDown, ← Fin.univ_val_map, s.property,
    leftContent_stendhalWeight]

private theorem redLabels_eraseWord (b : DoubleBoundary I ℓ) :
    b.eraseWord.filterMap Sum.getRight? = List.finRange ℓ := by
  rw [eraseWord, List.filterMap_map]
  simpa only [Function.comp_def, DoubleStrand.getRight?_erase] using b.redOrder

private theorem list_content (w : List (I ⊕ Fin ℓ)) :
    (w : Multiset (I ⊕ Fin ℓ)) =
      (w.filterMap Sum.getLeft? : Multiset I).map Sum.inl +
      (w.filterMap Sum.getRight? : Multiset (Fin ℓ)).map Sum.inr := by
  induction w with
  | nil => simp
  | cons x w ih =>
    cases x with
    | inl x =>
      simp only [List.filterMap_cons, Sum.getLeft?_inl, Sum.getRight?_inl,
        ← Multiset.cons_coe, Multiset.map_cons, Multiset.cons_add]
      exact congrArg (Multiset.cons (.inl x)) ih
    | inr x =>
      simp only [List.filterMap_cons, Sum.getLeft?_inr, Sum.getRight?_inr,
        ← Multiset.cons_coe, Multiset.map_cons, Multiset.add_cons]
      exact congrArg (Multiset.cons (.inr x)) ih

private theorem eraseWord_content (b : DoubleBoundary I ℓ) :
    (b.eraseWord : Multiset (I ⊕ Fin ℓ)) = stendhalWeight ℓ b.blackContent := by
  rw [list_content, redLabels_eraseWord, stendhalWeight, blackContent_eq,
    Multiset.filterMap_coe]
  rw [← List.ofFn_id, ← Fin.univ_val_map, Multiset.map_id]

/-- The ordinary sequence obtained by forgetting the orientations of a signed boundary. -/
def toSeq (b : DoubleBoundary I ℓ) {ν : Multiset I} (h : b.blackContent = ν) :
    Seq (stendhalWeight ℓ ν) :=
  KLRAlgebra.Seq.ofList b.eraseWord (by rw [eraseWord_content, h])

@[simp] theorem list_toSeq (b : DoubleBoundary I ℓ) {ν : Multiset I} (h : b.blackContent = ν) :
    List.ofFn (b.toSeq h).lbl = b.eraseWord := by
  unfold toSeq KLRAlgebra.Seq.ofList
  rw [← List.ofFn_congr _ b.eraseWord.get, List.ofFn_get]
  rw [← Multiset.coe_card, eraseWord_content, h]

theorem isRedOrdered_toSeq (b : DoubleBoundary I ℓ) {ν : Multiset I} (h : b.blackContent = ν) :
    IsRedOrdered (b.toSeq h) := by
  rw [← pairwise_red_iff, list_toSeq, redLabels_eraseWord]
  exact (List.sortedLT_finRange ℓ).pairwise

/-- The all-down part of Webster's signed boundary data in arXiv:1309.3796v2,
§4.5, Definitions 4.23 and 4.27, consists of the existing ordered Stendhal
sequences in each black multiset. -/
def allDownEquiv (ν : Multiset I) :
    {s : Seq (stendhalWeight ℓ ν) // IsRedOrdered s} ≃
      {b : DoubleBoundary I ℓ // b.AllDown ∧ b.blackContent = ν} where
  toFun s := ⟨ofDown s.1 s.2, allDown_ofDown s.1 s.2, blackContent_ofDown s.1 s.2⟩
  invFun b := ⟨b.1.toSeq b.2.2, b.1.isRedOrdered_toSeq b.2.2⟩
  left_inv s := by
    apply Subtype.ext
    apply Subtype.ext
    apply List.ofFn_injective
    rw [list_toSeq, eraseWord_ofDown]
  right_inv b := by
    apply Subtype.ext
    apply DoubleBoundary.ext
    change (List.ofFn (b.1.toSeq b.2.2).lbl).map DoubleStrand.down = b.1.word
    rw [list_toSeq, eraseWord, List.map_map]
    conv_rhs => rw [← List.map_id b.1.word]
    apply List.map_congr_left
    intro x hx
    cases x with
    | inr => rfl
    | inl s =>
      obtain ⟨(_ | _), i⟩ := s
      · rfl
      · exact False.elim (b.2.1 i hx)

end DoubleBoundary

/-- A double Stendhal triple with prescribed left and right weights, as in Webster,
arXiv:1309.3796v2, §4.5, Definition 4.23. The red family consists of dominant weights. -/
def DoubleStendhalTriple {C : CartanDatum I} {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (RD : WeightDatum C X Y) (Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x})
    (left right : X) :=
  {b : DoubleBoundary I ℓ // b.rightWeight RD (fun r => (Λ r).1) left = right}

end Categorification.Stendhal
