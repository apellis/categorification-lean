/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleDiagramCut
import Categorification.WeightedKLR.RedStrands.DoubleViolatingQuotient

/-!
# Vanishing at a violated cut

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
§4.5, Definition 4.27 and the proof of Lemma 4.28. A black strand of either
orientation at the left end of a horizontal cut makes the whole signed diagram zero.
-/
noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot StringDiagrams

universe w u v

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}} {k : Type w} [CommRing k]
  (P : Presentation.{w, max u v} (signature RD (Subtype.val ∘ Λ)) k)
  {η : X}

local notation "labels" => (Subtype.val ∘ Λ)

/-- The horizontal-cut criterion of Webster, arXiv:1309.3796v2, Definition 4.27.
No normal-form assumption is needed on either part of the raw signed diagram.
This applies, in particular, to a dotted bubble at the far left in Lemma 4.28. -/
theorem diagram_eq_zero_of_black_at_cut (b c : BoundaryCategory P η)
    {a : Obj (signature RD labels)} (u : obj RD labels 0 b.val.word ⟶ a)
    (v : a ⟶ obj RD labels 0 c.val.word)
    (h : ∃ l, (a.word.map Prod.snd).head? = some (.inl l)) :
    (violatingFunctor P η).map (InducedCategory.homMk (X := b) (Y := c) (P.diag (u ≫ v))) = 0 := by
  obtain ⟨t, rfl, -⟩ := existsUnique_triple_at_cut RD Λ b u
  have ht : t.val.IsViolated := by
    simpa only [obj, forget_colours, DoubleBoundary.IsViolated] using h
  rw [P.diag_comp]
  exact DoubleViolatingQuotient.map_eq_zero_of_factor k (tripleObj P) (x := b) (y := c) (z := t) ht
    (InducedCategory.homMk (P.diag u)) (InducedCategory.homMk (P.diag v))

end Categorification.Stendhal.DoubleDiagram
