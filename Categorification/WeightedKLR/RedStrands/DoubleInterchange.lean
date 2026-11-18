/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleDiagram
import StringDiagrams.Positional

/-!
# Interchanging disjoint signed Stendhal moves

The isotopies used in Webster, arXiv:1309.3796v2, Definition 4.24 and
Lemma 4.28 permit two local moves on disjoint sets of strands to be performed
in either order. This is the interchange law of the region-labelled signature.
-/
set_option backward.isDefEq.respectTransparency false

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot StringDiagrams

universe w u v
variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (Λ : Fin ℓ → X)
  {k : Type w} [CommRing k] (P : Presentation.{w,max u v} (signature RD Λ) k)
  (μ : X) (u : List (DoubleStrand I ℓ)) (g : Move I ℓ) (m : List (DoubleStrand I ℓ))
  (h : Move I ℓ) (v : List (DoubleStrand I ℓ))

local notation "W" => fun (s t : List (DoubleStrand I ℓ)) =>
  obj RD Λ μ (u ++ s ++ m ++ t ++ v)

/-- Apply the left move in a pair of separated intervals. -/
def separatedLeft (t : List (DoubleStrand I ℓ)) : W g.bottom t ⟶ W g.top t :=
  Diagram.cast (moveDiagram RD Λ μ u g (m ++ t ++ v))
    (by simp [List.append_assoc]) (by simp [List.append_assoc])

/-- Apply the right move in a pair of separated intervals. -/
def separatedRight (s : List (DoubleStrand I ℓ)) : W s h.bottom ⟶ W s h.top :=
  moveDiagram RD Λ μ (u ++ s ++ m) h v

/-- Two disjoint critical points in a signed diagram commute. This also covers
cups and caps and signed contexts with an arbitrary number of red strands. -/
theorem separatedMoves_comm :
    P.diag (separatedLeft RD Λ μ u g m v h.bottom) ≫ P.diag (separatedRight RD Λ μ u m h v g.top) =
      P.diag (separatedRight RD Λ μ u m h v g.bottom) ≫ P.diag (separatedLeft RD Λ μ u g m v h.top) := by
  rw [← P.diag_comp, ← P.diag_comp]
  let η := endWeight RD Λ μ u
  let ξ := endWeight RD Λ η g.bottom
  let ρ := endWeight RD Λ ξ m
  apply P.diag_interchange_of_layers_of_even μ (colours RD Λ μ u) (colours RD Λ ξ m)
    (colours RD Λ (endWeight RD Λ ρ h.bottom) v) (η, g) (ρ, h) (.inl rfl)
  all_goals
    rw [Diagram.layers_comp]
    simp [separatedLeft, separatedRight, moveDiagram, layer, signature, ξ, η, ρ, colours_append,
      endWeight_append, g.endWeight_top, h.endWeight_top, List.append_assoc]

end Categorification.Stendhal.DoubleDiagram
