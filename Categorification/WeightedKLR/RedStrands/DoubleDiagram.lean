/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleBoundary
import StringDiagrams.Presentation

/-!
# Layers of double Stendhal diagrams

Webster, arXiv:1309.3796v2, §4.5, Definitions 4.22–4.24. Black layers
are the KL dots, like-oriented crossings, cups and caps. Two mixed layers
move a black strand past a red strand in either order. Reading the boundary
from left to right fixes every intervening region. This signature gives the
diagrams before imposing the local relations of Definition 4.24.
-/

namespace Categorification.Stendhal.DoubleDiagram

open QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams CategoryTheory

variable {I X Y : Type*} {C : CartanDatum I} [AddCommGroup X] [AddCommGroup Y]
    (RD : WeightDatum C X Y) {ℓ : ℕ} (Λ : Fin ℓ → X)

/-- The elementary critical points of a double Stendhal diagram. -/
inductive Move (I : Type*) (ℓ : ℕ)
  | black (g : Shape I)
  | blackRed (b : Letter I) (r : Fin ℓ)
  | redBlack (r : Fin ℓ) (b : Letter I)

namespace Move

/-- Bottom word of the move. -/
def bottom : Move I ℓ → List (DoubleStrand I ℓ)
  | .black g => g.dom.map Sum.inl
  | .blackRed b r => [.inl b, .inr r]
  | .redBlack r b => [.inr r, .inl b]

/-- Top word of the move. -/
def top : Move I ℓ → List (DoubleStrand I ℓ)
  | .black g => g.cod.map Sum.inl
  | .blackRed b r => [.inr r, .inl b]
  | .redBlack r b => [.inl b, .inr r]

/-- Each mixed crossing preserves the ordered red list; black cups and caps
leave it empty on both sides. -/
theorem top_reds (g : Move I ℓ) :
    g.top.filterMap DoubleStrand.redLabel = g.bottom.filterMap DoubleStrand.redLabel := by
  cases g with
  | black g => cases g <;> rfl
  | blackRed | redBlack => rfl

end Move

/-- Region reached at the right end of a word with left label μ. -/
def endWeight (μ : X) (w : List (DoubleStrand I ℓ)) : X :=
  μ + (w.map (DoubleStrand.weight RD Λ)).sum

@[simp] theorem endWeight_cons (μ : X) (a : DoubleStrand I ℓ) (w : List (DoubleStrand I ℓ)) :
    endWeight RD Λ μ (a :: w) = endWeight RD Λ (μ + DoubleStrand.weight RD Λ a) w := by
  simp [endWeight, add_assoc]

theorem endWeight_append (μ : X) (u v : List (DoubleStrand I ℓ)) :
    endWeight RD Λ μ (u ++ v) = endWeight RD Λ (endWeight RD Λ μ u) v := by
  simp [endWeight, add_assoc]

theorem Move.endWeight_top (g : Move I ℓ) (μ : X) :
    endWeight RD Λ μ g.top = endWeight RD Λ μ g.bottom := by
  cases g with
  | black g =>
    cases g <;> simp [Move.top, Move.bottom, Shape.dom, Shape.cod, endWeight,
      DoubleStrand.weight, Letter.dual, add_comm]
  | blackRed | redBlack =>
    simp [Move.top, Move.bottom, endWeight, add_comm]

/-- Annotate each strand by the region on its left. -/
def colours (μ : X) : List (DoubleStrand I ℓ) → List (X × DoubleStrand I ℓ)
  | [] => []
  | a :: w => (μ, a) :: colours (μ + DoubleStrand.weight RD Λ a) w

theorem colours_append (μ : X) (u v : List (DoubleStrand I ℓ)) :
    colours RD Λ μ (u ++ v) = colours RD Λ μ u ++ colours RD Λ (endWeight RD Λ μ u) v := by
  induction u generalizing μ with
  | nil => simp [colours, endWeight]
  | cons a u ih => simp [colours, ih]

/-- The region-labelled signature for Webster, Definition 4.22. -/
def signature : Signature where
  Region := X
  Colour := X × DoubleStrand I ℓ
  colourSrc := Prod.fst
  colourTgt c := c.1 + DoubleStrand.weight RD Λ c.2
  Gen := X × Move I ℓ
  dom g := colours RD Λ g.1 g.2.bottom
  cod g := colours RD Λ g.1 g.2.top
  left := Prod.fst
  right g := endWeight RD Λ g.1 g.2.bottom

instance : (signature RD Λ).IsEven := ⟨fun _ => rfl⟩

/-- The region-labelled string-diagram object of a word. -/
def obj (μ : X) (w : List (DoubleStrand I ℓ)) : Obj (signature RD Λ) := ⟨μ, colours RD Λ μ w⟩

theorem colours_ok (μ : X) (w : List (DoubleStrand I ℓ)) :
    (signature RD Λ).ok μ (colours RD Λ μ w) := by
  induction w generalizing μ with
  | nil => trivial
  | cons a w ih => exact ⟨rfl, ih _⟩

theorem colours_endR (μ : X) (w : List (DoubleStrand I ℓ)) :
    (signature RD Λ).endR μ (colours RD Λ μ w) = endWeight RD Λ μ w := by
  induction w generalizing μ with
  | nil => change μ = μ + 0; exact (add_zero μ).symm
  | cons a w ih => exact (ih _).trans (endWeight_cons RD Λ μ a w).symm

/-- Insert a move between two arbitrary words of identity strands. -/
def layer (μ : X) (u : List (DoubleStrand I ℓ)) (g : Move I ℓ) (v : List (DoubleStrand I ℓ)) :
    Layer (signature RD Λ) :=
  let t := endWeight RD Λ μ u
  ⟨μ, colours RD Λ μ u, (t, g), colours RD Λ (endWeight RD Λ t g.bottom) v⟩

/-- The region labels match at every generator in a context, including cups
and caps of either sign and mixed red/black crossings. -/
theorem layer_valid (μ : X) (u : List (DoubleStrand I ℓ)) (g : Move I ℓ)
    (v : List (DoubleStrand I ℓ)) : (layer RD Λ μ u g v).Valid :=
  ⟨colours_ok .., colours_endR .., colours_ok .., colours_endR .., colours_ok ..,
    (colours_endR ..).trans (g.endWeight_top RD Λ _), colours_ok ..⟩

theorem layer_dom (μ : X) (u : List (DoubleStrand I ℓ)) (g : Move I ℓ)
    (v : List (DoubleStrand I ℓ)) :
    (layer RD Λ μ u g v).dom = obj RD Λ μ (u ++ g.bottom ++ v) := by
  simp [layer, Layer.dom, obj, signature, colours_append, List.append_assoc]
  exact List.append_assoc ..

theorem layer_cod (μ : X) (u : List (DoubleStrand I ℓ)) (g : Move I ℓ)
    (v : List (DoubleStrand I ℓ)) :
    (layer RD Λ μ u g v).cod = obj RD Λ μ (u ++ g.top ++ v) := by
  simp [layer, Layer.cod, obj, signature, colours_append, List.append_assoc, g.endWeight_top]
  exact List.append_assoc ..

/-- A move with the two signed boundary words as its source and target. -/
def moveDiagram (μ : X) (u : List (DoubleStrand I ℓ)) (g : Move I ℓ) (v : List (DoubleStrand I ℓ)) :
    obj RD Λ μ (u ++ g.bottom ++ v) ⟶ obj RD Λ μ (u ++ g.top ++ v) :=
  Diagram.layer _ (layer_valid RD Λ μ u g v) (layer_dom ..) (layer_cod ..)

end Categorification.Stendhal.DoubleDiagram
