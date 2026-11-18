/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleDiagram
import StringDiagrams.Biadjunction.PivotalExtension

/-!
# Red crossings and caps in a double Stendhal diagram

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
§4.5, Definition 4.24 and the proof of Theorem 4.25. The latter writes a
red/downward crossing as the mate of the red/upward crossing via a cup and
a cap. In counit form, the red strand starts between the two black ends of a
cap. Sliding it to either side and then capping gives the same morphism.
The two choices of the black orientation give the two counit equations.
-/

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe w u v₁ v₂

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X : Type v₁} {Y : Type v₂}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (Λ : Fin ℓ → X)

/-- The cap with the red strand initially between its black endpoints, moving
the red strand to the right before applying the cap. -/
def redCapLeft (μ : X) (u : List (DoubleStrand I ℓ)) (l : Letter I) (r : Fin ℓ)
    (v : List (DoubleStrand I ℓ)) :
    obj RD Λ μ (u ++ [.inl l.dual, .inr r, .inl l] ++ v) ⟶ obj RD Λ μ (u ++ [.inr r] ++ v) :=
  let d := moveDiagram RD Λ μ (u ++ [.inl l.dual]) (.redBlack r l) v
  let e := moveDiagram RD Λ μ u (.black (.cap l)) (.inr r :: v)
  let mid := obj RD Λ μ (u ++ [.inl l.dual, .inl l, .inr r] ++ v)
  Diagram.cast (b' := mid) d (by simp [List.append_assoc, Move.bottom])
    (by simp [mid, List.append_assoc, Move.top]) ≫
  Diagram.cast e (by simp [mid, List.append_assoc, Move.bottom])
    (by simp [List.append_assoc, Move.top])

/-- The cap with the red strand initially between its black endpoints, moving
the red strand to the left before applying the cap. -/
def redCapRight (μ : X) (u : List (DoubleStrand I ℓ)) (l : Letter I) (r : Fin ℓ)
    (v : List (DoubleStrand I ℓ)) :
    obj RD Λ μ (u ++ [.inl l.dual, .inr r, .inl l] ++ v) ⟶ obj RD Λ μ (u ++ [.inr r] ++ v) :=
  let d := moveDiagram RD Λ μ u (.blackRed l.dual r) (.inl l :: v)
  let e := moveDiagram RD Λ μ (u ++ [.inr r]) (.black (.cap l)) v
  let mid := obj RD Λ μ (u ++ [.inr r, .inl l.dual, .inl l] ++ v)
  Diagram.cast (b' := mid) d (by simp [List.append_assoc, Move.bottom])
    (by simp [mid, List.append_assoc, Move.top]) ≫
  Diagram.cast e (by simp [mid, List.append_assoc, Move.bottom])
    (by simp [Move.top])

/-- A red/cap mate relation in an arbitrary signed context. -/
structure RedCapRelation (X : Type v₁) (I : Type u) (ℓ : ℕ) where
  leftWeight : X
  left : List (DoubleStrand I ℓ)
  black : Letter I
  red : Fin ℓ
  right : List (DoubleStrand I ℓ)

variable {k : Type w} [CommRing k]

/-- Adjoin the counit form of the two red/cap mate equations of Webster,
arXiv:1309.3796v2, §4.5, proof of Theorem 4.25. -/
def addRedCapRelations (P : Presentation.{w, max u v₁} (signature RD Λ) k) :
    Presentation.{w, max u v₁} (signature RD Λ) k :=
  P.addRels (RedCapRelation X I ℓ)
    (fun a => obj RD Λ a.leftWeight (a.left ++ [.inl a.black.dual, .inr a.red, .inl a.black] ++ a.right))
    (fun a => obj RD Λ a.leftWeight (a.left ++ [.inr a.red] ++ a.right))
    (fun a => LinDiagram.of (redCapLeft RD Λ a.leftWeight a.left a.black a.red a.right) -
      LinDiagram.of (redCapRight RD Λ a.leftWeight a.left a.black a.red a.right))

/-- The straddled form of the red/cap equation in the presented category. -/
theorem redCap_slide (P : Presentation.{w, max u v₁} (signature RD Λ) k)
    (μ : X) (u : List (DoubleStrand I ℓ)) (l : Letter I) (r : Fin ℓ)
    (v : List (DoubleStrand I ℓ)) :
    (addRedCapRelations RD Λ P).diag (redCapLeft RD Λ μ u l r v) =
      (addRedCapRelations RD Λ P).diag (redCapRight RD Λ μ u l r v) :=
  (addRedCapRelations RD Λ P).diag_eq_of_rel (.inr ⟨μ, u, l, r, v⟩) rfl

end Categorification.Stendhal.DoubleDiagram
