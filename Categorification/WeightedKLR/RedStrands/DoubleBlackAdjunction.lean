/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleDiagram
import StringDiagrams.Biadjunction.Zigzag

/-!
# Black biadjunction and dot cyclicity in double Stendhal diagrams

Webster, arXiv:1309.3796v2 and v3, §2.2, Definition 2.4 and §4.5,
Definition 4.24. The black cups and caps satisfy both biadjunction triangles,
and moving a dot across a cup or cap exchanges the up and down dots. These
relations use the region on the physical left and hold within any signed
context. They are independent of the black crossing parameters.
-/

noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe w u v
variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
    (RD : WeightDatum C X Y) {ℓ : ℕ} (Λ : Fin ℓ → X)
    (μ : X) (L : List (DoubleStrand I ℓ)) (l : Letter I) (R : List (DoubleStrand I ℓ))

local notation "strand" => obj RD Λ μ (L ++ [Sum.inl l] ++ R)
local notation "pair" => obj RD Λ μ (L ++ [Sum.inl l, Sum.inl l.dual] ++ R)
local notation "triple" => obj RD Λ μ (L ++ [Sum.inl l, Sum.inl l.dual, Sum.inl l] ++ R)
local notation "base" => obj RD Λ μ (L ++ R)

/-- The black triangle creating the pair to the left and annihilating the pair
to the right of the surviving strand. -/
def blackSnakeLeft : End strand :=
  let a := moveDiagram RD Λ μ L (.black (.cup l)) (.inl l :: R)
  let b := moveDiagram RD Λ μ (L ++ [.inl l]) (.black (.cap l)) R
  Diagram.cast (b' := triple) a (by simp [Move.bottom, Shape.dom])
    (by simp [Move.top, Shape.cod, List.append_assoc]) ≫
  Diagram.cast b (by simp [Move.bottom, Shape.dom, List.append_assoc])
    (by simp [Move.top, Shape.cod])

/-- The black triangle creating the pair to the right and annihilating the pair
to the left of the surviving strand. -/
def blackSnakeRight : End strand :=
  let a := moveDiagram RD Λ μ (L ++ [.inl l]) (.black (.cup l.dual)) R
  let b := moveDiagram RD Λ μ L (.black (.cap l.dual)) (.inl l :: R)
  Diagram.cast (b' := triple) a (by simp [Move.bottom, Shape.dom])
    (by simp [Move.top, Shape.cod, List.append_assoc]) ≫
  Diagram.cast b (by simp [Move.bottom, Shape.dom, List.append_assoc])
    (by simp [Move.top, Shape.cod])

/-- Insert a cup of the given orientation into a signed context. -/
def blackCup : base ⟶ pair :=
  Diagram.cast (moveDiagram RD Λ μ L (.black (.cup l)) R)
    (by simp [Move.bottom, Shape.dom]) rfl

/-- Close the black pair in the given signed context. -/
def blackCap : pair ⟶ base :=
  Diagram.cast (moveDiagram RD Λ μ L (.black (.cap l.dual)) R)
    (by simp [Move.bottom, Shape.dom]) (by simp [Move.top, Shape.cod])

/-- A dot on the left leg of the black pair. -/
def blackPairDotLeft : End pair :=
  Diagram.cast (moveDiagram RD Λ μ L (.black (.dot l)) (.inl l.dual :: R))
    (by simp [Move.bottom, Shape.dom, List.append_assoc])
    (by simp [Move.top, Shape.cod, List.append_assoc])

/-- A dot on the right leg of the black pair. -/
def blackPairDotRight : End pair :=
  Diagram.cast (moveDiagram RD Λ μ (L ++ [.inl l]) (.black (.dot l.dual)) R)
    (by simp [Move.bottom, Shape.dom, List.append_assoc])
    (by simp [Move.top, Shape.cod, List.append_assoc])

/-- The left leg of a cup carries the dot. -/
def blackCupDotLeft : base ⟶ pair :=
  blackCup RD Λ μ L l R ≫ blackPairDotLeft RD Λ μ L l R

/-- The right leg of a cup carries the dot. -/
def blackCupDotRight : base ⟶ pair :=
  blackCup RD Λ μ L l R ≫ blackPairDotRight RD Λ μ L l R

/-- The left leg of a cap carries the dot. -/
def blackCapDotLeft : pair ⟶ base :=
  blackPairDotLeft RD Λ μ L l R ≫ blackCap RD Λ μ L l R

/-- The right leg of a cap carries the dot. -/
def blackCapDotRight : pair ⟶ base :=
  blackPairDotRight RD Λ μ L l R ≫ blackCap RD Λ μ L l R

/-- The two biadjunction equations and two cup and cap dot slides, with either
orientation of the indicated black strand. -/
inductive BlackAdjunctionKind
  | snakeLeft | snakeRight | cupDot | capDot

/-- A biadjunction or dot-slide relation in a signed context. -/
structure BlackAdjunctionRelation (X : Type v) (I : Type u) (ℓ : ℕ) where
  kind : BlackAdjunctionKind
  leftWeight : X
  left : List (DoubleStrand I ℓ)
  letter : Letter I
  right : List (DoubleStrand I ℓ)

variable {k : Type w} [CommRing k]

private def BlackAdjunctionRelation.dom (r : BlackAdjunctionRelation X I ℓ) :
    Obj (signature RD Λ) :=
  match r.kind with
  | .snakeLeft | .snakeRight => obj RD Λ r.leftWeight (r.left ++ [.inl r.letter] ++ r.right)
  | .cupDot => obj RD Λ r.leftWeight (r.left ++ r.right)
  | .capDot => obj RD Λ r.leftWeight (r.left ++ [.inl r.letter, .inl r.letter.dual] ++ r.right)

private def BlackAdjunctionRelation.cod (r : BlackAdjunctionRelation X I ℓ) :
    Obj (signature RD Λ) :=
  match r.kind with
  | .snakeLeft | .snakeRight => obj RD Λ r.leftWeight (r.left ++ [.inl r.letter] ++ r.right)
  | .cupDot => obj RD Λ r.leftWeight (r.left ++ [.inl r.letter, .inl r.letter.dual] ++ r.right)
  | .capDot => obj RD Λ r.leftWeight (r.left ++ r.right)

open LinDiagram in
private def blackAdjunctionRelation :
    (r : BlackAdjunctionRelation X I ℓ) → LinDiagram k (r.dom RD Λ) (r.cod RD Λ)
  | ⟨.snakeLeft, μ, L, l, R⟩ => of (blackSnakeLeft RD Λ μ L l R) - of (𝟙 _)
  | ⟨.snakeRight, μ, L, l, R⟩ => of (blackSnakeRight RD Λ μ L l R) - of (𝟙 _)
  | ⟨.cupDot, μ, L, l, R⟩ =>
    of (blackCupDotLeft RD Λ μ L l R) - of (blackCupDotRight RD Λ μ L l R)
  | ⟨.capDot, μ, L, l, R⟩ =>
    of (blackCapDotLeft RD Λ μ L l R) - of (blackCapDotRight RD Λ μ L l R)

/-- Adjoin the black biadjunction and dot-cyclicity block of Webster,
arXiv:1309.3796v2 and v3, Definition 2.4, to a double diagram presentation. -/
def addBlackAdjunctionRelations (P : Presentation.{w, max u v} (signature RD Λ) k) :
    Presentation.{w, max u v} (signature RD Λ) k :=
  P.addRels _ (BlackAdjunctionRelation.dom RD Λ) (BlackAdjunctionRelation.cod RD Λ)
    (blackAdjunctionRelation RD Λ)

variable (P : Presentation.{w, max u v} (signature RD Λ) k)
local notation "P₁" => addBlackAdjunctionRelations RD Λ P

/-- The black snake with the cup to the left gives the identity. -/
theorem blackSnakeLeft_eq :
    (P₁).diag (blackSnakeLeft RD Λ μ L l R) = 𝟙 _ :=
  ((P₁).diag_eq_of_rel (.inr ⟨.snakeLeft, μ, L, l, R⟩) rfl).trans ((P₁).diag_id _)

/-- The black snake with the cup to the right gives the identity. -/
theorem blackSnakeRight_eq :
    (P₁).diag (blackSnakeRight RD Λ μ L l R) = 𝟙 _ :=
  ((P₁).diag_eq_of_rel (.inr ⟨.snakeRight, μ, L, l, R⟩) rfl).trans ((P₁).diag_id _)

/-- Move a dot between the two legs of a black cup. -/
theorem blackCup_dot_slide :
    (P₁).diag (blackCupDotLeft RD Λ μ L l R) =
      (P₁).diag (blackCupDotRight RD Λ μ L l R) :=
  (P₁).diag_eq_of_rel (.inr ⟨.cupDot, μ, L, l, R⟩) rfl

/-- Move a dot between the two legs of a black cap. -/
theorem blackCap_dot_slide :
    (P₁).diag (blackCapDotLeft RD Λ μ L l R) =
      (P₁).diag (blackCapDotRight RD Λ μ L l R) :=
  (P₁).diag_eq_of_rel (.inr ⟨.capDot, μ, L, l, R⟩) rfl

end Categorification.Stendhal.DoubleDiagram
