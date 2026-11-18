/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleDiagramRewriting
import Categorification.WeightedKLR.RedStrands.DoubleRedCup
import Categorification.WeightedKLR.RedStrands.DoubleRedUp
import StringDiagrams.Transport

/-!
# Passing a cap through a red strand

Webster, arXiv:1309.3796v2, §4.5, Definition 4.24 and Lemma 4.28.
The counit mate replaces the second crossing in a cap passing through red
by the inverse direction of the first crossing. The resulting bigon is
an identity on an upward leg and a dot power on a downward leg.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe w u v
variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) {ℓ : ℕ} (Λ : Fin ℓ → X)
  (μ : X) (L : List (DoubleStrand I ℓ)) (l : Letter I) (r : Fin ℓ) (R : List (DoubleStrand I ℓ))

local notation "a" => (Sum.inl l.dual : DoubleStrand I ℓ)
local notation "b" => (Sum.inl l : DoubleStrand I ℓ)
local notation "red" => (Sum.inr r : DoubleStrand I ℓ)
local notation "W" => obj RD Λ μ
local notation "redOnly" => W (L ++ [red] ++ R)
local notation "redLeft" => W (L ++ [red, a] ++ b :: R)
local notation "redRight" => W (L ++ [a] ++ [b, red] ++ R)
local notation "middle" => W (L ++ [a, red, b] ++ R)
local notation "middleL" => W (L ++ [a, red] ++ b :: R)
local notation "middleR" => W (L ++ [a] ++ [red, b] ++ R)

private theorem middle_left : middleL = middle := by simp [List.append_assoc]
private theorem middle_right : middleR = middle := by simp [List.append_assoc]

/-- The red strand starts to the left, crosses both black legs to the right,
and the two black legs are capped. -/
def capWithRedPassingLeft : redLeft ⟶ redOnly :=
  moveDiagram RD Λ μ L (.redBlack r l.dual) (b :: R) ≫
    Diagram.cast (redCapLeft RD Λ μ L l r R) (middle_left RD Λ μ L l r R).symm rfl

/-- The red strand starts to the right, crosses both black legs to the left,
and the two black legs are capped. -/
def capWithRedPassingRight : redRight ⟶ redOnly :=
  moveDiagram RD Λ μ (L ++ [a]) (.blackRed l r) R ≫
    Diagram.cast (redCapRight RD Λ μ L l r R) (middle_right RD Λ μ L l r R).symm rfl

/-- Cap the black legs while the red strand remains on the left. -/
def capKeepingRedLeft : redLeft ⟶ redOnly :=
  Diagram.cast (moveDiagram RD Λ μ (L ++ [red]) (.black (.cap l)) R)
    (by simp [Move.bottom, Shape.dom, List.append_assoc]) (by simp [Move.top, Shape.cod])

/-- Cap the black legs while the red strand remains on the right. -/
def capKeepingRedRight : redRight ⟶ redOnly :=
  Diagram.cast (moveDiagram RD Λ μ L (.black (.cap l)) (red :: R))
    (by simp [Move.bottom, Shape.dom, List.append_assoc]) (by simp [Move.top, Shape.cod, List.append_assoc])

private theorem cast_redCapRight_left :
    Diagram.cast (redCapRight RD Λ μ L l r R) (middle_left RD Λ μ L l r R).symm rfl =
      moveDiagram RD Λ μ L (.blackRed l.dual r) (b :: R) ≫ capKeepingRedLeft RD Λ μ L l r R := by
  apply Diagram.ext
  rfl

private theorem cast_redCapLeft_right :
    Diagram.cast (redCapLeft RD Λ μ L l r R) (middle_right RD Λ μ L l r R).symm rfl =
      moveDiagram RD Λ μ (L ++ [a]) (.redBlack r l) R ≫ capKeepingRedRight RD Λ μ L l r R := by
  apply Diagram.ext
  rfl

variable {k : Type w} [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k) (exponents : Fin ℓ → I →₀ ℕ)
  (P : Presentation.{w, max u v} (signature RD Λ) k)

local notation "U" => addRedUpRelations RD Λ k P
local notation "D" => addDownRelations RD Λ (affineCoverQ Q exponents) (U)
local notation "T" => addRedCapRelations RD Λ (D)

private theorem capWithRedPassingLeft_eq :
    (T).diag (capWithRedPassingLeft RD Λ μ L l r R) =
      (T).diag (moveDiagram RD Λ μ L (.redBlack r l.dual) (b :: R) ≫
        moveDiagram RD Λ μ L (.blackRed l.dual r) (b :: R)) ≫
        (T).diag (capKeepingRedLeft RD Λ μ L l r R) := by
  unfold capWithRedPassingLeft
  rw [Presentation.diag_comp, ← Presentation.castHom_diag,
    redCap_slide RD Λ (D) μ L l r R, Presentation.castHom_diag, cast_redCapRight_left,
    Presentation.diag_comp, ← Category.assoc, ← Presentation.diag_comp]

private theorem capWithRedPassingRight_eq :
    (T).diag (capWithRedPassingRight RD Λ μ L l r R) =
      (T).diag (moveDiagram RD Λ μ (L ++ [a]) (.blackRed l r) R ≫
        moveDiagram RD Λ μ (L ++ [a]) (.redBlack r l) R) ≫
        (T).diag (capKeepingRedRight RD Λ μ L l r R) := by
  unfold capWithRedPassingRight
  rw [Presentation.diag_comp, ← Presentation.castHom_diag,
    ← redCap_slide RD Λ (D) μ L l r R, Presentation.castHom_diag, cast_redCapLeft_right,
    Presentation.diag_comp, ← Category.assoc, ← Presentation.diag_comp]

/-- If red first meets the upward leg while passing a cap from left to right,
the cap may be taken immediately with red still on the left. -/
theorem capWithRedPassingLeft_up (i : I) :
    (T).diag (capWithRedPassingLeft RD Λ μ L (false, i) r R) =
      (T).diag (capKeepingRedLeft RD Λ μ L (false, i) r R) := by
  rw [capWithRedPassingLeft_eq]
  have h := (redUpCrossingIso RD Λ P μ L r i (.inl (false, i) :: R)).hom_inv_id
  change (U).diag _ ≫ (U).diag _ = _ at h
  rw [← Presentation.diag_comp, ← (U).diag_id] at h
  refine (congrArg (· ≫ (T).diag (capKeepingRedLeft RD Λ μ L (false, i) r R))
    (show (T).diag _ = (T).diag _ from diag_eq_addRels (D) (diag_eq_addRels (U) h))).trans ?_
  rw [Presentation.diag_id, Category.id_comp]

/-- If red first meets the upward leg while passing a cap from right to left,
the cap may be taken immediately with red still on the right. -/
theorem capWithRedPassingRight_up (i : I) :
    (T).diag (capWithRedPassingRight RD Λ μ L (true, i) r R) =
      (T).diag (capKeepingRedRight RD Λ μ L (true, i) r R) := by
  rw [capWithRedPassingRight_eq]
  have h := (redUpCrossingIso RD Λ P μ (L ++ [.inl (false, i)]) r i R).inv_hom_id
  change (U).diag _ ≫ (U).diag _ = _ at h
  rw [← Presentation.diag_comp, ← (U).diag_id] at h
  refine (congrArg (· ≫ (T).diag (capKeepingRedRight RD Λ μ L (true, i) r R))
    (show (T).diag _ = (T).diag _ from diag_eq_addRels (D) (diag_eq_addRels (U) h))).trans ?_
  rw [Presentation.diag_id, Category.id_comp]

private theorem diag_pow {B : Presentation.{w, max u v} (signature RD Λ) k}
    {s : Obj (signature RD Λ)} (f : End s) (n : ℕ) :
    B.diag (f ^ n) = End.of (B.diag f) ^ n := by
  induction n with
  | zero => exact B.diag_id _
  | succ n ih => rw [pow_succ, End.mul_def, B.diag_comp, ih, pow_succ, End.mul_def]

/-- If red first meets the downward leg while passing a cap from left to right,
the replacement consists of the red dot power on that leg followed by the cap. -/
theorem capWithRedPassingLeft_down (i : I) :
    (T).diag (capWithRedPassingLeft RD Λ μ L (true, i) r R) =
      (End.of ((T).diag (redDownDotRedLeft RD Λ μ L r i (.inl (true, i) :: R))) ^ exponents r i) ≫
        (T).diag (capKeepingRedLeft RD Λ μ L (true, i) r R) := by
  rw [capWithRedPassingLeft_eq, ← diag_pow]
  apply congrArg (· ≫ (T).diag (capKeepingRedLeft RD Λ μ L (true, i) r R))
  apply diag_eq_addRels (D)
  rw [diag_pow]
  exact redDown_bigon_redLeft RD Λ Q exponents (U) μ L r i (.inl (true, i) :: R)

/-- If red first meets the downward leg while passing a cap from right to left,
the replacement consists of the red dot power on that leg followed by the cap. -/
theorem capWithRedPassingRight_down (i : I) :
    (T).diag (capWithRedPassingRight RD Λ μ L (false, i) r R) =
      (End.of ((T).diag (redDownDotBlackLeft RD Λ μ (L ++ [.inl (true, i)]) r i R)) ^ exponents r i) ≫
        (T).diag (capKeepingRedRight RD Λ μ L (false, i) r R) := by
  rw [capWithRedPassingRight_eq, ← diag_pow]
  apply congrArg (· ≫ (T).diag (capKeepingRedRight RD Λ μ L (false, i) r R))
  apply diag_eq_addRels (D)
  rw [diag_pow]
  exact redDown_bigon_blackLeft RD Λ Q exponents (U) μ (L ++ [.inl (true, i)]) r i R

end Categorification.Stendhal.DoubleDiagram
