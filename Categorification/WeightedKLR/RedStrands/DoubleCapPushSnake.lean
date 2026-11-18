/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCapPushLocal

/-!
# Lowering a dotted triangle

A cup and a cap meeting along one leg form a biadjunction triangle. In the
cap-push argument of Webster, arXiv:1309.3796v2, Lemma 4.28, dots on the
original strand between those two critical points move below the cup. The
resulting straight strand is strictly below the height of the excursion.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe w u v
variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (Λ : Fin ℓ → X)
  (μ : X) (L : List (DoubleStrand I ℓ)) (l : Letter I) (R : List (DoubleStrand I ℓ))

local notation "strand" => obj RD Λ μ (L ++ [Sum.inl l] ++ R)
local notation "triple" => obj RD Λ μ (L ++ [Sum.inl l, Sum.inl l.dual, Sum.inl l] ++ R)

private def triangleCup : strand ⟶ triple :=
  Diagram.cast (moveDiagram RD Λ μ L (.black (.cup l)) (.inl l :: R))
    (by simp [Move.bottom, Shape.dom]) (by simp [Move.top, Shape.cod, List.append_assoc])

private def triangleCap : triple ⟶ strand :=
  Diagram.cast (moveDiagram RD Λ μ (L ++ [.inl l]) (.black (.cap l)) R)
    (by simp [Move.bottom, Shape.dom, List.append_assoc]) (by simp [Move.top, Shape.cod])

/-- A dot on the original strand below the triangle. -/
def strandDot : End strand :=
  Diagram.cast (moveDiagram RD Λ μ L (.black (.dot l)) R) rfl rfl

private def originalDot : End triple :=
  Diagram.cast (moveDiagram RD Λ μ (L ++ [.inl l, .inl l.dual]) (.black (.dot l)) R)
    (by simp [Move.bottom, Shape.dom, List.append_assoc])
    (by simp [Move.top, Shape.cod, List.append_assoc])

/-- The path from a cup on the left to a cap on the right with `n` dots
on the strand entering from below. -/
def dottedSnakeLeft (n : ℕ) : End strand :=
  triangleCup RD Λ μ L l R ≫ (originalDot RD Λ μ L l R ^ n) ≫ triangleCap RD Λ μ L l R

variable {k : Type w} [CommRing k] (P : Presentation.{w,max u v} (signature RD Λ) k)
local notation "P₁" => addBlackAdjunctionRelations RD Λ P
local notation "cup" => triangleCup RD Λ μ L l R
local notation "cap" => triangleCap RD Λ μ L l R
local notation "x" => strandDot RD Λ μ L l R
local notation "y" => originalDot RD Λ μ L l R

private theorem triangle_dot : (P₁).diag cup ≫ (P₁).diag y = (P₁).diag x ≫ (P₁).diag cup := by
  let η := endWeight RD Λ μ L
  let θ := endWeight RD Λ η [.inl l]
  rw [← (P₁).diag_comp, ← (P₁).diag_comp]
  apply (P₁).diag_interchange_of_layers_of_even μ (colours RD Λ μ L) [] (colours RD Λ θ R)
    (η, .black (.cup l)) (η, .black (.dot l)) (.inl rfl)
  all_goals
    simp [triangleCup, originalDot, strandDot, moveDiagram, layer, signature, η, θ,
      colours_append, Move.bottom, Move.top, Shape.dom, Shape.cod, colours, endWeight,
      DoubleStrand.weight, Letter.dual, add_assoc]

/-- In the black biadjunction presentation the dotted triangle is exactly a
straight strand carrying the same number of dots. -/
theorem dottedSnakeLeft_eq (n : ℕ) :
    (P₁).diag (dottedSnakeLeft RD Λ μ L l R n) = (P₁).diag (x ^ n) := by
  have h (m : ℕ) : (P₁).diag cup ≫ (P₁).diag (y ^ m) = (P₁).diag (x ^ m) ≫ (P₁).diag cup := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, pow_succ]
      change (P₁).diag cup ≫ (P₁).diag (y ≫ y ^ m) = (P₁).diag (x ≫ x ^ m) ≫ (P₁).diag cup
      rw [Presentation.diag_comp, Presentation.diag_comp, ← Category.assoc,
        triangle_dot RD Λ μ L l R P, Category.assoc, ih, Category.assoc]
  have snake : (P₁).diag cup ≫ (P₁).diag cap = 𝟙 _ := by
    rw [← Presentation.diag_comp]
    exact blackSnakeLeft_eq RD Λ μ L l R P
  rw [dottedSnakeLeft, Presentation.diag_comp, Presentation.diag_comp, ← Category.assoc,
    h, Category.assoc, snake, Category.comp_id]

/-- The intersecting dotted peak lowers in an arbitrary signed exterior word. -/
theorem dottedSnakeLeft_lower (n : ℕ) :
    (P₁).diag (dottedSnakeLeft RD Λ μ L l R n) ∈ lowerCutSpan (P₁) strand strand (cutHeight strand + 1) := by
  apply Submodule.subset_span
  refine ⟨x ^ n, ?_, dottedSnakeLeft_eq RD Λ μ L l R P n⟩
  intro M hm
  suffices ht : M.cod = strand by rw [ht]; omega
  induction n with
  | zero => simp at hm
  | succ n ih =>
    rw [pow_succ] at hm
    change M ∈ Diagram.layers (x ≫ x ^ n) at hm
    rw [Diagram.layers_comp] at hm
    rcases List.mem_append.mp hm with h | h
    · have hM : M = layer RD Λ μ L (.black (.dot l)) R := by simpa [strandDot, moveDiagram] using h
      rw [hM, layer_cod]
      rfl
    · exact ih h

end Categorification.Stendhal.DoubleDiagram
