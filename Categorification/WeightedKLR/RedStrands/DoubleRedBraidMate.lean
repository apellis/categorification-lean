/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleRedBraidClosure

/-!
# Bending one strand of the downward red braid

Webster, arXiv:1309.3796v2, Definition 4.5, (4.1a), and Definition 4.24.
Applying a cup and a cap bends one outer black strand of the ordinary braid.
Its divided-difference correction consists of the same cup and cap with dots.
-/
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot StringDiagrams KLR.Diagram
open scoped Matrix

universe w u v
variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (Λ : Fin ℓ → X)
  (μ : X) (L : List (DoubleStrand I ℓ)) (r : Fin ℓ) (i j : I) (R : List (DoubleStrand I ℓ))

/-- The side on which the upward strand appears at the bottom after mating the braid. -/
inductive RedBraidMateSide
  | left | right

private abbrev E (i : I) : DoubleStrand I ℓ := .inl (true, i)
private abbrev F (i : I) : DoubleStrand I ℓ := .inl (false, i)
private abbrev red (r : Fin ℓ) : DoubleStrand I ℓ := .inr r

def RedBraidMateSide.bottom : RedBraidMateSide → List (DoubleStrand I ℓ)
  | .left => [E i, F j, red r]
  | .right => [red r, F j, E i]

def RedBraidMateSide.flip : RedBraidMateSide → RedBraidMateSide
  | .left => .right
  | .right => .left

def RedBraidMateSide.colour (i j : I) : RedBraidMateSide → I
  | .left => j
  | .right => i

private abbrev bottomLabel (s : RedBraidMateSide) : I ⊕ Fin ℓ := .inl (s.colour i j)
local notation "redLabel" => (Sum.inr r : I ⊕ Fin ℓ)
private abbrev braidObj (s : RedBraidMateSide) := ob [bottomLabel i j s, redLabel, bottomLabel i j s.flip]
local notation "src" => braidObj r i j
local notation "D" => downContextObj RD Λ μ (L ++ [E i]) (E i :: R)
private abbrev mateObj (s : RedBraidMateSide) := obj RD Λ μ (L ++ s.bottom r i j ++ R)
local notation "M" => mateObj RD Λ μ L r i j R

/-- The cup below the downward red braid. -/
def redBraidMateCup (s : RedBraidMateSide) : M s ⟶ D (src s) := by
  cases s with
  | left =>
    exact Diagram.cast (moveDiagram RD Λ μ (L ++ [E i, F j, red r]) (.black (.cup (false,i))) R)
      (by simp [mateObj, RedBraidMateSide.bottom, Move.bottom])
      (by simp [RedBraidMateSide.flip, RedBraidMateSide.colour, downContextObj, Move.top, ob,
        braidObj, KLR.Diagram.sig, DoubleStrand.down, List.append_assoc, E, F, red, bottomLabel])
  | right =>
    exact Diagram.cast (moveDiagram RD Λ μ L (.black (.cup (true,i))) (red r :: F j :: E i :: R))
      (by simp [mateObj, RedBraidMateSide.bottom, Move.bottom, List.append_assoc])
      (by simp [RedBraidMateSide.flip, RedBraidMateSide.colour, downContextObj, Move.top, ob,
        braidObj, KLR.Diagram.sig, DoubleStrand.down, List.append_assoc, E, F, red, bottomLabel])

/-- The cap above the downward red braid. -/
def redBraidMateCap (s : RedBraidMateSide) : D (src s.flip) ⟶ M s.flip := by
  cases s with
  | left =>
    exact Diagram.cast (moveDiagram RD Λ μ L (.black (.cap (false,i))) (red r :: F j :: E i :: R))
      (by simp [RedBraidMateSide.flip, RedBraidMateSide.colour, downContextObj, Move.bottom, ob,
        braidObj, KLR.Diagram.sig, DoubleStrand.down, List.append_assoc, E, F, red, bottomLabel])
      (by simp [mateObj, RedBraidMateSide.bottom, RedBraidMateSide.flip, Move.top, List.append_assoc])
  | right =>
    exact Diagram.cast (moveDiagram RD Λ μ (L ++ [E i, F j, red r]) (.black (.cap (true,i))) R)
      (by simp [RedBraidMateSide.flip, RedBraidMateSide.colour, downContextObj, Move.bottom, ob,
        braidObj, KLR.Diagram.sig, DoubleStrand.down, List.append_assoc, E, F, red, bottomLabel])
      (by simp [mateObj, RedBraidMateSide.bottom, RedBraidMateSide.flip, Move.top])

variable {k : Type w} [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k)
  (exponents : Fin ℓ → I →₀ ℕ) (P : Presentation.{w,max u v} (signature RD Λ) k)
local notation "Qₐ" => affineCoverQ Q exponents
local notation "P₀" => KLR.Diagram.pres k Qₐ
local notation "P₁" => addDownRelations RD Λ Qₐ P
local notation "tr" => downPresentedFunctor RD Λ Qₐ P μ (L ++ [E i]) (E i :: R)

/-- Take the one-strand mate inside an arbitrary signed context. -/
def redBraidMate (s : RedBraidMateSide) :
    ((P₀).obj (src s) ⟶ (P₀).obj (src s.flip)) →ₗ[k] ((P₁).obj (M s) ⟶ (P₁).obj (M s.flip)) :=
  (Linear.leftComp k ((P₁).obj (M s.flip)) ((P₁).diag (redBraidMateCup RD Λ μ L r i j R s))).comp
    ((Linear.rightComp k ((P₁).obj (D (src s))) ((P₁).diag (redBraidMateCap RD Λ μ L r i j R s))).comp
      ((tr).mapLinearMap k))

local notation "bL" => fun (i j : I) => braidL (Sum.inl i) redLabel (Sum.inl j)
local notation "bR" => fun (i j : I) => braidR (Sum.inl i) redLabel (Sum.inl j)

/-- The one-strand mates of the two ordinary braid words agree for distinct
black colours. This is Webster (4.1a) applied between a cup and a cap. -/
theorem redBraidMate_ne (h : i ≠ j) (s : RedBraidMateSide) :
    let mate := redBraidMate RD Λ μ L r i j R Q exponents P s
    mate ((P₀).diag (Diagram.cast (bL (s.colour i j) (s.flip.colour i j)) rfl (by cases s <;> rfl))) =
    mate ((P₀).diag (Diagram.cast (bR (s.colour i j) (s.flip.colour i j)) rfl (by cases s <;> rfl))) := by
  cases s <;> dsimp only [RedBraidMateSide.colour, RedBraidMateSide.flip, Diagram.cast_rfl]
  all_goals
    apply congrArg
    apply braid_at Qₐ (u := []) (v := []) _ _ _ rfl rfl
    simp_all [Ne.symm h]

/-- The one-strand mate on endomorphisms of the equal-colour downward triple. -/
def redEqualBraidMate (s : RedBraidMateSide) :
    End ((P₀).obj (ob [.inl i, redLabel, .inl i])) →ₗ[k]
      ((P₁).obj (mateObj RD Λ μ L r i i R s) ⟶ (P₁).obj (mateObj RD Λ μ L r i i R s.flip)) := by
  cases s
  · exact redBraidMate RD Λ μ L r i i R Q exponents P .left
  · exact redBraidMate RD Λ μ L r i i R Q exponents P .right

/-- For equal black colours, the difference of the two one-strand mates is a sum
of mated pure-dot terms. The empty sum covers red exponent zero. -/
theorem redBraidMate_eq (s : RedBraidMateSide) :
    let black : I ⊕ Fin ℓ := .inl i
    let close := redEqualBraidMate RD Λ μ L r i R Q exponents P s
    close ((P₀).diag (braidL black redLabel black)) - close ((P₀).diag (braidR black redLabel black)) =
      ∑ m ∈ Finset.range (exponents r i), close (End.of ((P₀).diag (E0 black redLabel black)) ^ m *
        End.of ((P₀).diag (E2 black redLabel black)) ^ (exponents r i - 1 - m)) := by
  let black : I ⊕ Fin ℓ := .inl i
  have hb := braidQ_at Qₐ (u := []) (v := []) (c := black) (d := redLabel)
    Sum.inl_ne_inr (braidL black redLabel black) (braidR black redLabel black)
    (E0 black redLabel black) (E1 black redLabel black) (E2 black redLabel black) rfl rfl rfl rfl rfl
  rw [qbar_affineCoverQ_black_red, KL3.Diagram.ncEval_sum_aux] at hb
  simp only [KL3.Diagram.ncEval_X0_pow_mul_X2_pow, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hb
  simpa only [map_sub, map_sum] using congrArg (redEqualBraidMate RD Λ μ L r i R Q exponents P s) hb

end Categorification.Stendhal.DoubleDiagram
