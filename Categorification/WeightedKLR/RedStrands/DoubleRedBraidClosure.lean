/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleRedBubbleCoefficients
import Categorification.WeightedKLR.RedStrands.DoubleDownRelations
import Categorification.Diagrams.KL3.BubbleSlidesGen

/-!
# The capped red braid in double Stendhal diagrams

Webster, arXiv:1309.3796v2, Definitions 4.5 and 4.24. Closing the two black
strands of the downward black–red–black braid by a clockwise cup and a
counterclockwise cup on opposite sides of red gives the signed version of
the closed divided difference. This is the analogue of the starting step
of the mixed Grassmannian calculation in Brundan–Ellis, arXiv:1701.04133v2,
proof of Proposition 7.3(iii).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot StringDiagrams
open KLR.Diagram
open scoped Matrix

universe w u v
variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (Λ : Fin ℓ → X)
  (μ : X) (L : List (DoubleStrand I ℓ)) (i : I) (r : Fin ℓ)
  (R : List (DoubleStrand I ℓ))

local notation "upStrand" => (Sum.inl (true, i) : DoubleStrand I ℓ)
local notation "downStrand" => (Sum.inl (false, i) : DoubleStrand I ℓ)
local notation "redStrand" => (Sum.inr r : DoubleStrand I ℓ)
local notation "blackLabel" => (Sum.inl i : I ⊕ Fin ℓ)
local notation "redLabel" => (Sum.inr r : I ⊕ Fin ℓ)
local notation "b₀" => obj RD Λ μ (L ++ [redStrand] ++ R)
local notation "b₁" => obj RD Λ μ (L ++ [upStrand, downStrand, redStrand] ++ R)
local notation "b₂" => obj RD Λ μ (L ++ [redStrand, downStrand, upStrand] ++ R)
local notation "a" => ob [blackLabel, redLabel, blackLabel]
local notation "b" => downContextObj RD Λ μ (L ++ [upStrand]) (upStrand :: R) a

/-- Create a clockwise black cup on the left and a counterclockwise black cup
on the right of the red strand. The inner black legs are both downward. -/
def redBraidClosureCups : b₀ ⟶ b :=
  let c := moveDiagram RD Λ μ L (.black (.cup (true, i))) (redStrand :: R)
  let d := moveDiagram RD Λ μ (L ++ [upStrand, downStrand, redStrand]) (.black (.cup (false, i))) R
  Diagram.cast (b' := b₁) c (by simp [Move.bottom, List.append_assoc])
    (by simp [Move.top]) ≫
  Diagram.cast d (by simp [Move.bottom])
    (by simp [Move.top, downContextObj, ob, DoubleStrand.down, List.append_assoc])

/-- Cap the two black pairs used in the red braid closure. -/
def redBraidClosureCaps : b ⟶ b₀ :=
  let c := moveDiagram RD Λ μ L (.black (.cap (false, i))) (redStrand :: downStrand :: upStrand :: R)
  let d := moveDiagram RD Λ μ (L ++ [redStrand]) (.black (.cap (true, i))) R
  Diagram.cast (b' := b₂) c
    (by simp [Move.bottom, downContextObj, ob, DoubleStrand.down, List.append_assoc])
    (by simp [Move.top]) ≫
  Diagram.cast d (by simp [Move.bottom, List.append_assoc]) (by simp [Move.top])

variable {k : Type w} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (exponents : Fin ℓ → I →₀ ℕ)
  (P : Presentation.{w, max u v} (signature RD Λ) k)

local notation "Qₐ" => affineCoverQ Q exponents
local notation "P₀" => KLR.Diagram.pres k Qₐ
local notation "P₁" => addDownRelations RD Λ Qₐ P
local notation "F" => downPresentedFunctor RD Λ Qₐ P μ (L ++ [upStrand]) (upStrand :: R)

/-- Put a downward endomorphism inside the two black loops at a red strand. -/
def closeRedBraid : End ((P₀).obj a) →ₗ[k] End ((P₁).obj b₀) :=
  (Linear.leftComp k ((P₁).obj b₀) ((P₁).diag (redBraidClosureCups RD Λ μ L i r R))).comp
    ((Linear.rightComp k ((P₁).obj b) ((P₁).diag (redBraidClosureCaps RD Λ μ L i r R))).comp
      ((F).mapLinearMap k))

/-- Closing the two braid diagrams gives the sum of closed dot monomials
from the divided difference. The vanishing of either closed braid is a
separate use of the black curls and the red cup/cap mates. -/
theorem closeRedBraid_sub :
    let close := closeRedBraid RD Λ μ L i r R Q exponents P
    close ((P₀).diag (braidL blackLabel redLabel blackLabel)) -
      close ((P₀).diag (braidR blackLabel redLabel blackLabel)) =
        ∑ j ∈ Finset.range (exponents r i),
          close (End.of ((P₀).diag (E0 blackLabel redLabel blackLabel)) ^ j *
            End.of ((P₀).diag (E2 blackLabel redLabel blackLabel)) ^ (exponents r i - 1 - j)) := by
  let close := closeRedBraid RD Λ μ L i r R Q exponents P
  have h := braidQ_at Qₐ (u := []) (v := []) (c := blackLabel) (d := redLabel)
    Sum.inl_ne_inr (braidL blackLabel redLabel blackLabel) (braidR blackLabel redLabel blackLabel)
    (E0 blackLabel redLabel blackLabel) (E1 blackLabel redLabel blackLabel)
    (E2 blackLabel redLabel blackLabel) rfl rfl rfl rfl rfl
  rw [qbar_affineCoverQ_black_red, KL3.Diagram.ncEval_sum_aux] at h
  simp only [KL3.Diagram.ncEval_X0_pow_mul_X2_pow, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h
  simpa only [map_sub, map_sum] using congrArg close h

end Categorification.Stendhal.DoubleDiagram
