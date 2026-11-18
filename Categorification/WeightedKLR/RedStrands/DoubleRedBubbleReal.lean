/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleRedBraidBubbles

/-!
# Transport of normalized real bubbles through a red strand

Webster, arXiv:1309.3796v2, §2.2 and §4.5, proof of Lemma 4.28.
The normalized degree index is preserved by sliding a real bubble through red.
Clockwise bubbles start from the right, counterclockwise bubbles from the left.
Cyclicity of the reflected black KL presentation moves the dots to the canonical
leg of the clockwise bubble.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory StringDiagrams QuantumGroup QuantumGroup.UDot KL3.Diagram

universe u v w
variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) {ℓ : ℕ} (Λ : Fin ℓ → X) {k : Type w} [CommRing k]
  (μ : X) (L : List (DoubleStrand I ℓ)) (i : I) (r : Fin ℓ) (R : List (DoubleStrand I ℓ))
  (Q : I → I → MvPolynomial (Fin 2) k) (exponents : Fin ℓ → I →₀ ℕ)
  (P : Presentation.{w, max u v} (signature RD Λ) k)

local notation "rS" => (Sum.inr r : DoubleStrand I ℓ)
local notation "initial" => L ++ [rS] ++ R
local notation "Pb" => addBlackKLRelations RD Λ P
local notation "Pd" => addDownRelations RD Λ (affineCoverQ Q exponents)
  (addRedUpRelations RD Λ k (addRedCapRelations RD Λ (addRedCupRelations RD Λ (Pb))))
local notation "nL" => ip RD i (endWeight RD Λ μ L)
local notation "nR" => ip RD i (endWeight RD Λ μ (L ++ [rS]))
local notation "before" => normalizedBubbleBeforeRed RD Λ μ L i r R Q exponents P
local notation "after" => normalizedBubbleAfterRed RD Λ μ L i r R Q exponents P
local notation "B" => reflectedBubble RD Λ μ L r R Q exponents P

/-- At a nonnegative dot index, the extended bubble is the corresponding real KL diagram. -/
theorem BubbleOrientation.beforeReflectionExtended_of_nonneg
    (s : BubbleOrientation) (ξ : X) {m : ℤ} (hm : 0 ≤ m) :
    s.beforeReflectionExtended RD k ξ i m = LinDiagram.of (s.beforeReflection RD ξ i m.toNat) := by
  cases s
  · exact ccwL_of_nonneg RD k ξ i hm
  · exact cwL_of_nonneg RD k ξ i hm

private theorem reflectedBubble_of (u v : List (DoubleStrand I ℓ))
    (e : obj RD Λ μ (u ++ blackWord [] ++ v) = obj RD Λ μ initial)
    (f : End (ob RD (endWeight RD Λ μ u) [])) :
    B u v e (LinDiagram.of f) = (Pd).diag (Diagram.cast (blackDiagram RD Λ μ u v f) e e) := by
  change (Pd).castHom e e ((Pd).lin (blackLinear RD Λ k μ u v (LinDiagram.of f))) = _
  rw [blackLinear_of, Presentation.castHom_lin, LinDiagram.cast_of, Presentation.lin_of]

/-- Interpret a normalized real coefficient before red as a diagram with its integer dot index. -/
theorem normalizedBubbleBeforeRed_eq_real (s : BubbleOrientation) (d : ℕ)
    (h : 0 ≤ s.degreeZeroDots nL + d) :
    before s d = (Pd).diag (Diagram.cast (blackDiagram RD Λ μ L (rS :: R)
      (s.beforeReflection RD (endWeight RD Λ μ L) i (s.degreeZeroDots nL + d).toNat))
      (beforeEq RD Λ μ L r R) (beforeEq RD Λ μ L r R)) := by
  rw [normalizedBubbleBeforeRed, BubbleOrientation.beforeReflectionExtended_of_nonneg _ _ _ _ h, reflectedBubble_of]

/-- Interpret a normalized real coefficient after red as a diagram with its integer dot index. -/
theorem normalizedBubbleAfterRed_eq_real (s : BubbleOrientation) (d : ℕ)
    (h : 0 ≤ s.degreeZeroDots nR + d) :
    after s d = (Pd).diag (Diagram.cast (blackDiagram RD Λ μ (L ++ [rS]) R
      (s.beforeReflection RD (endWeight RD Λ μ (L ++ [rS])) i (s.degreeZeroDots nR + d).toNat))
      (afterEq RD Λ μ L r R) (afterEq RD Λ μ L r R)) := by
  rw [normalizedBubbleAfterRed, BubbleOrientation.beforeReflectionExtended_of_nonneg _ _ _ _ h, reflectedBubble_of]

/-- At a negative left coroot coordinate, all clockwise coefficients before red are real. -/
theorem normalizedClockwiseBefore_eq_real_of_neg (d : ℕ) (hn : nL ≤ -1) :
    before .clockwise d = (Pd).diag (cwBubbleBeforeRed RD Λ μ L i r R ((-nL-1).toNat + d)) := by
  have h : 0 ≤ -nL - 1 + (d : ℤ) := by omega
  have eq := normalizedBubbleBeforeRed_eq_real RD Λ μ L i r R Q exponents P .clockwise d h
  change before .clockwise d = (Pd).diag (cwBubbleBeforeRed RD Λ μ L i r R ((-nL-1+d).toNat)) at eq
  rwa [show (-nL - 1 + d).toNat = (-nL-1).toNat + d by omega] at eq

/-- At a positive right coroot coordinate, all counterclockwise coefficients after red are real. -/
theorem normalizedCounterclockwiseAfter_eq_real_of_pos (d : ℕ) (hn : 1 ≤ nR) :
    after .counterclockwise d = (Pd).diag (ccwBubbleAfterRed RD Λ μ L i r R ((nR-1).toNat + d)) := by
  have h : 0 ≤ nR - 1 + (d : ℤ) := by omega
  have eq := normalizedBubbleAfterRed_eq_real RD Λ μ L i r R Q exponents P .counterclockwise d h
  change after .counterclockwise d = (Pd).diag (ccwBubbleAfterRed RD Λ μ L i r R ((nR-1+d).toNat)) at eq
  rwa [show (nR - 1 + d).toNat = (nR-1).toNat + d by omega] at eq

private theorem clockwiseDownLeg_cast (u v : List (DoubleStrand I ℓ))
    (e : obj RD Λ μ (u ++ blackWord [] ++ v) = obj RD Λ μ initial) (m : ℕ) :
    (Pd).diag (Diagram.cast (blackDiagram RD Λ μ u v (clockwiseDownLeg RD (endWeight RD Λ μ u) i m)) e e) =
      (Pd).diag (Diagram.cast (blackDiagram RD Λ μ u v (ccwReal RD (endWeight RD Λ μ u) i m)) e e) := by
  classical
  rw [← reflectedBubble_of, ← reflectedBubble_of]
  exact reflectedBubble_preserves RD Λ μ L r R Q exponents P u v e _ _ (lin_clockwiseDownLeg RD _ i m)

/-- KL cyclicity gives the real clockwise slide in the presentation with reflected black relations. -/
theorem cwBubble_slide_of_blackKL (m : ℕ) :
    (Pd).diag (cwBubbleAfterRed RD Λ μ L i r R m) =
      (Pd).diag (cwBubbleBeforeRed RD Λ μ L i r R (m + exponents r i)) := by
  have left (a : ℕ) : (Pd).diag (clockwiseBubbleBeforeRed RD Λ μ L i r R a) =
      (Pd).diag (cwBubbleBeforeRed RD Λ μ L i r R a) := by
    refine Eq.trans ?_ (clockwiseDownLeg_cast RD Λ μ L i r R Q exponents P L (rS :: R) (beforeEq ..) a)
    congr 1
    apply Diagram.ext
    rw [layers_clockwiseBubbleBeforeRed, Diagram.layers_cast, layers_clockwiseDownLeg]
  have right (a : ℕ) : (Pd).diag (clockwiseBubbleAfterRed RD Λ μ L i r R a) =
      (Pd).diag (cwBubbleAfterRed RD Λ μ L i r R a) := by
    refine Eq.trans ?_ (clockwiseDownLeg_cast RD Λ μ L i r R Q exponents P (L ++ [rS]) R (afterEq ..) a)
    congr 1
    apply Diagram.ext
    rw [layers_clockwiseBubbleAfterRed, Diagram.layers_cast, layers_clockwiseDownLeg]
  rw [← right, ← left]
  exact clockwiseBubble_slide RD Λ μ L i r R Q exponents (Pb) m

/-- Webster v2, Lemma 4.28. The clockwise slide preserves normalized degree
when its dot index on the right is nonnegative. -/
theorem normalizedClockwise_slide_of_real (d : ℕ) (hδ : nR = nL + (exponents r i : ℤ))
    (h : 0 ≤ -nR - 1 + (d : ℤ)) :
    before .clockwise d = after .clockwise d := by
  have hL : 0 ≤ -nL - 1 + (d : ℤ) := by omega
  rw [normalizedBubbleBeforeRed_eq_real RD Λ μ L i r R Q exponents P .clockwise d hL,
    normalizedBubbleAfterRed_eq_real RD Λ μ L i r R Q exponents P .clockwise d h]
  change (Pd).diag (cwBubbleBeforeRed RD Λ μ L i r R ((-nL-1+d).toNat)) =
    (Pd).diag (cwBubbleAfterRed RD Λ μ L i r R ((-nR-1+d).toNat))
  rw [cwBubble_slide_of_blackKL, show (-nL-1+d).toNat = (-nR-1+d).toNat + exponents r i by omega]

/-- Webster v2, Lemma 4.28. The counterclockwise slide preserves normalized degree
when its dot index on the left is nonnegative. -/
theorem normalizedCounterclockwise_slide_of_real (d : ℕ) (hδ : nR = nL + (exponents r i : ℤ))
    (h : 0 ≤ nL - 1 + (d : ℤ)) :
    before .counterclockwise d = after .counterclockwise d := by
  have hR : 0 ≤ nR - 1 + (d : ℤ) := by omega
  rw [normalizedBubbleBeforeRed_eq_real RD Λ μ L i r R Q exponents P .counterclockwise d h,
    normalizedBubbleAfterRed_eq_real RD Λ μ L i r R Q exponents P .counterclockwise d hR]
  change (Pd).diag (ccwBubbleBeforeRed RD Λ μ L i r R (nL-1+d).toNat) =
    (Pd).diag (ccwBubbleAfterRed RD Λ μ L i r R (nR-1+d).toNat)
  rw [ccwBubble_slide RD Λ μ L i r R Q exponents (Pb),
    show (nR-1+d).toNat = (nL-1+d).toNat + exponents r i by omega]

end Categorification.Stendhal.DoubleDiagram
