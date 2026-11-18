/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleMarkedRedTransport
import Categorification.WeightedKLR.RedStrands.DoubleRedBubbleInverse
import Categorification.WeightedKLR.RedStrands.DoubleRedBubbleReal

/-! # Normalized bubble transport across a red strand

Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29.
Closing the downward black–red–black braid supplies the coefficients in
which neither orientation has a real representative on both sides.
-/
noncomputable section
namespace Categorification.Stendhal.DoubleDiagram
open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams
universe u v w
variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) {ℓ : ℕ} (Λ : Fin ℓ → X) {k : Type w} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (exponents : Fin ℓ → I →₀ ℕ)
  (P : Presentation.{w,max u v} (signature RD Λ) k)
  (μ : X) (L : List (DoubleStrand I ℓ)) (i : I) (r : Fin ℓ) (R : List (DoubleStrand I ℓ))
local notation "red" => (Sum.inr r : DoubleStrand I ℓ)
local notation "Pr" => addRedUpSlideRelations RD Λ P
local notation "Pd" => addDownRelations RD Λ (affineCoverQ Q exponents)
  (addRedUpRelations RD Λ k (addRedCapRelations RD Λ (addRedCupRelations RD Λ (addBlackKLRelations RD Λ Pr))))
local notation "before" => normalizedBubbleBeforeRed RD Λ μ L i r R Q exponents (Pr)
local notation "after" => normalizedBubbleAfterRed RD Λ μ L i r R Q exponents (Pr)
local notation "nL" => ip RD i (endWeight RD Λ μ L)
local notation "nR" => ip RD i (endWeight RD Λ μ (L ++ [red]))

private theorem mixed_normalized_coeff [DecidableEq I]
    (hδ : nR = nL + (exponents r i : ℤ)) (d : ℕ) (hd : 0 < d)
    (hl : (d : ℤ) ≤ -nL) (hr : (d : ℤ) ≤ nR)
    (bl : ∀ a, (before) .clockwise a = (Pd).diag
      (cwBubbleBeforeRed RD Λ μ L i r R ((-nL - 1).toNat + a)))
    (br : ∀ a, (after) .counterclockwise a = (Pd).diag
      (ccwBubbleAfterRed RD Λ μ L i r R ((nR - 1).toNat + a))) :
    sconv ((before) .clockwise) ((after) .counterclockwise) d = 0 := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  have h := pointedRedBraid_convolution_zero RD Λ Q exponents P μ L i r R N
    (by omega) (by omega) hδ
  simpa only [funext bl, funext br] using h

private theorem normalized_eq_of_real_slides [DecidableEq I]
    (hδ : nR = nL + (exponents r i : ℤ))
    (zL : ∀ o, (before) o 0 = 1) (zR : ∀ o, (after) o 0 = 1)
    (invL : ∀ d, sconv ((before) .clockwise) ((before) .counterclockwise) d = if d = 0 then 1 else 0)
    (invR : ∀ d, sconv ((after) .clockwise) ((after) .counterclockwise) d = if d = 0 then 1 else 0)
    (cslide : ∀ d : ℕ, 0 ≤ -nR - 1 + d → (before) .clockwise d = (after) .clockwise d)
    (uslide : ∀ d : ℕ, 0 ≤ nL - 1 + d → (before) .counterclockwise d = (after) .counterclockwise d)
    (bl : ∀ a, nL ≤ -1 → (before) .clockwise a = (Pd).diag
      (cwBubbleBeforeRed RD Λ μ L i r R ((-nL - 1).toNat + a)))
    (br : ∀ a, 1 ≤ nR → (after) .counterclockwise a = (Pd).diag
      (ccwBubbleAfterRed RD Λ μ L i r R ((nR - 1).toNat + a)))
    (o : BubbleOrientation) (d : ℕ) : (before) o d = (after) o d := by
  have hb := redBubbleCoefficients_eq_of_sign_change nL (exponents r i)
    ((before) .clockwise) ((before) .counterclockwise) ((after) .clockwise) ((after) .counterclockwise)
    (zL _) (zL _) (zR _) (zR _) invL invR (fun a h => cslide a (by rwa [hδ])) uslide
    (fun a ha hl hr => mixed_normalized_coeff RD Λ Q exponents P μ L i r R hδ a ha hl
      (by rwa [hδ]) (fun j => bl j (by omega)) (fun j => br j (by omega))) d
  cases o with
  | clockwise => exact hb.1
  | counterclockwise => exact hb.2

/-- Webster v3, Lemma 4.29, the normalized bubble slide across red. In the
reflected KL III presentation with red/up dot slides, real and fake bubbles
pass a red strand in either orientation and every degree. The red exponent
is the difference of the two coroot coordinates. -/
theorem normalizedBubble_slide (hδ : nR = nL + (exponents r i : ℤ))
    (o : BubbleOrientation) (d : ℕ) : (before) o d = (after) o d := by
  classical
  apply normalized_eq_of_real_slides RD Λ Q exponents P μ L i r R hδ
  · exact normalizedBubbleBeforeRed_zero RD Λ μ L i r R Q exponents (Pr)
  · exact normalizedBubbleAfterRed_zero RD Λ μ L i r R Q exponents (Pr)
  · exact normalizedBubbleBeforeRed_sconv RD Λ μ L i r R Q exponents (Pr)
  · exact normalizedBubbleAfterRed_sconv RD Λ μ L i r R Q exponents (Pr)
  · intro a
    exact normalizedClockwise_slide_of_real RD Λ μ L i r R Q exponents (Pr) a hδ
  · intro a
    exact normalizedCounterclockwise_slide_of_real RD Λ μ L i r R Q exponents (Pr) a hδ
  · intro a
    exact normalizedClockwiseBefore_eq_real_of_neg RD Λ μ L i r R Q exponents (Pr) a
  · intro a
    exact normalizedCounterclockwiseAfter_eq_real_of_pos RD Λ μ L i r R Q exponents (Pr) a

end Categorification.Stendhal.DoubleDiagram
