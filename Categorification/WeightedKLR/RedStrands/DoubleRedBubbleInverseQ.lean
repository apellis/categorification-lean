/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleRedBraidBubblesQ
import Categorification.Diagrams.KL3.BubbleSlidesAll

/-!
# Normalized inverse bubble series on either side of red

Webster, arXiv:1309.3796v2, §4.5, Lemma 4.28. In the reflected presentation,
Khovanov–Lauda III, arXiv:0807.3250v1, Definition 3.1, equation
`eq_infinite_Grass` gives the normalized series in either region adjacent
to the red strand. The order of multiplication in the endomorphism ring
is accounted for by the commutation of black bubbles in a single region.

This is the version of `DoubleRedBubbleInverse` in which the black strands carry the relations of
Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3, Definition 1.1, `r = 1`; `CLQ.pres RD k sc`) instead
of the KL III relations. Each declaration carries the suffix `Q`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe u v w
variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) {ℓ : ℕ} (Λ : Fin ℓ → X) {k : Type w} [CommRing k] (sc : KL3.Diagram.CL.CLScalars C k)
  (μ : X) (L : List (DoubleStrand I ℓ)) (i : I) (r : Fin ℓ) (R : List (DoubleStrand I ℓ))
  (Q : I → I → MvPolynomial (Fin 2) k) (exponents : Fin ℓ → I →₀ ℕ)
  (P : Presentation.{w, max u v} (signature RD Λ) k)

local notation "red" => (Sum.inr r : DoubleStrand I ℓ)
local notation "Pb" => addBlackKLRelationsQ RD Λ sc P
local notation "Pcup" => addRedCupRelations RD Λ (Pb)
local notation "Pcap" => addRedCapRelations RD Λ (Pcup)
local notation "Pup" => addRedUpRelations RD Λ k (Pcap)
local notation "Pd" => addDownRelations RD Λ (affineCoverQ Q exponents) (Pup)
local notation "K" => CLQ.pres RD k sc

private abbrev rawNormalized (η : X) (s : BubbleOrientation) (d : ℕ) :
    LEnd RD k (ob RD η []) :=
  s.beforeReflectionExtended RD k η i (s.degreeZeroDots (ip RD i η) + d)

private theorem rawNormalized_zeroQ (η : X) (s : BubbleOrientation) :
    (K).lin (rawNormalized RD i η s 0) = (K).lin (1 : LEnd RD k (ob RD η [])) := by
  cases s
  · exact (by simpa [rawNormalized, BubbleOrientation.beforeReflectionExtended,
        BubbleOrientation.degreeZeroDots] using CLQ.ccwU_deg0 RD k sc η i)
  · exact (by simpa [rawNormalized, BubbleOrientation.beforeReflectionExtended,
        BubbleOrientation.degreeZeroDots] using CLQ.cwU_deg0 RD k sc η i)

private theorem rawNormalized_sconvQ (η : X) (d : ℕ) :
    (K).lin (sconv (rawNormalized RD i η .clockwise)
      (rawNormalized RD i η .counterclockwise) d : LEnd RD k (ob RD η [])) =
      (K).lin (if d = 0 then (1 : LEnd RD k (ob RD η [])) else 0) := by
  change ((K).linFunctor.mapLinearMap k) (∑ a ∈ Finset.range (d + 1),
      rawNormalized RD i η .counterclockwise (d - a) ≫ rawNormalized RD i η .clockwise a) = _
  rw [map_sum]
  calc
    _ = ∑ a ∈ Finset.range (d + 1),
        NF.ccwU (CLQ.pres RD k sc) η i (-ip RD i η - 1 + a) ≫ NF.cwU (CLQ.pres RD k sc) η i (ip RD i η - 1 + ((d : ℤ) - a)) := by
      apply Finset.sum_congr rfl
      intro a ha
      have hle : a ≤ d := by simpa using (Finset.mem_range.mp ha : a < d + 1)
      change (K).lin (cwL RD k η i (ip RD i η - 1 + ((d - a : ℕ) : ℤ)) ≫
          ccwL RD k η i (-ip RD i η - 1 + a)) = _
      rw [Presentation.lin_comp, CLQ.endEmpty_comm, Nat.cast_sub hle]
    _ = _ := by
      rw [CLQ.grassmannian_all]
      split_ifs with h
      · exact ((K).lin_id _).symm
      · exact ((K).lin_zero).symm

section Context

variable (u v : List (DoubleStrand I ℓ))
  (e : obj RD Λ μ (u ++ blackWord [] ++ v) = obj RD Λ μ (L ++ [Sum.inr r] ++ R))

local notation "η" => endWeight RD Λ μ u
local notation "F" => reflectedBubbleQ RD Λ sc μ L r R Q exponents P u v e

private theorem reflectedBubble_mulQ (f g : LEnd RD k (ob RD η [])) :
    (F) (f * g) = (F) f * (F) g := by
  change (Pd).castHom e e ((Pd).lin (blackLinear RD Λ k μ u v (g ≫ f))) =
    (Pd).castHom e e ((Pd).lin (blackLinear RD Λ k μ u v g)) ≫
      (Pd).castHom e e ((Pd).lin (blackLinear RD Λ k μ u v f))
  rw [blackLinear_comp, Presentation.lin_comp, Presentation.castHom_comp]

private theorem reflectedBubble_normalized_zeroQ (s : BubbleOrientation) :
    (F) (rawNormalized RD i η s 0) = 1 :=
  (reflectedBubble_preservesQ RD Λ sc μ L r R Q exponents P u v e _ 1
    (rawNormalized_zeroQ RD sc i η s)).trans
    (reflectedBubble_oneQ RD Λ sc μ L r R Q exponents P u v e)

private theorem reflectedBubble_normalized_sconvQ (d : ℕ) :
    sconv (fun a => (F) (rawNormalized RD i η .clockwise a))
      (fun b => (F) (rawNormalized RD i η .counterclockwise b)) d =
      if d = 0 then 1 else 0 := by
  calc
    _ = (F) (sconv (rawNormalized RD i η .clockwise) (rawNormalized RD i η .counterclockwise) d) := by
      rw [sconv, sconv, map_sum]
      exact Finset.sum_congr rfl fun a _ => (reflectedBubble_mulQ RD Λ sc μ L r R Q exponents P u v e _ _).symm
    _ = (F) (if d = 0 then (1 : LEnd RD k (ob RD η [])) else 0) :=
      reflectedBubble_preservesQ RD Λ sc μ L r R Q exponents P u v e _ _ (rawNormalized_sconvQ RD sc i η d)
    _ = _ := by
      split_ifs
      · exact reflectedBubble_oneQ RD Λ sc μ L r R Q exponents P u v e
      · exact map_zero _

end Context

/-- Both normalized bubble series before red have constant coefficient `1`. -/
@[simp] theorem normalizedBubbleBeforeRed_zeroQ (s : BubbleOrientation) :
    normalizedBubbleBeforeRedQ RD Λ sc μ L i r R Q exponents P s 0 = 1 :=
  reflectedBubble_normalized_zeroQ RD Λ sc μ L i r R Q exponents P L (red :: R) (beforeEq RD Λ μ L r R) s

/-- Both normalized bubble series after red have constant coefficient `1`. -/
@[simp] theorem normalizedBubbleAfterRed_zeroQ (s : BubbleOrientation) :
    normalizedBubbleAfterRedQ RD Λ sc μ L i r R Q exponents P s 0 = 1 :=
  reflectedBubble_normalized_zeroQ RD Λ sc μ L i r R Q exponents P (L ++ [red]) R (afterEq RD Λ μ L r R) s

/-- The clockwise and counterclockwise series before red satisfy the
infinite Grassmannian relation in every normalized degree. -/
theorem normalizedBubbleBeforeRed_sconvQ (d : ℕ) :
    sconv (normalizedBubbleBeforeRedQ RD Λ sc μ L i r R Q exponents P .clockwise)
      (normalizedBubbleBeforeRedQ RD Λ sc μ L i r R Q exponents P .counterclockwise) d =
      if d = 0 then 1 else 0 :=
  reflectedBubble_normalized_sconvQ RD Λ sc μ L i r R Q exponents P L (red :: R) (beforeEq RD Λ μ L r R) d

/-- The clockwise and counterclockwise series after red satisfy the
infinite Grassmannian relation in every normalized degree. -/
theorem normalizedBubbleAfterRed_sconvQ (d : ℕ) :
    sconv (normalizedBubbleAfterRedQ RD Λ sc μ L i r R Q exponents P .clockwise)
      (normalizedBubbleAfterRedQ RD Λ sc μ L i r R Q exponents P .counterclockwise) d =
      if d = 0 then 1 else 0 :=
  reflectedBubble_normalized_sconvQ RD Λ sc μ L i r R Q exponents P (L ++ [red]) R (afterEq RD Λ μ L r R) d

end Categorification.Stendhal.DoubleDiagram
