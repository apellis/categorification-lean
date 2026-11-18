/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleMixedRelations

/-!
# The black curl and opposite mixed identities in double Stendhal diagrams

Webster, arXiv:1309.3796v2, §2.2, (2.3a), (2.3b), (2.3d) and (2.4b),
and v3, (2.4a), (2.4b), (2.4d) and (2.5b), as used in §4.5,
Definition 4.24. Together with the mixed identities in
`DoubleMixedRelations`, these give the two directions of the mixed
black decomposition. The curls use the one-colour normalization
`r_i = 1`, and the unequal-colour bigon uses the directed leading unit.
-/

noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory StringDiagrams QuantumGroup QuantumGroup.UDot KL3.Diagram

universe w u v
variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
    (RD : WeightDatum C X Y) {ℓ : ℕ} (Λ : Fin ℓ → X) (k : Type w) [CommRing k]

/-- Curls on an upward strand, and mixed bigons with the upward strand on the
physical left of the downward strand. -/
inductive BlackCurlRelation (X : Type v) (I : Type u) (ℓ : ℕ)
  | left (μ : X) (L R : List (DoubleStrand I ℓ)) (i : I)
  | right (μ : X) (L R : List (DoubleStrand I ℓ)) (i : I)
  | equal (μ : X) (L R : List (DoubleStrand I ℓ)) (i : I)
  | distinct (μ : X) (L R : List (DoubleStrand I ℓ)) (i j : I) (h : i ≠ j)

private def BlackCurlRelation.boundary : BlackCurlRelation X I ℓ → Obj (signature RD Λ)
  | .left μ L R i | .right μ L R i => obj RD Λ μ (L ++ blackWord [up i] ++ R)
  | .equal μ L R i => obj RD Λ μ (L ++ blackWord [dn i, up i] ++ R)
  | .distinct μ L R i j _ => obj RD Λ μ (L ++ blackWord [dn i, up j] ++ R)

open LinDiagram in
private def blackCurlRelation (t : I → I → kˣ) :
    (x : BlackCurlRelation X I ℓ) → LinDiagram k (x.boundary RD Λ) (x.boundary RD Λ)
  | .left μ L R i =>
    let η := endWeight RD Λ μ L
    blackLinear RD Λ k μ L R (of (curlR RD i η) - curlRHS RD k i η)
  | .right μ L R i =>
    let η := endWeight RD Λ μ L
    blackLinear RD Λ k μ L R (of (curlL RD i η) - curlLHS RD k i η)
  | .equal μ L R i =>
    let η := endWeight RD Λ μ L
    blackLinear RD Λ k μ L R
      (of (𝟙 _) + of (crossr RD i i η ≫ crossl RD i i η) - decompFESum RD k i η)
  | .distinct μ L R i j _ =>
    let η := endWeight RD Λ μ L
    blackLinear RD Λ k μ L R
      (of (crossr RD j i η ≫ crossl RD j i η) - (t i j : k) • of (𝟙 _))

variable {k}

/-- Adjoin the two one-colour curl relations and the opposite mixed black
relations, in every signed context. -/
def addBlackCurlRelations (t : I → I → kˣ) (P : Presentation.{w, max u v} (signature RD Λ) k) :
    Presentation.{w, max u v} (signature RD Λ) k :=
  P.addRels _ (BlackCurlRelation.boundary RD Λ) (BlackCurlRelation.boundary RD Λ)
    (blackCurlRelation RD Λ k t)

variable (t : I → I → kˣ) (P : Presentation.{w, max u v} (signature RD Λ) k)
local notation "Q" => addBlackCurlRelations RD Λ t P
local notation "B" => blackMorphism RD Λ (Q)

private theorem blackCurl_relation_zero (x : BlackCurlRelation X I ℓ) :
    (Q).lin (blackCurlRelation RD Λ k t x) = 0 :=
  (Q).lin_rel_self (.inr x)

/-- The curl to the physical left, written as a sum of dots and bubbles. -/
theorem blackCurlLeft (μ : X) (L R : List (DoubleStrand I ℓ)) (i : I) :
    let η := endWeight RD Λ μ L
    (B) μ L R (LinDiagram.of (curlR RD i η)) = (B) μ L R (curlRHS RD k i η) := by
  let η := endWeight RD Λ μ L
  have h := blackCurl_relation_zero RD Λ t P (.left μ L R i)
  change (B) μ L R (LinDiagram.of (curlR RD i η) - curlRHS RD k i η) = 0 at h
  rwa [map_sub, sub_eq_zero] at h

/-- The curl to the physical right, written as a sum of dots and bubbles. -/
theorem blackCurlRight (μ : X) (L R : List (DoubleStrand I ℓ)) (i : I) :
    let η := endWeight RD Λ μ L
    (B) μ L R (LinDiagram.of (curlL RD i η)) = (B) μ L R (curlLHS RD k i η) := by
  let η := endWeight RD Λ μ L
  have h := blackCurl_relation_zero RD Λ t P (.right μ L R i)
  change (B) μ L R (LinDiagram.of (curlL RD i η) - curlLHS RD k i η) = 0 at h
  rwa [map_sub, sub_eq_zero] at h

/-- On a physical up/down pair of the same colour, the identity plus the
double mixed crossing equals the cap–bubble–cup sum. -/
theorem mixedBlack_opposite_eq (μ : X) (L R : List (DoubleStrand I ℓ)) (i : I) :
    let η := endWeight RD Λ μ L
    (B) μ L R (LinDiagram.of (𝟙 _) +
      LinDiagram.of (crossr RD i i η ≫ crossl RD i i η)) = (B) μ L R (decompFESum RD k i η) := by
  let η := endWeight RD Λ μ L
  have h := blackCurl_relation_zero RD Λ t P (.equal μ L R i)
  change (B) μ L R (LinDiagram.of (𝟙 _) +
    LinDiagram.of (crossr RD i i η ≫ crossl RD i i η) - decompFESum RD k i η) = 0 at h
  rwa [map_sub, sub_eq_zero] at h

/-- On a physical up/down pair of distinct colours, the double mixed crossing
equals the straight diagram times the directed leading unit. -/
theorem mixedBlack_opposite_ne (μ : X) (L R : List (DoubleStrand I ℓ)) (i j : I) (h : i ≠ j) :
    let η := endWeight RD Λ μ L
    (B) μ L R (LinDiagram.of (crossr RD j i η ≫ crossl RD j i η)) =
      (t i j : k) • (B) μ L R (LinDiagram.of (𝟙 _)) := by
  let η := endWeight RD Λ μ L
  have he := blackCurl_relation_zero RD Λ t P (.distinct μ L R i j h)
  change (B) μ L R (LinDiagram.of (crossr RD j i η ≫ crossl RD j i η) -
    (t i j : k) • LinDiagram.of (𝟙 _)) = 0 at he
  rwa [map_sub, map_smul, sub_eq_zero] at he

end Categorification.Stendhal.DoubleDiagram
