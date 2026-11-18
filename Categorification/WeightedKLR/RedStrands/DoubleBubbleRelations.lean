/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleMixedRelations

/-!
# Webster's bubble relations in signed contexts

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
§2.2, Definition 2.4, (2.2a)–(2.2b), p. 9, as included by §4.5, Definition 4.24.
Vertical reflection exchanges the clockwise and counterclockwise KL III
bubbles and moves their base weight to the left. For coroot coordinate `n`
of that region, the clockwise and counterclockwise thresholds for the number
of dots are `-n - 1` and `n - 1`.

The printed (2.2a) labels the bubbles `-n - 1 - j` and `n - 1 - j` and gives
zero for `j < 0`, which is positive degree for these labels. We use the
preceding prose, with vanishing in negative degree and scalar one in degree
zero. In the printed indices this reverses the strict vanishing inequality
to `j > 0`, as in arXiv:1309.3796v3, (2.3a), p. 9. The printed (2.2b) has
upper bound `j + n + 1` and lower bound `-n - 1`, giving an empty sum with
right-hand side one at `n = j = -2`. The same upper bound appears in v3, (2.3b).
For the inverse-series identity the upper bound is `j - n + 1`, where the
second bubble has degree zero. With this correction, `d = j + 2` and
`a = k + n + 1` give the degree indices `a` and `d - a`. The fake bubbles
use the KL III inverse recursion, and the stacked product represents the
pair of disjoint bubbles by interchange.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
    (RD : WeightDatum C X Y) {ℓ : ℕ} (Λ : Fin ℓ → X)

/-- The orientation of the bubble as drawn in a double Stendhal diagram. -/
inductive BubbleOrientation
  | clockwise
  | counterclockwise

/-- The number of dots of a degree-zero bubble, possibly a fake bubble. -/
def BubbleOrientation.degreeZeroDots : BubbleOrientation → ℤ → ℤ
  | .clockwise, n => -n - 1
  | .counterclockwise, n => n - 1

/-- The cup letter on the physical left of a bubble. -/
def BubbleOrientation.cupLetter (s : BubbleOrientation) (i : I) : Letter I :=
  match s with
  | .clockwise => up i
  | .counterclockwise => dn i

/-- The raw KL III bubble whose vertical reflection has orientation `s`. -/
def BubbleOrientation.beforeReflection (s : BubbleOrientation) (η : X) (i : I) (m : ℕ) :
    ob RD η [] ⟶ ob RD η [] :=
  match s with
  | .clockwise => ccwReal RD η i m
  | .counterclockwise => cwReal RD η i m

/-- The reflected bubble has the indicated cup, dots on the left leg and the matching
cap. The original right region is the physical left region of the bubble. -/
theorem realBubble_layers (μ : X) (L R : List (DoubleStrand I ℓ))
    (s : BubbleOrientation) (i : I) (m : ℕ) :
    Diagram.layers (blackDiagram RD Λ μ L R
      (s.beforeReflection RD (endWeight RD Λ μ L) i m)) =
      [layer RD Λ μ L (.black (.cup (s.cupLetter i))) R] ++
      List.replicate m (layer RD Λ μ L (.black (.dot (s.cupLetter i)))
        (.inl (s.cupLetter i).dual :: R)) ++
      [layer RD Λ μ L (.black (.cap (s.cupLetter i).dual)) R] := by
  cases s <;>
    simp [BubbleOrientation.beforeReflection, BubbleOrientation.cupLetter, ccwReal, cwReal,
      layers_blackDiagram_mkD, blackWord, List.map_append, List.map_replicate]

variable (k : Type w) [CommRing k]

/-- The real or fake KL III bubble whose reflection has orientation `s`. -/
def BubbleOrientation.beforeReflectionExtended (s : BubbleOrientation) (η : X) (i : I)
    (m : ℤ) : LEnd RD k (ob RD η []) :=
  match s with
  | .clockwise => ccwL RD k η i m
  | .counterclockwise => cwL RD k η i m

/-- The corrected real bubble conditions (2.2a) and the inversion relation
(2.2b), at the region determined by the outer left weight and the prefix. -/
inductive BubbleRelation
  | degree (μ : X) (L R : List (DoubleStrand I ℓ)) (s : BubbleOrientation) (i : I) (m : ℕ)
      (hm : (m : ℤ) ≤ s.degreeZeroDots (ip RD i (endWeight RD Λ μ L)))
  | inverse (μ : X) (L R : List (DoubleStrand I ℓ)) (i : I) (d : ℕ)

private abbrev bubbleContext (μ : X) (L R : List (DoubleStrand I ℓ)) : Obj (signature RD Λ) :=
  obj RD Λ μ (L ++ blackWord [] ++ R)

private def BubbleRelation.boundary : BubbleRelation RD Λ → Obj (signature RD Λ)
  | .degree μ L R .. | .inverse μ L R .. => bubbleContext RD Λ μ L R

private def bubbleInverse (η : X) (i : I) (d : ℕ) : LEnd RD k (ob RD η []) :=
  ∑ a ∈ Finset.range (d + 1),
    ccwL RD k η i (-ip RD i η - 1 + a) ≫ cwL RD k η i (ip RD i η - 1 + ((d : ℤ) - a))

private def bubbleRelation (a : BubbleRelation RD Λ) :
    LinDiagram k (a.boundary RD Λ) (a.boundary RD Λ) :=
  match a with
  | .degree μ L R s i m _ =>
    let η := endWeight RD Λ μ L
    blackLinear RD Λ k μ L R (LinDiagram.of (s.beforeReflection RD η i m) -
      if (m : ℤ) = s.degreeZeroDots (ip RD i η) then LinDiagram.of (𝟙 _) else 0)
  | .inverse μ L R i d =>
    let η := endWeight RD Λ μ L
    blackLinear RD Λ k μ L R (bubbleInverse RD k η i d -
      if d = 0 then (1 : LEnd RD k (ob RD η [])) else 0)

/-- Adjoin the bubble relations of Webster, arXiv:1309.3796v2, §2.2,
to a presentation on the double Stendhal signature. -/
def addBubbleRelations (P : Presentation.{w, max u v} (signature RD Λ) k) :
    Presentation.{w, max u v} (signature RD Λ) k :=
  P.addRels _ (BubbleRelation.boundary RD Λ) (BubbleRelation.boundary RD Λ)
    (bubbleRelation RD Λ k)

variable {k} (P : Presentation.{w, max u v} (signature RD Λ) k)

local notation "Q" => addBubbleRelations RD Λ k P
local notation "B" => blackMorphism RD Λ Q

private theorem bubble_comp (μ : X) (L R : List (DoubleStrand I ℓ))
    (f g : LEnd RD k (ob RD (endWeight RD Λ μ L) [])) :
    B μ L R (f ≫ g) = B μ L R f ≫ B μ L R g := by
  change (Q).lin (blackLinear RD Λ k μ L R (f ≫ g)) = _
  rw [blackLinear_comp, Presentation.lin_comp]
  rfl

private theorem bubble_id (μ : X) (L R : List (DoubleStrand I ℓ)) :
    B μ L R (LinDiagram.of (𝟙 (ob RD (endWeight RD Λ μ L) []))) =
      𝟙 ((Q).obj (bubbleContext RD Λ μ L R)) := by
  change (Q).lin (blackLinear RD Λ k μ L R (LinDiagram.of (𝟙 _))) = _
  rw [blackLinear_of, Presentation.lin_of, blackDiagram_id, Presentation.diag_id]

/-- A real bubble of negative degree vanishes, and a real bubble of degree zero
equals the identity. This is the prose formulation of (2.2a) in Webster,
arXiv:1309.3796v2, §2.2, Definition 2.4. -/
theorem realBubble_eq_of_le (μ : X) (L R : List (DoubleStrand I ℓ)) (s : BubbleOrientation)
    (i : I) (m : ℕ) (hm : (m : ℤ) ≤ s.degreeZeroDots (ip RD i (endWeight RD Λ μ L))) :
    let η := endWeight RD Λ μ L
    B μ L R (LinDiagram.of (s.beforeReflection RD η i m)) =
      if (m : ℤ) = s.degreeZeroDots (ip RD i η) then 𝟙 _ else 0 := by
  let η := endWeight RD Λ μ L
  have h := (Q).lin_rel_self (.inr (.degree μ L R s i m hm))
  change B μ L R (LinDiagram.of (s.beforeReflection RD η i m) -
    if (m : ℤ) = s.degreeZeroDots (ip RD i η) then LinDiagram.of (𝟙 _) else 0) = 0 at h
  rw [map_sub, sub_eq_zero] at h
  simpa only [apply_ite, bubble_id, map_zero] using h

/-- The corrected normalization in (2.2a) also holds for fake bubbles
defined by the inverse recursion in Webster, arXiv:1309.3796v2, §2.2. -/
theorem bubble_eq_of_le (μ : X) (L R : List (DoubleStrand I ℓ)) (s : BubbleOrientation)
    (i : I) (m : ℤ) (h : m ≤ s.degreeZeroDots (ip RD i (endWeight RD Λ μ L))) :
    let η := endWeight RD Λ μ L
    B μ L R (s.beforeReflectionExtended RD k η i m) =
      if m = s.degreeZeroDots (ip RD i η) then 𝟙 _ else 0 := by
  let η := endWeight RD Λ μ L
  let n := ip RD i η
  change B μ L R (s.beforeReflectionExtended RD k η i m) =
    if m = s.degreeZeroDots n then 𝟙 _ else 0
  by_cases hm : 0 ≤ m
  · have hnat := Int.toNat_of_nonneg hm
    have he := realBubble_eq_of_le RD Λ P μ L R s i m.toNat (by rwa [hnat])
    cases s <;> simpa [η, n, BubbleOrientation.beforeReflectionExtended,
      BubbleOrientation.beforeReflection, ccwL, cwL, hm, hnat] using he
  · have inv_eq (c : ℕ → LEnd RD k (ob RD η [])) (e : ℤ)
        (he : e = m - s.degreeZeroDots n) :
        (if 0 ≤ e then grassInv c e.toNat else 0) =
          if m = s.degreeZeroDots n then 1 else 0 := by
      change m ≤ s.degreeZeroDots n at h
      by_cases hm0 : m = s.degreeZeroDots n
      · have he0 : e = 0 := by omega
        simp [he0, hm0, grassInv_zero]
      · have hlt : ¬ 0 ≤ e := by omega
        simp [hlt, hm0]
    have hw : s.beforeReflectionExtended RD k η i m =
        if m = s.degreeZeroDots n then 1 else 0 := by
      cases s <;> simp only [BubbleOrientation.beforeReflectionExtended, ccwL, cwL, ite_eq_right hm]
      all_goals
        exact inv_eq _ _ (by simp only [n, BubbleOrientation.degreeZeroDots]; omega)
    rw [hw]
    have hid : B μ L R (1 : LEnd RD k (ob RD η [])) = 𝟙 _ := bubble_id RD Λ P μ L R
    by_cases hd : m = s.degreeZeroDots n
    · simp only [ite_eq_left hd, hid]
    · simp only [ite_eq_right hd, map_zero]

/-- The inverse-series form of Webster, arXiv:1309.3796v2, §2.2, (2.2b),
with the corrected upper summation bound. The orientation reversal sends the two KL III bubble families
`ccwL` and `cwL` to the physical clockwise and counterclockwise families. -/
theorem bubbleGrassmannian (μ : X) (L R : List (DoubleStrand I ℓ)) (i : I) (d : ℕ) :
    let η := endWeight RD Λ μ L
    ∑ a ∈ Finset.range (d + 1),
      B μ L R (ccwL RD k η i (-ip RD i η - 1 + a)) ≫
        B μ L R (cwL RD k η i (ip RD i η - 1 + ((d : ℤ) - a))) =
      if d = 0 then 𝟙 _ else 0 := by
  let η := endWeight RD Λ μ L
  have h := (Q).lin_rel_self (.inr (.inverse μ L R i d))
  change B μ L R (bubbleInverse RD k η i d -
    if d = 0 then (1 : LEnd RD k (ob RD η [])) else 0) = 0 at h
  rw [map_sub, sub_eq_zero] at h
  have hid : B μ L R (1 : LEnd RD k (ob RD η [])) = 𝟙 _ := bubble_id RD Λ P μ L R
  simpa only [bubbleInverse, map_sum, bubble_comp, apply_ite, hid, map_zero] using h

end Categorification.Stendhal.DoubleDiagram
