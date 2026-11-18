/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleDiagram
import StringDiagrams.Biadjunction.PivotalExtension

/-!
# The red and upward black crossings

In Webster, arXiv:1309.3796v2, §4.5, Definition 4.24, equation (4.4e)
identifies both red/upward black bigons with the corresponding straight
strands. The proof of Theorem 4.29 uses these identities when moving an
upward black strand to the left across a red strand. Its citation of
(4.4d) points to the preceding three-strand relation.

The two relations here can be adjoined to any presentation on the double
Stendhal signature. The other relations of Definition 4.24 are separate.
-/

-- Diagram boundary casts use the region-labelled signature.
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open QuantumGroup QuantumGroup.UDot StringDiagrams CategoryTheory

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
    (RD : WeightDatum C X Y) {ℓ : ℕ} (Λ : Fin ℓ → X) (k : Type w) [CommRing k]

/-- Red and upward black in the order at the bottom of a bigon in (4.4e). -/
inductive RedUpSide
  | redLeft | upLeft

private def RedUpSide.move (s : RedUpSide) (r : Fin ℓ) (i : I) : Move I ℓ :=
  match s with
  | .redLeft => .redBlack r (true, i)
  | .upLeft => .blackRed (true, i) r

private def RedUpSide.bigon (s : RedUpSide) (μ : X) (u : List (DoubleStrand I ℓ))
    (r : Fin ℓ) (i : I) (v : List (DoubleStrand I ℓ)) :
    End (obj RD Λ μ (u ++ (s.move r i).bottom ++ v)) :=
  match s with
  | .redLeft => moveDiagram RD Λ μ u (.redBlack r (true, i)) v ≫
      moveDiagram RD Λ μ u (.blackRed (true, i) r) v
  | .upLeft => moveDiagram RD Λ μ u (.blackRed (true, i) r) v ≫
      moveDiagram RD Λ μ u (.redBlack r (true, i)) v

/-- A red/upward bigon is specified by its left region, its two labels and
the order of the strands at its boundary. -/
structure RedUpRelation (X : Type v) (I : Type u) (ℓ : ℕ) where
  leftWeight : X
  red : Fin ℓ
  up : I
  side : RedUpSide

private def bareBigon (μ : X) (r : Fin ℓ) (i : I) (s : RedUpSide) :
    End (obj RD Λ μ (s.move r i).bottom) := by
  cases s with
  | redLeft => exact RedUpSide.bigon RD Λ .redLeft μ [] r i []
  | upLeft => exact RedUpSide.bigon RD Λ .upLeft μ [] r i []

/-- Adjoin the two local red/upward bigons (4.4e) to a presentation.
Their generating instances have no surrounding strands. -/
def addRedUpRelations (P : Presentation.{w, max u v} (signature RD Λ) k) :
    Presentation.{w, max u v} (signature RD Λ) k :=
  let boundary (a : RedUpRelation X I ℓ) :=
    obj RD Λ a.leftWeight (a.side.move a.red a.up).bottom
  P.addRels _ boundary boundary fun ⟨μ, r, i, s⟩ =>
    LinDiagram.of (bareBigon RD Λ μ r i s) - LinDiagram.of (𝟙 _)

variable {k} (P : Presentation.{w, max u v} (signature RD Λ) k)

private theorem redUp_bigon (s : RedUpSide) (μ : X) (u : List (DoubleStrand I ℓ))
    (r : Fin ℓ) (i : I) (v : List (DoubleStrand I ℓ)) :
    (addRedUpRelations RD Λ k P).diag (s.bigon RD Λ μ u r i v) = 𝟙 _ := by
  let t := endWeight RD Λ μ u
  let b := (s.move r i).bottom
  let tail : List (signature RD Λ).Colour := colours RD Λ (endWeight RD Λ t b) v
  have hw : (obj RD Λ t b).WhiskerOK (obj RD Λ μ u) tail :=
    ⟨colours_ok .., colours_endR .., by
      change (signature RD Λ).ok ((signature RD Λ).endR t (colours RD Λ t b)) tail
      rw [colours_endR]
      exact colours_ok ..⟩
  have hobj : (obj RD Λ t b).whisker (obj RD Λ μ u) tail =
      obj RD Λ μ (u ++ b ++ v) := by
    refine Obj.ext ?_ ?_
    · rfl
    simp [Obj.whisker, obj, colours_append, tail, t]
  let Q := addRedUpRelations RD Λ k P
  have h := Q.lin_rel_cast (.inr ⟨t, r, i, s⟩) (obj RD Λ μ u) tail hw hobj hobj
  change Q.lin (LinDiagram.cast (LinDiagram.whisker
    (LinDiagram.of (bareBigon RD Λ t r i s) - LinDiagram.of (𝟙 _)) _ _ hw) _ _) = 0 at h
  rw [LinDiagram.whisker_sub, LinDiagram.cast_sub, Presentation.lin_sub,
    sub_eq_zero] at h
  simp only [LinDiagram.whisker_of, LinDiagram.cast_of, Presentation.lin_of] at h
  refine (Q.diag_eq_of_layers_eq ?_).trans (h.trans ((Q.diag_eq_of_layers_eq ?_).trans (Q.diag_id _)))
  · cases s <;>
      simp [bareBigon, RedUpSide.bigon, RedUpSide.move, moveDiagram, layer, Layer.whisker, obj,
        colours, endWeight, t, tail, b, Move.bottom, add_comm, add_left_comm, add_assoc]
  · simp
    rfl

/-- In any word, the crossing moving the upward strand left of the red strand
is an isomorphism with the opposite crossing as inverse, by (4.4e). -/
def redUpCrossingIso (μ : X) (u : List (DoubleStrand I ℓ)) (r : Fin ℓ) (i : I)
    (v : List (DoubleStrand I ℓ)) :
    (addRedUpRelations RD Λ k P).obj (obj RD Λ μ (u ++ [.inr r, .inl (true, i)] ++ v)) ≅
      (addRedUpRelations RD Λ k P).obj (obj RD Λ μ (u ++ [.inl (true, i), .inr r] ++ v)) where
  hom := (addRedUpRelations RD Λ k P).diag (moveDiagram RD Λ μ u (.redBlack r (true, i)) v)
  inv := (addRedUpRelations RD Λ k P).diag (moveDiagram RD Λ μ u (.blackRed (true, i) r) v)
  hom_inv_id := by
    exact ((addRedUpRelations RD Λ k P).diag_comp _ _).symm.trans
      (redUp_bigon RD Λ P .redLeft μ u r i v)
  inv_hom_id := by
    exact ((addRedUpRelations RD Λ k P).diag_comp _ _).symm.trans
      (redUp_bigon RD Λ P .upLeft μ u r i v)

end Categorification.Stendhal.DoubleDiagram
