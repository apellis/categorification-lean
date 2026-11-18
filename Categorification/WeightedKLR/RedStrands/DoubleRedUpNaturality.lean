/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KLR.Basic
import Categorification.WeightedKLR.RedStrands.DoubleRedUp
import StringDiagrams.Biadjunction.PivotalExtension

/-!
# The red/upward crossing and dot slides

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
§4.5, Definition 4.24, (4.4c,d). A red strand can pass a crossing of two
upward black strands, and a dot on an upward black strand, in either direction.
-/

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe w u v

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (Λ : Fin ℓ → X)

/-- A single generator of the upward black KLR diagrams. -/
abbrev UpBlackMove (I : Type u) := KLR.Diagram.Gen I

namespace UpBlackMove

def shape : UpBlackMove I → Shape I
  | .dot i => .dot (true, i)
  | .cross i j => .cross true i j

abbrev bottom (g : UpBlackMove I) : List I := g.dom

abbrev top (g : UpBlackMove I) : List I := g.cod

end UpBlackMove

/-- The physical upward word for a list of black colours. -/
def upBlackWord (s : List I) : List (DoubleStrand I ℓ) := s.map (fun i => .inl (true, i))

private theorem upMove_bottom (g : UpBlackMove I) :
    (Move.black (ℓ := ℓ) g.shape).bottom = upBlackWord g.bottom := by cases g <;> rfl

private theorem upMove_top (g : UpBlackMove I) :
    (Move.black (ℓ := ℓ) g.shape).top = upBlackWord g.top := by cases g <;> rfl

/-- Move the red left-to-right through an entire list of upward black strands. -/
def redThroughUpWord (μ : X) (r : Fin ℓ) (u : List (DoubleStrand I ℓ)) (s : List I)
    (v : List (DoubleStrand I ℓ)) :
    obj RD Λ μ (u ++ [.inr r] ++ upBlackWord s ++ v) ⟶
      obj RD Λ μ (u ++ upBlackWord s ++ [.inr r] ++ v) :=
  match s with
  | [] => eqToHom (by simp [upBlackWord])
  | i :: t =>
    let f := moveDiagram RD Λ μ u (.redBlack r (true, i)) (upBlackWord t ++ v)
    let g := redThroughUpWord μ r (u ++ [.inl (true, i)]) t v
    Diagram.cast (b' := _) f (by simp [Move.bottom, upBlackWord, List.append_assoc])
      (by simp [Move.top, List.append_assoc]) ≫
    Diagram.cast g rfl (by simp [upBlackWord, List.append_assoc])

/-- Move the red right-to-left through an entire list of upward black strands. -/
def upWordThroughRed (μ : X) (r : Fin ℓ) (u : List (DoubleStrand I ℓ)) (s : List I)
    (v : List (DoubleStrand I ℓ)) :
    obj RD Λ μ (u ++ upBlackWord s ++ [.inr r] ++ v) ⟶
      obj RD Λ μ (u ++ [.inr r] ++ upBlackWord s ++ v) :=
  match s with
  | [] => eqToHom (by simp [upBlackWord])
  | i :: t =>
    let f := upWordThroughRed μ r (u ++ [.inl (true, i)]) t v
    let g := moveDiagram RD Λ μ u (.blackRed (true, i) r) (upBlackWord t ++ v)
    Diagram.cast f (by simp [upBlackWord, List.append_assoc]) rfl ≫
    Diagram.cast g (by simp [Move.bottom, List.append_assoc])
      (by simp [Move.top, upBlackWord, List.append_assoc])

/-- A black upward dot or crossing in the prescribed signed context. -/
def upBlackMoveDiagram (μ : X) (u : List (DoubleStrand I ℓ)) (g : UpBlackMove I)
    (v : List (DoubleStrand I ℓ)) :
    obj RD Λ μ (u ++ upBlackWord g.bottom ++ v) ⟶
      obj RD Λ μ (u ++ upBlackWord g.top ++ v) :=
  Diagram.cast (moveDiagram RD Λ μ u (.black g.shape) v)
    (by rw [upMove_bottom]) (by rw [upMove_top])

/-- The sides of (4.4c,d) with the red initially on the left. -/
def redUpSlide (μ : X) (u : List (DoubleStrand I ℓ)) (r : Fin ℓ) (g : UpBlackMove I)
    (v : List (DoubleStrand I ℓ)) (moveFirst : Bool) :
    obj RD Λ μ (u ++ [.inr r] ++ upBlackWord g.bottom ++ v) ⟶
      obj RD Λ μ (u ++ upBlackWord g.top ++ [.inr r] ++ v) :=
  if moveFirst then
    redThroughUpWord RD Λ μ r u g.bottom v ≫
      Diagram.cast (upBlackMoveDiagram RD Λ μ u g (.inr r :: v))
        (by simp [List.append_assoc]) (by simp [List.append_assoc])
  else
    upBlackMoveDiagram RD Λ μ (u ++ [.inr r]) g v ≫ redThroughUpWord RD Λ μ r u g.top v

/-- The vertical mirrors of (4.4c,d), with red initially on the right. -/
def redUpSlideMirror (μ : X) (u : List (DoubleStrand I ℓ)) (r : Fin ℓ) (g : UpBlackMove I)
    (v : List (DoubleStrand I ℓ)) (moveFirst : Bool) :
    obj RD Λ μ (u ++ upBlackWord g.bottom ++ [.inr r] ++ v) ⟶
      obj RD Λ μ (u ++ [.inr r] ++ upBlackWord g.top ++ v) :=
  if moveFirst then upWordThroughRed RD Λ μ r u g.bottom v ≫ upBlackMoveDiagram RD Λ μ (u ++ [.inr r]) g v
  else
    Diagram.cast (upBlackMoveDiagram RD Λ μ u g (.inr r :: v))
      (by simp [List.append_assoc]) (by simp [List.append_assoc]) ≫ upWordThroughRed RD Λ μ r u g.top v

variable {k : Type w} [CommRing k] (P : Presentation.{w, max u v} (signature RD Λ) k)

/-- The two displayed slides of Webster (4.4c,d) and both of their vertical mirrors,
at every weight and in every signed context. -/
def addRedUpSlideRelations : Presentation.{w, max u v} (signature RD Λ) k :=
  P.addRels (X × List (DoubleStrand I ℓ) × Fin ℓ × UpBlackMove I × List (DoubleStrand I ℓ) × Bool)
    (fun ⟨μ, u, r, g, v, mirror⟩ => obj RD Λ μ (if mirror then u ++ upBlackWord g.bottom ++ [.inr r] ++ v
      else u ++ [.inr r] ++ upBlackWord g.bottom ++ v))
    (fun ⟨μ, u, r, g, v, mirror⟩ => obj RD Λ μ (if mirror then u ++ [.inr r] ++ upBlackWord g.top ++ v
      else u ++ upBlackWord g.top ++ [.inr r] ++ v))
    (fun ⟨μ, u, r, g, v, mirror⟩ => by
      cases mirror
      · exact LinDiagram.of (redUpSlide RD Λ μ u r g v false) - LinDiagram.of (redUpSlide RD Λ μ u r g v true)
      · exact LinDiagram.of (redUpSlideMirror RD Λ μ u r g v false) - LinDiagram.of (redUpSlideMirror RD Λ μ u r g v true))

/-- Moving a red from left to right commutes with an upward dot or crossing, (4.4c,d). -/
theorem redUp_slide (μ : X) (u : List (DoubleStrand I ℓ)) (r : Fin ℓ) (g : UpBlackMove I)
    (v : List (DoubleStrand I ℓ)) :
    (addRedUpSlideRelations RD Λ P).diag (redUpSlide RD Λ μ u r g v false) =
    (addRedUpSlideRelations RD Λ P).diag (redUpSlide RD Λ μ u r g v true) :=
  (addRedUpSlideRelations RD Λ P).diag_eq_of_rel (.inr ⟨μ, u, r, g, v, false⟩) rfl

/-- Moving a red from right to left commutes with an upward dot or crossing, by the
vertical mirrors in Definition 4.24. -/
theorem redUp_slide_mirror (μ : X) (u : List (DoubleStrand I ℓ)) (r : Fin ℓ) (g : UpBlackMove I)
    (v : List (DoubleStrand I ℓ)) :
    (addRedUpSlideRelations RD Λ P).diag (redUpSlideMirror RD Λ μ u r g v false) =
    (addRedUpSlideRelations RD Λ P).diag (redUpSlideMirror RD Λ μ u r g v true) :=
  (addRedUpSlideRelations RD Λ P).diag_eq_of_rel (.inr ⟨μ, u, r, g, v, true⟩) rfl

end Categorification.Stendhal.DoubleDiagram
