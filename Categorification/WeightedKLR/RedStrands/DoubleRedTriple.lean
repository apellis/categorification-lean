/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleRedUpNaturality
import StringDiagrams.Transport

/-!
# The triple-point switch with a middle red strand

Webster, arXiv:1309.3796v2, §4.5, Definition 4.24 and Lemma 4.28.
Compose (4.4c) with inverse red/up crossings to move a red strand through an
upward crossing when the red strand starts between the two black strands.
-/
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe w u v
variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (Λ : Fin ℓ → X)
  (μ : X) (u v : List (DoubleStrand I ℓ)) (r : Fin ℓ) (i j : I)

private abbrev E (i : I) : DoubleStrand I ℓ := .inl (true, i)
private abbrev red (r : Fin ℓ) : DoubleStrand I ℓ := .inr r
local notation "W" => fun w => obj RD Λ μ (u ++ w ++ v)

/-- A local move with two exterior signed contexts and two local contexts. -/
private def between (l : List (DoubleStrand I ℓ)) (g : Move I ℓ) (t : List (DoubleStrand I ℓ)) :
    W (l ++ g.bottom ++ t) ⟶ W (l ++ g.top ++ t) :=
  Diagram.cast (moveDiagram RD Λ μ (u ++ l) g (t ++ v))
    (by simp [List.append_assoc]) (by simp [List.append_assoc])

local notation "D" => between RD Λ μ u v

/-- Move the middle red to the left, cross the two black strands, then move red to
the middle again. -/
def middleRedViaLeft : W [E i, red r, E j] ⟶ W [E j, red r, E i] :=
  D [] (.blackRed (true, i) r) [E j] ≫ D [red r] (.black (.cross true i j)) [] ≫
    D [] (.redBlack r (true, j)) [E i]

/-- Move the middle red to the right, cross the two black strands, then return it
to the middle. -/
def middleRedViaRight : W [E i, red r, E j] ⟶ W [E j, red r, E i] :=
  D [E i] (.redBlack r (true, j)) [] ≫ D [] (.black (.cross true i j)) [red r] ≫
    D [E j] (.blackRed (true, i) r) []

/-- Layers of the route taking the middle red to the left first. -/
theorem layers_middleRedViaLeft :
    Diagram.layers (middleRedViaLeft RD Λ μ u v r i j) =
      [layer RD Λ μ u (.blackRed (true, i) r) (E j :: v),
       layer RD Λ μ (u ++ [red r]) (.black (.cross true i j)) v,
       layer RD Λ μ u (.redBlack r (true, j)) (E i :: v)] := by
  simp [middleRedViaLeft, between, moveDiagram]

/-- Layers of the route taking the middle red to the right first. -/
theorem layers_middleRedViaRight :
    Diagram.layers (middleRedViaRight RD Λ μ u v r i j) =
      [layer RD Λ μ (u ++ [E i]) (.redBlack r (true, j)) v,
       layer RD Λ μ u (.black (.cross true i j)) (red r :: v),
       layer RD Λ μ (u ++ [E j]) (.blackRed (true, i) r) v] := by
  simp [middleRedViaRight, between, moveDiagram]

variable {k : Type w} [CommRing k] (P : Presentation.{w,max u v} (signature RD Λ) k)

local notation "T" => addRedUpRelations RD Λ k (addRedUpSlideRelations RD Λ P)

private theorem up_red_bigon (l t : List (DoubleStrand I ℓ)) (i : I) :
    (T).diag (D l (.blackRed (true, i) r) t) ≫ (T).diag (D l (.redBlack r (true, i)) t) = 𝟙 _ := by
  let e := redUpCrossingIso RD Λ (addRedUpSlideRelations RD Λ P) μ (u ++ l) r i (t ++ v)
  unfold between
  rw [← Presentation.castHom_diag, ← Presentation.castHom_diag, ← Presentation.castHom_comp]
  change (T).castHom _ _ (e.inv ≫ e.hom) = _
  rw [Iso.inv_hom_id, Presentation.castHom_id]

private theorem red_up_bigon (l t : List (DoubleStrand I ℓ)) (i : I) :
    (T).diag (D l (.redBlack r (true, i)) t) ≫ (T).diag (D l (.blackRed (true, i) r) t) = 𝟙 _ := by
  let e := redUpCrossingIso RD Λ (addRedUpSlideRelations RD Λ P) μ (u ++ l) r i (t ++ v)
  unfold between
  rw [← Presentation.castHom_diag, ← Presentation.castHom_diag, ← Presentation.castHom_comp]
  change (T).castHom _ _ (e.hom ≫ e.inv) = _
  rw [Iso.hom_inv_id, Presentation.castHom_id]

private theorem outer_red_slide :
    (T).diag (D [red r] (.black (.cross true i j)) []) ≫
      (T).diag (D [] (.redBlack r (true, j)) [E i]) ≫
      (T).diag (D [E j] (.redBlack r (true, i)) []) =
    (T).diag (D [] (.redBlack r (true, i)) [E j]) ≫
      (T).diag (D [E i] (.redBlack r (true, j)) []) ≫
      (T).diag (D [] (.black (.cross true i j)) [red r]) := by
  have h : (T).diag (redUpSlide RD Λ μ u r (.cross i j) v false) =
      (T).diag (redUpSlide RD Λ μ u r (.cross i j) v true) :=
    (T).diag_eq_of_rel (.inl (.inr ⟨μ, u, r, .cross i j, v, false⟩)) rfl
  have hs : obj RD Λ μ (u ++ [.inr r] ++ upBlackWord [i,j] ++ v) = W [red r, E i, E j] := by
    simp [upBlackWord, red, E, List.append_assoc]
  have ht : obj RD Λ μ (u ++ upBlackWord [j,i] ++ [.inr r] ++ v) = W [E j, E i, red r] := by
    simp [upBlackWord, red, E, List.append_assoc]
  have h' := congrArg ((T).castHom hs ht) h
  simp only [Presentation.castHom_diag] at h'
  repeat rw [← (T).diag_comp]
  refine ((T).diag_eq_of_layers_eq ?_).trans (h'.trans ((T).diag_eq_of_layers_eq ?_))
  all_goals simp [between, redUpSlide, upBlackMoveDiagram, upBlackWord, redThroughUpWord,
    UpBlackMove.shape, moveDiagram]

private theorem cancel_outer_crossings {𝒜 : Type*} [Category 𝒜] {A₀ A₁ A₂ B₀ B₁ B₂ : 𝒜}
    {a : A₀ ⟶ A₁} {a' : A₁ ⟶ A₀} {b : A₁ ⟶ A₂} {c : B₀ ⟶ B₁} {d : B₁ ⟶ B₂}
    {d' : B₂ ⟶ B₁} {x : A₀ ⟶ B₀} {y : A₂ ⟶ B₂} (h : x ≫ c ≫ d = a ≫ b ≫ y)
    (ha : a' ≫ a = 𝟙 A₁) (hd : d ≫ d' = 𝟙 B₁) :
    a' ≫ x ≫ c = b ≫ y ≫ d' := by
  simpa only [Category.assoc, hd, Category.comp_id, reassoc_of% ha, Category.id_comp] using
    congrArg (fun f => a' ≫ f ≫ d') h

/-- In Webster's crossing induction (arXiv:1309.3796v2, §4.5, Lemma 4.28), a
red strand between two upward strands can move through their crossing. This middle
case follows from the outer case (4.4c) and the two red/up bigons (4.4e). -/
theorem middleRed_triplePoint :
    (T).diag (middleRedViaLeft RD Λ μ u v r i j) =
      (T).diag (middleRedViaRight RD Λ μ u v r i j) := by
  rw [middleRedViaLeft, middleRedViaRight]
  simp only [Presentation.diag_comp]
  exact cancel_outer_crossings (outer_red_slide RD Λ μ u v r i j P)
    (up_red_bigon RD Λ μ u v r P [] [E j] i) (red_up_bigon RD Λ μ u v r P [E j] [] i)

end Categorification.Stendhal.DoubleDiagram
