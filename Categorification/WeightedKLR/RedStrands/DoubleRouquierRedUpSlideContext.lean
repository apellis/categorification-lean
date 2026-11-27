/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleRouquierRedUpSlide
import Categorification.WeightedKLR.RedStrands.DoubleRouquierRedContext

/-!
# The red/upward slide relations in every context

Webster, arXiv:1309.3796v3, (4.4c,d), in the proof of Theorem 4.25. The slides of a red strand
past an upward dot or crossing, proved without context in `DoubleRouquierRedUpSlide`, hold in
every signed context: each side of a relation of `addRedUpSlideRelations` is the whiskering of
the bare relation.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory CategoryTheory.Bicategory QuantumGroup QuantumGroup.UDot KL3.Diagram
  StringDiagrams TwoRep Diagrams.BicatInterp

universe u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {ℓ : ℕ} {Λ : Fin ℓ → X}

section Whisker

/-- A side of (4.4c,d) in context is the whiskering of the bare side. -/
theorem redUpSlide_eq_whisker (μ : X) (u : List (DoubleStrand I ℓ)) (r : Fin ℓ)
    (g : UpBlackMove I) (v : List (DoubleStrand I ℓ)) (b : Bool) {x : X}
    (hx : x = endWeight RD Λ (endWeight RD Λ μ u) ([] ++ [.inr r] ++ upBlackWord g.bottom ++ []))
    (hw : (obj RD Λ (endWeight RD Λ μ u) ([] ++ [.inr r] ++ upBlackWord g.bottom ++ [])).WhiskerOK
      (obj RD Λ μ u) (colours RD Λ x v)) (e₁ e₂) :
    redUpSlide RD Λ μ u r g v b = Diagram.cast (Diagram.whisker
      (redUpSlide RD Λ (endWeight RD Λ μ u) [] r g [] b) (obj RD Λ μ u) _ hw) e₁ e₂ := by
  subst hx
  apply Diagram.ext
  rw [Diagram.layers_cast, Diagram.layers_whisker]
  cases g <;> cases b <;>
    simp (disch := double_regions) [redUpSlide, upBlackMoveDiagram, redThroughUpWord,
      moveDiagram, upBlackWord, UpBlackMove.shape, layer_whisker (RD := RD) (Λ := Λ)]

/-- A mirrored side of (4.4c,d) in context is the whiskering of the bare side. -/
theorem redUpSlideMirror_eq_whisker (μ : X) (u : List (DoubleStrand I ℓ)) (r : Fin ℓ)
    (g : UpBlackMove I) (v : List (DoubleStrand I ℓ)) (b : Bool) {x : X}
    (hx : x = endWeight RD Λ (endWeight RD Λ μ u) ([] ++ upBlackWord g.bottom ++ [.inr r] ++ []))
    (hw : (obj RD Λ (endWeight RD Λ μ u) ([] ++ upBlackWord g.bottom ++ [.inr r] ++ [])).WhiskerOK
      (obj RD Λ μ u) (colours RD Λ x v)) (e₁ e₂) :
    redUpSlideMirror RD Λ μ u r g v b = Diagram.cast (Diagram.whisker
      (redUpSlideMirror RD Λ (endWeight RD Λ μ u) [] r g [] b) (obj RD Λ μ u) _ hw) e₁ e₂ := by
  subst hx
  apply Diagram.ext
  rw [Diagram.layers_cast, Diagram.layers_whisker]
  cases g <;> cases b <;>
    simp (disch := double_regions) [redUpSlideMirror, upBlackMoveDiagram, upWordThroughRed,
      moveDiagram, upBlackWord, UpBlackMove.shape, layer_whisker (RD := RD) (Λ := Λ)] <;> rfl



end Whisker

section Relations

variable {B : Type*} [Bicategory B] [∀ a b : B, Preadditive (a ⟶ b)] [AdditiveWhiskering B]
  {k : Type*} [CommRing k] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (g : b ⟶ c), (postcomp a g).Linear k]
  (S : RouqFamily (B := B) RD)
  (red : (r : Fin ℓ) → {x y : X} → x + Λ r = y → (S.obj y ⟶ S.obj x))
  (upIso : (r : Fin ℓ) → (i : I) → {μ μ₁ μ₂ μ₃ : X} → (h₁ : μ + RD.iX i = μ₁) →
    (h₂ : μ + Λ r = μ₂) → (h₃ : μ₁ + Λ r = μ₃) → (h₄ : μ₂ + RD.iX i = μ₃) →
    (S.F i h₄ ≫ red r h₂ ≅ red r h₃ ≫ S.F i h₁))
  (Sc : CL.CLScalars C k)

omit [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (g : b ⟶ c), (postcomp a g).Linear k] in
/-- The bare relations of `addRedUpSlideRelations`, at any starting weight. -/
theorem genImg_redUpSlide_bare (hdot : UpIsoDotNatural S red upIso)
    (hcross : UpIsoCrossNatural S red upIso Sc) (m : X) (r : Fin ℓ) (g : UpBlackMove I)
    {s t : X} (ha : Cond s t (obj RD Λ m ([] ++ [.inr r] ++ upBlackWord g.bottom ++ [])))
    (hb : Cond s t (obj RD Λ m ([] ++ upBlackWord g.top ++ [.inr r] ++ []))) :
    admissibleMap (k := k) (genImg S red upIso Sc) ha hb
      (LinDiagram.of (redUpSlide RD Λ m [] r g [] false) -
        LinDiagram.of (redUpSlide RD Λ m [] r g [] true)) = 0 := by
  obtain rfl : m = s := ha.2.2
  rw [map_sub, sub_eq_zero]
  cases g with
  | dot i =>
    exact genImg_redUpSlide_dot (S := S) (red := red) (upIso := upIso) (Sc := Sc)
      hdot i r ha hb
  | cross i j =>
    exact genImg_redUpSlide_cross (S := S) (red := red) (upIso := upIso) (Sc := Sc)
      hcross i j r ha hb

omit [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (g : b ⟶ c), (postcomp a g).Linear k] in
/-- The bare mirrored relations of `addRedUpSlideRelations`, at any starting weight. -/
theorem genImg_redUpSlideMirror_bare (hdot : UpIsoDotNatural S red upIso)
    (hcross : UpIsoCrossNatural S red upIso Sc) (m : X) (r : Fin ℓ) (g : UpBlackMove I)
    {s t : X} (ha : Cond s t (obj RD Λ m ([] ++ upBlackWord g.bottom ++ [.inr r] ++ [])))
    (hb : Cond s t (obj RD Λ m ([] ++ [.inr r] ++ upBlackWord g.top ++ []))) :
    admissibleMap (k := k) (genImg S red upIso Sc) ha hb
      (LinDiagram.of (redUpSlideMirror RD Λ m [] r g [] false) -
        LinDiagram.of (redUpSlideMirror RD Λ m [] r g [] true)) = 0 := by
  obtain rfl : m = s := ha.2.2
  rw [map_sub, sub_eq_zero]
  cases g with
  | dot i =>
    exact genImg_redUpSlideMirror_dot (S := S) (red := red) (upIso := upIso) (Sc := Sc)
      hdot i r ha hb
  | cross i j =>
    exact (genImg_redUpSlideMirror_cross (S := S) (red := red) (upIso := upIso)
      (Sc := Sc) hcross i j r ha hb).symm

/-- **The red/upward slide relations hold** for the generator images of a Rouquier family
whose red/upward isomorphisms are natural for upward dots and crossings (Webster,
arXiv:1309.3796v3, (4.4c,d), proof of Theorem 4.25): in every context, moving a red strand from
left to right through upward black strands commutes with a dot or a crossing. -/
theorem genImg_redUpSlide (hdot : UpIsoDotNatural S red upIso)
    (hcross : UpIsoCrossNatural S red upIso Sc) (μ : X) (u : List (DoubleStrand I ℓ))
    (r : Fin ℓ) (g : UpBlackMove I) (v : List (DoubleStrand I ℓ)) {s t : X}
    (ha : Cond s t (obj RD Λ μ (u ++ [.inr r] ++ upBlackWord g.bottom ++ v)))
    (hb : Cond s t (obj RD Λ μ (u ++ upBlackWord g.top ++ [.inr r] ++ v))) :
    admissibleMap (k := k) (genImg S red upIso Sc) ha hb
      (LinDiagram.of (redUpSlide RD Λ μ u r g v false) -
        LinDiagram.of (redUpSlide RD Λ μ u r g v true)) = 0 := by
  have hx₂ : endWeight RD Λ (endWeight RD Λ μ u) ([] ++ [.inr r] ++ upBlackWord g.bottom ++ []) =
      endWeight RD Λ (endWeight RD Λ μ u) ([] ++ upBlackWord g.top ++ [.inr r] ++ []) := by
    cases g <;> simp [endWeight, upBlackWord, DoubleStrand.weight] <;> abel
  have hw := obj_whiskerOK (RD := RD) (Λ := Λ) μ u
    ([] ++ [.inr r] ++ upBlackWord g.bottom ++ []) v rfl
  have e₁ := (obj_whisker (RD := RD) (Λ := Λ) μ u
    ([] ++ [.inr r] ++ upBlackWord g.bottom ++ []) v rfl).trans
      (congrArg (obj RD Λ μ) (show _ = u ++ [.inr r] ++ upBlackWord g.bottom ++ v by simp))
  have e₂ := (obj_whisker (RD := RD) (Λ := Λ) μ u
    ([] ++ upBlackWord g.top ++ [.inr r] ++ []) v hx₂).trans
      (congrArg (obj RD Λ μ) (show _ = u ++ upBlackWord g.top ++ [.inr r] ++ v by simp))
  rw [redUpSlide_eq_whisker μ u r g v false rfl hw e₁ e₂,
    redUpSlide_eq_whisker μ u r g v true rfl hw e₁ e₂, ← LinDiagram.cast_of,
    ← LinDiagram.cast_of, ← LinDiagram.cast_sub, ← LinDiagram.whisker_of,
    ← LinDiagram.whisker_of, ← LinDiagram.whisker_sub]
  refine admissibleMap_cast_eq_zero _ _ e₁ e₂ ha hb ?_
  refine admissibleMap_whisker_eq_zero _ _ _ _ hw ?_ _ _
  intro ha' hb'
  exact genImg_redUpSlide_bare S red upIso Sc hdot hcross _ r g ha' hb'

/-- **The mirrored red/upward slide relations hold** (Webster, arXiv:1309.3796v3, vertical
mirrors of (4.4c,d), proof of Theorem 4.25): in every context, moving a red strand from right
to left through upward black strands commutes with a dot or a crossing. -/
theorem genImg_redUpSlideMirror (hdot : UpIsoDotNatural S red upIso)
    (hcross : UpIsoCrossNatural S red upIso Sc) (μ : X) (u : List (DoubleStrand I ℓ))
    (r : Fin ℓ) (g : UpBlackMove I) (v : List (DoubleStrand I ℓ)) {s t : X}
    (ha : Cond s t (obj RD Λ μ (u ++ upBlackWord g.bottom ++ [.inr r] ++ v)))
    (hb : Cond s t (obj RD Λ μ (u ++ [.inr r] ++ upBlackWord g.top ++ v))) :
    admissibleMap (k := k) (genImg S red upIso Sc) ha hb
      (LinDiagram.of (redUpSlideMirror RD Λ μ u r g v false) -
        LinDiagram.of (redUpSlideMirror RD Λ μ u r g v true)) = 0 := by
  have hx₂ : endWeight RD Λ (endWeight RD Λ μ u) ([] ++ upBlackWord g.bottom ++ [.inr r] ++ []) =
      endWeight RD Λ (endWeight RD Λ μ u) ([] ++ [.inr r] ++ upBlackWord g.top ++ []) := by
    cases g <;> simp [endWeight, upBlackWord, DoubleStrand.weight] <;> abel
  have hw := obj_whiskerOK (RD := RD) (Λ := Λ) μ u
    ([] ++ upBlackWord g.bottom ++ [.inr r] ++ []) v rfl
  have e₁ := (obj_whisker (RD := RD) (Λ := Λ) μ u
    ([] ++ upBlackWord g.bottom ++ [.inr r] ++ []) v rfl).trans
      (congrArg (obj RD Λ μ) (show _ = u ++ upBlackWord g.bottom ++ [.inr r] ++ v by simp))
  have e₂ := (obj_whisker (RD := RD) (Λ := Λ) μ u
    ([] ++ [.inr r] ++ upBlackWord g.top ++ []) v hx₂).trans
      (congrArg (obj RD Λ μ) (show _ = u ++ [.inr r] ++ upBlackWord g.top ++ v by simp))
  rw [redUpSlideMirror_eq_whisker μ u r g v false rfl hw e₁ e₂,
    redUpSlideMirror_eq_whisker μ u r g v true rfl hw e₁ e₂, ← LinDiagram.cast_of,
    ← LinDiagram.cast_of, ← LinDiagram.cast_sub, ← LinDiagram.whisker_of,
    ← LinDiagram.whisker_of, ← LinDiagram.whisker_sub]
  refine admissibleMap_cast_eq_zero _ _ e₁ e₂ ha hb ?_
  refine admissibleMap_whisker_eq_zero _ _ _ _ hw (fun ha' hb' => ?_) _ _
  exact genImg_redUpSlideMirror_bare S red upIso Sc hdot hcross _ r g ha' hb'

end Relations

end Categorification.Stendhal.DoubleDiagram
