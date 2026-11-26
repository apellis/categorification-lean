/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleRouquierRedCup

/-!
# Red cups and caps in context, in the double model of a Rouquier family

Webster, arXiv:1309.3796v3, §4.5, proof of Theorem 4.25. Every red cup and red cap relation of
the double signature is a whiskering of one without context (`redCupLeft_whisker`, ...), so the
generator images of a Rouquier family kill all of them (`genImg_redCup`, `genImg_redCap`).
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

local notation "T" => signature RD Λ

/-- Region arithmetic in layers of the double signature. -/
macro "double_regions" : tactic => `(tactic| ((try dsimp only [layer, signature, colours,
  Signature.endR]) <;> simp [endWeight, Move.bottom, Move.top, DoubleStrand.weight, sgn] <;>
  abel_nf <;> done))


section Context

theorem layer_whisker (μ : X) (u u' v' v : List (DoubleStrand I ℓ)) (g : Move I ℓ) {x : X}
    (hx : x = endWeight RD Λ (endWeight RD Λ μ u) (u' ++ g.bottom ++ v')) :
    (layer RD Λ (endWeight RD Λ μ u) u' g v').whisker (obj RD Λ μ u) (colours RD Λ x v) =
      layer RD Λ μ (u ++ u') g (v' ++ v) := by
  subst hx
  apply Layer.ext
  · rfl
  · simp [Layer.whisker, layer, obj, colours_append]
  · simp [Layer.whisker, layer, endWeight_append]
  · simp [Layer.whisker, layer, colours_append, endWeight_append]

theorem obj_whisker (μ : X) (u w v : List (DoubleStrand I ℓ)) {x : X}
    (hx : x = endWeight RD Λ (endWeight RD Λ μ u) w) :
    (obj RD Λ (endWeight RD Λ μ u) w).whisker (obj RD Λ μ u) (colours RD Λ x v) =
      obj RD Λ μ (u ++ w ++ v) := by
  subst hx
  refine Obj.ext rfl ?_
  simp [Obj.whisker, obj, colours_append]

theorem obj_whiskerOK (μ : X) (u w v : List (DoubleStrand I ℓ)) {x : X}
    (hx : x = endWeight RD Λ (endWeight RD Λ μ u) w) :
    (obj RD Λ (endWeight RD Λ μ u) w).WhiskerOK (obj RD Λ μ u) (colours RD Λ x v) := by
  subst hx
  refine ⟨colours_ok RD Λ μ u, colours_endR RD Λ μ u, ?_⟩
  have e := colours_endR RD Λ (endWeight RD Λ μ u) w
  have h := colours_ok RD Λ (endWeight RD Λ (endWeight RD Λ μ u) w) v
  exact (congrArg (fun z => (T).ok z (colours RD Λ (endWeight RD Λ (endWeight RD Λ μ u) w) v)) e).mpr h

theorem weight_dual (l : Letter I) :
    DoubleStrand.weight RD Λ (.inl l) + DoubleStrand.weight RD Λ (.inl l.dual) = 0 := by
  obtain ⟨_ | _, i⟩ := l <;> simp [DoubleStrand.weight, sgn, Letter.dual]

end Context

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

/-- **The red cup relations hold** for the generator images of a Rouquier family (Webster,
arXiv:1309.3796v3, proof of Theorem 4.25): in every context, a black cup of either orientation
slides through a red strand. -/
theorem genImg_redCup (a : RedCapRelation X I ℓ) {s t : X}
    (ha : Cond s t (obj RD Λ a.leftWeight (a.left ++ [.inr a.red] ++ a.right)))
    (hb : Cond s t (obj RD Λ a.leftWeight
      (a.left ++ [.inl a.black, .inr a.red, .inl a.black.dual] ++ a.right))) :
    admissibleMap (k := k) (genImg S red upIso Sc) ha hb
      (LinDiagram.of (redCupLeft RD Λ a.leftWeight a.left a.black a.red a.right) -
        LinDiagram.of (redCupRight RD Λ a.leftWeight a.left a.black a.red a.right)) = 0 := by
  obtain ⟨μ, u, l, r, v⟩ := a
  dsimp only at ha hb ⊢
  have hx₁ : endWeight RD Λ (endWeight RD Λ μ u) [.inr r] =
      endWeight RD Λ (endWeight RD Λ μ u) ([] ++ [.inr r] ++ []) := rfl
  have hx₂ : endWeight RD Λ (endWeight RD Λ μ u) [.inr r] =
      endWeight RD Λ (endWeight RD Λ μ u) ([] ++ [.inl l, .inr r, .inl l.dual] ++ []) := by
    obtain ⟨_ | _, i⟩ := l <;> simp [endWeight, DoubleStrand.weight, sgn, Letter.dual]
  have hw := obj_whiskerOK (RD := RD) (Λ := Λ) μ u ([] ++ [.inr r] ++ []) v hx₁
  have e₁ := obj_whisker (RD := RD) (Λ := Λ) μ u ([] ++ [.inr r] ++ []) v hx₁
  have e₂ := obj_whisker (RD := RD) (Λ := Λ) μ u ([] ++ [.inl l, .inr r, .inl l.dual] ++ []) v hx₂
  have hL : redCupLeft RD Λ μ u l r v = Diagram.cast (Diagram.whisker
      (redCupLeft RD Λ (endWeight RD Λ μ u) [] l r []) (obj RD Λ μ u) _ hw) e₁ e₂ := by
    apply Diagram.ext
    rw [Diagram.layers_cast, Diagram.layers_whisker]
    simp only [redCupLeft, moveDiagram, Diagram.layers_comp, Diagram.layers_cast,
      Diagram.layers_layer, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    rw [layer_whisker (RD := RD) (Λ := Λ) μ u [] [.inr r] v _ (by simp [endWeight, Move.bottom]),
      layer_whisker (RD := RD) (Λ := Λ) μ u [.inl l] [] v _ (by
        rw [hx₂]; obtain ⟨_ | _, i⟩ := l <;>
          simp [endWeight, Move.bottom, DoubleStrand.weight, sgn, Letter.dual])]
    simp
  have hR : redCupRight RD Λ μ u l r v = Diagram.cast (Diagram.whisker
      (redCupRight RD Λ (endWeight RD Λ μ u) [] l r []) (obj RD Λ μ u) _ hw) e₁ e₂ := by
    apply Diagram.ext
    rw [Diagram.layers_cast, Diagram.layers_whisker]
    simp only [redCupRight, moveDiagram, Diagram.layers_comp, Diagram.layers_cast,
      Diagram.layers_layer, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    rw [layer_whisker (RD := RD) (Λ := Λ) μ u [.inr r] [] v _ (by simp [endWeight, Move.bottom]),
      layer_whisker (RD := RD) (Λ := Λ) μ u [] [.inl l.dual] v _ (by
        rw [hx₂]; obtain ⟨_ | _, i⟩ := l <;>
          simp [endWeight, Move.bottom, DoubleStrand.weight, sgn, Letter.dual])]
    simp
  rw [hL, hR, ← LinDiagram.cast_of, ← LinDiagram.cast_of, ← LinDiagram.cast_sub,
    ← LinDiagram.whisker_of, ← LinDiagram.whisker_of, ← LinDiagram.whisker_sub]
  refine admissibleMap_cast_eq_zero _ _ e₁ e₂ ha hb ?_
  refine admissibleMap_whisker_eq_zero _ _ _ _ hw (fun ha' hb' => ?_) _ _
  rw [map_sub, sub_eq_zero]
  obtain ⟨_ | _, i⟩ := l
  · exact genImg_redCup_bare_dn S red upIso Sc i r ha' hb'
  · exact genImg_redCup_bare_up S red upIso Sc i r ha' hb'

/-- **The red cap relations hold** for the generator images of a Rouquier family (Webster,
arXiv:1309.3796v3, proof of Theorem 4.25): in every context, a black cap of either orientation
slides through a red strand. -/
theorem genImg_redCap (a : RedCapRelation X I ℓ) {s t : X}
    (ha : Cond s t (obj RD Λ a.leftWeight
      (a.left ++ [.inl a.black.dual, .inr a.red, .inl a.black] ++ a.right)))
    (hb : Cond s t (obj RD Λ a.leftWeight (a.left ++ [.inr a.red] ++ a.right))) :
    admissibleMap (k := k) (genImg S red upIso Sc) ha hb
      (LinDiagram.of (redCapLeft RD Λ a.leftWeight a.left a.black a.red a.right) -
        LinDiagram.of (redCapRight RD Λ a.leftWeight a.left a.black a.red a.right)) = 0 := by
  obtain ⟨μ, u, l, r, v⟩ := a
  dsimp only at ha hb ⊢
  have hx₁ : endWeight RD Λ (endWeight RD Λ μ u) [.inr r] =
      endWeight RD Λ (endWeight RD Λ μ u) ([] ++ [.inr r] ++ []) := rfl
  have hx₂ : endWeight RD Λ (endWeight RD Λ μ u) [.inr r] =
      endWeight RD Λ (endWeight RD Λ μ u) ([] ++ [.inl l.dual, .inr r, .inl l] ++ []) := by
    obtain ⟨_ | _, i⟩ := l <;> simp [endWeight, DoubleStrand.weight, sgn, Letter.dual]
  have hw := obj_whiskerOK (RD := RD) (Λ := Λ) μ u ([] ++ [.inl l.dual, .inr r, .inl l] ++ []) v
    hx₂
  have e₁ := obj_whisker (RD := RD) (Λ := Λ) μ u ([] ++ [.inl l.dual, .inr r, .inl l] ++ []) v hx₂
  have e₂ := obj_whisker (RD := RD) (Λ := Λ) μ u ([] ++ [.inr r] ++ []) v hx₁
  have hL : redCapLeft RD Λ μ u l r v = Diagram.cast (Diagram.whisker
      (redCapLeft RD Λ (endWeight RD Λ μ u) [] l r []) (obj RD Λ μ u) _ hw) e₁ e₂ := by
    apply Diagram.ext
    rw [Diagram.layers_cast, Diagram.layers_whisker]
    simp only [redCapLeft, moveDiagram, Diagram.layers_comp, Diagram.layers_cast,
      Diagram.layers_layer, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    rw [layer_whisker (RD := RD) (Λ := Λ) μ u [.inl l.dual] [] v _ (by
        rw [hx₂]; obtain ⟨_ | _, i⟩ := l <;>
          simp [endWeight, Move.bottom, DoubleStrand.weight, sgn, Letter.dual]),
      layer_whisker (RD := RD) (Λ := Λ) μ u [] [.inr r] v _ (by
        rw [hx₂]; obtain ⟨_ | _, i⟩ := l <;>
          simp [endWeight, Move.bottom, DoubleStrand.weight, sgn, Letter.dual])]
    simp
  have hR : redCapRight RD Λ μ u l r v = Diagram.cast (Diagram.whisker
      (redCapRight RD Λ (endWeight RD Λ μ u) [] l r []) (obj RD Λ μ u) _ hw) e₁ e₂ := by
    apply Diagram.ext
    rw [Diagram.layers_cast, Diagram.layers_whisker]
    simp only [redCapRight, moveDiagram, Diagram.layers_comp, Diagram.layers_cast,
      Diagram.layers_layer, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    rw [layer_whisker (RD := RD) (Λ := Λ) μ u [] [.inl l] v _ (by
        rw [hx₂]; obtain ⟨_ | _, i⟩ := l <;>
          simp [endWeight, Move.bottom, DoubleStrand.weight, sgn, Letter.dual]),
      layer_whisker (RD := RD) (Λ := Λ) μ u [.inr r] [] v _ (by
        rw [hx₂]; obtain ⟨_ | _, i⟩ := l <;>
          simp [endWeight, Move.bottom, DoubleStrand.weight, sgn, Letter.dual])]
    simp
  rw [hL, hR, ← LinDiagram.cast_of, ← LinDiagram.cast_of, ← LinDiagram.cast_sub,
    ← LinDiagram.whisker_of, ← LinDiagram.whisker_of, ← LinDiagram.whisker_sub]
  refine admissibleMap_cast_eq_zero _ _ e₁ e₂ ha hb ?_
  refine admissibleMap_whisker_eq_zero _ _ _ _ hw (fun ha' hb' => ?_) _ _
  rw [map_sub, sub_eq_zero]
  obtain ⟨_ | _, i⟩ := l
  · exact genImg_redCap_bare_dn S red upIso Sc i r ha' hb'
  · exact genImg_redCap_bare_up S red upIso Sc i r ha' hb'

end Categorification.Stendhal.DoubleDiagram
