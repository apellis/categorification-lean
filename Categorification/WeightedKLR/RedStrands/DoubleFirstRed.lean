/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleViolatedCut
import StringDiagrams.InterchangeLayers

/-! # The first strand of a surviving signed diagram

Webster, arXiv:1309.3796v2, §4.5, Definition 4.27. Every layer incident to
the left edge has a black-first boundary on at least one side.
-/
noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams
universe u v w
variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}}
  {k : Type w} [CommRing k] (P : Presentation.{w,max u v} (signature RD (Subtype.val ∘ Λ)) k)
  {η : X}
local notation "lab" => Subtype.val ∘ Λ

private theorem blackFirst_of_leftEmpty (L : Layer (signature RD lab)) (hl : L.left = []) :
    (∃ l, (L.dom.word.map Prod.snd).head? = some (.inl l)) ∨
    (∃ l, (L.cod.word.map Prod.snd).head? = some (.inl l)) := by
  obtain ⟨μ, u, ⟨ξ, g⟩, v⟩ := L
  change u = [] at hl
  subst u
  change List (X × DoubleStrand I ℓ) at v
  change (∃ l, ((colours RD lab ξ g.bottom ++ v).map Prod.snd).head? = some (.inl l)) ∨
    (∃ l, ((colours RD lab ξ g.top ++ v).map Prod.snd).head? = some (.inl l))
  simp only [List.map_append, forget_colours]
  cases g with
  | black g => cases g <;> simp [Move.bottom, Move.top, Shape.dom, Shape.cod]
  | blackRed l r => exact Or.inl ⟨l,rfl⟩
  | redBlack r l => exact Or.inr ⟨l,rfl⟩

/-- Any signed diagram acting on the leftmost strand, or creating a pair
to its left, vanishes in the violating quotient. -/
theorem diagram_eq_zero_of_leftEmptyLayer (b c : BoundaryCategory P η)
    (d : obj RD lab 0 b.val.word ⟶ obj RD lab 0 c.val.word)
    {L : Layer (signature RD lab)} (hL : L ∈ Diagram.layers d) (hl : L.left = []) :
    (violatingFunctor P η).map (InducedCategory.homMk (X := b) (Y := c) (P.diag d)) = 0 := by
  obtain ⟨pre,post,h⟩ := List.append_of_mem hL
  have hc := Diagram.chain d
  rw [h] at hc
  obtain ⟨hp,hs⟩ := hc.of_append
  let first := Diagram.mk pre hp
  let mid := Diagram.layer L hs.1 hs.2.1 rfl
  let last := Diagram.mk post hs.2.2
  have he : d = (first ≫ mid) ≫ last := by
    apply Diagram.ext
    simpa only [Diagram.layers_comp, first, mid, last, Diagram.layers_layer,
      Diagram.layers_mk, List.append_assoc, List.singleton_append] using h
  rw [he]
  rcases blackFirst_of_leftEmpty L hl with hd | hc
  · rw [Category.assoc]
    apply diagram_eq_zero_of_black_at_cut
    rwa [← hs.2.1]
  · exact diagram_eq_zero_of_black_at_cut P b c _ _ hc

/-- Every layer in a diagram whose image is nonzero has a spectator on the
left. For an ordered loading in the violating quotient this protects the
first red throughout the path. -/
theorem left_nonempty_of_diagram_ne_zero (b c : BoundaryCategory P η)
    (d : obj RD lab 0 b.val.word ⟶ obj RD lab 0 c.val.word)
    (h : (violatingFunctor P η).map (InducedCategory.homMk (X := b) (Y := c) (P.diag d)) ≠ 0) :
    ∀ L ∈ Diagram.layers d, L.left ≠ [] :=
  fun _ hL hl => h (diagram_eq_zero_of_leftEmptyLayer P b c d hL hl)

end Categorification.Stendhal.DoubleDiagram
