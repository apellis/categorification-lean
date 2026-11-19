/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCLNegligible
import Categorification.TwoRep.RouqModel
import Categorification.KLR.CyclotomicAction.GlobalFamily

/-!
# Red-negligible 2-morphisms whiskered by words of the cyclotomic family

Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29. In the cyclotomic evaluation of a
double diagram, the image of a local relation is whiskered on the right by the image of the
word to its left. A red strand is upward in every such word, so the word only contains
cyclotomic restrictions at black colours. Whiskering by the image of such a word preserves
red-negligibility (`RedNegligible.whiskerRight_word`).
-/

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory Bicategory KLR KLR.CyclotomicAction TwoRep KL3.Diagram
  Categorification.Diagrams.BicatInterp

universe u v w u₁

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {a : I → Polynomial k}
  {hc : ∀ δ c (z : CycKLR k Q a δ), Commute z (cyclotomicColourDot Q a δ c)}
  {Rd : Set I}
  (hQ : KLRSymm Q)
  (hlead : ∀ j l, j ≠ l → ∃ c : k, IsUnit c ∧ (polyInY (Q j l)).leadingCoeff = Polynomial.C c)
  (ha : ∀ j, (a j).Monic)
  {C : QuantumGroup.CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  {RD : QuantumGroup.UDot.WeightDatum C X Y} {Λ : X}
  (hΛ : ∀ i, ((a i).natDegree : ℤ) = RD.pair (RD.iY i) Λ)
  (hdeg : ∀ i j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) = -RD.pair (RD.iY i) (RD.iX j))

/-- A colour that may occur in a word whisker: upward, or of a non-red colour. -/
def RedAllowed (Rd : Set I) (c : Col I X) : Prop := c.l.1 = true ∨ c.l.2 ∉ Rd

set_option quotPrecheck false in
set_option hygiene false in
local notation "Fam" => Categorification.KLR.CyclotomicAction.cyclotomicFamily.{u, v, w} hQ hlead ha RD Λ hΛ hdeg

namespace RedNegligible

variable {Z : LinearCat.{v, max (max u v) w, max (max u v) w + 1} k}

include hQ hlead ha hΛ hdeg in
/-- Whiskering by the image of a single allowed strand preserves red-negligibility. -/
theorem whiskerRight_strandAt (c : Col I X) (hc' : RedAllowed Rd c) {x y : X}
    (hx : (psig RD).colourTgt c = x) (hy : (psig RD).colourSrc c = y)
    {F G : Z ⟶ weightSpace.{u, v, w} Q a RD Λ x} {θ : F ⟶ G}
    (hθ : RedNegligible Q a hc Rd RD Λ θ) :
    RedNegligible Q a hc Rd RD Λ (θ ▷ (Fam).model.strandAt c x y hx hy) := by
  obtain ⟨⟨b, i⟩, r⟩ := c
  cases b with
  | true => exact hθ.whiskerRight_globalE i (RouqFamily.up_reg i hx hy)
  | false =>
    have hi : i ∉ Rd := by
      rcases hc' with h | h
      · exact absurd h Bool.false_ne_true
      · exact h
    exact hθ.whiskerRight_globalF i hi (RouqFamily.dn_reg i hx hy)

/-- Whiskering by a composite reduces to iterated whiskering. -/
theorem whiskerRight_comp_of {x y z : X} {f : weightSpace.{u, v, w} Q a RD Λ x ⟶
    weightSpace.{u, v, w} Q a RD Λ y} {g : weightSpace.{u, v, w} Q a RD Λ y ⟶
    weightSpace.{u, v, w} Q a RD Λ z} {F G : Z ⟶ weightSpace.{u, v, w} Q a RD Λ x}
    {θ : F ⟶ G} (h : RedNegligible Q a hc Rd RD Λ ((θ ▷ f) ▷ g)) :
    RedNegligible Q a hc Rd RD Λ (θ ▷ (f ≫ g)) := by
  rw [whiskerRight_comp]
  rw [← Category.assoc]
  exact (h.comp_left _).comp_right _

include hQ hlead ha hΛ hdeg in
/-- **Whiskering by the image of an allowed word preserves red-negligibility.** -/
theorem whiskerRight_word : ∀ (s : X) (ws : List (Col I X)) (t : X) (h : (psig RD).ok s ws)
    (e : (psig RD).endR s ws = t) (_ : ∀ c ∈ ws, RedAllowed Rd c)
    {F G : Z ⟶ weightSpace.{u, v, w} Q a RD Λ t} {θ : F ⟶ G},
    RedNegligible Q a hc Rd RD Λ θ →
    RedNegligible Q a hc Rd RD Λ (θ ▷ (Fam).model.word s ws t h e)
  | _, [], _, _, rfl, _, _, _, θ, hθ => by
    have := (hθ.comp_left (ρ_ _).hom).comp_right (ρ_ _).inv
    rw [Category.assoc, ← whiskerRight_id] at this
    exact this
  | s, [c], t, h, e, hw, _, _, θ, hθ =>
    whiskerRight_strandAt hQ hlead ha hΛ hdeg c (hw c (List.mem_singleton_self c)) e h.1 hθ
  | s, c :: c' :: ws, t, h, e, hw, _, _, θ, hθ => by
    exact whiskerRight_comp_of (whiskerRight_strandAt hQ hlead ha hΛ hdeg c
      (hw c List.mem_cons_self) rfl h.1
      (whiskerRight_word _ (c' :: ws) t h.2 e (fun d hd => hw d (List.mem_cons_of_mem c hd))
        hθ))

end RedNegligible

end Categorification.Stendhal
