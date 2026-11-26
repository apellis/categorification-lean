/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleRouquierRedUp
import Categorification.WeightedKLR.RedStrands.DoubleRedUpNaturality
import Categorification.Diagrams.BicatInterpChain

/-!
# Red strands slide past upward dots and crossings in the double model

Webster, arXiv:1309.3796v3, (4.4c,d), in the proof of Theorem 4.25. If the red/upward
isomorphisms `upIso` of a Rouquier family are natural for the upward dots and crossings
(`UpIsoDotNatural`, `UpIsoCrossNatural`), the generator images `genImg` satisfy the relations of
`addRedUpSlideRelations`: moving a red strand through upward black strands commutes with a dot
or a crossing on them.
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

local notation "fwT" => fw (S := signature RD Λ)
local notation "wU" i => DoubleStrand.weight RD Λ (Sum.inl (true, i))

variable {B : Type*} [Bicategory B] [∀ a b : B, Preadditive (a ⟶ b)] [AdditiveWhiskering B]
  {k : Type*} [CommRing k] [∀ a b : B, Linear k (a ⟶ b)]
  (S : RouqFamily (B := B) RD)
  (red : (r : Fin ℓ) → {x y : X} → x + Λ r = y → (S.obj y ⟶ S.obj x))
  (upIso : (r : Fin ℓ) → (i : I) → {μ μ₁ μ₂ μ₃ : X} → (h₁ : μ + RD.iX i = μ₁) →
    (h₂ : μ + Λ r = μ₂) → (h₃ : μ₁ + Λ r = μ₃) → (h₄ : μ₂ + RD.iX i = μ₃) →
    (S.F i h₄ ≫ red r h₂ ≅ red r h₃ ≫ S.F i h₁))
  (Sc : CL.CLScalars C k)

/-- The red/upward isomorphisms are natural for upward dots, (4.4c). -/
def UpIsoDotNatural : Prop :=
  ∀ (r : Fin ℓ) (i : I) {μ μ₁ μ₂ μ₃ : X} (h₁ : μ + RD.iX i = μ₁) (h₂ : μ + Λ r = μ₂)
    (h₃ : μ₁ + Λ r = μ₃) (h₄ : μ₂ + RD.iX i = μ₃),
    S.dotDn i h₄ ▷ red r h₂ ≫ (upIso r i h₁ h₂ h₃ h₄).hom =
      (upIso r i h₁ h₂ h₃ h₄).hom ≫ red r h₃ ◁ S.dotDn i h₁

theorem blackImg_dot_up' (z : X) (i : I) {a b : X} (ha hb hd hde hc hce) {x y : X}
    (hx : a = x) (hy : b = y) (h : x + RD.iX i = y) :
    blackImg S red Sc z (.dot (true, i)) a b ha hb hd hde hc hce ≍ S.dotDn i h := by
  subst hx hy; rfl

variable {S red upIso}

theorem genImg_redUpSlide_dot (hdot : UpIsoDotNatural S red upIso) (i : I) (r : Fin ℓ)
    {s t : X}
    (ha : Cond s t (obj RD Λ s ([] ++ [.inr r] ++ upBlackWord (KLR.Diagram.Gen.dot i).dom ++ [])))
    (hb : Cond s t (obj RD Λ s ([] ++ upBlackWord (KLR.Diagram.Gen.dot i).cod ++ [.inr r] ++ []))) :
    admissibleMap (k := k) (genImg S red upIso Sc) ha hb
        (LinDiagram.of (redUpSlide RD Λ s [] r (.dot i) [] false)) =
      admissibleMap (k := k) (genImg S red upIso Sc) ha hb
        (LinDiagram.of (redUpSlide RD Λ s [] r (.dot i) [] true)) := by
  obtain rfl : (s + Λ r) + (wU i) = t := ha.2.1
  rw [admissibleMap_of, admissibleMap_of]
  change admissibleChain _ _ _ _ _ _ _ = admissibleChain _ _ _ _ _ _ _
  dsimp only [ObjectProperty.homMk]
  rw [admissibleChain_congr _ (show Diagram.layers (redUpSlide RD Λ s [] r (.dot i) [] false) =
      [layer RD Λ s [.inr r] (.black (.dot (true, i))) [],
        layer RD Λ s [] (.redBlack r (true, i)) []]
      by simp [redUpSlide, upBlackMoveDiagram, redThroughUpWord, moveDiagram, upBlackWord,
        UpBlackMove.shape]),
    admissibleChain_congr _ (show Diagram.layers (redUpSlide RD Λ s [] r (.dot i) [] true) =
      [layer RD Λ s [] (.redBlack r (true, i)) [],
        layer RD Λ s [] (.black (.dot (true, i))) [.inr r]]
      by simp [redUpSlide, upBlackMoveDiagram, redThroughUpWord, moveDiagram, upBlackWord,
        UpBlackMove.shape])]
  rw [admissibleChain_pair, admissibleChain_pair]
  simp only [coreC_eq]
  unfold core
  have h₁ : s + RD.iX i = (s + (wU i)) := by double_regions
  have h₄ : (s + Λ r) + RD.iX i = ((s + Λ r) + (wU i)) := by double_regions
  have h₃ : (s + (wU i)) + Λ r = ((s + Λ r) + (wU i)) := by double_regions
  let R := fwT s [(s, .inr r)] (s + Λ r) ⟨rfl, trivial⟩ rfl
  let U := fwT (s + Λ r) [(s + Λ r, .inl (true, i))] ((s + Λ r) + (wU i)) ⟨rfl, trivial⟩ rfl
  let U' := fwT s [(s, .inl (true, i))] (s + (wU i)) ⟨rfl, trivial⟩ rfl
  let R' := fwT (s + (wU i)) [((s + (wU i)), .inr r)] ((s + Λ r) + (wU i)) ⟨rfl, trivial⟩ h₃
  refine chain₂_heq (doubleModel S red)
      (p₁ := 𝟙 _) (q₁ := R) (x₁ := U) (y₁ := U)
      (p₂ := 𝟙 _) (q₂ := 𝟙 _) (x₂ := U ≫ R) (y₂ := R' ≫ U')
      (p₃ := 𝟙 _) (q₃ := 𝟙 _) (x₃ := U ≫ R) (y₃ := R' ≫ U')
      (p₄ := R') (q₄ := 𝟙 _) (x₄ := U') (y₄ := U')
      (S.dotDn i h₄) (upIso r i h₁ rfl h₃ h₄).hom (upIso r i h₁ rfl h₃ h₄).hom (S.dotDn i h₁)
      (λ_ _).symm (𝟙 _ ◁ (ρ_ _).inv) (λ_ _ ≪≫ ρ_ _)
      ((ρ_ _).symm ≪≫ (λ_ _).symm) ((λ_ _).hom ≫ (α_ _ _ _).hom) (whiskerLeftIso R' (ρ_ U'))
      ?hmain ?hn1 ?hm1 ?hr1 ?hl1 ?hd1 ?he1 _ ?hg1 _ _ ?hn2 ?hm2 ?hr2 ?hl2 ?hd2 ?he2 _ ?hg2 _ _
      ?hn3 ?hm3 ?hr3 ?hl3 ?hd3 ?he3 _ ?hg3 _ _ ?hn4 ?hm4 ?hr4 ?hl4 ?hd4 ?he4 _ ?hg4 _ _
      _ _ _ _ _ _
  case hmain =>
    have := slide_right_hyp (doubleModel S red) (U := U) (R := R) (R' := R') (U' := U')
      (S.dotDn i h₄) (upIso r i h₁ rfl h₃ h₄).hom (S.dotDn i h₁) (hdot r i h₁ rfl h₃ h₄)
    convert this using 2
  case hg1 =>
    refine (heq_of_eq (genImg_blackOn S red upIso Sc _ _ _ _ _ _ _ _ _ _)).trans ?_
    exact blackImg_dot_up' S red Sc _ i _ _ _ _ _ _ (by double_regions) (by double_regions) h₄
  case hg4 =>
    refine (heq_of_eq (genImg_blackOn S red upIso Sc _ _ _ _ _ _ _ _ _ _)).trans ?_
    exact blackImg_dot_up' S red Sc _ i _ _ _ _ _ _ (by double_regions) (by double_regions) h₁
  case hg2 =>
    exact upIso_hom_heq S red upIso r i (by double_regions) (by double_regions)
      (by double_regions) (by double_regions) _ _ _ _ _ _ _ _
  case hg3 =>
    exact upIso_hom_heq S red upIso r i (by double_regions) (by double_regions)
      (by double_regions) (by double_regions) _ _ _ _ _ _ _ _
  case hn1 => double_regions
  case hm1 => double_regions
  case hr1 => double_nil
  case hl1 => double_single
  case hd1 => double_single
  case he1 => double_single
  case hn2 => double_regions
  case hm2 => double_regions
  case hr2 => double_nil
  case hl2 => double_nil
  case hd2 => double_pair
  case he2 => double_pair
  case hn3 => double_regions
  case hm3 => double_regions
  case hr3 => double_nil
  case hl3 => double_nil
  case hd3 => double_pair
  case he3 => double_pair
  case hn4 => double_regions
  case hm4 => double_regions
  case hr4 => double_single
  case hl4 => double_nil
  case hd4 => double_single
  case he4 => double_single

end Categorification.Stendhal.DoubleDiagram
