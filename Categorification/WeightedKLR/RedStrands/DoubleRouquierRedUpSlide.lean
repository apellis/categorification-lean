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

/-- The red/upward isomorphisms are natural for upward crossings, (4.4d): a red strand passing to
the right through two upward strands commutes with their crossing. -/
def UpIsoCrossNatural (Sc : CL.CLScalars C k) : Prop :=
  ∀ (r : Fin ℓ) (i j : I) {μ ρ ρi ρj ν μi μj μij : X} (hr : μ + Λ r = ρ)
    (hi : ρ + RD.iX i = ρi) (hj : ρi + RD.iX j = ν) (hi' : ρj + RD.iX i = ν)
    (hj' : ρ + RD.iX j = ρj) (h₁ : μ + RD.iX j = μj) (h₃ : μj + Λ r = ρj)
    (h₁' : μj + RD.iX i = μij) (h₃' : μij + Λ r = ν) (g₁ : μ + RD.iX i = μi)
    (g₃ : μi + Λ r = ρi) (g₁' : μi + RD.iX j = μij),
    (α_ _ _ _).inv ≫ S.crossDn Sc i j hj hi hi' hj' ▷ red r hr ≫ (α_ _ _ _).hom ≫
        S.F i hi' ◁ (upIso r j h₁ hr h₃ hj').hom ≫ (α_ _ _ _).inv ≫
        (upIso r i h₁' h₃ h₃' hi').hom ▷ S.F j h₁ ≫ (α_ _ _ _).hom =
      S.F j hj ◁ (upIso r i g₁ hr g₃ hi).hom ≫ (α_ _ _ _).inv ≫
        (upIso r j g₁' g₃ h₃' hj).hom ▷ S.F i g₁ ≫ (α_ _ _ _).hom ≫
        red r h₃' ◁ S.crossDn Sc i j g₁' g₁ h₁' h₁

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

theorem genImg_redUpSlideMirror_dot (hdot : UpIsoDotNatural S red upIso) (i : I) (r : Fin ℓ)
    {s t : X}
    (ha : Cond s t (obj RD Λ s ([] ++ upBlackWord (KLR.Diagram.Gen.dot i).dom ++ [.inr r] ++ [])))
    (hb : Cond s t (obj RD Λ s ([] ++ [.inr r] ++ upBlackWord (KLR.Diagram.Gen.dot i).cod ++ []))) :
    admissibleMap (k := k) (genImg S red upIso Sc) ha hb
        (LinDiagram.of (redUpSlideMirror RD Λ s [] r (.dot i) [] false)) =
      admissibleMap (k := k) (genImg S red upIso Sc) ha hb
        (LinDiagram.of (redUpSlideMirror RD Λ s [] r (.dot i) [] true)) := by
  obtain rfl : (s + (wU i)) + Λ r = t := ha.2.1
  rw [admissibleMap_of, admissibleMap_of]
  change admissibleChain _ _ _ _ _ _ _ = admissibleChain _ _ _ _ _ _ _
  dsimp only [ObjectProperty.homMk]
  rw [admissibleChain_congr _ (show Diagram.layers (redUpSlideMirror RD Λ s [] r (.dot i) [] false) =
      [layer RD Λ s [] (.black (.dot (true, i))) [.inr r],
        layer RD Λ s [] (.blackRed (true, i) r) []]
      by simp [redUpSlideMirror, upBlackMoveDiagram, upWordThroughRed, moveDiagram, upBlackWord,
        UpBlackMove.shape]; rfl),
    admissibleChain_congr _ (show Diagram.layers (redUpSlideMirror RD Λ s [] r (.dot i) [] true) =
      [layer RD Λ s [] (.blackRed (true, i) r) [],
        layer RD Λ s [.inr r] (.black (.dot (true, i))) []]
      by simp [redUpSlideMirror, upBlackMoveDiagram, upWordThroughRed, moveDiagram, upBlackWord,
        UpBlackMove.shape]; rfl)]
  rw [admissibleChain_pair, admissibleChain_pair]
  simp only [coreC_eq]
  unfold core
  have h₁ : s + RD.iX i = (s + (wU i)) := by double_regions
  have h₄ : (s + Λ r) + RD.iX i = ((s + (wU i)) + Λ r) := by double_regions
  have hh : (s + Λ r) + (wU i) = ((s + (wU i)) + Λ r) := by double_regions
  let U := fwT s [(s, .inl (true, i))] (s + (wU i)) ⟨rfl, trivial⟩ rfl
  let R := fwT (s + (wU i)) [(s + (wU i), .inr r)] ((s + (wU i)) + Λ r) ⟨rfl, trivial⟩ rfl
  let R'' := fwT s [(s, .inr r)] (s + Λ r) ⟨rfl, trivial⟩ rfl
  let U'' := fwT (s + Λ r) [((s + Λ r), .inl (true, i))] ((s + (wU i)) + Λ r) ⟨rfl, trivial⟩ hh
  refine chain₂_heq (doubleModel S red)
      (p₁ := R) (q₁ := 𝟙 _) (x₁ := U) (y₁ := U)
      (p₂ := 𝟙 _) (q₂ := 𝟙 _) (x₂ := R ≫ U) (y₂ := U'' ≫ R'')
      (p₃ := 𝟙 _) (q₃ := 𝟙 _) (x₃ := R ≫ U) (y₃ := U'' ≫ R'')
      (p₄ := 𝟙 _) (q₄ := R'') (x₄ := U'') (y₄ := U'')
      (S.dotDn i h₁) (upIso r i h₁ rfl rfl h₄).inv (upIso r i h₁ rfl rfl h₄).inv (S.dotDn i h₄)
      (whiskerLeftIso R (ρ_ U).symm) ((α_ R U (𝟙 _)).inv ≫ (λ_ _).inv) (λ_ _ ≪≫ ρ_ _)
      ((ρ_ _).symm ≪≫ (λ_ _).symm) (𝟙 _ ◁ (ρ_ _).hom) (λ_ _)
      ?hmain ?hn1 ?hm1 ?hr1 ?hl1 ?hd1 ?he1 _ ?hg1 _ _ ?hn2 ?hm2 ?hr2 ?hl2 ?hd2 ?he2 _ ?hg2 _ _
      ?hn3 ?hm3 ?hr3 ?hl3 ?hd3 ?he3 _ ?hg3 _ _ ?hn4 ?hm4 ?hr4 ?hl4 ?hd4 ?he4 _ ?hg4 _ _
      _ _ _ _ _ _
  case hmain =>
    have hd := hdot r i h₁ rfl rfl h₄
    have e : red r rfl ◁ S.dotDn i h₁ ≫ (upIso r i h₁ rfl rfl h₄).inv =
        (upIso r i h₁ rfl rfl h₄).inv ≫ S.dotDn i h₄ ▷ red r rfl := by
      rw [Iso.comp_inv_eq, Category.assoc, hd, Iso.inv_hom_id_assoc]
    have := slide_left_hyp (doubleModel S red) (U := U) (R := R) (U'' := U'') (R'' := R'')
      (S.dotDn i h₁) (upIso r i h₁ rfl rfl h₄).inv (S.dotDn i h₄) e
    convert this using 2
  case hg1 =>
    refine (heq_of_eq (genImg_blackOn S red upIso Sc _ _ _ _ _ _ _ _ _ _)).trans ?_
    exact blackImg_dot_up' S red Sc _ i _ _ _ _ _ _ (by double_regions) (by double_regions) h₁
  case hg4 =>
    refine (heq_of_eq (genImg_blackOn S red upIso Sc _ _ _ _ _ _ _ _ _ _)).trans ?_
    exact blackImg_dot_up' S red Sc _ i _ _ _ _ _ _ (by double_regions) (by double_regions) h₄
  case hg2 =>
    exact upIso_inv_heq S red upIso r i (by double_regions) (by double_regions)
      (by double_regions) (by double_regions) _ _ _ _ _ _ _ _
  case hg3 =>
    exact upIso_inv_heq S red upIso r i (by double_regions) (by double_regions)
      (by double_regions) (by double_regions) _ _ _ _ _ _ _ _
  case hn1 => double_regions
  case hm1 => double_regions
  case hr1 => double_single
  case hl1 => double_nil
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
  case hr4 => double_nil
  case hl4 => double_single
  case hd4 => double_single
  case he4 => double_single

theorem genImg_redUpSlide_cross (hcross : UpIsoCrossNatural S red upIso Sc) (i j : I)
    (r : Fin ℓ) {s t : X}
    (ha : Cond s t (obj RD Λ s ([] ++ [.inr r] ++ upBlackWord (KLR.Diagram.Gen.cross i j).dom ++
      [])))
    (hb : Cond s t (obj RD Λ s ([] ++ upBlackWord (KLR.Diagram.Gen.cross i j).cod ++ [.inr r] ++
      []))) :
    admissibleMap (k := k) (genImg S red upIso Sc) ha hb
        (LinDiagram.of (redUpSlide RD Λ s [] r (.cross i j) [] false)) =
      admissibleMap (k := k) (genImg S red upIso Sc) ha hb
        (LinDiagram.of (redUpSlide RD Λ s [] r (.cross i j) [] true)) := by
  obtain rfl : ((s + Λ r) + (wU i)) + (wU j) = t := ha.2.1
  rw [admissibleMap_of, admissibleMap_of]
  change admissibleChain _ _ _ _ _ _ _ = admissibleChain _ _ _ _ _ _ _
  dsimp only [ObjectProperty.homMk]
  rw [admissibleChain_congr _ (show Diagram.layers (redUpSlide RD Λ s [] r (.cross i j) [] false) =
      [layer RD Λ s [.inr r] (.black (.cross true i j)) [],
        layer RD Λ s [] (.redBlack r (true, j)) [.inl (true, i)],
        layer RD Λ s [.inl (true, j)] (.redBlack r (true, i)) []]
      by simp [redUpSlide, upBlackMoveDiagram, redThroughUpWord, moveDiagram, upBlackWord,
        UpBlackMove.shape]),
    admissibleChain_congr _ (show Diagram.layers (redUpSlide RD Λ s [] r (.cross i j) [] true) =
      [layer RD Λ s [] (.redBlack r (true, i)) [.inl (true, j)],
        layer RD Λ s [.inl (true, i)] (.redBlack r (true, j)) [],
        layer RD Λ s [] (.black (.cross true i j)) [.inr r]]
      by simp [redUpSlide, upBlackMoveDiagram, redThroughUpWord, moveDiagram, upBlackWord,
        UpBlackMove.shape])]
  have hi : (s + Λ r) + RD.iX i = (s + Λ r) + (wU i) := by double_regions
  have hj : ((s + Λ r) + (wU i)) + RD.iX j = ((s + Λ r) + (wU i)) + (wU j) := by double_regions
  have hi' : ((s + Λ r) + (wU j)) + RD.iX i = ((s + Λ r) + (wU i)) + (wU j) := by double_regions
  have hj' : (s + Λ r) + RD.iX j = (s + Λ r) + (wU j) := by double_regions
  have h₁ : s + RD.iX j = s + (wU j) := by double_regions
  have h₃ : (s + (wU j)) + Λ r = (s + Λ r) + (wU j) := by double_regions
  have h₁' : (s + (wU j)) + RD.iX i = (s + (wU j)) + (wU i) := by double_regions
  have h₃' : ((s + (wU j)) + (wU i)) + Λ r = ((s + Λ r) + (wU i)) + (wU j) := by double_regions
  have g₁ : s + RD.iX i = s + (wU i) := by double_regions
  have g₃ : (s + (wU i)) + Λ r = (s + Λ r) + (wU i) := by double_regions
  have g₁' : (s + (wU i)) + RD.iX j = (s + (wU j)) + (wU i) := by double_regions
  have e₁ : ((s + Λ r) + (wU j)) + (wU i) = ((s + Λ r) + (wU i)) + (wU j) := by double_regions
  have e₅ : (s + (wU i)) + (wU j) = (s + (wU j)) + (wU i) := by double_regions
  let R0 := fwT s [(s, .inr r)] (s + Λ r) ⟨rfl, trivial⟩ rfl
  let Ui := fwT (s + Λ r) [(s + Λ r, .inl (true, i))] ((s + Λ r) + (wU i)) ⟨rfl, trivial⟩ rfl
  let Uj := fwT ((s + Λ r) + (wU i)) [((s + Λ r) + (wU i), .inl (true, j))]
    (((s + Λ r) + (wU i)) + (wU j)) ⟨rfl, trivial⟩ rfl
  let Ui2 := fwT ((s + Λ r) + (wU j)) [((s + Λ r) + (wU j), .inl (true, i))]
    (((s + Λ r) + (wU i)) + (wU j)) ⟨rfl, trivial⟩ e₁
  let Uj2 := fwT (s + Λ r) [(s + Λ r, .inl (true, j))] ((s + Λ r) + (wU j)) ⟨rfl, trivial⟩ rfl
  let R3 := fwT (s + (wU j)) [(s + (wU j), .inr r)] ((s + Λ r) + (wU j)) ⟨rfl, trivial⟩ h₃
  let Uj3 := fwT s [(s, .inl (true, j))] (s + (wU j)) ⟨rfl, trivial⟩ rfl
  let R4 := fwT ((s + (wU j)) + (wU i)) [((s + (wU j)) + (wU i), .inr r)]
    (((s + Λ r) + (wU i)) + (wU j)) ⟨rfl, trivial⟩ h₃'
  let Ui4 := fwT (s + (wU j)) [(s + (wU j), .inl (true, i))] ((s + (wU j)) + (wU i))
    ⟨rfl, trivial⟩ rfl
  let R5 := fwT (s + (wU i)) [(s + (wU i), .inr r)] ((s + Λ r) + (wU i)) ⟨rfl, trivial⟩ g₃
  let Ui5 := fwT s [(s, .inl (true, i))] (s + (wU i)) ⟨rfl, trivial⟩ rfl
  let Uj6 := fwT (s + (wU i)) [(s + (wU i), .inl (true, j))] ((s + (wU j)) + (wU i))
    ⟨rfl, trivial⟩ e₅
  refine admissibleChain₃_heq (doubleModel S red) (genImg S red upIso Sc) _ _ ha hb rfl rfl
      (p₁ := 𝟙 _) (q₁ := R0) (x₁ := Uj ≫ Ui) (y₁ := Ui2 ≫ Uj2)
      (p₂ := Ui2) (q₂ := 𝟙 _) (x₂ := Uj2 ≫ R0) (y₂ := R3 ≫ Uj3)
      (p₃ := 𝟙 _) (q₃ := Uj3) (x₃ := Ui2 ≫ R3) (y₃ := R4 ≫ Ui4)
      (p₄ := Uj) (q₄ := 𝟙 _) (x₄ := Ui ≫ R0) (y₄ := R5 ≫ Ui5)
      (p₅ := 𝟙 _) (q₅ := Ui5) (x₅ := Uj ≫ R5) (y₅ := R4 ≫ Uj6)
      (p₆ := R4) (q₆ := 𝟙 _) (x₆ := Uj6 ≫ Ui5) (y₆ := Ui4 ≫ Uj3)
      (S.crossDn Sc i j hj hi hi' hj') (upIso r j h₁ rfl h₃ hj').hom
      (upIso r i h₁' h₃ h₃' hi').hom (upIso r i g₁ rfl g₃ hi).hom
      (upIso r j g₁' g₃ h₃' hj).hom (S.crossDn Sc i j g₁' g₁ h₁' h₁)
      ((α_ Uj Ui R0).symm ≪≫ (λ_ _).symm) ((λ_ _).hom ≫ (α_ _ _ _).hom ≫ Ui2 ◁ (ρ_ _).inv)
      (Ui2 ◁ (ρ_ _).hom ≫ (α_ _ _ _).inv ≫ (λ_ _).inv) (λ_ _ ≪≫ α_ R4 Ui4 Uj3)
      (whiskerLeftIso Uj (ρ_ (Ui ≫ R0)).symm) (Uj ◁ (ρ_ _).hom ≫ (α_ _ _ _).inv ≫ (λ_ _).inv)
      ((λ_ _).hom ≫ (α_ _ _ _).hom ≫ R4 ◁ (ρ_ _).inv) (whiskerLeftIso R4 (ρ_ (Ui4 ≫ Uj3)))
      ?hmain ?hn1 ?hm1 ?hr1 ?hl1 ?hd1 ?he1 ?hg1 ?hn2 ?hm2 ?hr2 ?hl2 ?hd2 ?he2 ?hg2 ?hn3 ?hm3 ?hr3 ?hl3 ?hd3 ?he3 ?hg3 ?hn4 ?hm4 ?hr4 ?hl4 ?hd4 ?he4 ?hg4 ?hn5 ?hm5 ?hr5 ?hl5 ?hd5 ?he5 ?hg5 ?hn6 ?hm6 ?hr6 ?hl6 ?hd6 ?he6 ?hg6
  case hmain =>
    have := slide3_right_hyp (doubleModel S red) (R0 := R0) (Ui := Ui) (Uj := Uj) (Ui2 := Ui2)
      (Uj2 := Uj2) (R3 := R3) (Uj3 := Uj3) (R4 := R4) (Ui4 := Ui4) (R5 := R5) (Ui5 := Ui5)
      (Uj6 := Uj6) (S.crossDn Sc i j hj hi hi' hj') (upIso r j h₁ rfl h₃ hj').hom
      (upIso r i h₁' h₃ h₃' hi').hom (upIso r i g₁ rfl g₃ hi).hom
      (upIso r j g₁' g₃ h₃' hj).hom (S.crossDn Sc i j g₁' g₁ h₁' h₁)
      (hcross r i j rfl hi hj hi' hj' h₁ h₃ h₁' h₃' g₁ g₃ g₁')
    convert this using 2
  case hg1 =>
    intro _ _ _ _
    refine (heq_of_eq (genImg_blackOn S red upIso Sc _ _ _ _ _ _ _ _ _ _)).trans ?_
    exact crossDn_heq S Sc i j (by double_regions) (by double_regions) _ _ _ _ _ _ _ _
  case hg6 =>
    intro _ _ _ _
    refine (heq_of_eq (genImg_blackOn S red upIso Sc _ _ _ _ _ _ _ _ _ _)).trans ?_
    exact crossDn_heq S Sc i j (by double_regions) (by double_regions) _ _ _ _ _ _ _ _
  case hg2 =>
    intro _ _ _ _
    exact upIso_hom_heq S red upIso r _ (by double_regions) (by double_regions)
      (by double_regions) (by double_regions) _ _ _ _ _ _ _ _
  case hg3 =>
    intro _ _ _ _
    exact upIso_hom_heq S red upIso r _ (by double_regions) (by double_regions)
      (by double_regions) (by double_regions) _ _ _ _ _ _ _ _
  case hg4 =>
    intro _ _ _ _
    exact upIso_hom_heq S red upIso r _ (by double_regions) (by double_regions)
      (by double_regions) (by double_regions) _ _ _ _ _ _ _ _
  case hg5 =>
    intro _ _ _ _
    exact upIso_hom_heq S red upIso r _ (by double_regions) (by double_regions)
      (by double_regions) (by double_regions) _ _ _ _ _ _ _ _
  case hn1 => double_regions
  case hm1 => double_regions
  case hr1 => intro _ _; double_nil
  case hl1 => intro _ _; double_single
  case hd1 => intro _ _; double_pair
  case he1 => intro _ _; double_pair
  case hn2 => double_regions
  case hm2 => double_regions
  case hr2 => intro _ _; double_single
  case hl2 => intro _ _; double_nil
  case hd2 => intro _ _; double_pair
  case he2 => intro _ _; double_pair
  case hn3 => double_regions
  case hm3 => double_regions
  case hr3 => intro _ _; double_nil
  case hl3 => intro _ _; double_single
  case hd3 => intro _ _; double_pair
  case he3 => intro _ _; double_pair
  case hn4 => double_regions
  case hm4 => double_regions
  case hr4 => intro _ _; double_single
  case hl4 => intro _ _; double_nil
  case hd4 => intro _ _; double_pair
  case he4 => intro _ _; double_pair
  case hn5 => double_regions
  case hm5 => double_regions
  case hr5 => intro _ _; double_nil
  case hl5 => intro _ _; double_single
  case hd5 => intro _ _; double_pair
  case he5 => intro _ _; double_pair
  case hn6 => double_regions
  case hm6 => double_regions
  case hr6 => intro _ _; double_single
  case hl6 => intro _ _; double_nil
  case hd6 => intro _ _; double_pair
  case he6 => intro _ _; double_pair

theorem genImg_redUpSlideMirror_cross (hcross : UpIsoCrossNatural S red upIso Sc) (i j : I)
    (r : Fin ℓ) {s t : X}
    (ha : Cond s t (obj RD Λ s ([] ++ upBlackWord (KLR.Diagram.Gen.cross i j).dom ++ [.inr r] ++
      [])))
    (hb : Cond s t (obj RD Λ s ([] ++ [.inr r] ++ upBlackWord (KLR.Diagram.Gen.cross i j).cod ++
      []))) :
    admissibleMap (k := k) (genImg S red upIso Sc) ha hb
        (LinDiagram.of (redUpSlideMirror RD Λ s [] r (.cross i j) [] true)) =
      admissibleMap (k := k) (genImg S red upIso Sc) ha hb
        (LinDiagram.of (redUpSlideMirror RD Λ s [] r (.cross i j) [] false)) := by
  obtain rfl : ((s + (wU i)) + (wU j)) + Λ r = t := ha.2.1
  rw [admissibleMap_of, admissibleMap_of]
  change admissibleChain _ _ _ _ _ _ _ = admissibleChain _ _ _ _ _ _ _
  dsimp only [ObjectProperty.homMk]
  rw [admissibleChain_congr _ (show Diagram.layers
        (redUpSlideMirror RD Λ s [] r (.cross i j) [] false) =
      [layer RD Λ s [] (.black (.cross true i j)) [.inr r],
        layer RD Λ s [.inl (true, j)] (.blackRed (true, i) r) [],
        layer RD Λ s [] (.blackRed (true, j) r) [.inl (true, i)]]
      by simp [redUpSlideMirror, upBlackMoveDiagram, upWordThroughRed, moveDiagram, upBlackWord,
        UpBlackMove.shape]; rfl),
    admissibleChain_congr _ (show Diagram.layers
        (redUpSlideMirror RD Λ s [] r (.cross i j) [] true) =
      [layer RD Λ s [.inl (true, i)] (.blackRed (true, j) r) [],
        layer RD Λ s [] (.blackRed (true, i) r) [.inl (true, j)],
        layer RD Λ s [.inr r] (.black (.cross true i j)) []]
      by simp [redUpSlideMirror, upBlackMoveDiagram, upWordThroughRed, moveDiagram, upBlackWord,
        UpBlackMove.shape]; rfl)]
  -- regions: `s i j r` at the bottom, `s r j i` at the top
  have hi : (s + Λ r) + RD.iX i = (s + (wU i)) + Λ r := by double_regions
  have hj : ((s + (wU i)) + Λ r) + RD.iX j = ((s + (wU i)) + (wU j)) + Λ r := by double_regions
  have hi' : ((s + Λ r) + (wU j)) + RD.iX i = ((s + (wU i)) + (wU j)) + Λ r := by
    double_regions
  have hj' : (s + Λ r) + RD.iX j = (s + Λ r) + (wU j) := by double_regions
  have h₁ : s + RD.iX j = s + (wU j) := by double_regions
  have h₃ : (s + (wU j)) + Λ r = (s + Λ r) + (wU j) := by double_regions
  have h₁' : (s + (wU j)) + RD.iX i = (s + (wU i)) + (wU j) := by double_regions
  have g₁ : s + RD.iX i = s + (wU i) := by double_regions
  have g₁' : (s + (wU i)) + RD.iX j = (s + (wU i)) + (wU j) := by double_regions
  have k₁ : ((s + (wU i)) + Λ r) + (wU j) = ((s + (wU i)) + (wU j)) + Λ r := by double_regions
  have k₂ : (s + Λ r) + (wU i) = (s + (wU i)) + Λ r := by double_regions
  have k₃ : ((s + Λ r) + (wU j)) + (wU i) = ((s + (wU i)) + (wU j)) + Λ r := by double_regions
  have k₄ : (s + (wU j)) + (wU i) = (s + (wU i)) + (wU j) := by double_regions
  let Ui := fwT s [(s, .inl (true, i))] (s + (wU i)) ⟨rfl, trivial⟩ rfl
  let Uj := fwT (s + (wU i)) [(s + (wU i), .inl (true, j))] ((s + (wU i)) + (wU j))
    ⟨rfl, trivial⟩ rfl
  let R := fwT ((s + (wU i)) + (wU j)) [((s + (wU i)) + (wU j), .inr r)]
    (((s + (wU i)) + (wU j)) + Λ r) ⟨rfl, trivial⟩ rfl
  let R' := fwT (s + (wU i)) [(s + (wU i), .inr r)] ((s + (wU i)) + Λ r) ⟨rfl, trivial⟩ rfl
  let Uj' := fwT ((s + (wU i)) + Λ r) [((s + (wU i)) + Λ r, .inl (true, j))]
    (((s + (wU i)) + (wU j)) + Λ r) ⟨rfl, trivial⟩ k₁
  let R'' := fwT s [(s, .inr r)] (s + Λ r) ⟨rfl, trivial⟩ rfl
  let Ui'' := fwT (s + Λ r) [(s + Λ r, .inl (true, i))] ((s + (wU i)) + Λ r) ⟨rfl, trivial⟩ k₂
  let Uj3 := fwT (s + Λ r) [(s + Λ r, .inl (true, j))] ((s + Λ r) + (wU j)) ⟨rfl, trivial⟩ rfl
  let Ui3 := fwT ((s + Λ r) + (wU j)) [((s + Λ r) + (wU j), .inl (true, i))]
    (((s + (wU i)) + (wU j)) + Λ r) ⟨rfl, trivial⟩ k₃
  let Uj4 := fwT s [(s, .inl (true, j))] (s + (wU j)) ⟨rfl, trivial⟩ rfl
  let Ui4 := fwT (s + (wU j)) [(s + (wU j), .inl (true, i))] ((s + (wU i)) + (wU j))
    ⟨rfl, trivial⟩ k₄
  let R5 := fwT (s + (wU j)) [(s + (wU j), .inr r)] ((s + Λ r) + (wU j)) ⟨rfl, trivial⟩ h₃
  refine admissibleChain₃_heq (doubleModel S red) (genImg S red upIso Sc) _ _ ha hb rfl rfl
      (p₁ := 𝟙 _) (q₁ := Ui) (x₁ := R ≫ Uj) (y₁ := Uj' ≫ R')
      (p₂ := Uj') (q₂ := 𝟙 _) (x₂ := R' ≫ Ui) (y₂ := Ui'' ≫ R'')
      (p₃ := 𝟙 _) (q₃ := R'') (x₃ := Uj' ≫ Ui'') (y₃ := Ui3 ≫ Uj3)
      (p₄ := R) (q₄ := 𝟙 _) (x₄ := Uj ≫ Ui) (y₄ := Ui4 ≫ Uj4)
      (p₅ := 𝟙 _) (q₅ := Uj4) (x₅ := R ≫ Ui4) (y₅ := Ui3 ≫ R5)
      (p₆ := Ui3) (q₆ := 𝟙 _) (x₆ := R5 ≫ Uj4) (y₆ := Uj3 ≫ R'')
      (upIso r j g₁' rfl rfl hj).inv (upIso r i g₁ rfl rfl hi).inv
      (S.crossDn Sc i j hj hi hi' hj') (S.crossDn Sc i j g₁' g₁ h₁' h₁)
      (upIso r i h₁' h₃ rfl hi').inv (upIso r j h₁ rfl h₃ hj').inv
      ((α_ R Uj Ui).symm ≪≫ (λ_ _).symm) ((λ_ _).hom ≫ (α_ _ _ _).hom ≫ Uj' ◁ (ρ_ _).inv)
      (Uj' ◁ (ρ_ _).hom ≫ (α_ _ _ _).inv ≫ (λ_ _).inv) (λ_ _ ≪≫ α_ Ui3 Uj3 R'')
      (whiskerLeftIso R (ρ_ (Uj ≫ Ui)).symm) (R ◁ (ρ_ _).hom ≫ (α_ _ _ _).inv ≫ (λ_ _).inv)
      ((λ_ _).hom ≫ (α_ _ _ _).hom ≫ Ui3 ◁ (ρ_ _).inv) (whiskerLeftIso Ui3 (ρ_ (Uj3 ≫ R'')))
      ?hmain ?hn1 ?hm1 ?hr1 ?hl1 ?hd1 ?he1 ?hg1 ?hn2 ?hm2 ?hr2 ?hl2 ?hd2 ?he2 ?hg2 ?hn3 ?hm3 ?hr3 ?hl3 ?hd3 ?he3 ?hg3 ?hn4 ?hm4 ?hr4 ?hl4 ?hd4 ?he4 ?hg4 ?hn5 ?hm5 ?hr5 ?hl5 ?hd5 ?he5 ?hg5 ?hn6 ?hm6 ?hr6 ?hl6 ?hd6 ?he6 ?hg6
  case hmain =>
    have hc := hcross r i j rfl hi hj hi' hj' h₁ h₃ h₁' rfl g₁ rfl g₁'
    let P := whiskerLeftIso (S.F i hi') (upIso r j h₁ rfl h₃ hj') ≪≫ (α_ _ _ _).symm ≪≫
      whiskerRightIso (upIso r i h₁' h₃ rfl hi') (S.F j h₁) ≪≫ α_ _ _ _
    let Q := whiskerLeftIso (S.F j hj) (upIso r i g₁ rfl rfl hi) ≪≫ (α_ _ _ _).symm ≪≫
      whiskerRightIso (upIso r j g₁' rfl rfl hj) (S.F i g₁) ≪≫ α_ _ _ _
    have hc' : ((α_ _ _ _).inv ≫ S.crossDn Sc i j hj hi hi' hj' ▷ red r rfl ≫ (α_ _ _ _).hom) ≫
        P.hom = Q.hom ≫ red r rfl ◁ S.crossDn Sc i j g₁' g₁ h₁' h₁ := by
      simp only [P, Q, Iso.trans_hom, whiskerLeftIso_hom, Iso.symm_hom, whiskerRightIso_hom,
        Category.assoc]
      exact hc
    have key : Q.inv ≫ ((α_ _ _ _).inv ≫ S.crossDn Sc i j hj hi hi' hj' ▷ red r rfl ≫
        (α_ _ _ _).hom) = red r rfl ◁ S.crossDn Sc i j g₁' g₁ h₁' h₁ ≫ P.inv := by
      rw [Iso.inv_comp_eq, ← reassoc_of% hc', Iso.hom_inv_id, Category.comp_id]
    simp only [P, Q, Iso.trans_inv, whiskerLeftIso_inv, Iso.symm_inv, whiskerRightIso_inv,
      Category.assoc] at key
    have := slide3_left_hyp (doubleModel S red) (R := R) (Uj := Uj) (Ui := Ui) (Uj' := Uj')
      (R' := R') (Ui'' := Ui'') (R'' := R'') (Ui3 := Ui3) (Uj3 := Uj3) (Ui4 := Ui4) (Uj4 := Uj4)
      (R5 := R5) (upIso r j g₁' rfl rfl hj).inv (upIso r i g₁ rfl rfl hi).inv
      (S.crossDn Sc i j hj hi hi' hj') (S.crossDn Sc i j g₁' g₁ h₁' h₁)
      (upIso r i h₁' h₃ rfl hi').inv (upIso r j h₁ rfl h₃ hj').inv key
    convert this using 2
  case hg3 =>
    intro _ _ _ _
    refine (heq_of_eq (genImg_blackOn S red upIso Sc _ _ _ _ _ _ _ _ _ _)).trans ?_
    exact crossDn_heq S Sc i j (by double_regions) (by double_regions) _ _ _ _ _ _ _ _
  case hg4 =>
    intro _ _ _ _
    refine (heq_of_eq (genImg_blackOn S red upIso Sc _ _ _ _ _ _ _ _ _ _)).trans ?_
    exact crossDn_heq S Sc i j (by double_regions) (by double_regions) _ _ _ _ _ _ _ _
  case hg1 =>
    intro _ _ _ _
    exact upIso_inv_heq S red upIso r _ (by double_regions) (by double_regions)
      (by double_regions) (by double_regions) _ _ _ _ _ _ _ _
  case hg2 =>
    intro _ _ _ _
    exact upIso_inv_heq S red upIso r _ (by double_regions) (by double_regions)
      (by double_regions) (by double_regions) _ _ _ _ _ _ _ _
  case hg5 =>
    intro _ _ _ _
    exact upIso_inv_heq S red upIso r _ (by double_regions) (by double_regions)
      (by double_regions) (by double_regions) _ _ _ _ _ _ _ _
  case hg6 =>
    intro _ _ _ _
    exact upIso_inv_heq S red upIso r _ (by double_regions) (by double_regions)
      (by double_regions) (by double_regions) _ _ _ _ _ _ _ _
  case hn1 => double_regions
  case hm1 => double_regions
  case hr1 => intro _ _; double_nil
  case hl1 => intro _ _; double_single
  case hd1 => intro _ _; double_pair
  case he1 => intro _ _; double_pair
  case hn2 => double_regions
  case hm2 => double_regions
  case hr2 => intro _ _; double_single
  case hl2 => intro _ _; double_nil
  case hd2 => intro _ _; double_pair
  case he2 => intro _ _; double_pair
  case hn3 => double_regions
  case hm3 => double_regions
  case hr3 => intro _ _; double_nil
  case hl3 => intro _ _; double_single
  case hd3 => intro _ _; double_pair
  case he3 => intro _ _; double_pair
  case hn4 => double_regions
  case hm4 => double_regions
  case hr4 => intro _ _; double_single
  case hl4 => intro _ _; double_nil
  case hd4 => intro _ _; double_pair
  case he4 => intro _ _; double_pair
  case hn5 => double_regions
  case hm5 => double_regions
  case hr5 => intro _ _; double_nil
  case hl5 => intro _ _; double_single
  case hd5 => intro _ _; double_pair
  case he5 => intro _ _; double_pair
  case hn6 => double_regions
  case hm6 => double_regions
  case hr6 => intro _ _; double_single
  case hl6 => intro _ _; double_nil
  case hd6 => intro _ _; double_pair
  case he6 => intro _ _; double_pair

end Categorification.Stendhal.DoubleDiagram
