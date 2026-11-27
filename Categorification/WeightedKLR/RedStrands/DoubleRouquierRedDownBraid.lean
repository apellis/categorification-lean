/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleRouquierRedDownBigon
import Categorification.WeightedKLR.RedStrands.DoubleRouquierRedUpSlide

/-!
# Downward triple points with one red strand in a Rouquier family

Webster, arXiv:1309.3796v3, (4.1a–c) in the proof of Theorem 4.25, read downward. A downward
braid relation `ψ₀ψ₁ψ₀ = ψ₁ψ₀ψ₁` on three strands one of which is red is killed by the generator
images `genImg` as soon as the red/down crossings `a′` (`redDownQuot`) and `b′`
(`redDownDot`) are natural for the downward black crossing in the corresponding position
(`DownDotCrossNatural`, `DownQuotCrossNatural`, `DownMidCrossNatural`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory CategoryTheory.Bicategory QuantumGroup QuantumGroup.UDot KL3.Diagram
  StringDiagrams TwoRep Diagrams.BicatInterp

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {ℓ : ℕ} {Λ : Fin ℓ → X}

section Alg

variable {B' : Type*} [Bicategory B'] [∀ a b : B', Preadditive (a ⟶ b)]
  {k : Type w} [CommRing k] [∀ a b : B', Linear k (a ⟶ b)]
  {M : Model (signature RD Λ) B'} (G : GenImg M)

/-- The translation of three downward layers is a signed diagram with the three translated
layers. -/
theorem downLinear_dl3 (s : X) (l₁ r₁ l₂ r₂ l₃ r₃ : List (I ⊕ Fin ℓ))
    (g₁ g₂ g₃ : KLR.Diagram.Gen (I ⊕ Fin ℓ)) {mv₁ mv₂ mv₃ : Move I ℓ}
    (hm₁ : downMove g₁ = some mv₁) (hm₂ : downMove g₂ = some mv₂) (hm₃ : downMove g₃ = some mv₃)
    {a b c d : Obj (KLR.Diagram.sig (I ⊕ Fin ℓ))}
    (e₁ : l₁ ++ g₁.dom ++ r₁ = a.word) (e₁' : l₁ ++ g₁.cod ++ r₁ = b.word)
    (e₂ : l₂ ++ g₂.dom ++ r₂ = b.word) (e₂' : l₂ ++ g₂.cod ++ r₂ = c.word)
    (e₃ : l₃ ++ g₃.dom ++ r₃ = c.word) (e₃' : l₃ ++ g₃.cod ++ r₃ = d.word) :
    ∃ D : downContextObj RD Λ s [] [] a ⟶ downContextObj RD Λ s [] [] d,
      Diagram.layers D =
        [layer RD Λ s ([] ++ l₁.map DoubleStrand.down) mv₁ (r₁.map DoubleStrand.down ++ []),
          layer RD Λ s ([] ++ l₂.map DoubleStrand.down) mv₂ (r₂.map DoubleStrand.down ++ []),
          layer RD Λ s ([] ++ l₃.map DoubleStrand.down) mv₃ (r₃.map DoubleStrand.down ++ [])] ∧
      downLinear RD Λ k s [] [] (LinDiagram.of
        (KLR.Diagram.dl l₁ g₁ r₁ e₁ e₁' ≫ KLR.Diagram.dl l₂ g₂ r₂ e₂ e₂' ≫
          KLR.Diagram.dl l₃ g₃ r₃ e₃ e₃')) = LinDiagram.of D := by
  rw [LinDiagram.of_comp, LinDiagram.of_comp, downLinear_comp, downLinear_comp]
  simp only [KLR.Diagram.dl]
  rw [downLinear_layer, downLinear_layer, downLinear_layer,
    downLinearLayer_of_move RD Λ k s [] [] (KLR.Diagram.lay l₁ g₁ r₁) hm₁,
    downLinearLayer_of_move RD Λ k s [] [] (KLR.Diagram.lay l₂ g₂ r₂) hm₂,
    downLinearLayer_of_move RD Λ k s [] [] (KLR.Diagram.lay l₃ g₃ r₃) hm₃,
    LinDiagram.cast_of, LinDiagram.cast_of, LinDiagram.cast_of, ← LinDiagram.of_comp,
    ← LinDiagram.of_comp]
  exact ⟨_, by simp, rfl⟩

end Alg

local notation "fwT" => fw (S := signature RD Λ)
local notation "wD" i => DoubleStrand.weight RD Λ (Sum.inl (false, i))

variable {B : Type*} [Bicategory B] [∀ a b : B, Preadditive (a ⟶ b)] [AdditiveWhiskering B]
  {k : Type w} [CommRing k] [∀ a b : B, Linear k (a ⟶ b)]
  (S : RouqFamily (B := B) RD)
  (red : (r : Fin ℓ) → {x y : X} → x + Λ r = y → (S.obj y ⟶ S.obj x))
  (upIso : (r : Fin ℓ) → (i : I) → {μ μ₁ μ₂ μ₃ : X} → (h₁ : μ + RD.iX i = μ₁) →
    (h₂ : μ + Λ r = μ₂) → (h₃ : μ₁ + Λ r = μ₃) → (h₄ : μ₂ + RD.iX i = μ₃) →
    (S.F i h₄ ≫ red r h₂ ≅ red r h₃ ≫ S.F i h₁))
  (Sc : CL.CLScalars C k)

/-- **The crossing `b′` is natural for a downward crossing to its right** (Webster,
arXiv:1309.3796v3, (4.1) read downward, with the red strand on the left): a red strand passing
to the right of two downward strands commutes with their crossing. -/
def DownDotCrossNatural : Prop :=
  ∀ (r : Fin ℓ) (i j : I) {μ ρ ρi ρj ν μi μj μij : X} (hr : μ + Λ r = ρ)
    (hi : ρi + RD.iX i = ρ) (hj : ν + RD.iX j = ρi) (hi' : ν + RD.iX i = ρj)
    (hj' : ρj + RD.iX j = ρ) (g₁ : μj + RD.iX j = μ) (g₃ : μj + Λ r = ρj)
    (k₁ : μij + RD.iX i = μj) (k₃ : μij + Λ r = ν) (f₁ : μi + RD.iX i = μ)
    (f₃ : μi + Λ r = ρi) (f₁' : μij + RD.iX j = μi),
    (α_ _ _ _).inv ≫ S.cross i j hj hi hi' hj' ▷ red r hr ≫ (α_ _ _ _).hom ≫
        S.E i hi' ◁ redDownDot S red upIso r j g₁ g₃ hr hj' ≫ (α_ _ _ _).inv ≫
        redDownDot S red upIso r i k₁ k₃ g₃ hi' ▷ S.E j g₁ ≫ (α_ _ _ _).hom =
      S.E j hj ◁ redDownDot S red upIso r i f₁ f₃ hr hi ≫ (α_ _ _ _).inv ≫
        redDownDot S red upIso r j f₁' k₃ f₃ hj ▷ S.E i f₁ ≫ (α_ _ _ _).hom ≫
        red r k₃ ◁ S.cross i j f₁' f₁ k₁ g₁

theorem cross_dn_heq (z : X) (i j : I) {a b : X} (ha hb hd hde hc hce) {a' b' c' d' : X}
    (hx : a = d') (hy : b = a') (h₁ : a' + RD.iX j = b') (h₂ : b' + RD.iX i = d')
    (h₃ : a' + RD.iX i = c') (h₄ : c' + RD.iX j = d') :
    blackImg S red Sc z (.cross false i j) a b ha hb hd hde hc hce ≍ S.cross i j h₁ h₂ h₃ h₄ := by
  subst hx hy
  exact cross_heq S i j rfl rfl _ _ _ _ h₁ h₂ h₃ h₄

variable {S red upIso}

/-- **The downward braid `[r, i, j]`** is killed by the generator images. -/
theorem admissibleMap_braid_rbb (hn : DownDotCrossNatural S red upIso)
    (Q : I ⊕ Fin ℓ → I ⊕ Fin ℓ → MvPolynomial (Fin 2) k) (r : Fin ℓ) (i j : I)
    (h : ¬ ((Sum.inr r : I ⊕ Fin ℓ) = .inl j ∧ (Sum.inr r : I ⊕ Fin ℓ) ≠ .inl i))
    (m : X) {x y : X}
    (ha : Cond x y (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inr r, .inl i, .inl j])))
    (hb : Cond x y (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inl j, .inl i, .inr r]))) :
    admissibleMap (genImg S red upIso Sc) ha hb (downLinear RD Λ k m [] []
      (KLR.Diagram.relation k Q (.braid (.inr r) (.inl i) (.inl j) h))) = 0 := by
  obtain rfl : m = x := ha.2.2
  obtain rfl : ((m + Λ r) + (wD i)) + (wD j) = y := ha.2.1
  rw [relation_braid, map_sub, map_sub, sub_eq_zero]
  obtain ⟨D, hD, eD⟩ := downLinear_dl3 (RD := RD) (Λ := Λ) (k := k) m [] [.inl j] [.inl i] [] [] [.inr r]
    (.cross (.inr r) (.inl i)) (.cross (.inr r) (.inl j)) (.cross (.inl i) (.inl j))
    rfl rfl rfl (a := KLR.Diagram.ob [.inr r, .inl i, .inl j])
    (b := KLR.Diagram.ob [.inl i, .inr r, .inl j]) (c := KLR.Diagram.ob [.inl i, .inl j, .inr r])
    (d := KLR.Diagram.ob [.inl j, .inl i, .inr r]) rfl rfl rfl rfl rfl rfl
  obtain ⟨D', hD', eD'⟩ := downLinear_dl3 (RD := RD) (Λ := Λ) (k := k) m [.inr r] [] [] [.inl i] [.inl j] []
    (.cross (.inl i) (.inl j)) (.cross (.inr r) (.inl j)) (.cross (.inr r) (.inl i))
    rfl rfl rfl (a := KLR.Diagram.ob [.inr r, .inl i, .inl j])
    (b := KLR.Diagram.ob [.inr r, .inl j, .inl i]) (c := KLR.Diagram.ob [.inl j, .inr r, .inl i])
    (d := KLR.Diagram.ob [.inl j, .inl i, .inr r]) rfl rfl rfl rfl rfl rfl
  erw [eD, eD', admissibleMap_of, admissibleMap_of]
  change admissibleChain _ _ _ _ _ _ _ = admissibleChain _ _ _ _ _ _ _
  dsimp only [ObjectProperty.homMk]
  simp only [List.map_cons, List.map_nil, DoubleStrand.down, List.nil_append,
    List.append_nil] at hD hD'
  rw [admissibleChain_congr _ hD, admissibleChain_congr _ hD']
  symm
  have hi : ((m + Λ r) + (wD i)) + RD.iX i = m + Λ r := by double_regions
  have hj : (((m + Λ r) + (wD i)) + (wD j)) + RD.iX j = (m + Λ r) + (wD i) := by double_regions
  have hi' : (((m + Λ r) + (wD i)) + (wD j)) + RD.iX i = (m + Λ r) + (wD j) := by
    double_regions
  have hj' : ((m + Λ r) + (wD j)) + RD.iX j = m + Λ r := by double_regions
  have g₁ : (m + (wD j)) + RD.iX j = m := by double_regions
  have h₃ : (m + (wD j)) + Λ r = (m + Λ r) + (wD j) := by double_regions
  have k₁ : ((m + (wD j)) + (wD i)) + RD.iX i = m + (wD j) := by double_regions
  have h₃' : ((m + (wD j)) + (wD i)) + Λ r = ((m + Λ r) + (wD i)) + (wD j) := by
    double_regions
  have f₁ : (m + (wD i)) + RD.iX i = m := by double_regions
  have g₃ : (m + (wD i)) + Λ r = (m + Λ r) + (wD i) := by double_regions
  have f₁' : ((m + (wD j)) + (wD i)) + RD.iX j = m + (wD i) := by double_regions
  have e₁ : ((m + Λ r) + (wD j)) + (wD i) = ((m + Λ r) + (wD i)) + (wD j) := by double_regions
  have e₅ : (m + (wD i)) + (wD j) = (m + (wD j)) + (wD i) := by double_regions
  let R0 := fwT m [(m, .inr r)] (m + Λ r) ⟨rfl, trivial⟩ rfl
  let Ui := fwT (m + Λ r) [(m + Λ r, .inl (false, i))] ((m + Λ r) + (wD i)) ⟨rfl, trivial⟩ rfl
  let Uj := fwT ((m + Λ r) + (wD i)) [((m + Λ r) + (wD i), .inl (false, j))]
    (((m + Λ r) + (wD i)) + (wD j)) ⟨rfl, trivial⟩ rfl
  let Ui2 := fwT ((m + Λ r) + (wD j)) [((m + Λ r) + (wD j), .inl (false, i))]
    (((m + Λ r) + (wD i)) + (wD j)) ⟨rfl, trivial⟩ e₁
  let Uj2 := fwT (m + Λ r) [(m + Λ r, .inl (false, j))] ((m + Λ r) + (wD j)) ⟨rfl, trivial⟩ rfl
  let R3 := fwT (m + (wD j)) [(m + (wD j), .inr r)] ((m + Λ r) + (wD j)) ⟨rfl, trivial⟩ h₃
  let Uj3 := fwT m [(m, .inl (false, j))] (m + (wD j)) ⟨rfl, trivial⟩ rfl
  let R4 := fwT ((m + (wD j)) + (wD i)) [((m + (wD j)) + (wD i), .inr r)]
    (((m + Λ r) + (wD i)) + (wD j)) ⟨rfl, trivial⟩ h₃'
  let Ui4 := fwT (m + (wD j)) [(m + (wD j), .inl (false, i))] ((m + (wD j)) + (wD i))
    ⟨rfl, trivial⟩ rfl
  let R5 := fwT (m + (wD i)) [(m + (wD i), .inr r)] ((m + Λ r) + (wD i)) ⟨rfl, trivial⟩ g₃
  let Ui5 := fwT m [(m, .inl (false, i))] (m + (wD i)) ⟨rfl, trivial⟩ rfl
  let Uj6 := fwT (m + (wD i)) [(m + (wD i), .inl (false, j))] ((m + (wD j)) + (wD i))
    ⟨rfl, trivial⟩ e₅
  refine admissibleChain₃_heq (doubleModel S red) (genImg S red upIso Sc) _ _ ha hb rfl rfl
      (p₁ := 𝟙 _) (q₁ := R0) (x₁ := Uj ≫ Ui) (y₁ := Ui2 ≫ Uj2)
      (p₂ := Ui2) (q₂ := 𝟙 _) (x₂ := Uj2 ≫ R0) (y₂ := R3 ≫ Uj3)
      (p₃ := 𝟙 _) (q₃ := Uj3) (x₃ := Ui2 ≫ R3) (y₃ := R4 ≫ Ui4)
      (p₄ := Uj) (q₄ := 𝟙 _) (x₄ := Ui ≫ R0) (y₄ := R5 ≫ Ui5)
      (p₅ := 𝟙 _) (q₅ := Ui5) (x₅ := Uj ≫ R5) (y₅ := R4 ≫ Uj6)
      (p₆ := R4) (q₆ := 𝟙 _) (x₆ := Uj6 ≫ Ui5) (y₆ := Ui4 ≫ Uj3)
      (S.cross i j hj hi hi' hj') (redDownDot S red upIso r j g₁ h₃ rfl hj')
      (redDownDot S red upIso r i k₁ h₃' h₃ hi') (redDownDot S red upIso r i f₁ g₃ rfl hi)
      (redDownDot S red upIso r j f₁' h₃' g₃ hj) (S.cross i j f₁' f₁ k₁ g₁)
      ((α_ Uj Ui R0).symm ≪≫ (λ_ _).symm) ((λ_ _).hom ≫ (α_ _ _ _).hom ≫ Ui2 ◁ (ρ_ _).inv)
      (Ui2 ◁ (ρ_ _).hom ≫ (α_ _ _ _).inv ≫ (λ_ _).inv) (λ_ _ ≪≫ α_ R4 Ui4 Uj3)
      (whiskerLeftIso Uj (ρ_ (Ui ≫ R0)).symm) (Uj ◁ (ρ_ _).hom ≫ (α_ _ _ _).inv ≫ (λ_ _).inv)
      ((λ_ _).hom ≫ (α_ _ _ _).hom ≫ R4 ◁ (ρ_ _).inv) (whiskerLeftIso R4 (ρ_ (Ui4 ≫ Uj3)))
      ?hmain ?hn1 ?hm1 ?hr1 ?hl1 ?hd1 ?he1 ?hg1 ?hn2 ?hm2 ?hr2 ?hl2 ?hd2 ?he2 ?hg2 ?hn3 ?hm3 ?hr3
      ?hl3 ?hd3 ?he3 ?hg3 ?hn4 ?hm4 ?hr4 ?hl4 ?hd4 ?he4 ?hg4 ?hn5 ?hm5 ?hr5 ?hl5 ?hd5 ?he5 ?hg5
      ?hn6 ?hm6 ?hr6 ?hl6 ?hd6 ?he6 ?hg6
  case hmain =>
    have := slide3_right_hyp (doubleModel S red) (R0 := R0) (Ui := Ui) (Uj := Uj) (Ui2 := Ui2)
      (Uj2 := Uj2) (R3 := R3) (Uj3 := Uj3) (R4 := R4) (Ui4 := Ui4) (R5 := R5) (Ui5 := Ui5)
      (Uj6 := Uj6) (S.cross i j hj hi hi' hj') (redDownDot S red upIso r j g₁ h₃ rfl hj')
      (redDownDot S red upIso r i k₁ h₃' h₃ hi') (redDownDot S red upIso r i f₁ g₃ rfl hi)
      (redDownDot S red upIso r j f₁' h₃' g₃ hj) (S.cross i j f₁' f₁ k₁ g₁)
      (hn r i j rfl hi hj hi' hj' g₁ h₃ k₁ h₃' f₁ g₃ f₁')
    convert this using 2
  case hg1 =>
    intro _ _ _ _
    refine (heq_of_eq (genImg_blackOn S red upIso Sc _ _ _ _ _ _ _ _ _ _)).trans ?_
    exact cross_dn_heq S red Sc _ i j _ _ _ _ _ _ (by double_regions) (by double_regions) _ _ _ _
  case hg6 =>
    intro _ _ _ _
    refine (heq_of_eq (genImg_blackOn S red upIso Sc _ _ _ _ _ _ _ _ _ _)).trans ?_
    exact cross_dn_heq S red Sc _ i j _ _ _ _ _ _ (by double_regions) (by double_regions) _ _ _ _
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
  case hg2 =>
    intro _ _ _ _
    exact redDownDot_heq S red upIso r _ (by double_regions) (by double_regions)
      (by double_regions) (by double_regions) _ _ _ _ _ _ _ _
  case hg3 =>
    intro _ _ _ _
    exact redDownDot_heq S red upIso r _ (by double_regions) (by double_regions)
      (by double_regions) (by double_regions) _ _ _ _ _ _ _ _
  case hg4 =>
    intro _ _ _ _
    exact redDownDot_heq S red upIso r _ (by double_regions) (by double_regions)
      (by double_regions) (by double_regions) _ _ _ _ _ _ _ _
  case hg5 =>
    intro _ _ _ _
    exact redDownDot_heq S red upIso r _ (by double_regions) (by double_regions)
      (by double_regions) (by double_regions) _ _ _ _ _ _ _ _

end Categorification.Stendhal.DoubleDiagram
