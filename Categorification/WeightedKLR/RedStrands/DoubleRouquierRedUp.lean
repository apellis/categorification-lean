/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleRouquierRedCup
import Categorification.WeightedKLR.RedStrands.DoubleRedUp

/-!
# The red/upward bigons in the double model of a Rouquier family

Webster, arXiv:1309.3796v3, (4.4e), in the proof of Theorem 4.25. The red/upward crossings of
the generator images `genImg` are the two directions of the isomorphism `upIso`, so both red/upward
bigons act as identities (`genImg_redUpBigon`). The general step is `pair_merge`: two layers with
the same surrounding strands whose generator images compose to the identity act as the identity.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Diagrams.BicatInterp

open CategoryTheory Bicategory StringDiagrams

variable {S : Signature} {C : Type*} [Bicategory C] (M : Model S C)

/-- **Two inverse layers cancel.** Two layers with the same surrounding 1-morphisms `p`, `q`, the
first from `x` to `y` and the second from `y` back to `x`, whose generator images compose to the
identity, have the identity as their composite image. The pieces of the layers agree with the
canonical ones up to equality of regions and heterogeneous equality. -/
theorem pair_merge {a₀ a₁ b c : FB S} {p : a₀ ⟶ b} {q : c ⟶ a₁} {x y : b ⟶ c}
    {n₁ m₁ n₂ m₂ : FB S} {p₁ : a₀ ⟶ n₁} {q₁ : m₁ ⟶ a₁} {d₁ c₁ : n₁ ⟶ m₁}
    {p₂ : a₀ ⟶ n₂} {q₂ : m₂ ⟶ a₁} {d₂ c₂ : n₂ ⟶ m₂}
    (hn₁ : n₁ = b) (hm₁ : m₁ = c) (hn₂ : n₂ = b) (hm₂ : m₂ = c)
    (hp₁ : p₁ ≍ p) (hq₁ : q₁ ≍ q) (hd₁ : d₁ ≍ x) (hc₁ : c₁ ≍ y)
    (hp₂ : p₂ ≍ p) (hq₂ : q₂ ≍ q) (hd₂ : d₂ ≍ y) (hc₂ : c₂ ≍ x)
    (g₁ : M.lift.map d₁ ⟶ M.lift.map c₁) (g₂ : M.lift.map d₂ ⟶ M.lift.map c₂)
    (γ₁ : M.lift.map x ⟶ M.lift.map y) (γ₂ : M.lift.map y ⟶ M.lift.map x)
    (hg₁ : g₁ ≍ γ₁) (hg₂ : g₂ ≍ γ₂) (hγ : γ₁ ≫ γ₂ = 𝟙 _)
    {P P₁ Q₁ P₂ Q₂ : a₀ ⟶ a₁}
    (E₀ : P ⟶ P₁) (A₁ : P₁ ⟶ p₁ ≫ (d₁ ≫ q₁)) (B₁ : p₁ ≫ (c₁ ≫ q₁) ⟶ Q₁) (E₁ : Q₁ ⟶ P₂)
    (A₂ : P₂ ⟶ p₂ ≫ (d₂ ≫ q₂)) (B₂ : p₂ ≫ (c₂ ≫ q₂) ⟶ Q₂) (E₂ : Q₂ ⟶ P) :
    M.lift.map₂ E₀ ≫ (M.lift.map₂ A₁ ≫ midK M p₁ q₁ g₁ ≫ M.lift.map₂ B₁) ≫ M.lift.map₂ E₁ ≫
        (M.lift.map₂ A₂ ≫ midK M p₂ q₂ g₂ ≫ M.lift.map₂ B₂) ≫ M.lift.map₂ E₂ = 𝟙 _ := by
  subst hn₁ hm₁ hn₂ hm₂
  obtain rfl := eq_of_heq hp₁; obtain rfl := eq_of_heq hq₁; obtain rfl := eq_of_heq hd₁
  obtain rfl := eq_of_heq hc₁; obtain rfl := eq_of_heq hp₂; obtain rfl := eq_of_heq hq₂
  obtain rfl := eq_of_heq hd₂; obtain rfl := eq_of_heq hc₂
  obtain rfl := eq_of_heq hg₁; obtain rfl := eq_of_heq hg₂
  have hmid : M.lift.map₂ B₁ ≫ M.lift.map₂ E₁ ≫ M.lift.map₂ A₂ = 𝟙 _ := by
    rw [← PrelaxFunctor.map₂_comp, ← PrelaxFunctor.map₂_comp, ← PrelaxFunctor.map₂_id]
    exact lift_map₂_eq M _ _
  have hout : M.lift.map₂ E₀ ≫ M.lift.map₂ A₁ ≫ M.lift.map₂ B₂ ≫ M.lift.map₂ E₂ = 𝟙 _ := by
    rw [← PrelaxFunctor.map₂_comp, ← PrelaxFunctor.map₂_comp, ← PrelaxFunctor.map₂_comp,
      ← PrelaxFunctor.map₂_id]
    exact lift_map₂_eq M _ _
  simp only [Category.assoc]
  rw [reassoc_of% hmid]
  rw [← reassoc_of% (midK_comp M _ _ g₁ g₂), hγ, midK_id, Category.id_comp]
  simpa only [Category.assoc] using hout

end Categorification.Diagrams.BicatInterp

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

theorem genImg_redUpBigon_redLeft (i : I) (r : Fin ℓ) {s t : X}
    (ha : Cond s t (obj RD Λ s (RedUpSide.redLeft.move r i).bottom)) :
    admissibleMap (k := k) (genImg S red upIso Sc) ha ha
        (LinDiagram.of (bareBigon RD Λ s r i .redLeft)) =
      admissibleMap (k := k) (genImg S red upIso Sc) ha ha (LinDiagram.of (𝟙 _)) := by
  obtain rfl : (s + Λ r) + (wU i) = t := ha.2.1
  rw [admissibleMap_of, admissibleMap_of]
  change admissibleChain _ _ _ _ _ _ _ = 𝟙 _
  dsimp only [ObjectProperty.homMk]
  rw [admissibleChain_congr _ (show Diagram.layers (bareBigon RD Λ s r i .redLeft) =
      [layer RD Λ s [] (.redBlack r (true, i)) [], layer RD Λ s [] (.blackRed (true, i) r) []]
      by simp [bareBigon, RedUpSide.bigon, moveDiagram])]
  rw [admissibleChain_pair, coreC_eq, coreC_eq]
  unfold core
  have h₁ : s + RD.iX i = (s + (wU i)) := by double_regions
  have h₄ : (s + Λ r) + RD.iX i = ((s + Λ r) + (wU i)) := by double_regions
  have h₃ : (s + (wU i)) + Λ r = ((s + Λ r) + (wU i)) := by double_regions
  refine pair_merge (doubleModel S red)
      (p := 𝟙 (fo ((s + Λ r) + (wU i)))) (q := 𝟙 (fo s))
      (x := fwT (s + Λ r) [(s + Λ r, .inl (true, i))] ((s + Λ r) + (wU i)) ⟨rfl, trivial⟩ rfl ≫
        fwT s [(s, .inr r)] (s + Λ r) ⟨rfl, trivial⟩ rfl)
      (y := fwT (s + (wU i)) [((s + (wU i)), .inr r)] ((s + Λ r) + (wU i)) ⟨rfl, trivial⟩ h₃ ≫
        fwT s [(s, .inl (true, i))] (s + (wU i)) ⟨rfl, trivial⟩ rfl)
      ?hn₁ ?hm₁ ?hn₂ ?hm₂ ?hp₁ ?hq₁ ?hd₁ ?hc₁ ?hp₂ ?hq₂ ?hd₂ ?hc₂ _ _
      (upIso r i h₁ rfl h₃ h₄).hom (upIso r i h₁ rfl h₃ h₄).inv ?hg₁ ?hg₂
      (Iso.hom_inv_id _) _ _ _ _ _ _ _
  case hg₁ =>
    exact upIso_hom_heq S red upIso r i (by double_regions) (by double_regions)
      (by double_regions) (by double_regions) _ _ _ _ _ _ _ _
  case hg₂ =>
    exact upIso_inv_heq S red upIso r i (by double_regions) (by double_regions)
      (by double_regions) (by double_regions) _ _ _ _ _ _ _ _
  case hn₁ => double_regions
  case hm₁ => double_regions
  case hn₂ => double_regions
  case hm₂ => double_regions
  case hp₁ => double_nil
  case hq₁ => double_nil
  case hd₁ => double_pair
  case hc₁ => double_pair
  case hp₂ => double_nil
  case hq₂ => double_nil
  case hd₂ => double_pair
  case hc₂ => double_pair

theorem genImg_redUpBigon_upLeft (i : I) (r : Fin ℓ) {s t : X}
    (ha : Cond s t (obj RD Λ s (RedUpSide.upLeft.move r i).bottom)) :
    admissibleMap (k := k) (genImg S red upIso Sc) ha ha
        (LinDiagram.of (bareBigon RD Λ s r i .upLeft)) =
      admissibleMap (k := k) (genImg S red upIso Sc) ha ha (LinDiagram.of (𝟙 _)) := by
  obtain rfl : (s + (wU i)) + Λ r = t := ha.2.1
  rw [admissibleMap_of, admissibleMap_of]
  change admissibleChain _ _ _ _ _ _ _ = 𝟙 _
  dsimp only [ObjectProperty.homMk]
  rw [admissibleChain_congr _ (show Diagram.layers (bareBigon RD Λ s r i .upLeft) =
      [layer RD Λ s [] (.blackRed (true, i) r) [], layer RD Λ s [] (.redBlack r (true, i)) []]
      by simp [bareBigon, RedUpSide.bigon, moveDiagram])]
  rw [admissibleChain_pair, coreC_eq, coreC_eq]
  unfold core
  have h₁ : s + RD.iX i = (s + (wU i)) := by double_regions
  have h₄ : (s + Λ r) + RD.iX i = ((s + (wU i)) + Λ r) := by double_regions
  have hh : (s + Λ r) + (wU i) = ((s + (wU i)) + Λ r) := by double_regions
  refine pair_merge (doubleModel S red)
      (p := 𝟙 (fo ((s + (wU i)) + Λ r))) (q := 𝟙 (fo s))
      (x := fwT (s + (wU i)) [(s + (wU i), .inr r)] ((s + (wU i)) + Λ r) ⟨rfl, trivial⟩ rfl ≫
        fwT s [(s, .inl (true, i))] (s + (wU i)) ⟨rfl, trivial⟩ rfl)
      (y := fwT (s + Λ r) [((s + Λ r), .inl (true, i))] ((s + (wU i)) + Λ r) ⟨rfl, trivial⟩ hh ≫
        fwT s [(s, .inr r)] (s + Λ r) ⟨rfl, trivial⟩ rfl)
      ?hn₁ ?hm₁ ?hn₂ ?hm₂ ?hp₁ ?hq₁ ?hd₁ ?hc₁ ?hp₂ ?hq₂ ?hd₂ ?hc₂ _ _
      (upIso r i h₁ rfl rfl h₄).inv (upIso r i h₁ rfl rfl h₄).hom ?hg₁ ?hg₂
      (Iso.inv_hom_id _) _ _ _ _ _ _ _
  case hg₁ =>
    exact upIso_inv_heq S red upIso r i (by double_regions) (by double_regions)
      (by double_regions) (by double_regions) _ _ _ _ _ _ _ _
  case hg₂ =>
    exact upIso_hom_heq S red upIso r i (by double_regions) (by double_regions)
      (by double_regions) (by double_regions) _ _ _ _ _ _ _ _
  case hn₁ => double_regions
  case hm₁ => double_regions
  case hn₂ => double_regions
  case hm₂ => double_regions
  case hp₁ => double_nil
  case hq₁ => double_nil
  case hd₁ => double_pair
  case hc₁ => double_pair
  case hp₂ => double_nil
  case hq₂ => double_nil
  case hd₂ => double_pair
  case hc₂ => double_pair

/-- **The red/upward bigons act as identities** for the generator images of a Rouquier family
(Webster, arXiv:1309.3796v3, (4.4e), proof of Theorem 4.25): every relation adjoined by
`addRedUpRelations` is killed. -/
theorem genImg_redUp (a : RedUpRelation X I ℓ) {s t : X}
    (ha : Cond s t (obj RD Λ a.leftWeight (a.side.move a.red a.up).bottom))
    (hb : Cond s t (obj RD Λ a.leftWeight (a.side.move a.red a.up).bottom)) :
    admissibleMap (k := k) (genImg S red upIso Sc) ha hb
      (LinDiagram.of (bareBigon RD Λ a.leftWeight a.red a.up a.side) - LinDiagram.of (𝟙 _)) =
        0 := by
  obtain ⟨μ, r, i, side⟩ := a
  dsimp only at ha hb ⊢
  obtain rfl : μ = s := ha.2.2
  rw [map_sub, sub_eq_zero]
  cases side
  · have h := genImg_redUpBigon_redLeft (k := k) S red upIso Sc i r ha
    exact h
  · have h := genImg_redUpBigon_upLeft (k := k) S red upIso Sc i r ha
    exact h

end Categorification.Stendhal.DoubleDiagram
