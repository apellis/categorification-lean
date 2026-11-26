/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleRouquierRed
import Categorification.WeightedKLR.RedStrands.DoubleRedCup
import Categorification.WeightedKLR.RedStrands.DoubleRedCap
import Categorification.Diagrams.BicatInterpMate

/-!
# Red cups and caps in the double model of a Rouquier family

Webster, arXiv:1309.3796v3, §4.5, proof of Theorem 4.25. The red/down crossings `a′`, `b′` of
the generator images `genImg` are the mates of the red/up crossings (`redDownQuot`, `redDownDot`).
Hence a black cup or cap slides through a red strand: the two sides of each red cup relation
(`redCupLeft`, `redCupRight`) and of each red cap relation (`redCapLeft`, `redCapRight`) have the
same image, for both orientations of the black strand (`genImg_redCup`, `genImg_redCap`). The
equality is the unit or counit form of the mate correspondence (`mateEquiv_unit`,
`mateEquiv_counit`), transported to the interpretation by `cup_key_heq` and `cap_key_heq`.
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
local notation "fwT" => fw (S := signature RD Λ)
local notation "wU" i => DoubleStrand.weight RD Λ (Sum.inl (true, i))
local notation "wD" i => DoubleStrand.weight RD Λ (Sum.inl (false, i))

/-- Region arithmetic in layers of the double signature. -/
macro "double_regions" : tactic => `(tactic| ((try dsimp only [layer, signature, colours,
  Signature.endR]) <;> simp [endWeight, Move.bottom, Move.top, DoubleStrand.weight, sgn] <;>
  abel_nf <;> done))

section Free

variable {Sg : Signature}

theorem hom_of_heq {x x' y y' : RQ Sg} {f : x ⟶ y} {f' : x' ⟶ y'} (hx : x = x')
    (hy : y = y') (h : f.1 = f'.1) :
    (FreeBicategory.Hom.of f : fo (S := Sg) x ⟶ fo y) ≍
      (FreeBicategory.Hom.of f' : fo x' ⟶ fo y') := by
  subst hx hy; rw [Subtype.ext h]

theorem fw_nil_heq {s t s' : Sg.Region} (h : Sg.ok s []) (e : Sg.endR s [] = t)
    (hs : s = s') : fw s [] t h e ≍ 𝟙 (fo (S := Sg) s') := by
  subst hs; subst e; rfl

theorem comp_heq {a a' b b' c c' : FB Sg} {f : a ⟶ b} {f' : a' ⟶ b'} {g : b ⟶ c}
    {g' : b' ⟶ c'} (ha : a = a') (hb : b = b') (hc : c = c') (hf : f ≍ f') (hg : g ≍ g') :
    f ≫ g ≍ f' ≫ g' := by
  subst ha hb hc; obtain rfl := eq_of_heq hf; obtain rfl := eq_of_heq hg; rfl

end Free

/-- A single strand of a relation instance agrees with the canonical one. -/
macro "double_single" : tactic =>
  `(tactic| exact hom_of_heq (by double_regions) (by double_regions) (by double_regions))

/-- An empty word of a relation instance agrees with the canonical identity. -/
macro "double_nil" : tactic => `(tactic| exact fw_nil_heq _ _ (by double_regions))

/-- A word of two strands of a relation instance agrees with the canonical composite. -/
macro "double_pair" : tactic =>
  `(tactic| exact comp_heq (by double_regions) (by double_regions) (by double_regions)
    (hom_of_heq (by double_regions) (by double_regions) (by double_regions))
    (hom_of_heq (by double_regions) (by double_regions) (by double_regions)))

variable {B : Type*} [Bicategory B] [∀ a b : B, Preadditive (a ⟶ b)] [AdditiveWhiskering B]
  {k : Type*} [CommRing k] [∀ a b : B, Linear k (a ⟶ b)]
  (S : RouqFamily (B := B) RD)
  (red : (r : Fin ℓ) → {x y : X} → x + Λ r = y → (S.obj y ⟶ S.obj x))
  (upIso : (r : Fin ℓ) → (i : I) → {μ μ₁ μ₂ μ₃ : X} → (h₁ : μ + RD.iX i = μ₁) →
    (h₂ : μ + Λ r = μ₂) → (h₃ : μ₁ + Λ r = μ₃) → (h₄ : μ₂ + RD.iX i = μ₃) →
    (S.F i h₄ ≫ red r h₂ ≅ red r h₃ ≫ S.F i h₁))
  (Sc : CL.CLScalars C k)

section Transport

theorem blackImg_cup_up' (z : X) (i : I) {a b : X} (ha hb hd hde hc hce) {x y : X}
    (hx : a = x) (h : x + RD.iX i = y) :
    blackImg S red Sc z (.cup (true, i)) a b ha hb hd hde hc hce ≍ (S.adj i h).unit := by
  subst hx; exact blackImg_cup_up S red Sc z i ha hb hd hde hc hce h

theorem blackImg_cup_dn' (z : X) (i : I) {a b : X} (ha hb hd hde hc hce) {x y : X}
    (hy : a = y) (h : x + RD.iX i = y) :
    blackImg S red Sc z (.cup (false, i)) a b ha hb hd hde hc hce ≍ (S.adjL i h).unit := by
  subst hy; exact blackImg_cup_dn S red Sc z i ha hb hd hde hc hce h

theorem blackImg_cap_up' (z : X) (i : I) {a b : X} (ha hb hd hde hc hce) {x y : X}
    (hy : b = y) (h : x + RD.iX i = y) :
    blackImg S red Sc z (.cap (true, i)) a b ha hb hd hde hc hce ≍ (S.adj i h).counit := by
  subst hy; exact blackImg_cap_up S red Sc z i ha hb hd hde hc hce h

theorem blackImg_cap_dn' (z : X) (i : I) {a b : X} (ha hb hd hde hc hce) {x y : X}
    (hx : b = x) (h : x + RD.iX i = y) :
    blackImg S red Sc z (.cap (false, i)) a b ha hb hd hde hc hce ≍ (S.adjL i h).counit := by
  subst hx; exact blackImg_cap_dn S red Sc z i ha hb hd hde hc hce h

omit [AdditiveWhiskering B] in
theorem upIso_hom_heq (r : Fin ℓ) (i : I) {μ μ₁ μ₂ μ₃ μ' μ₁' μ₂' μ₃' : X}
    (e : μ = μ') (e₁ : μ₁ = μ₁') (e₂ : μ₂ = μ₂') (e₃ : μ₃ = μ₃')
    (h₁ : μ + RD.iX i = μ₁) (h₂ : μ + Λ r = μ₂) (h₃ : μ₁ + Λ r = μ₃) (h₄ : μ₂ + RD.iX i = μ₃)
    (h₁' : μ' + RD.iX i = μ₁') (h₂' : μ' + Λ r = μ₂') (h₃' : μ₁' + Λ r = μ₃')
    (h₄' : μ₂' + RD.iX i = μ₃') :
    (upIso r i h₁ h₂ h₃ h₄).hom ≍ (upIso r i h₁' h₂' h₃' h₄').hom := by
  subst e e₁ e₂ e₃; rfl

omit [AdditiveWhiskering B] in
theorem upIso_inv_heq (r : Fin ℓ) (i : I) {μ μ₁ μ₂ μ₃ μ' μ₁' μ₂' μ₃' : X}
    (e : μ = μ') (e₁ : μ₁ = μ₁') (e₂ : μ₂ = μ₂') (e₃ : μ₃ = μ₃')
    (h₁ : μ + RD.iX i = μ₁) (h₂ : μ + Λ r = μ₂) (h₃ : μ₁ + Λ r = μ₃) (h₄ : μ₂ + RD.iX i = μ₃)
    (h₁' : μ' + RD.iX i = μ₁') (h₂' : μ' + Λ r = μ₂') (h₃' : μ₁' + Λ r = μ₃')
    (h₄' : μ₂' + RD.iX i = μ₃') :
    (upIso r i h₁ h₂ h₃ h₄).inv ≍ (upIso r i h₁' h₂' h₃' h₄').inv := by
  subst e e₁ e₂ e₃; rfl

omit [AdditiveWhiskering B] in
theorem redDownQuot_heq (r : Fin ℓ) (i : I) {μ μ₁ μ₂ μ₃ μ' μ₁' μ₂' μ₃' : X}
    (e : μ = μ') (e₁ : μ₁ = μ₁') (e₂ : μ₂ = μ₂') (e₃ : μ₃ = μ₃')
    (h₁ : μ + RD.iX i = μ₁) (h₂ : μ + Λ r = μ₂) (h₃ : μ₁ + Λ r = μ₃) (h₄ : μ₂ + RD.iX i = μ₃)
    (h₁' : μ' + RD.iX i = μ₁') (h₂' : μ' + Λ r = μ₂') (h₃' : μ₁' + Λ r = μ₃')
    (h₄' : μ₂' + RD.iX i = μ₃') :
    redDownQuot S red upIso r i h₁ h₂ h₃ h₄ ≍ redDownQuot S red upIso r i h₁' h₂' h₃' h₄' := by
  subst e e₁ e₂ e₃; rfl

theorem redDownDot_heq (r : Fin ℓ) (i : I) {μ μ₁ μ₂ μ₃ μ' μ₁' μ₂' μ₃' : X}
    (e : μ = μ') (e₁ : μ₁ = μ₁') (e₂ : μ₂ = μ₂') (e₃ : μ₃ = μ₃')
    (h₁ : μ + RD.iX i = μ₁) (h₂ : μ + Λ r = μ₂) (h₃ : μ₁ + Λ r = μ₃) (h₄ : μ₂ + RD.iX i = μ₃)
    (h₁' : μ' + RD.iX i = μ₁') (h₂' : μ' + Λ r = μ₂') (h₃' : μ₁' + Λ r = μ₃')
    (h₄' : μ₂' + RD.iX i = μ₃') :
    redDownDot S red upIso r i h₁ h₂ h₃ h₄ ≍ redDownDot S red upIso r i h₁' h₂' h₃' h₄' := by
  subst e e₁ e₂ e₃; rfl

end Transport

/-- Rewrite the generator image of a black layer as `blackImg`. -/
macro "black_gen" : tactic =>
  `(tactic| refine (heq_of_eq (genImg_blackOn S red upIso Sc _ _ _ _ _ _ _ _ _ _)).trans ?_)

theorem genImg_redCup_bare_up (i : I) (r : Fin ℓ) {s t : X}
    (ha : Cond s t (obj RD Λ s ([] ++ [.inr r] ++ [])))
    (hb : Cond s t (obj RD Λ s ([] ++ [.inl (true, i), .inr r, .inl (false, i)] ++ []))) :
    admissibleMap (k := k) (genImg S red upIso Sc) ha hb
        (LinDiagram.of (redCupLeft RD Λ s [] (true, i) r [])) =
      admissibleMap (k := k) (genImg S red upIso Sc) ha hb
        (LinDiagram.of (redCupRight RD Λ s [] (true, i) r [])) := by
  obtain rfl : s + Λ r = t := ha.2.1
  rw [admissibleMap_of, admissibleMap_of]
  change admissibleChain _ _ _ _ _ _ _ = admissibleChain _ _ _ _ _ _ _
  dsimp only [ObjectProperty.homMk]
  rw [admissibleChain_congr _ (show Diagram.layers (redCupLeft RD Λ s [] (true, i) r []) =
      [layer RD Λ s [] (.black (.cup (true, i))) [.inr r],
        layer RD Λ s [.inl (true, i)] (.blackRed (false, i) r) []]
      by simp [redCupLeft, moveDiagram]),
    admissibleChain_congr _ (show Diagram.layers (redCupRight RD Λ s [] (true, i) r []) =
      [layer RD Λ s [.inr r] (.black (.cup (true, i))) [],
        layer RD Λ s [] (.redBlack r (true, i)) [.inl (false, i)]]
      by simp [redCupRight, moveDiagram])]
  rw [admissibleChain_pair, admissibleChain_pair, coreC_eq, coreC_eq, coreC_eq, coreC_eq]
  unfold core
  have h₁ : s + RD.iX i = (s + (wU i)) := by double_regions
  have h₄ : (s + Λ r) + RD.iX i = ((s + Λ r) + (wU i)) := by double_regions
  have h₃ : (s + (wU i)) + Λ r = ((s + Λ r) + (wU i)) := by double_regions
  have hd : (s + (wU i)) + (wD i) = s := by double_regions
  have hd' : ((s + Λ r) + (wU i)) + (wD i) = s + Λ r := by double_regions
  refine cup_key_heq (doubleModel S red) (a₂ := fo (s + (wU i))) (a₃ := fo ((s + Λ r) + (wU i)))
      (x := fwT s [(s, .inr r)] (s + Λ r) ⟨rfl, trivial⟩ rfl)
      (up := fwT s [(s, .inl (true, i))] (s + (wU i)) ⟨rfl, trivial⟩ rfl)
      (dn := fwT (s + (wU i)) [((s + (wU i)), .inl (false, i))] s ⟨rfl, trivial⟩ hd)
      (up' := fwT (s + Λ r) [(s + Λ r, .inl (true, i))] ((s + Λ r) + (wU i)) ⟨rfl, trivial⟩ rfl)
      (dn' := fwT ((s + Λ r) + (wU i)) [(((s + Λ r) + (wU i)), .inl (false, i))] (s + Λ r) ⟨rfl, trivial⟩ hd')
      (x' := fwT (s + (wU i)) [((s + (wU i)), .inr r)] ((s + Λ r) + (wU i)) ⟨rfl, trivial⟩ h₃)
      ?hn₁ ?hm₁ ?hn₂ ?hm₂ ?hn₃ ?hm₃ ?hn₄ ?hm₄ ?hp₁ ?hq₁ ?hd₁ ?hc₁ ?hp₂ ?hq₂ ?hd₂ ?hc₂
      ?hp₃ ?hq₃ ?hd₃ ?hc₃ ?hp₄ ?hq₄ ?hd₄ ?hc₄ _ _ _ _ (S.adj i h₁).unit (redDownQuot S red upIso r i h₁ rfl h₃ h₄) (S.adj i h₄).unit
      (upIso r i h₁ rfl h₃ h₄).hom
      ?hg₁ ?hg₂ ?hg₃ ?hg₄ ?hmate _ _ _ _ _ _ _ _ _ _ _ _ _ _
  case hmate =>
    have key := mateEquiv_unit (S.adj i h₄) (S.adj i h₁) (redDownQuot S red upIso r i h₁ rfl h₃ h₄)
    rw [redDownQuot, Equiv.apply_symm_apply] at key
    exact key
  case hg₁ => black_gen; refine blackImg_cup_up' S red Sc _ i _ _ _ _ _ _ ?_ h₁; double_regions
  case hg₃ => black_gen; refine blackImg_cup_up' S red Sc _ i _ _ _ _ _ _ ?_ h₄; double_regions
  case hg₂ =>
    exact redDownQuot_heq S red upIso r i (by double_regions) (by double_regions)
      (by double_regions) (by double_regions) _ _ _ _ _ _ _ _
  case hg₄ =>
    exact upIso_hom_heq S red upIso r i (by double_regions) (by double_regions)
      (by double_regions) (by double_regions) _ _ _ _ _ _ _ _
  case hn₁ => double_regions
  case hm₁ => double_regions
  case hn₂ => double_regions
  case hm₂ => double_regions
  case hn₃ => double_regions
  case hm₃ => double_regions
  case hn₄ => double_regions
  case hm₄ => double_regions
  case hp₁ => double_single
  case hq₁ => double_nil
  case hd₁ => double_nil
  case hc₁ => double_pair
  case hp₂ => double_nil
  case hq₂ => double_single
  case hd₂ => double_pair
  case hc₂ => double_pair
  case hp₃ => double_nil
  case hq₃ => double_single
  case hd₃ => double_nil
  case hc₃ => double_pair
  case hp₄ => double_single
  case hq₄ => double_nil
  case hd₄ => double_pair
  case hc₄ => double_pair

theorem genImg_redCup_bare_dn (i : I) (r : Fin ℓ) {s t : X}
    (ha : Cond s t (obj RD Λ s ([] ++ [.inr r] ++ [])))
    (hb : Cond s t (obj RD Λ s ([] ++ [.inl (false, i), .inr r, .inl (true, i)] ++ []))) :
    admissibleMap (k := k) (genImg S red upIso Sc) ha hb
        (LinDiagram.of (redCupLeft RD Λ s [] (false, i) r [])) =
      admissibleMap (k := k) (genImg S red upIso Sc) ha hb
        (LinDiagram.of (redCupRight RD Λ s [] (false, i) r [])) := by
  obtain rfl : s + Λ r = t := ha.2.1
  rw [admissibleMap_of, admissibleMap_of]
  change admissibleChain _ _ _ _ _ _ _ = admissibleChain _ _ _ _ _ _ _
  dsimp only [ObjectProperty.homMk]
  rw [admissibleChain_congr _ (show Diagram.layers (redCupLeft RD Λ s [] (false, i) r []) =
      [layer RD Λ s [] (.black (.cup (false, i))) [.inr r],
        layer RD Λ s [.inl (false, i)] (.blackRed (true, i) r) []]
      by simp [redCupLeft, moveDiagram]),
    admissibleChain_congr _ (show Diagram.layers (redCupRight RD Λ s [] (false, i) r []) =
      [layer RD Λ s [.inr r] (.black (.cup (false, i))) [],
        layer RD Λ s [] (.redBlack r (false, i)) [.inl (true, i)]]
      by simp [redCupRight, moveDiagram])]
  rw [admissibleChain_pair, admissibleChain_pair, coreC_eq, coreC_eq, coreC_eq, coreC_eq]
  unfold core
  have h₁ : (s + (wD i)) + RD.iX i = s := by double_regions
  have h₄ : ((s + Λ r) + (wD i)) + RD.iX i = s + Λ r := by double_regions
  have h₃ : (s + (wD i)) + Λ r = ((s + Λ r) + (wD i)) := by double_regions
  have hd : (s + (wD i)) + (wU i) = s := by double_regions
  have hd' : ((s + Λ r) + (wD i)) + (wU i) = s + Λ r := by double_regions
  refine cup_key_heq (doubleModel S red) (a₂ := fo (s + (wD i))) (a₃ := fo ((s + Λ r) + (wD i)))
      (x := fwT s [(s, .inr r)] (s + Λ r) ⟨rfl, trivial⟩ rfl)
      (up := fwT s [(s, .inl (false, i))] (s + (wD i)) ⟨rfl, trivial⟩ rfl)
      (dn := fwT (s + (wD i)) [((s + (wD i)), .inl (true, i))] s ⟨rfl, trivial⟩ hd)
      (up' := fwT (s + Λ r) [(s + Λ r, .inl (false, i))] ((s + Λ r) + (wD i)) ⟨rfl, trivial⟩ rfl)
      (dn' := fwT ((s + Λ r) + (wD i)) [(((s + Λ r) + (wD i)), .inl (true, i))] (s + Λ r) ⟨rfl, trivial⟩ hd')
      (x' := fwT (s + (wD i)) [((s + (wD i)), .inr r)] ((s + Λ r) + (wD i)) ⟨rfl, trivial⟩ h₃)
      ?hn₁ ?hm₁ ?hn₂ ?hm₂ ?hn₃ ?hm₃ ?hn₄ ?hm₄ ?hp₁ ?hq₁ ?hd₁ ?hc₁ ?hp₂ ?hq₂ ?hd₂ ?hc₂
      ?hp₃ ?hq₃ ?hd₃ ?hc₃ ?hp₄ ?hq₄ ?hd₄ ?hc₄ _ _ _ _ (S.adjL i h₁).unit (upIso r i h₁ h₃ rfl h₄).inv (S.adjL i h₄).unit
      (redDownDot S red upIso r i h₁ h₃ rfl h₄)
      ?hg₁ ?hg₂ ?hg₃ ?hg₄ ?hmate _ _ _ _ _ _ _ _ _ _ _ _ _ _
  case hmate => exact mateEquiv_unit (S.adjL i h₄) (S.adjL i h₁) (upIso r i h₁ h₃ rfl h₄).inv
  case hg₁ => black_gen; refine blackImg_cup_dn' S red Sc _ i _ _ _ _ _ _ ?_ h₁; double_regions
  case hg₃ => black_gen; refine blackImg_cup_dn' S red Sc _ i _ _ _ _ _ _ ?_ h₄; double_regions
  case hg₂ =>
    exact upIso_inv_heq S red upIso r i (by double_regions) (by double_regions)
      (by double_regions) (by double_regions) _ _ _ _ _ _ _ _
  case hg₄ =>
    exact redDownDot_heq S red upIso r i (by double_regions) (by double_regions)
      (by double_regions) (by double_regions) _ _ _ _ _ _ _ _
  case hn₁ => double_regions
  case hm₁ => double_regions
  case hn₂ => double_regions
  case hm₂ => double_regions
  case hn₃ => double_regions
  case hm₃ => double_regions
  case hn₄ => double_regions
  case hm₄ => double_regions
  case hp₁ => double_single
  case hq₁ => double_nil
  case hd₁ => double_nil
  case hc₁ => double_pair
  case hp₂ => double_nil
  case hq₂ => double_single
  case hd₂ => double_pair
  case hc₂ => double_pair
  case hp₃ => double_nil
  case hq₃ => double_single
  case hd₃ => double_nil
  case hc₃ => double_pair
  case hp₄ => double_single
  case hq₄ => double_nil
  case hd₄ => double_pair
  case hc₄ => double_pair

theorem genImg_redCap_bare_up (i : I) (r : Fin ℓ) {s t : X}
    (ha : Cond s t (obj RD Λ s ([] ++ [.inl (false, i), .inr r, .inl (true, i)] ++ [])))
    (hb : Cond s t (obj RD Λ s ([] ++ [.inr r] ++ []))) :
    admissibleMap (k := k) (genImg S red upIso Sc) ha hb
        (LinDiagram.of (redCapLeft RD Λ s [] (true, i) r [])) =
      admissibleMap (k := k) (genImg S red upIso Sc) ha hb
        (LinDiagram.of (redCapRight RD Λ s [] (true, i) r [])) := by
  obtain rfl : s + Λ r = t := hb.2.1
  rw [admissibleMap_of, admissibleMap_of]
  change admissibleChain _ _ _ _ _ _ _ = admissibleChain _ _ _ _ _ _ _
  dsimp only [ObjectProperty.homMk]
  rw [admissibleChain_congr _ (show Diagram.layers (redCapLeft RD Λ s [] (true, i) r []) =
      [layer RD Λ s [.inl (false, i)] (.redBlack r (true, i)) [],
        layer RD Λ s [] (.black (.cap (true, i))) [.inr r]]
      by simp [redCapLeft, moveDiagram]),
    admissibleChain_congr _ (show Diagram.layers (redCapRight RD Λ s [] (true, i) r []) =
      [layer RD Λ s [] (.blackRed (false, i) r) [.inl (true, i)],
        layer RD Λ s [.inr r] (.black (.cap (true, i))) []]
      by simp [redCapRight, moveDiagram])]
  rw [admissibleChain_pair, admissibleChain_pair, coreC_eq, coreC_eq, coreC_eq, coreC_eq]
  unfold core
  have h₁ : (s + (wD i)) + RD.iX i = s := by double_regions
  have h₄ : ((s + Λ r) + (wD i)) + RD.iX i = s + Λ r := by double_regions
  have h₃ : (s + (wD i)) + Λ r = ((s + Λ r) + (wD i)) := by double_regions
  have hu : (s + (wD i)) + (wU i) = s := by double_regions
  have hu' : ((s + Λ r) + (wD i)) + (wU i) = s + Λ r := by double_regions
  refine cap_key_heq (doubleModel S red) (a₂ := fo (s + (wD i))) (a₃ := fo ((s + Λ r) + (wD i)))
      (x := fwT s [(s, .inr r)] (s + Λ r) ⟨rfl, trivial⟩ rfl)
      (up := fwT (s + (wD i)) [((s + (wD i)), .inl (true, i))] s ⟨rfl, trivial⟩ hu)
      (dn := fwT s [(s, .inl (false, i))] (s + (wD i)) ⟨rfl, trivial⟩ rfl)
      (up' := fwT ((s + Λ r) + (wD i)) [(((s + Λ r) + (wD i)), .inl (true, i))] (s + Λ r) ⟨rfl, trivial⟩ hu')
      (dn' := fwT (s + Λ r) [(s + Λ r, .inl (false, i))] ((s + Λ r) + (wD i)) ⟨rfl, trivial⟩ rfl)
      (x' := fwT (s + (wD i)) [((s + (wD i)), .inr r)] ((s + Λ r) + (wD i)) ⟨rfl, trivial⟩ h₃)
      ?hn₁ ?hm₁ ?hn₂ ?hm₂ ?hn₃ ?hm₃ ?hn₄ ?hm₄ ?hp₁ ?hq₁ ?hd₁ ?hc₁ ?hp₂ ?hq₂ ?hd₂ ?hc₂
      ?hp₃ ?hq₃ ?hd₃ ?hc₃ ?hp₄ ?hq₄ ?hd₄ ?hc₄ _ _ _ _ (upIso r i h₁ h₃ rfl h₄).hom (S.adj i h₁).counit
      (redDownQuot S red upIso r i h₁ h₃ rfl h₄) (S.adj i h₄).counit
      ?hg₁ ?hg₂ ?hg₃ ?hg₄ ?hmate _ _ _ _ _ _ _ _ _ _ _ _ _ _
  case hmate =>
    have key := mateEquiv_counit (S.adj i h₄) (S.adj i h₁) (redDownQuot S red upIso r i h₁ h₃ rfl h₄)
    rw [redDownQuot, Equiv.apply_symm_apply] at key
    exact key
  case hg₂ => black_gen; refine blackImg_cap_up' S red Sc _ i _ _ _ _ _ _ ?_ h₁; double_regions
  case hg₄ => black_gen; refine blackImg_cap_up' S red Sc _ i _ _ _ _ _ _ ?_ h₄; double_regions
  case hg₁ =>
    exact upIso_hom_heq S red upIso r i (by double_regions) (by double_regions)
      (by double_regions) (by double_regions) _ _ _ _ _ _ _ _
  case hg₃ =>
    exact redDownQuot_heq S red upIso r i (by double_regions) (by double_regions)
      (by double_regions) (by double_regions) _ _ _ _ _ _ _ _
  case hn₁ => double_regions
  case hm₁ => double_regions
  case hn₂ => double_regions
  case hm₂ => double_regions
  case hn₃ => double_regions
  case hm₃ => double_regions
  case hn₄ => double_regions
  case hm₄ => double_regions
  case hp₁ => double_nil
  case hq₁ => double_single
  case hd₁ => double_pair
  case hc₁ => double_pair
  case hp₂ => double_single
  case hq₂ => double_nil
  case hd₂ => double_pair
  case hc₂ => double_nil
  case hp₃ => double_single
  case hq₃ => double_nil
  case hd₃ => double_pair
  case hc₃ => double_pair
  case hp₄ => double_nil
  case hq₄ => double_single
  case hd₄ => double_pair
  case hc₄ => double_nil

theorem genImg_redCap_bare_dn (i : I) (r : Fin ℓ) {s t : X}
    (ha : Cond s t (obj RD Λ s ([] ++ [.inl (true, i), .inr r, .inl (false, i)] ++ [])))
    (hb : Cond s t (obj RD Λ s ([] ++ [.inr r] ++ []))) :
    admissibleMap (k := k) (genImg S red upIso Sc) ha hb
        (LinDiagram.of (redCapLeft RD Λ s [] (false, i) r [])) =
      admissibleMap (k := k) (genImg S red upIso Sc) ha hb
        (LinDiagram.of (redCapRight RD Λ s [] (false, i) r [])) := by
  obtain rfl : s + Λ r = t := hb.2.1
  rw [admissibleMap_of, admissibleMap_of]
  change admissibleChain _ _ _ _ _ _ _ = admissibleChain _ _ _ _ _ _ _
  dsimp only [ObjectProperty.homMk]
  rw [admissibleChain_congr _ (show Diagram.layers (redCapLeft RD Λ s [] (false, i) r []) =
      [layer RD Λ s [.inl (true, i)] (.redBlack r (false, i)) [],
        layer RD Λ s [] (.black (.cap (false, i))) [.inr r]]
      by simp [redCapLeft, moveDiagram]),
    admissibleChain_congr _ (show Diagram.layers (redCapRight RD Λ s [] (false, i) r []) =
      [layer RD Λ s [] (.blackRed (true, i) r) [.inl (false, i)],
        layer RD Λ s [.inr r] (.black (.cap (false, i))) []]
      by simp [redCapRight, moveDiagram])]
  rw [admissibleChain_pair, admissibleChain_pair, coreC_eq, coreC_eq, coreC_eq, coreC_eq]
  unfold core
  have h₁ : s + RD.iX i = (s + (wU i)) := by double_regions
  have h₄ : (s + Λ r) + RD.iX i = ((s + Λ r) + (wU i)) := by double_regions
  have h₃ : (s + (wU i)) + Λ r = ((s + Λ r) + (wU i)) := by double_regions
  have hu : (s + (wU i)) + (wD i) = s := by double_regions
  have hu' : ((s + Λ r) + (wU i)) + (wD i) = s + Λ r := by double_regions
  refine cap_key_heq (doubleModel S red) (a₂ := fo (s + (wU i))) (a₃ := fo ((s + Λ r) + (wU i)))
      (x := fwT s [(s, .inr r)] (s + Λ r) ⟨rfl, trivial⟩ rfl)
      (up := fwT (s + (wU i)) [((s + (wU i)), .inl (false, i))] s ⟨rfl, trivial⟩ hu)
      (dn := fwT s [(s, .inl (true, i))] (s + (wU i)) ⟨rfl, trivial⟩ rfl)
      (up' := fwT ((s + Λ r) + (wU i)) [(((s + Λ r) + (wU i)), .inl (false, i))] (s + Λ r) ⟨rfl, trivial⟩ hu')
      (dn' := fwT (s + Λ r) [(s + Λ r, .inl (true, i))] ((s + Λ r) + (wU i)) ⟨rfl, trivial⟩ rfl)
      (x' := fwT (s + (wU i)) [((s + (wU i)), .inr r)] ((s + Λ r) + (wU i)) ⟨rfl, trivial⟩ h₃)
      ?hn₁ ?hm₁ ?hn₂ ?hm₂ ?hn₃ ?hm₃ ?hn₄ ?hm₄ ?hp₁ ?hq₁ ?hd₁ ?hc₁ ?hp₂ ?hq₂ ?hd₂ ?hc₂
      ?hp₃ ?hq₃ ?hd₃ ?hc₃ ?hp₄ ?hq₄ ?hd₄ ?hc₄ _ _ _ _ (redDownDot S red upIso r i h₁ rfl h₃ h₄) (S.adjL i h₁).counit
      (upIso r i h₁ rfl h₃ h₄).inv (S.adjL i h₄).counit
      ?hg₁ ?hg₂ ?hg₃ ?hg₄ ?hmate _ _ _ _ _ _ _ _ _ _ _ _ _ _
  case hmate =>
    exact mateEquiv_counit (S.adjL i h₄) (S.adjL i h₁) (upIso r i h₁ rfl h₃ h₄).inv
  case hg₂ => black_gen; refine blackImg_cap_dn' S red Sc _ i _ _ _ _ _ _ ?_ h₁; double_regions
  case hg₄ => black_gen; refine blackImg_cap_dn' S red Sc _ i _ _ _ _ _ _ ?_ h₄; double_regions
  case hg₁ =>
    exact redDownDot_heq S red upIso r i (by double_regions) (by double_regions)
      (by double_regions) (by double_regions) _ _ _ _ _ _ _ _
  case hg₃ =>
    exact upIso_inv_heq S red upIso r i (by double_regions) (by double_regions)
      (by double_regions) (by double_regions) _ _ _ _ _ _ _ _
  case hn₁ => double_regions
  case hm₁ => double_regions
  case hn₂ => double_regions
  case hm₂ => double_regions
  case hn₃ => double_regions
  case hm₃ => double_regions
  case hn₄ => double_regions
  case hm₄ => double_regions
  case hp₁ => double_nil
  case hq₁ => double_single
  case hd₁ => double_pair
  case hc₁ => double_pair
  case hp₂ => double_single
  case hq₂ => double_nil
  case hd₂ => double_pair
  case hc₂ => double_nil
  case hp₃ => double_single
  case hq₃ => double_nil
  case hd₃ => double_pair
  case hc₃ => double_pair
  case hp₄ => double_nil
  case hq₄ => double_single
  case hd₄ => double_pair
  case hc₄ => double_nil

end Categorification.Stendhal.DoubleDiagram
