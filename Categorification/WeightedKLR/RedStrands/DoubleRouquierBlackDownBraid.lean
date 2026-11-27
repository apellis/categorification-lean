/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleRouquierBlackDown

/-!
# Downward black triple points in a Rouquier family

Webster, arXiv:1309.3796v3, proof of Theorem 4.25: the downward braid relation
`ψ₀ψ₁ψ₀ = ψ₁ψ₀ψ₁` on three black strands is killed by the generator images `genImg` when the
family's crossings satisfy the braid relation in the corresponding colours (`DownBlackBraid`).
This holds for one repeated colour by `RouqFamily.braid` and for distinct outer colours by
`RouqUpKLR.braid` (Brundan, arXiv:1501.00350v1, Definition 1.1, (1.4)).

## Main results

* `admissibleMap_braid_bbb`: the downward braid on `[i, j, c]` from `DownBlackBraid`;
* `downBlackBraid_of_ne`, `downBlackBraid_self`: `DownBlackBraid` for `i ≠ c` and for
  `i = j = c`.
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

local notation "fwT" => fw (S := signature RD Λ)
local notation "wD" i => DoubleStrand.weight RD Λ (Sum.inl (false, i))

variable {B : Type*} [Bicategory B] [∀ a b : B, Preadditive (a ⟶ b)] [AdditiveWhiskering B]
  {k : Type w} [CommRing k] [∀ a b : B, Linear k (a ⟶ b)]
  (S : RouqFamily (B := B) RD)
  {red : (r : Fin ℓ) → {x y : X} → x + Λ r = y → (S.obj y ⟶ S.obj x)}
  {upIso : (r : Fin ℓ) → (i : I) → {μ μ₁ μ₂ μ₃ : X} → (h₁ : μ + RD.iX i = μ₁) →
    (h₂ : μ + Λ r = μ₂) → (h₃ : μ₁ + Λ r = μ₃) → (h₄ : μ₂ + RD.iX i = μ₃) →
    (S.F i h₄ ≫ red r h₂ ≅ red r h₃ ≫ S.F i h₁)}
  (Sc : CL.CLScalars C k)

/-- The braid relation of the family's crossings in the colours `i, j, c` (the shape of
`RouqUpKLR.braid`). -/
def DownBlackBraid (i j c : I) : Prop :=
  ∀ {l w₁ w₂ w₃ w₄ w₅ w₆ m : X} (e1 : l + RD.iX c = w₁) (e2 : w₁ + RD.iX j = w₂)
    (e3 : w₂ + RD.iX i = m) (e4 : w₁ + RD.iX i = w₃) (e5 : w₃ + RD.iX j = m)
    (e6 : l + RD.iX i = w₄) (e7 : w₄ + RD.iX c = w₃) (e8 : w₄ + RD.iX j = w₅)
    (e9 : w₅ + RD.iX c = m) (e10 : l + RD.iX j = w₆) (e11 : w₆ + RD.iX c = w₂)
    (e12 : w₆ + RD.iX i = w₅),
    S.E c e1 ◁ S.cross i j e2 e3 e4 e5 ≫
        ((α_ (S.E c e1) (S.E i e4) (S.E j e5)).inv ≫ S.cross i c e1 e4 e6 e7 ▷ S.E j e5 ≫
          (α_ (S.E i e6) (S.E c e7) (S.E j e5)).hom) ≫
        S.E i e6 ◁ S.cross j c e7 e5 e8 e9 =
      ((α_ (S.E c e1) (S.E j e2) (S.E i e3)).inv ≫ S.cross j c e1 e2 e10 e11 ▷ S.E i e3 ≫
          (α_ (S.E j e10) (S.E c e11) (S.E i e3)).hom) ≫
        S.E j e10 ◁ S.cross i c e11 e3 e12 e9 ≫
        ((α_ (S.E j e10) (S.E i e12) (S.E c e9)).inv ≫ S.cross i j e10 e12 e6 e8 ▷ S.E c e9 ≫
          (α_ (S.E i e6) (S.E j e8) (S.E c e9)).hom)

omit [AdditiveWhiskering B] in
/-- The family's braid relation for distinct outer colours (Brundan (1.4)). -/
theorem downBlackBraid_of_ne {Qb : I → I → MvPolynomial (Fin 2) k} (H : RouqUpKLR S Qb)
    (i j c : I) (h : i ≠ c) : DownBlackBraid S i j c :=
  fun e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 =>
    H.braid i j c h e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12

omit [AdditiveWhiskering B] in
/-- The family's braid relation for one colour (`RouqFamily.braid`). -/
theorem downBlackBraid_self (i : I) : DownBlackBraid S i i i := by
  unfold DownBlackBraid
  intro l w₁ w₂ w₃ w₄ w₅ w₆ m e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12
  obtain rfl : w₄ = w₁ := e6.symm.trans e1
  obtain rfl : w₆ = w₄ := e10.symm.trans e1
  obtain rfl : w₃ = w₂ := e4.symm.trans e2
  obtain rfl : w₅ = w₃ := e8.symm.trans e2
  exact S.braid i e1 e2 e3

variable {S}

/-- **The downward braid on `[i, j, c]`** with three black strands is killed by the generator
images. -/
theorem admissibleMap_braid_bbb (i j c : I) (hbr : DownBlackBraid S i j c)
    (Q : I ⊕ Fin ℓ → I ⊕ Fin ℓ → MvPolynomial (Fin 2) k)
    (h : ¬ ((Sum.inl i : I ⊕ Fin ℓ) = .inl c ∧ (Sum.inl i : I ⊕ Fin ℓ) ≠ .inl j))
    (m : X) {x y : X}
    (ha : Cond x y (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inl i, .inl j, .inl c])))
    (hb : Cond x y (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inl c, .inl j, .inl i]))) :
    admissibleMap (genImg S red upIso Sc) ha hb (downLinear RD Λ k m [] []
      (KLR.Diagram.relation k Q (.braid (.inl i) (.inl j) (.inl c) h))) = 0 := by
  obtain rfl : m = x := ha.2.2
  obtain rfl : ((m + (wD i)) + (wD j)) + (wD c) = y := ha.2.1
  rw [relation_braid, map_sub, map_sub, sub_eq_zero]
  obtain ⟨D, hD, eD⟩ := downLinear_dl3 (RD := RD) (Λ := Λ) (k := k) m [] [.inl c] [.inl j] []
    [] [.inl i] (.cross (.inl i) (.inl j)) (.cross (.inl i) (.inl c)) (.cross (.inl j) (.inl c))
    rfl rfl rfl (a := KLR.Diagram.ob [.inl i, .inl j, .inl c])
    (b := KLR.Diagram.ob [.inl j, .inl i, .inl c]) (c := KLR.Diagram.ob [.inl j, .inl c, .inl i])
    (d := KLR.Diagram.ob [.inl c, .inl j, .inl i]) rfl rfl rfl rfl rfl rfl
  obtain ⟨D', hD', eD'⟩ := downLinear_dl3 (RD := RD) (Λ := Λ) (k := k) m [.inl i] [] []
    [.inl j] [.inl c] [] (.cross (.inl j) (.inl c)) (.cross (.inl i) (.inl c))
    (.cross (.inl i) (.inl j)) rfl rfl rfl (a := KLR.Diagram.ob [.inl i, .inl j, .inl c])
    (b := KLR.Diagram.ob [.inl i, .inl c, .inl j]) (c := KLR.Diagram.ob [.inl c, .inl i, .inl j])
    (d := KLR.Diagram.ob [.inl c, .inl j, .inl i]) rfl rfl rfl rfl rfl rfl
  erw [eD, eD', admissibleMap_of, admissibleMap_of]
  change admissibleChain _ _ _ _ _ _ _ = admissibleChain _ _ _ _ _ _ _
  dsimp only [ObjectProperty.homMk]
  simp only [List.map_cons, List.map_nil, DoubleStrand.down, List.nil_append,
    List.append_nil] at hD hD'
  rw [admissibleChain_congr _ hD, admissibleChain_congr _ hD']
  symm
  have e₁ : ((m + (wD i)) + (wD c)) + (wD j) = ((m + (wD i)) + (wD j)) + (wD c) := by
    double_regions
  have h₃ : (m + (wD c)) + (wD i) = (m + (wD i)) + (wD c) := by double_regions
  have h₃' : ((m + (wD c)) + (wD j)) + (wD i) = ((m + (wD i)) + (wD j)) + (wD c) := by
    double_regions
  have g₃ : (m + (wD j)) + (wD i) = (m + (wD i)) + (wD j) := by double_regions
  have e₅ : (m + (wD j)) + (wD c) = (m + (wD c)) + (wD j) := by double_regions
  have pUj : (((m + (wD i)) + (wD j)) + (wD c)) + RD.iX c = (m + (wD i)) + (wD j) := by
    double_regions
  have pUi : ((m + (wD i)) + (wD j)) + RD.iX j = m + (wD i) := by double_regions
  have pR0 : (m + (wD i)) + RD.iX i = m := by double_regions
  have pUi2 : (((m + (wD i)) + (wD j)) + (wD c)) + RD.iX j = (m + (wD i)) + (wD c) := by
    double_regions
  have pUj2 : ((m + (wD i)) + (wD c)) + RD.iX c = m + (wD i) := by double_regions
  have pR3 : ((m + (wD i)) + (wD c)) + RD.iX i = m + (wD c) := by double_regions
  have pUj3 : (m + (wD c)) + RD.iX c = m := by double_regions
  have pR4 : (((m + (wD i)) + (wD j)) + (wD c)) + RD.iX i = (m + (wD c)) + (wD j) := by
    double_regions
  have pUi4 : ((m + (wD c)) + (wD j)) + RD.iX j = m + (wD c) := by double_regions
  have pR5 : ((m + (wD i)) + (wD j)) + RD.iX i = m + (wD j) := by double_regions
  have pUi5 : (m + (wD j)) + RD.iX j = m := by double_regions
  have pUj6 : ((m + (wD c)) + (wD j)) + RD.iX c = m + (wD j) := by double_regions
  let R0 := fwT m [(m, .inl (false, i))] (m + (wD i)) ⟨rfl, trivial⟩ rfl
  let Ui := fwT (m + (wD i)) [(m + (wD i), .inl (false, j))] ((m + (wD i)) + (wD j))
    ⟨rfl, trivial⟩ rfl
  let Uj := fwT ((m + (wD i)) + (wD j)) [((m + (wD i)) + (wD j), .inl (false, c))]
    (((m + (wD i)) + (wD j)) + (wD c)) ⟨rfl, trivial⟩ rfl
  let Ui2 := fwT ((m + (wD i)) + (wD c)) [((m + (wD i)) + (wD c), .inl (false, j))]
    (((m + (wD i)) + (wD j)) + (wD c)) ⟨rfl, trivial⟩ e₁
  let Uj2 := fwT (m + (wD i)) [(m + (wD i), .inl (false, c))] ((m + (wD i)) + (wD c))
    ⟨rfl, trivial⟩ rfl
  let R3 := fwT (m + (wD c)) [(m + (wD c), .inl (false, i))] ((m + (wD i)) + (wD c))
    ⟨rfl, trivial⟩ h₃
  let Uj3 := fwT m [(m, .inl (false, c))] (m + (wD c)) ⟨rfl, trivial⟩ rfl
  let R4 := fwT ((m + (wD c)) + (wD j)) [((m + (wD c)) + (wD j), .inl (false, i))]
    (((m + (wD i)) + (wD j)) + (wD c)) ⟨rfl, trivial⟩ h₃'
  let Ui4 := fwT (m + (wD c)) [(m + (wD c), .inl (false, j))] ((m + (wD c)) + (wD j))
    ⟨rfl, trivial⟩ rfl
  let R5 := fwT (m + (wD j)) [(m + (wD j), .inl (false, i))] ((m + (wD i)) + (wD j))
    ⟨rfl, trivial⟩ g₃
  let Ui5 := fwT m [(m, .inl (false, j))] (m + (wD j)) ⟨rfl, trivial⟩ rfl
  let Uj6 := fwT (m + (wD j)) [(m + (wD j), .inl (false, c))] ((m + (wD c)) + (wD j))
    ⟨rfl, trivial⟩ e₅
  refine admissibleChain₃_heq (doubleModel S red) (genImg S red upIso Sc) _ _ ha hb rfl rfl
      (p₁ := 𝟙 _) (q₁ := R0) (x₁ := Uj ≫ Ui) (y₁ := Ui2 ≫ Uj2)
      (p₂ := Ui2) (q₂ := 𝟙 _) (x₂ := Uj2 ≫ R0) (y₂ := R3 ≫ Uj3)
      (p₃ := 𝟙 _) (q₃ := Uj3) (x₃ := Ui2 ≫ R3) (y₃ := R4 ≫ Ui4)
      (p₄ := Uj) (q₄ := 𝟙 _) (x₄ := Ui ≫ R0) (y₄ := R5 ≫ Ui5)
      (p₅ := 𝟙 _) (q₅ := Ui5) (x₅ := Uj ≫ R5) (y₅ := R4 ≫ Uj6)
      (p₆ := R4) (q₆ := 𝟙 _) (x₆ := Uj6 ≫ Ui5) (y₆ := Ui4 ≫ Uj3)
      (S.cross j c pUj pUi pUi2 pUj2) (S.cross i c pUj2 pR0 pR3 pUj3)
      (S.cross i j pUi2 pR3 pR4 pUi4) (S.cross i j pUi pR0 pR5 pUi5)
      (S.cross i c pUj pR5 pR4 pUj6) (S.cross j c pUj6 pUi5 pUi4 pUj3)
      ((α_ Uj Ui R0).symm ≪≫ (λ_ _).symm) ((λ_ _).hom ≫ (α_ _ _ _).hom ≫ Ui2 ◁ (ρ_ _).inv)
      (Ui2 ◁ (ρ_ _).hom ≫ (α_ _ _ _).inv ≫ (λ_ _).inv) (λ_ _ ≪≫ α_ R4 Ui4 Uj3)
      (whiskerLeftIso Uj (ρ_ (Ui ≫ R0)).symm) (Uj ◁ (ρ_ _).hom ≫ (α_ _ _ _).inv ≫ (λ_ _).inv)
      ((λ_ _).hom ≫ (α_ _ _ _).hom ≫ R4 ◁ (ρ_ _).inv) (whiskerLeftIso R4 (ρ_ (Ui4 ≫ Uj3)))
      ?hmain ?hn1 ?hm1 ?hr1 ?hl1 ?hd1 ?he1 ?hg1 ?hn2 ?hm2 ?hr2 ?hl2 ?hd2 ?he2 ?hg2 ?hn3 ?hm3 ?hr3
      ?hl3 ?hd3 ?he3 ?hg3 ?hn4 ?hm4 ?hr4 ?hl4 ?hd4 ?he4 ?hg4 ?hn5 ?hm5 ?hr5 ?hl5 ?hd5 ?he5 ?hg5
      ?hn6 ?hm6 ?hr6 ?hl6 ?hd6 ?he6 ?hg6
  case hmain =>
    have hb' := hbr pUj pUi pR0 pR5 pUi5 pR4 pUj6 pUi4 pUj3 pUi2 pUj2 pR3
    simp only [Category.assoc] at hb'
    have := slide3_right_hyp (doubleModel S red) (R0 := R0) (Ui := Ui) (Uj := Uj) (Ui2 := Ui2)
      (Uj2 := Uj2) (R3 := R3) (Uj3 := Uj3) (R4 := R4) (Ui4 := Ui4) (R5 := R5) (Ui5 := Ui5)
      (Uj6 := Uj6) (S.cross j c pUj pUi pUi2 pUj2) (S.cross i c pUj2 pR0 pR3 pUj3)
      (S.cross i j pUi2 pR3 pR4 pUi4) (S.cross i j pUi pR0 pR5 pUi5)
      (S.cross i c pUj pR5 pR4 pUj6) (S.cross j c pUj6 pUi5 pUi4 pUj3)
      hb'.symm
    convert this using 2
  case hn1 => double_regions
  case hm1 => double_regions
  case hr1 => intro _ _; double_nil
  case hl1 => intro _ _; double_single
  case hd1 => intro _ _; double_pair
  case he1 => intro _ _; double_pair
  case hg1 =>
    intro _ _ _ _
    refine (heq_of_eq (genImg_blackOn S red upIso Sc _ _ _ _ _ _ _ _ _ _)).trans ?_
    exact cross_dn_heq S red Sc _ _ _ _ _ _ _ _ _ (by double_regions) (by double_regions)
      _ _ _ _
  case hn2 => double_regions
  case hm2 => double_regions
  case hr2 => intro _ _; double_single
  case hl2 => intro _ _; double_nil
  case hd2 => intro _ _; double_pair
  case he2 => intro _ _; double_pair
  case hg2 =>
    intro _ _ _ _
    refine (heq_of_eq (genImg_blackOn S red upIso Sc _ _ _ _ _ _ _ _ _ _)).trans ?_
    exact cross_dn_heq S red Sc _ _ _ _ _ _ _ _ _ (by double_regions) (by double_regions)
      _ _ _ _
  case hn3 => double_regions
  case hm3 => double_regions
  case hr3 => intro _ _; double_nil
  case hl3 => intro _ _; double_single
  case hd3 => intro _ _; double_pair
  case he3 => intro _ _; double_pair
  case hg3 =>
    intro _ _ _ _
    refine (heq_of_eq (genImg_blackOn S red upIso Sc _ _ _ _ _ _ _ _ _ _)).trans ?_
    exact cross_dn_heq S red Sc _ _ _ _ _ _ _ _ _ (by double_regions) (by double_regions)
      _ _ _ _
  case hn4 => double_regions
  case hm4 => double_regions
  case hr4 => intro _ _; double_single
  case hl4 => intro _ _; double_nil
  case hd4 => intro _ _; double_pair
  case he4 => intro _ _; double_pair
  case hg4 =>
    intro _ _ _ _
    refine (heq_of_eq (genImg_blackOn S red upIso Sc _ _ _ _ _ _ _ _ _ _)).trans ?_
    exact cross_dn_heq S red Sc _ _ _ _ _ _ _ _ _ (by double_regions) (by double_regions)
      _ _ _ _
  case hn5 => double_regions
  case hm5 => double_regions
  case hr5 => intro _ _; double_nil
  case hl5 => intro _ _; double_single
  case hd5 => intro _ _; double_pair
  case he5 => intro _ _; double_pair
  case hg5 =>
    intro _ _ _ _
    refine (heq_of_eq (genImg_blackOn S red upIso Sc _ _ _ _ _ _ _ _ _ _)).trans ?_
    exact cross_dn_heq S red Sc _ _ _ _ _ _ _ _ _ (by double_regions) (by double_regions)
      _ _ _ _
  case hn6 => double_regions
  case hm6 => double_regions
  case hr6 => intro _ _; double_single
  case hl6 => intro _ _; double_nil
  case hd6 => intro _ _; double_pair
  case he6 => intro _ _; double_pair
  case hg6 =>
    intro _ _ _ _
    refine (heq_of_eq (genImg_blackOn S red upIso Sc _ _ _ _ _ _ _ _ _ _)).trans ?_
    exact cross_dn_heq S red Sc _ _ _ _ _ _ _ _ _ (by double_regions) (by double_regions)
      _ _ _ _

end Categorification.Stendhal.DoubleDiagram
