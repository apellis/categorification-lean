/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleRouquierBlackDown
import Categorification.WeightedKLR.RedStrands.DoubleRouquierRedDownBraidQ

/-!
# The downward black triple point `[i, j, i]` in a Rouquier family

Webster, arXiv:1309.3796v3, proof of Theorem 4.25: the downward braid relation
`ψ₀ψ₁ψ₀ - ψ₁ψ₀ψ₁ = Q̄_ij(x₀, x₁, x₂)` on black strands `[i, j, i]`, `i ≠ j`, is killed by the
generator images when the family satisfies the mixed KLR relation `RouqUpKLR.braidQ`
(Brundan, arXiv:1501.00350v1, Definition 1.1, (1.4)) for the same polynomials.

## Main results

* `downEndAlg_E0_iji`, `downEndAlg_E1_iji`, `downEndAlg_E2_iji`: the dots on `[i, j, i]`;
* `admissibleMap_braidL_iji`, `admissibleMap_braidR_iji`: the two triple composites;
* `admissibleMap_braidQ_iji`: the relation.
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

/-- Conjugation by an isomorphism, as an algebra map of endomorphism algebras. -/
def conjEndAlg {k : Type w} [CommRing k] {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞]
    [Linear k 𝒞] {Z Z' : 𝒞} (e : Z ≅ Z') : End Z →ₐ[k] End Z' where
  toFun φ := (e.inv ≫ φ ≫ e.hom : Z' ⟶ Z')
  map_one' := by
    show e.inv ≫ 𝟙 Z ≫ e.hom = 𝟙 Z'
    simp
  map_mul' φ ψ := by
    show e.inv ≫ (ψ ≫ φ) ≫ e.hom = (e.inv ≫ ψ ≫ e.hom) ≫ (e.inv ≫ φ ≫ e.hom)
    simp
  map_zero' := by
    show e.inv ≫ (0 : Z ⟶ Z) ≫ e.hom = 0
    simp
  map_add' φ ψ := by
    show e.inv ≫ ((φ : Z ⟶ Z) + (ψ : Z ⟶ Z)) ≫ e.hom =
      (e.inv ≫ φ ≫ e.hom : Z' ⟶ Z') + (e.inv ≫ ψ ≫ e.hom : Z' ⟶ Z')
    rw [Preadditive.add_comp, Preadditive.comp_add]
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    show e.inv ≫ (r • 𝟙 Z) ≫ e.hom = r • 𝟙 Z'
    rw [Linear.smul_comp, Category.id_comp, Linear.comp_smul, Iso.inv_hom_id]

theorem conjEndAlg_apply {k : Type w} [CommRing k] {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞]
    [Linear k 𝒞] {Z Z' : 𝒞} (e : Z ≅ Z') (φ : End Z) :
    conjEndAlg (k := k) e φ = (e.inv ≫ φ ≫ e.hom : Z' ⟶ Z') := rfl

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

section Dots

variable (m : X) (i j : I)

theorem downLinear_E0_iji :
    downLinear RD Λ k m [] [] (LinDiagram.of
        (KLR.Diagram.E0 (Sum.inl i : I ⊕ Fin ℓ) (.inl j) (.inl i))) =
      LinDiagram.of (Diagram.cast (moveDiagram RD Λ m [] (.black (.dot (false, i)))
        [.inl (false, j), .inl (false, i)]) rfl rfl) := by
  rw [KLR.Diagram.E0, KLR.Diagram.dl, downLinear_layer,
    downLinearLayer_of_move (g := .black (.dot (false, i))) RD Λ k m [] [] _ rfl,
    LinDiagram.cast_of]
  congr 1

theorem downLinear_E1_iji :
    downLinear RD Λ k m [] [] (LinDiagram.of
        (KLR.Diagram.E1 (Sum.inl i : I ⊕ Fin ℓ) (.inl j) (.inl i))) =
      LinDiagram.of (Diagram.cast (moveDiagram RD Λ m [.inl (false, i)]
        (.black (.dot (false, j))) [.inl (false, i)]) rfl rfl) := by
  rw [KLR.Diagram.E1, KLR.Diagram.dl, downLinear_layer,
    downLinearLayer_of_move (g := .black (.dot (false, j))) RD Λ k m [] [] _ rfl,
    LinDiagram.cast_of]
  congr 1

theorem downLinear_E2_iji :
    downLinear RD Λ k m [] [] (LinDiagram.of
        (KLR.Diagram.E2 (Sum.inl i : I ⊕ Fin ℓ) (.inl j) (.inl i))) =
      LinDiagram.of (Diagram.cast (moveDiagram RD Λ m [.inl (false, i), .inl (false, j)]
        (.black (.dot (false, i))) []) rfl rfl) := by
  rw [KLR.Diagram.E2, KLR.Diagram.dl, downLinear_layer,
    downLinearLayer_of_move (g := .black (.dot (false, i))) RD Λ k m [] [] _ rfl,
    LinDiagram.cast_of]
  congr 1

/-- The image of the dot on the left strand of the downward word `[i, j, i]`. -/
theorem downEndAlg_E0_iji
    (hc : Cond m (((m + (wD i)) + (wD j)) + (wD i))
    (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inl i, .inl j, .inl i])))
    (f₁ : (m + (wD i)) + RD.iX i = m)
    (pUi : ((m + (wD i)) + (wD j)) + RD.iX j = m + (wD i))
    (q : (((m + (wD i)) + (wD j)) + (wD i)) + RD.iX i = (m + (wD i)) + (wD j))
    (N : fwT m (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inl i, .inl j, .inl i])).word
      (((m + (wD i)) + (wD j)) + (wD i)) hc.1 hc.2.1 ⟶
    (fwT ((m + (wD i)) + (wD j)) [((m + (wD i)) + (wD j), .inl (false, i))]
        (((m + (wD i)) + (wD j)) + (wD i)) ⟨rfl, trivial⟩ rfl ≫
      fwT (m + (wD i)) [(m + (wD i), .inl (false, j))] ((m + (wD i)) + (wD j))
        ⟨rfl, trivial⟩ rfl) ≫
      fwT m [(m, .inl (false, i))] (m + (wD i)) ⟨rfl, trivial⟩ rfl)
    (N' : (fwT ((m + (wD i)) + (wD j)) [((m + (wD i)) + (wD j), .inl (false, i))]
        (((m + (wD i)) + (wD j)) + (wD i)) ⟨rfl, trivial⟩ rfl ≫
      fwT (m + (wD i)) [(m + (wD i), .inl (false, j))] ((m + (wD i)) + (wD j))
        ⟨rfl, trivial⟩ rfl) ≫
      fwT m [(m, .inl (false, i))] (m + (wD i)) ⟨rfl, trivial⟩ rfl ⟶
    fwT m (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inl i, .inl j, .inl i])).word
      (((m + (wD i)) + (wD j)) + (wD i)) hc.1 hc.2.1) :
    downEndAlg (k := k) (genImg S red upIso Sc) m [.inl i, .inl j, .inl i] hc
        (LinDiagram.of (KLR.Diagram.E0 (Sum.inl i : I ⊕ Fin ℓ) (.inl j) (.inl i))) =
      (doubleModel S red).lift.map₂ N ≫ ((S.E i q ≫ S.E j pUi) ◁ S.dot i f₁) ≫
        (doubleModel S red).lift.map₂ N' := by
  rw [downEndAlg_apply, downLinear_E0_iji, admissibleMap_of]
  change admissibleChain _ _ _ _ _ _ _ = _
  dsimp only [ObjectProperty.homMk]
  rw [admissibleChain_congr _ (show Diagram.layers (Diagram.cast (moveDiagram RD Λ m []
      (.black (.dot (false, i))) [.inl (false, j), .inl (false, i)]) rfl rfl) =
      [layer RD Λ m [] (.black (.dot (false, i))) [.inl (false, j), .inl (false, i)]] by
        simp [moveDiagram])]
  let R0 := fwT m [(m, .inl (false, i))] (m + (wD i)) ⟨rfl, trivial⟩ rfl
  let Ui := fwT (m + (wD i)) [(m + (wD i), .inl (false, j))] ((m + (wD i)) + (wD j))
    ⟨rfl, trivial⟩ rfl
  let Uj := fwT ((m + (wD i)) + (wD j)) [((m + (wD i)) + (wD j), .inl (false, i))]
    (((m + (wD i)) + (wD j)) + (wD i)) ⟨rfl, trivial⟩ rfl
  rw [admissibleChain₁_conj (doubleModel S red) _ _ _ _ (p₁ := Uj ≫ Ui) (q₁ := 𝟙 _) (x₁ := R0)
    (y₁ := R0) (S.dot i f₁) (N ≫ (Uj ≫ Ui) ◁ (ρ_ R0).inv) ((Uj ≫ Ui) ◁ (ρ_ R0).hom ≫ N')
    ?hn ?hm ?hr ?hl ?hd ?he ?hg]
  · simp only [midK, PrelaxFunctor.map₂_comp, lift_map₂_whiskerLeft,
      lift_map₂_rightUnitor_hom, Category.assoc]
    congr 1
    rw [← Category.assoc, ← Category.assoc, ← whiskerLeft_comp, ← whiskerLeft_comp,
      Category.assoc, lift_map₂_rightUnitor_inv]
    congr 2
    change (ρ_ _).inv ≫ S.dot i f₁ ▷ 𝟙 _ ≫ (ρ_ _).hom = _
    rw [whiskerRight_id]
    simp
  case hg =>
    intro _ _ _ _
    refine (heq_of_eq (genImg_blackOn S red upIso Sc _ _ _ _ _ _ _ _ _ _)).trans ?_
    exact blackImg_dot_dn' S red Sc _ i _ _ _ _ _ _ (by double_regions) (by double_regions) f₁
  case hn => double_regions
  case hm => double_regions
  case hr => intro _ _; double_pair
  case hl => intro _ _; double_nil
  case hd => intro _ _; double_single
  case he => intro _ _; double_single

/-- The image of the dot on the middle strand of the downward word `[i, j, i]`. -/
theorem downEndAlg_E1_iji
    (hc : Cond m (((m + (wD i)) + (wD j)) + (wD i))
    (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inl i, .inl j, .inl i])))
    (f₁ : (m + (wD i)) + RD.iX i = m)
    (pUi : ((m + (wD i)) + (wD j)) + RD.iX j = m + (wD i))
    (q : (((m + (wD i)) + (wD j)) + (wD i)) + RD.iX i = (m + (wD i)) + (wD j))
    (N : fwT m (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inl i, .inl j, .inl i])).word
      (((m + (wD i)) + (wD j)) + (wD i)) hc.1 hc.2.1 ⟶
    (fwT ((m + (wD i)) + (wD j)) [((m + (wD i)) + (wD j), .inl (false, i))]
        (((m + (wD i)) + (wD j)) + (wD i)) ⟨rfl, trivial⟩ rfl ≫
      fwT (m + (wD i)) [(m + (wD i), .inl (false, j))] ((m + (wD i)) + (wD j))
        ⟨rfl, trivial⟩ rfl) ≫
      fwT m [(m, .inl (false, i))] (m + (wD i)) ⟨rfl, trivial⟩ rfl)
    (N' : (fwT ((m + (wD i)) + (wD j)) [((m + (wD i)) + (wD j), .inl (false, i))]
        (((m + (wD i)) + (wD j)) + (wD i)) ⟨rfl, trivial⟩ rfl ≫
      fwT (m + (wD i)) [(m + (wD i), .inl (false, j))] ((m + (wD i)) + (wD j))
        ⟨rfl, trivial⟩ rfl) ≫
      fwT m [(m, .inl (false, i))] (m + (wD i)) ⟨rfl, trivial⟩ rfl ⟶
    fwT m (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inl i, .inl j, .inl i])).word
      (((m + (wD i)) + (wD j)) + (wD i)) hc.1 hc.2.1) :
    downEndAlg (k := k) (genImg S red upIso Sc) m [.inl i, .inl j, .inl i] hc
        (LinDiagram.of (KLR.Diagram.E1 (Sum.inl i : I ⊕ Fin ℓ) (.inl j) (.inl i))) =
      (doubleModel S red).lift.map₂ N ≫ ((S.E i q ◁ S.dot j pUi) ▷ S.E i f₁) ≫
        (doubleModel S red).lift.map₂ N' := by
  rw [downEndAlg_apply, downLinear_E1_iji, admissibleMap_of]
  change admissibleChain _ _ _ _ _ _ _ = _
  dsimp only [ObjectProperty.homMk]
  rw [admissibleChain_congr _ (show Diagram.layers (Diagram.cast (moveDiagram RD Λ m
      [.inl (false, i)] (.black (.dot (false, j))) [.inl (false, i)]) rfl rfl) =
      [layer RD Λ m [.inl (false, i)] (.black (.dot (false, j))) [.inl (false, i)]] by
        simp [moveDiagram])]
  let R0 := fwT m [(m, .inl (false, i))] (m + (wD i)) ⟨rfl, trivial⟩ rfl
  let Ui := fwT (m + (wD i)) [(m + (wD i), .inl (false, j))] ((m + (wD i)) + (wD j))
    ⟨rfl, trivial⟩ rfl
  let Uj := fwT ((m + (wD i)) + (wD j)) [((m + (wD i)) + (wD j), .inl (false, i))]
    (((m + (wD i)) + (wD j)) + (wD i)) ⟨rfl, trivial⟩ rfl
  rw [admissibleChain₁_conj (doubleModel S red) _ _ _ _ (p₁ := Uj) (q₁ := R0) (x₁ := Ui)
    (y₁ := Ui) (S.dot j pUi) (N ≫ (α_ Uj Ui R0).hom) ((α_ Uj Ui R0).inv ≫ N')
    ?hn ?hm ?hr ?hl ?hd ?he ?hg]
  · simp only [midK, PrelaxFunctor.map₂_comp, lift_map₂_associator_hom,
      lift_map₂_associator_inv, Category.assoc]
    congr 1
    simp only [← Category.assoc]
    congr 1
    simp only [Category.assoc]
    change (α_ _ _ _).hom ≫ _ ◁ (S.dot j pUi ▷ _) ≫ (α_ _ _ _).inv = _
    simp
    rfl
  case hg =>
    intro _ _ _ _
    refine (heq_of_eq (genImg_blackOn S red upIso Sc _ _ _ _ _ _ _ _ _ _)).trans ?_
    exact blackImg_dot_dn' S red Sc _ j _ _ _ _ _ _ (by double_regions) (by double_regions)
      pUi
  case hn => double_regions
  case hm => double_regions
  case hr => intro _ _; double_single
  case hl => intro _ _; double_single
  case hd => intro _ _; double_single
  case he => intro _ _; double_single

/-- The image of the dot on the right strand of the downward word `[i, j, i]`. -/
theorem downEndAlg_E2_iji
    (hc : Cond m (((m + (wD i)) + (wD j)) + (wD i))
    (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inl i, .inl j, .inl i])))
    (f₁ : (m + (wD i)) + RD.iX i = m)
    (pUi : ((m + (wD i)) + (wD j)) + RD.iX j = m + (wD i))
    (q : (((m + (wD i)) + (wD j)) + (wD i)) + RD.iX i = (m + (wD i)) + (wD j))
    (N : fwT m (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inl i, .inl j, .inl i])).word
      (((m + (wD i)) + (wD j)) + (wD i)) hc.1 hc.2.1 ⟶
    (fwT ((m + (wD i)) + (wD j)) [((m + (wD i)) + (wD j), .inl (false, i))]
        (((m + (wD i)) + (wD j)) + (wD i)) ⟨rfl, trivial⟩ rfl ≫
      fwT (m + (wD i)) [(m + (wD i), .inl (false, j))] ((m + (wD i)) + (wD j))
        ⟨rfl, trivial⟩ rfl) ≫
      fwT m [(m, .inl (false, i))] (m + (wD i)) ⟨rfl, trivial⟩ rfl)
    (N' : (fwT ((m + (wD i)) + (wD j)) [((m + (wD i)) + (wD j), .inl (false, i))]
        (((m + (wD i)) + (wD j)) + (wD i)) ⟨rfl, trivial⟩ rfl ≫
      fwT (m + (wD i)) [(m + (wD i), .inl (false, j))] ((m + (wD i)) + (wD j))
        ⟨rfl, trivial⟩ rfl) ≫
      fwT m [(m, .inl (false, i))] (m + (wD i)) ⟨rfl, trivial⟩ rfl ⟶
    fwT m (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inl i, .inl j, .inl i])).word
      (((m + (wD i)) + (wD j)) + (wD i)) hc.1 hc.2.1) :
    downEndAlg (k := k) (genImg S red upIso Sc) m [.inl i, .inl j, .inl i] hc
        (LinDiagram.of (KLR.Diagram.E2 (Sum.inl i : I ⊕ Fin ℓ) (.inl j) (.inl i))) =
      (doubleModel S red).lift.map₂ N ≫ ((S.dot i q ▷ S.E j pUi) ▷ S.E i f₁) ≫
        (doubleModel S red).lift.map₂ N' := by
  rw [downEndAlg_apply, downLinear_E2_iji, admissibleMap_of]
  change admissibleChain _ _ _ _ _ _ _ = _
  dsimp only [ObjectProperty.homMk]
  rw [admissibleChain_congr _ (show Diagram.layers (Diagram.cast (moveDiagram RD Λ m
      [.inl (false, i), .inl (false, j)] (.black (.dot (false, i))) []) rfl rfl) =
      [layer RD Λ m [.inl (false, i), .inl (false, j)] (.black (.dot (false, i))) []] by
        simp [moveDiagram])]
  let R0 := fwT m [(m, .inl (false, i))] (m + (wD i)) ⟨rfl, trivial⟩ rfl
  let Ui := fwT (m + (wD i)) [(m + (wD i), .inl (false, j))] ((m + (wD i)) + (wD j))
    ⟨rfl, trivial⟩ rfl
  let Uj := fwT ((m + (wD i)) + (wD j)) [((m + (wD i)) + (wD j), .inl (false, i))]
    (((m + (wD i)) + (wD j)) + (wD i)) ⟨rfl, trivial⟩ rfl
  rw [admissibleChain₁_conj (doubleModel S red) _ _ _ _ (p₁ := 𝟙 _) (q₁ := Ui ≫ R0) (x₁ := Uj)
    (y₁ := Uj) (S.dot i q) (N ≫ (α_ Uj Ui R0).hom ≫ (λ_ _).inv)
    ((λ_ _).hom ≫ (α_ Uj Ui R0).inv ≫ N')
    ?hn ?hm ?hr ?hl ?hd ?he ?hg]
  · simp only [midK, PrelaxFunctor.map₂_comp, lift_map₂_associator_hom,
      lift_map₂_associator_inv, lift_map₂_leftUnitor_hom, lift_map₂_leftUnitor_inv,
      Category.assoc]
    congr 1
    simp only [← Category.assoc]
    congr 1
    simp only [Category.assoc]
    change (α_ _ _ _).hom ≫ (λ_ _).inv ≫ 𝟙 _ ◁ (S.dot i q ▷ _) ≫ (λ_ _).hom ≫
      (α_ _ _ _).inv = _
    simp
    rfl
  case hg =>
    intro _ _ _ _
    refine (heq_of_eq (genImg_blackOn S red upIso Sc _ _ _ _ _ _ _ _ _ _)).trans ?_
    exact blackImg_dot_dn' S red Sc _ i _ _ _ _ _ _ (by double_regions) (by double_regions) q
  case hn => double_regions
  case hm => double_regions
  case hr => intro _ _; double_nil
  case hl => intro _ _; double_pair
  case hd => intro _ _; double_single
  case he => intro _ _; double_single

end Dots

section Braid

variable {S red upIso}

/-- The image of the downward braid `ψ₀ψ₁ψ₀` on `[i, j, i]`, read through free 2-morphisms. -/
theorem admissibleMap_braidL_iji (m : X) (i j : I)
    (ha hb : Cond m (((m + (wD i)) + (wD j)) + (wD i))
      (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inl i, .inl j, .inl i])))
    (f₁ : (m + (wD i)) + RD.iX i = m)
    (q : (((m + (wD i)) + (wD j)) + (wD i)) + RD.iX i = (m + (wD i)) + (wD j))
    (N : fwT m (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inl i, .inl j, .inl i])).word
        (((m + (wD i)) + (wD j)) + (wD i)) ha.1 ha.2.1 ⟶
      (fwT ((m + (wD i)) + (wD j)) [((m + (wD i)) + (wD j), .inl (false, i))]
          (((m + (wD i)) + (wD j)) + (wD i)) ⟨rfl, trivial⟩ rfl ≫
        fwT (m + (wD i)) [(m + (wD i), .inl (false, j))] ((m + (wD i)) + (wD j))
          ⟨rfl, trivial⟩ rfl) ≫
        fwT m [(m, .inl (false, i))] (m + (wD i)) ⟨rfl, trivial⟩ rfl)
    (N' : (fwT ((m + (wD i)) + (wD j)) [((m + (wD i)) + (wD j), .inl (false, i))]
          (((m + (wD i)) + (wD j)) + (wD i)) ⟨rfl, trivial⟩ rfl ≫
        fwT (m + (wD i)) [(m + (wD i), .inl (false, j))] ((m + (wD i)) + (wD j))
          ⟨rfl, trivial⟩ rfl) ≫
        fwT m [(m, .inl (false, i))] (m + (wD i)) ⟨rfl, trivial⟩ rfl ⟶
      fwT m (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inl i, .inl j, .inl i])).word
        (((m + (wD i)) + (wD j)) + (wD i)) ha.1 ha.2.1)
    (q₃ : ((m + (wD i)) + (wD j)) + RD.iX i = m + (wD j))
    (pUi : ((m + (wD i)) + (wD j)) + RD.iX j = m + (wD i)) (h₅ : (m + (wD j)) + RD.iX j = m) :
    admissibleMap (genImg S red upIso Sc) ha hb (downLinear RD Λ k m [] []
      (LinDiagram.of (KLR.Diagram.braidL (Sum.inl i : I ⊕ Fin ℓ) (.inl j) (.inl i)))) =
      (doubleModel S red).lift.map₂ N ≫ (α_ (S.E i q) (S.E j pUi) (S.E i f₁)).hom ≫
        (S.E i q ◁ S.cross i j pUi f₁ q₃ h₅ ≫ (α_ _ _ _).inv ≫
        S.cross i i q q₃ q q₃ ▷ S.E j h₅ ≫ (α_ _ _ _).hom ≫
        S.E i q ◁ S.cross j i q₃ h₅ pUi f₁) ≫
        (α_ (S.E i q) (S.E j pUi) (S.E i f₁)).inv ≫ (doubleModel S red).lift.map₂ N' := by
  obtain ⟨D, hD, eD⟩ := downLinear_dl3 (RD := RD) (Λ := Λ) (k := k) m [] [.inl i] [.inl j] []
    [] [.inl i] (.cross (.inl i) (.inl j)) (.cross (.inl i) (.inl i)) (.cross (.inl j) (.inl i))
    rfl rfl rfl (a := KLR.Diagram.ob [.inl i, .inl j, .inl i])
    (b := KLR.Diagram.ob [.inl j, .inl i, .inl i]) (c := KLR.Diagram.ob [.inl j, .inl i, .inl i])
    (d := KLR.Diagram.ob [.inl i, .inl j, .inl i]) rfl rfl rfl rfl rfl rfl
  erw [eD, admissibleMap_of]
  change admissibleChain _ _ _ _ _ _ _ = _
  dsimp only [ObjectProperty.homMk]
  simp only [List.map_cons, List.map_nil, DoubleStrand.down, List.nil_append,
    List.append_nil] at hD
  rw [admissibleChain_congr _ hD]
  have e₄ : (m + (wD j)) + (wD i) = (m + (wD i)) + (wD j) := by double_regions
  let R0 := fwT m [(m, .inl (false, i))] (m + (wD i)) ⟨rfl, trivial⟩ rfl
  let Ui := fwT (m + (wD i)) [(m + (wD i), .inl (false, j))] ((m + (wD i)) + (wD j))
    ⟨rfl, trivial⟩ rfl
  let Uj := fwT ((m + (wD i)) + (wD j)) [((m + (wD i)) + (wD j), .inl (false, i))]
    (((m + (wD i)) + (wD j)) + (wD i)) ⟨rfl, trivial⟩ rfl
  let Ui5 := fwT m [(m, .inl (false, j))] (m + (wD j)) ⟨rfl, trivial⟩ rfl
  let R5 := fwT (m + (wD j)) [(m + (wD j), .inl (false, i))] ((m + (wD i)) + (wD j))
    ⟨rfl, trivial⟩ e₄
  erw [admissibleChain₃_conj (doubleModel S red) (genImg S red upIso Sc) _ ha hb
      (p₁ := Uj) (q₁ := 𝟙 _) (x₁ := Ui ≫ R0) (y₁ := R5 ≫ Ui5)
      (p₂ := 𝟙 _) (q₂ := Ui5) (x₂ := Uj ≫ R5) (y₂ := Uj ≫ R5)
      (p₃ := Uj) (q₃ := 𝟙 _) (x₃ := R5 ≫ Ui5) (y₃ := Ui ≫ R0)
      (S.cross i j pUi f₁ q₃ h₅) (S.cross i i q q₃ q q₃)
      (S.cross j i q₃ h₅ pUi f₁)
      (N ≫ (α_ Uj Ui R0).hom ≫ Uj ◁ (ρ_ _).inv) (Uj ◁ (ρ_ _).hom ≫ (α_ _ _ _).inv ≫ (λ_ _).inv)
      ((λ_ _).hom ≫ (α_ _ _ _).hom ≫ Uj ◁ (ρ_ _).inv) ((Uj ◁ (ρ_ _).hom ≫ (α_ _ _ _).inv) ≫ N')
      ?hn1 ?hm1 ?hr1 ?hl1 ?hd1 ?he1 ?hg1 ?hn2 ?hm2 ?hr2 ?hl2 ?hd2 ?he2 ?hg2
      ?hn3 ?hm3 ?hr3 ?hl3 ?hd3 ?he3 ?hg3]
  · simp only [midK, PrelaxFunctor.map₂_comp,
      lift_map₂_whiskerLeft, lift_map₂_associator_hom, lift_map₂_associator_inv,
      lift_map₂_leftUnitor_hom, lift_map₂_leftUnitor_inv, lift_map₂_rightUnitor_hom,
      lift_map₂_rightUnitor_inv, lift_map_comp, Category.assoc]
    congr 1
    simp only [← Category.assoc]
    congr 1
    simp only [Category.assoc]
    bicategory
  case hn1 => double_regions
  case hm1 => double_regions
  case hr1 => intro _ _; double_single
  case hl1 => intro _ _; double_nil
  case hd1 => intro _ _; double_pair
  case he1 => intro _ _; double_pair
  case hn2 => double_regions
  case hm2 => double_regions
  case hr2 => intro _ _; double_nil
  case hl2 => intro _ _; double_single
  case hd2 => intro _ _; double_pair
  case he2 => intro _ _; double_pair
  case hn3 => double_regions
  case hm3 => double_regions
  case hr3 => intro _ _; double_single
  case hl3 => intro _ _; double_nil
  case hd3 => intro _ _; double_pair
  case he3 => intro _ _; double_pair
  case hg1 =>
    intro _ _ _ _
    refine (heq_of_eq (genImg_blackOn S red upIso Sc _ _ _ _ _ _ _ _ _ _)).trans ?_
    exact cross_dn_heq S red Sc _ i j _ _ _ _ _ _ (by double_regions) (by double_regions) _ _ _ _
  case hg2 =>
    intro _ _ _ _
    refine (heq_of_eq (genImg_blackOn S red upIso Sc _ _ _ _ _ _ _ _ _ _)).trans ?_
    exact cross_dn_heq S red Sc _ i i _ _ _ _ _ _ (by double_regions) (by double_regions) _ _ _ _
  case hg3 =>
    intro _ _ _ _
    refine (heq_of_eq (genImg_blackOn S red upIso Sc _ _ _ _ _ _ _ _ _ _)).trans ?_
    exact cross_dn_heq S red Sc _ j i _ _ _ _ _ _ (by double_regions) (by double_regions) _ _ _ _

/-- The image of the downward braid `ψ₁ψ₀ψ₁` on `[i, j, i]`, read through free 2-morphisms. -/
theorem admissibleMap_braidR_iji (m : X) (i j : I)
    (ha hb : Cond m (((m + (wD i)) + (wD j)) + (wD i))
      (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inl i, .inl j, .inl i])))
    (f₁ : (m + (wD i)) + RD.iX i = m)
    (q : (((m + (wD i)) + (wD j)) + (wD i)) + RD.iX i = (m + (wD i)) + (wD j))
    (N : fwT m (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inl i, .inl j, .inl i])).word
        (((m + (wD i)) + (wD j)) + (wD i)) ha.1 ha.2.1 ⟶
      (fwT ((m + (wD i)) + (wD j)) [((m + (wD i)) + (wD j), .inl (false, i))]
          (((m + (wD i)) + (wD j)) + (wD i)) ⟨rfl, trivial⟩ rfl ≫
        fwT (m + (wD i)) [(m + (wD i), .inl (false, j))] ((m + (wD i)) + (wD j))
          ⟨rfl, trivial⟩ rfl) ≫
        fwT m [(m, .inl (false, i))] (m + (wD i)) ⟨rfl, trivial⟩ rfl)
    (N' : (fwT ((m + (wD i)) + (wD j)) [((m + (wD i)) + (wD j), .inl (false, i))]
          (((m + (wD i)) + (wD j)) + (wD i)) ⟨rfl, trivial⟩ rfl ≫
        fwT (m + (wD i)) [(m + (wD i), .inl (false, j))] ((m + (wD i)) + (wD j))
          ⟨rfl, trivial⟩ rfl) ≫
        fwT m [(m, .inl (false, i))] (m + (wD i)) ⟨rfl, trivial⟩ rfl ⟶
      fwT m (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inl i, .inl j, .inl i])).word
        (((m + (wD i)) + (wD j)) + (wD i)) ha.1 ha.2.1)
    (f₂ : ((m + (wD i)) + (wD i)) + RD.iX i = m + (wD i))
    (e₁ : ((m + (wD i)) + (wD i)) + (wD j) = ((m + (wD i)) + (wD j)) + (wD i))
    (pUi : ((m + (wD i)) + (wD j)) + RD.iX j = m + (wD i))
    (h₆ : (((m + (wD i)) + (wD j)) + (wD i)) + RD.iX j = (m + (wD i)) + (wD i)) :
    admissibleMap (genImg S red upIso Sc) ha hb (downLinear RD Λ k m [] []
      (LinDiagram.of (KLR.Diagram.braidR (Sum.inl i : I ⊕ Fin ℓ) (.inl j) (.inl i)))) =
      (doubleModel S red).lift.map₂ N ≫ (α_ (S.E i q) (S.E j pUi) (S.E i f₁)).hom ≫
        ((α_ _ _ _).inv ≫ S.cross j i q pUi h₆ f₂ ▷ S.E i f₁ ≫ (α_ _ _ _).hom ≫
        S.E j h₆ ◁ S.cross i i f₂ f₁ f₂ f₁ ≫ (α_ _ _ _).inv ≫
        S.cross i j h₆ f₂ q pUi ▷ S.E i f₁ ≫ (α_ _ _ _).hom) ≫
        (α_ (S.E i q) (S.E j pUi) (S.E i f₁)).inv ≫ (doubleModel S red).lift.map₂ N' := by
  obtain ⟨D, hD, eD⟩ := downLinear_dl3 (RD := RD) (Λ := Λ) (k := k) m [.inl i] [] [] [.inl j]
    [.inl i] [] (.cross (.inl j) (.inl i)) (.cross (.inl i) (.inl i)) (.cross (.inl i) (.inl j))
    rfl rfl rfl (a := KLR.Diagram.ob [.inl i, .inl j, .inl i])
    (b := KLR.Diagram.ob [.inl i, .inl i, .inl j]) (c := KLR.Diagram.ob [.inl i, .inl i, .inl j])
    (d := KLR.Diagram.ob [.inl i, .inl j, .inl i]) rfl rfl rfl rfl rfl rfl
  erw [eD, admissibleMap_of]
  change admissibleChain _ _ _ _ _ _ _ = _
  dsimp only [ObjectProperty.homMk]
  simp only [List.map_cons, List.map_nil, DoubleStrand.down, List.nil_append,
    List.append_nil] at hD
  rw [admissibleChain_congr _ hD]
  let R0 := fwT m [(m, .inl (false, i))] (m + (wD i)) ⟨rfl, trivial⟩ rfl
  let Ui := fwT (m + (wD i)) [(m + (wD i), .inl (false, j))] ((m + (wD i)) + (wD j))
    ⟨rfl, trivial⟩ rfl
  let Uj := fwT ((m + (wD i)) + (wD j)) [((m + (wD i)) + (wD j), .inl (false, i))]
    (((m + (wD i)) + (wD j)) + (wD i)) ⟨rfl, trivial⟩ rfl
  let Ui2 := fwT ((m + (wD i)) + (wD i)) [((m + (wD i)) + (wD i), .inl (false, j))]
    (((m + (wD i)) + (wD j)) + (wD i)) ⟨rfl, trivial⟩ e₁
  let Uj2 := fwT (m + (wD i)) [(m + (wD i), .inl (false, i))] ((m + (wD i)) + (wD i))
    ⟨rfl, trivial⟩ rfl
  erw [admissibleChain₃_conj (doubleModel S red) (genImg S red upIso Sc) _ ha hb
      (p₁ := 𝟙 _) (q₁ := R0) (x₁ := Uj ≫ Ui) (y₁ := Ui2 ≫ Uj2)
      (p₂ := Ui2) (q₂ := 𝟙 _) (x₂ := Uj2 ≫ R0) (y₂ := Uj2 ≫ R0)
      (p₃ := 𝟙 _) (q₃ := R0) (x₃ := Ui2 ≫ Uj2) (y₃ := Uj ≫ Ui)
      (S.cross j i q pUi h₆ f₂) (S.cross i i f₂ f₁ f₂ f₁)
      (S.cross i j h₆ f₂ q pUi)
      (N ≫ (λ_ _).inv) ((λ_ _).hom ≫ (α_ _ _ _).hom ≫ Ui2 ◁ (ρ_ _).inv)
      (Ui2 ◁ (ρ_ _).hom ≫ (α_ _ _ _).inv ≫ (λ_ _).inv) ((λ_ _).hom ≫ N')
      ?hn1 ?hm1 ?hr1 ?hl1 ?hd1 ?he1 ?hg1 ?hn2 ?hm2 ?hr2 ?hl2 ?hd2 ?he2 ?hg2
      ?hn3 ?hm3 ?hr3 ?hl3 ?hd3 ?he3 ?hg3]
  · simp only [midK, PrelaxFunctor.map₂_comp,
      lift_map₂_whiskerLeft, lift_map₂_associator_hom, lift_map₂_associator_inv,
      lift_map₂_leftUnitor_hom, lift_map₂_leftUnitor_inv, lift_map₂_rightUnitor_hom,
      lift_map₂_rightUnitor_inv, lift_map_comp, Category.assoc]
    congr 1
    simp only [← Category.assoc]
    congr 1
    simp only [Category.assoc]
    bicategory
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
  case hg1 =>
    intro _ _ _ _
    refine (heq_of_eq (genImg_blackOn S red upIso Sc _ _ _ _ _ _ _ _ _ _)).trans ?_
    exact cross_dn_heq S red Sc _ j i _ _ _ _ _ _ (by double_regions) (by double_regions) _ _ _ _
  case hg2 =>
    intro _ _ _ _
    refine (heq_of_eq (genImg_blackOn S red upIso Sc _ _ _ _ _ _ _ _ _ _)).trans ?_
    exact cross_dn_heq S red Sc _ i i _ _ _ _ _ _ (by double_regions) (by double_regions) _ _ _ _
  case hg3 =>
    intro _ _ _ _
    refine (heq_of_eq (genImg_blackOn S red upIso Sc _ _ _ _ _ _ _ _ _ _)).trans ?_
    exact cross_dn_heq S red Sc _ i j _ _ _ _ _ _ (by double_regions) (by double_regions) _ _ _ _

/-- **The downward braid `[i, j, i]`** with its correction term `Q̄_ij(x₀, x₁, x₂)` is killed by
the generator images, when the family satisfies the mixed KLR relations for the same
polynomials (Brundan, arXiv:1501.00350v1, Definition 1.1, (1.4)). -/
theorem admissibleMap_braidQ_iji {Qb : I → I → MvPolynomial (Fin 2) k} (H : RouqUpKLR S Qb)
    (Q : I ⊕ Fin ℓ → I ⊕ Fin ℓ → MvPolynomial (Fin 2) k) (i j : I) (hij : i ≠ j)
    (hQ : Q (.inl i) (.inl j) = Qb i j) (m : X) {x y : X}
    (ha : Cond x y (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inl i, .inl j, .inl i])))
    (hb : Cond x y (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inl i, .inl j, .inl i]))) :
    admissibleMap (genImg S red upIso Sc) ha hb (downLinear RD Λ k m [] []
      (KLR.Diagram.relation k Q (.braidQ (.inl i) (.inl j) (Sum.inl_injective.ne hij)))) = 0 := by
  obtain rfl : m = x := ha.2.2
  obtain rfl : ((m + (wD i)) + (wD j)) + (wD i) = y := ha.2.1
  have f₁ : (m + (wD i)) + RD.iX i = m := by double_regions
  have f₂ : ((m + (wD i)) + (wD i)) + RD.iX i = m + (wD i) := by double_regions
  have e₁ : ((m + (wD i)) + (wD i)) + (wD j) = ((m + (wD i)) + (wD j)) + (wD i) := by
    double_regions
  have q : (((m + (wD i)) + (wD j)) + (wD i)) + RD.iX i = (m + (wD i)) + (wD j) := by
    double_regions
  have q₃ : ((m + (wD i)) + (wD j)) + RD.iX i = m + (wD j) := by double_regions
  have pUi : ((m + (wD i)) + (wD j)) + RD.iX j = m + (wD i) := by double_regions
  have h₅ : (m + (wD j)) + RD.iX j = m := by double_regions
  have h₆ : (((m + (wD i)) + (wD j)) + (wD i)) + RD.iX j = (m + (wD i)) + (wD i) := by
    double_regions
  let e0 : ((S.E i q ≫ S.E j pUi) ≫ S.E i f₁) ≅ (doubleModel S red).word m
      (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inl i, .inl j, .inl i])).word
      (((m + (wD i)) + (wD j)) + (wD i)) ha.1 ha.2.1 := Iso.refl _
  rw [relation_braidQ, map_sub, map_sub, map_sub, map_sub, sub_eq_zero, sub_eq_iff_eq_add']
  erw [admissibleMap_braidL_iji Sc m i j ha hb f₁ q (𝟙 _) (𝟙 _) q₃ pUi h₅,
    admissibleMap_braidR_iji Sc m i j ha hb f₁ q (𝟙 _) (𝟙 _) f₂ e₁ pUi h₆]
  change _ = _ + downEndAlg (genImg S red upIso Sc) m [.inl i, .inl j, .inl i] ha _
  rw [KLR.Diagram.lpoly, AlgHom.map_ncEval, hQ]
  let φ := conjEndAlg (k := k) ((α_ (S.E i q) (S.E j pUi) (S.E i f₁)).symm ≪≫ e0)
  have hy : (fun a => downEndAlg (genImg S red upIso Sc) m [.inl i, .inl j, .inl i] ha
      (LinDiagram.of (R := k) (![KLR.Diagram.E0 (Sum.inl i : I ⊕ Fin ℓ) (.inl j) (.inl i),
        KLR.Diagram.E1 (Sum.inl i : I ⊕ Fin ℓ) (.inl j) (.inl i),
        KLR.Diagram.E2 (Sum.inl i : I ⊕ Fin ℓ) (.inl j) (.inl i)] a))) =
      fun a => φ (![S.E i q ◁ (S.E j pUi ◁ S.dot i f₁), S.E i q ◁ (S.dot j pUi ▷ S.E i f₁),
        S.dot i q ▷ (S.E j pUi ≫ S.E i f₁)] a) := by
    funext a
    fin_cases a
    · erw [downEndAlg_E0_iji S red upIso Sc m i j ha f₁ pUi q (𝟙 _) (𝟙 _)]
      simp only [PrelaxFunctor.map₂_id, Category.id_comp]
      erw [Category.comp_id]
      simp only [φ, conjEndAlg_apply, e0, Iso.trans_inv, Iso.trans_hom, Iso.symm_inv,
        Iso.symm_hom, Iso.refl_inv, Iso.refl_hom, Category.comp_id, Category.assoc]
      simp
      exact (Category.id_comp _).symm
    · erw [downEndAlg_E1_iji S red upIso Sc m i j ha f₁ pUi q (𝟙 _) (𝟙 _)]
      simp only [PrelaxFunctor.map₂_id, Category.id_comp]
      erw [Category.comp_id]
      simp only [φ, conjEndAlg_apply, e0, Iso.trans_inv, Iso.trans_hom, Iso.symm_inv,
        Iso.symm_hom, Iso.refl_inv, Iso.refl_hom, Category.comp_id, Category.assoc]
      simp
      exact (Category.id_comp _).symm
    · erw [downEndAlg_E2_iji S red upIso Sc m i j ha f₁ pUi q (𝟙 _) (𝟙 _)]
      simp only [PrelaxFunctor.map₂_id, Category.id_comp]
      erw [Category.comp_id]
      simp only [φ, conjEndAlg_apply, e0, Iso.trans_inv, Iso.trans_hom, Iso.symm_inv,
        Iso.symm_hom, Iso.refl_inv, Iso.refl_hom, Category.comp_id, Category.assoc]
      simp
      exact (Category.id_comp _).symm
  rw [hy, ← AlgHom.map_ncEval, ← H.braidQ i j hij q pUi f₁ q₃ h₅ h₆ f₂, map_sub]
  simp only [φ, conjEndAlg_apply, e0, Iso.trans_inv, Iso.trans_hom, Iso.symm_inv,
    Iso.symm_hom, Iso.refl_inv, Iso.refl_hom, PrelaxFunctor.map₂_id, Category.id_comp,
    Category.comp_id, Category.assoc]
  erw [Category.comp_id]
  simp only [Iso.hom_inv_id_assoc]
  erw [Category.id_comp, Category.id_comp]
  simp only [Iso.hom_inv_id, Category.comp_id]
  abel

end Braid

end Categorification.Stendhal.DoubleDiagram
