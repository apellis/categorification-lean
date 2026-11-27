/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleRouquierRedDownBraid
import Categorification.TwoRep.RouqUpKLR

/-!
# The downward black quadratic relations in a Rouquier family

Webster, arXiv:1309.3796v3, proof of Theorem 4.25: on the downward black strands the
generator images `genImg` are the Rouquier family's `E`'s, its dots and its crossings. The
KLR quadratic relations and dot slides of the downward black strands are then the family's
nilHecke relations (`RouqFamily.square`, `RouqLoc.slide_left`, `RouqLoc.slide_right`) for
a repeated label and the mixed KLR relations of `RouqUpKLR` (Brundan, arXiv:1501.00350v1,
Definition 1.1, (1.2)–(1.3)) for distinct labels.

## Main results

* `admissibleMap_X2_ij`, `downEndAlg_D0_ij`, `downEndAlg_D1_ij`: the one-layer images;
* `admissibleMap_sqEq_ii`, `admissibleMap_slideLEq_ii`, `admissibleMap_slideREq_ii`: the
  nilHecke relations on two downward strands of one colour;
* `admissibleMap_sqNe_ij`, `admissibleMap_slideLNe_ij`, `admissibleMap_slideRNe_ij`: the
  quadratic relation and the dot slides on two downward strands of distinct colours.
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
  (red : (r : Fin ℓ) → {x y : X} → x + Λ r = y → (S.obj y ⟶ S.obj x))
  (upIso : (r : Fin ℓ) → (i : I) → {μ μ₁ μ₂ μ₃ : X} → (h₁ : μ + RD.iX i = μ₁) →
    (h₂ : μ + Λ r = μ₂) → (h₃ : μ₁ + Λ r = μ₃) → (h₄ : μ₂ + RD.iX i = μ₃) →
    (S.F i h₄ ≫ red r h₂ ≅ red r h₃ ≫ S.F i h₁))
  (Sc : CL.CLScalars C k)

section OneLayer

theorem downLinear_X2_ij (s : X) (i j : I) :
    downLinear RD Λ k s [] [] (LinDiagram.of (KLR.Diagram.X2 (Sum.inl i : I ⊕ Fin ℓ) (.inl j))) =
      LinDiagram.of (Diagram.cast (moveDiagram RD Λ s [] (.black (.cross false i j)) [])
        rfl rfl) := by
  rw [KLR.Diagram.X2, KLR.Diagram.dl, downLinear_layer,
    downLinearLayer_of_move (g := .black (.cross false i j)) RD Λ k s [] [] _ rfl,
    LinDiagram.cast_of]
  congr 1

/-- **The image of the downward black crossing** on `[i, j]`: the crossing of the family. -/
theorem admissibleMap_X2_ij (s : X) (i j : I) {t : X}
    (hR : (s + (wD i)) + (wD j) = t) (he : (s + (wD j)) + (wD i) = t)
    (ha : Cond s t
      (downContextObj RD Λ s [] [] (KLR.Diagram.ob [.inl i, .inl j])))
    (hb : Cond s t
      (downContextObj RD Λ s [] [] (KLR.Diagram.ob [.inl j, .inl i])))
    (h₁ : t + RD.iX j = s + (wD i)) (h₂ : (s + (wD i)) + RD.iX i = s)
    (h₃ : t + RD.iX i = s + (wD j)) (h₄ : (s + (wD j)) + RD.iX j = s)
    (N : fwT s (downContextObj RD Λ s [] [] (KLR.Diagram.ob [.inl i, .inl j])).word
        t ha.1 ha.2.1 ⟶
      fwT (s + (wD i)) [((s + (wD i)), .inl (false, j))] t ⟨rfl, trivial⟩ hR ≫
        fwT s [(s, .inl (false, i))] (s + (wD i)) ⟨rfl, trivial⟩ rfl)
    (N' : fwT (s + (wD j)) [((s + (wD j)), .inl (false, i))] t ⟨rfl, trivial⟩ he ≫
        fwT s [(s, .inl (false, j))] (s + (wD j)) ⟨rfl, trivial⟩ rfl ⟶
      fwT s (downContextObj RD Λ s [] [] (KLR.Diagram.ob [.inl j, .inl i])).word
        t hb.1 hb.2.1) :
    admissibleMap (k := k) (genImg S red upIso Sc) ha hb
        (downLinear RD Λ k s [] []
          (LinDiagram.of (KLR.Diagram.X2 (Sum.inl i : I ⊕ Fin ℓ) (.inl j)))) =
      (doubleModel S red).lift.map₂ N ≫ S.cross i j h₁ h₂ h₃ h₄ ≫
        (doubleModel S red).lift.map₂ N' := by
  subst hR
  rw [downLinear_X2_ij, admissibleMap_of]
  change admissibleChain _ _ _ _ _ _ _ = _
  dsimp only [ObjectProperty.homMk]
  rw [admissibleChain_congr _ (show Diagram.layers (Diagram.cast (moveDiagram RD Λ s []
      (.black (.cross false i j)) []) rfl rfl) =
      [layer RD Λ s [] (.black (.cross false i j)) []] by simp [moveDiagram])]
  let Ej := fwT (s + (wD i)) [((s + (wD i)), .inl (false, j))] ((s + (wD i)) + (wD j))
    ⟨rfl, trivial⟩ rfl
  let Ei := fwT s [(s, .inl (false, i))] (s + (wD i)) ⟨rfl, trivial⟩ rfl
  let Ei' := fwT (s + (wD j)) [((s + (wD j)), .inl (false, i))] ((s + (wD i)) + (wD j))
    ⟨rfl, trivial⟩ he
  let Ej' := fwT s [(s, .inl (false, j))] (s + (wD j)) ⟨rfl, trivial⟩ rfl
  rw [admissibleChain₁_conj (doubleModel S red) _ _ _ _ (p₁ := 𝟙 _) (q₁ := 𝟙 _)
    (x₁ := Ej ≫ Ei) (y₁ := Ei' ≫ Ej') (S.cross i j h₁ h₂ h₃ h₄)
    (N ≫ (λ_ _).inv ≫ 𝟙 _ ◁ (ρ_ _).inv)
    (𝟙 _ ◁ (ρ_ _).hom ≫ (λ_ _).hom ≫ N') ?hn ?hm ?hr ?hl ?hd ?he ?hg]
  · simp only [midK, PrelaxFunctor.map₂_comp, lift_map₂_whiskerLeft, lift_map₂_leftUnitor_hom,
      lift_map₂_leftUnitor_inv, lift_map₂_rightUnitor_hom, lift_map₂_rightUnitor_inv,
      Category.assoc]
    congr 1
    exact unit_conj _ _
  case hg =>
    intro _ _ _ _
    refine (heq_of_eq (genImg_blackOn S red upIso Sc _ _ _ _ _ _ _ _ _ _)).trans ?_
    exact cross_dn_heq S red Sc _ i j _ _ _ _ _ _ (by double_regions) (by double_regions) _ _ _ _
  case hn => double_regions
  case hm => double_regions
  case hr => intro _ _; double_nil
  case hl => intro _ _; double_nil
  case hd => intro _ _; double_pair
  case he => intro _ _; double_pair

theorem downLinear_D0_ij (s : X) (i j : I) :
    downLinear RD Λ k s [] [] (LinDiagram.of (KLR.Diagram.D0 (Sum.inl i : I ⊕ Fin ℓ) (.inl j))) =
      LinDiagram.of (Diagram.cast (moveDiagram RD Λ s [] (.black (.dot (false, i))) [.inl (false, j)])
        rfl rfl) := by
  rw [KLR.Diagram.D0, KLR.Diagram.dl, downLinear_layer,
    downLinearLayer_of_move (g := .black (.dot (false, i))) RD Λ k s [] [] _ rfl,
    LinDiagram.cast_of]
  congr 1

/-- **The image of the dot on the left downward black strand** of `[i, j]`. -/
theorem downEndAlg_D0_ij (s : X) (i j : I) {t : X} (hR : (s + (wD i)) + (wD j) = t)
    (hc : Cond s t
      (downContextObj RD Λ s [] [] (KLR.Diagram.ob [.inl i, .inl j])))
    (h₁ : t + RD.iX j = s + (wD i)) (h₂ : (s + (wD i)) + RD.iX i = s)
    (N : fwT s (downContextObj RD Λ s [] [] (KLR.Diagram.ob [.inl i, .inl j])).word
        t hc.1 hc.2.1 ⟶
      fwT (s + (wD i)) [((s + (wD i)), .inl (false, j))] t ⟨rfl, trivial⟩ hR ≫
        fwT s [(s, .inl (false, i))] (s + (wD i)) ⟨rfl, trivial⟩ rfl)
    (N' : fwT (s + (wD i)) [((s + (wD i)), .inl (false, j))] t ⟨rfl, trivial⟩ hR ≫
        fwT s [(s, .inl (false, i))] (s + (wD i)) ⟨rfl, trivial⟩ rfl ⟶
      fwT s (downContextObj RD Λ s [] [] (KLR.Diagram.ob [.inl i, .inl j])).word
        t hc.1 hc.2.1) :
    downEndAlg (k := k) (genImg S red upIso Sc) s [.inl i, .inl j] hc
        (LinDiagram.of (KLR.Diagram.D0 (Sum.inl i : I ⊕ Fin ℓ) (.inl j))) =
      (doubleModel S red).lift.map₂ N ≫ (S.E j h₁ ◁ S.dot i h₂) ≫
        (doubleModel S red).lift.map₂ N' := by
  subst hR
  rw [downEndAlg_apply, downLinear_D0_ij, admissibleMap_of]
  change admissibleChain _ _ _ _ _ _ _ = _
  dsimp only [ObjectProperty.homMk]
  rw [admissibleChain_congr _ (show Diagram.layers (Diagram.cast (moveDiagram RD Λ s []
      (.black (.dot (false, i))) [.inl (false, j)]) rfl rfl) =
      [layer RD Λ s [] (.black (.dot (false, i))) [.inl (false, j)]] by simp [moveDiagram])]
  let Ej := fwT (s + (wD i)) [((s + (wD i)), .inl (false, j))] ((s + (wD i)) + (wD j))
    ⟨rfl, trivial⟩ rfl
  let Ei := fwT s [(s, .inl (false, i))] (s + (wD i)) ⟨rfl, trivial⟩ rfl
  rw [admissibleChain₁_conj (doubleModel S red) _ _ _ _ (p₁ := Ej) (q₁ := 𝟙 _) (x₁ := Ei)
    (y₁ := Ei) (S.dot i h₂) (N ≫ Ej ◁ (ρ_ Ei).inv) (Ej ◁ (ρ_ Ei).hom ≫ N')
    ?hn ?hm ?hr ?hl ?hd ?he ?hg]
  · simp only [midK, PrelaxFunctor.map₂_comp, lift_map₂_whiskerLeft,
      lift_map₂_rightUnitor_hom, Category.assoc]
    congr 1
    rw [← Category.assoc, ← Category.assoc, ← whiskerLeft_comp, ← whiskerLeft_comp,
      Category.assoc, lift_map₂_rightUnitor_inv]
    congr 2
    change (ρ_ _).inv ≫ S.dot i h₂ ▷ 𝟙 _ ≫ (ρ_ _).hom = _
    rw [whiskerRight_id]
    simp
  case hg =>
    intro _ _ _ _
    refine (heq_of_eq (genImg_blackOn S red upIso Sc _ _ _ _ _ _ _ _ _ _)).trans ?_
    exact blackImg_dot_dn' S red Sc _ i _ _ _ _ _ _ (by double_regions) (by double_regions) h₂
  case hn => double_regions
  case hm => double_regions
  case hr => intro _ _; double_single
  case hl => intro _ _; double_nil
  case hd => intro _ _; double_single
  case he => intro _ _; double_single

theorem downLinear_D1_ij (s : X) (i j : I) :
    downLinear RD Λ k s [] [] (LinDiagram.of (KLR.Diagram.D1 (Sum.inl i : I ⊕ Fin ℓ) (.inl j))) =
      LinDiagram.of (Diagram.cast (moveDiagram RD Λ s [.inl (false, i)] (.black (.dot (false, j))) [])
        rfl rfl) := by
  rw [KLR.Diagram.D1, KLR.Diagram.dl, downLinear_layer,
    downLinearLayer_of_move (g := .black (.dot (false, j))) RD Λ k s [] [] _ rfl,
    LinDiagram.cast_of]
  congr 1

/-- **The image of the dot on the right downward black strand** of `[i, j]`. -/
theorem downEndAlg_D1_ij (s : X) (i j : I) {t : X} (hR : (s + (wD i)) + (wD j) = t)
    (hc : Cond s t
      (downContextObj RD Λ s [] [] (KLR.Diagram.ob [.inl i, .inl j])))
    (h₁ : t + RD.iX j = s + (wD i)) (h₂ : (s + (wD i)) + RD.iX i = s)
    (N : fwT s (downContextObj RD Λ s [] [] (KLR.Diagram.ob [.inl i, .inl j])).word
        t hc.1 hc.2.1 ⟶
      fwT (s + (wD i)) [((s + (wD i)), .inl (false, j))] t ⟨rfl, trivial⟩ hR ≫
        fwT s [(s, .inl (false, i))] (s + (wD i)) ⟨rfl, trivial⟩ rfl)
    (N' : fwT (s + (wD i)) [((s + (wD i)), .inl (false, j))] t ⟨rfl, trivial⟩ hR ≫
        fwT s [(s, .inl (false, i))] (s + (wD i)) ⟨rfl, trivial⟩ rfl ⟶
      fwT s (downContextObj RD Λ s [] [] (KLR.Diagram.ob [.inl i, .inl j])).word
        t hc.1 hc.2.1) :
    downEndAlg (k := k) (genImg S red upIso Sc) s [.inl i, .inl j] hc
        (LinDiagram.of (KLR.Diagram.D1 (Sum.inl i : I ⊕ Fin ℓ) (.inl j))) =
      (doubleModel S red).lift.map₂ N ≫ (S.dot j h₁ ▷ S.E i h₂) ≫
        (doubleModel S red).lift.map₂ N' := by
  subst hR
  rw [downEndAlg_apply, downLinear_D1_ij, admissibleMap_of]
  change admissibleChain _ _ _ _ _ _ _ = _
  dsimp only [ObjectProperty.homMk]
  rw [admissibleChain_congr _ (show Diagram.layers (Diagram.cast (moveDiagram RD Λ s [.inl (false, i)]
      (.black (.dot (false, j))) []) rfl rfl) =
      [layer RD Λ s [.inl (false, i)] (.black (.dot (false, j))) []] by simp [moveDiagram])]
  let Ej := fwT (s + (wD i)) [((s + (wD i)), .inl (false, j))] ((s + (wD i)) + (wD j))
    ⟨rfl, trivial⟩ rfl
  let Ei := fwT s [(s, .inl (false, i))] (s + (wD i)) ⟨rfl, trivial⟩ rfl
  rw [admissibleChain₁_conj (doubleModel S red) _ _ _ _ (p₁ := 𝟙 _) (q₁ := Ei) (x₁ := Ej)
    (y₁ := Ej) (S.dot j h₁) (N ≫ (λ_ _).inv) ((λ_ _).hom ≫ N')
    ?hn ?hm ?hr ?hl ?hd ?he ?hg]
  · simp only [midK, PrelaxFunctor.map₂_comp, lift_map₂_leftUnitor_hom,
      lift_map₂_leftUnitor_inv, Category.assoc]
    congr 1
    exact lunit_conj _ _
  case hg =>
    intro _ _ _ _
    refine (heq_of_eq (genImg_blackOn S red upIso Sc _ _ _ _ _ _ _ _ _ _)).trans ?_
    exact blackImg_dot_dn' S red Sc _ j _ _ _ _ _ _ (by double_regions) (by double_regions) h₁
  case hn => double_regions
  case hm => double_regions
  case hr => intro _ _; double_nil
  case hl => intro _ _; double_single
  case hd => intro _ _; double_single
  case he => intro _ _; double_single

end OneLayer

section Quadratic

variable {S red upIso}

theorem relation_sqEq {J : Type*} (Q : J → J → MvPolynomial (Fin 2) k) (c : J) :
    KLR.Diagram.relation k Q (.sqEq c) =
      LinDiagram.of (KLR.Diagram.X2 c c ≫ KLR.Diagram.X2 c c) := rfl

theorem relation_slideLEq {J : Type*} (Q : J → J → MvPolynomial (Fin 2) k) (c : J) :
    KLR.Diagram.relation k Q (.slideLEq c) =
      LinDiagram.of (KLR.Diagram.X2 c c ≫ KLR.Diagram.D0 c c) -
        LinDiagram.of (KLR.Diagram.D1 c c ≫ KLR.Diagram.X2 c c) - LinDiagram.of (𝟙 _) := rfl

theorem relation_slideREq {J : Type*} (Q : J → J → MvPolynomial (Fin 2) k) (c : J) :
    KLR.Diagram.relation k Q (.slideREq c) =
      LinDiagram.of (KLR.Diagram.D0 c c ≫ KLR.Diagram.X2 c c) -
        LinDiagram.of (KLR.Diagram.X2 c c ≫ KLR.Diagram.D1 c c) - LinDiagram.of (𝟙 _) := rfl

variable (Q : I ⊕ Fin ℓ → I ⊕ Fin ℓ → MvPolynomial (Fin 2) k)

/-- **The downward nilHecke quadratic relation** `ψ² = 0` on two black strands of one colour
is killed by the generator images. -/
theorem admissibleMap_sqEq_ii (i : I) (m : X) {x y : X}
    (ha : Cond x y (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inl i, .inl i])))
    (hb : Cond x y (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inl i, .inl i]))) :
    admissibleMap (genImg S red upIso Sc) ha hb (downLinear RD Λ k m [] []
      (KLR.Diagram.relation k Q (.sqEq (.inl i)))) = 0 := by
  obtain rfl : m = x := ha.2.2
  obtain rfl : (m + (wD i)) + (wD i) = y := ha.2.1
  obtain rfl : ha = hb := rfl
  have h₁ : ((m + (wD i)) + (wD i)) + RD.iX i = m + (wD i) := by double_regions
  have h₂ : (m + (wD i)) + RD.iX i = m := by double_regions
  change downEndAlg (genImg S red upIso Sc) m [.inl i, .inl i] ha
    (KLR.Diagram.relation k Q (.sqEq (.inl i))) = 0
  rw [relation_sqEq, LinDiagram.of_comp, ← End.mul_def, map_mul]
  rw [downEndAlg_apply _ _ _ _ (LinDiagram.of (KLR.Diagram.X2 (Sum.inl i : I ⊕ Fin ℓ) (.inl i)))]
  erw [admissibleMap_X2_ij S red upIso Sc m i i rfl rfl ha ha h₁ h₂ h₁ h₂ (𝟙 _) (𝟙 _)]
  simp only [PrelaxFunctor.map₂_id, Category.id_comp, End.mul_def]
  erw [Category.comp_id]
  exact S.square i h₁ h₂

/-- **The downward nilHecke dot slide** `ψ x₀ - x₁ ψ = 1` on two black strands of one colour
is killed by the generator images. -/
theorem admissibleMap_slideLEq_ii (i : I) (m : X) {x y : X}
    (ha : Cond x y (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inl i, .inl i])))
    (hb : Cond x y (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inl i, .inl i]))) :
    admissibleMap (genImg S red upIso Sc) ha hb (downLinear RD Λ k m [] []
      (KLR.Diagram.relation k Q (.slideLEq (.inl i)))) = 0 := by
  obtain rfl : m = x := ha.2.2
  obtain rfl : (m + (wD i)) + (wD i) = y := ha.2.1
  obtain rfl : ha = hb := rfl
  have h₁ : ((m + (wD i)) + (wD i)) + RD.iX i = m + (wD i) := by double_regions
  have h₂ : (m + (wD i)) + RD.iX i = m := by double_regions
  change downEndAlg (genImg S red upIso Sc) m [.inl i, .inl i] ha
    (KLR.Diagram.relation k Q (.slideLEq (.inl i))) = 0
  rw [relation_slideLEq, LinDiagram.of_comp, LinDiagram.of_comp, ← End.mul_def,
    ← End.mul_def, show LinDiagram.of (𝟙 _) = (1 : End (Free.of k (KLR.Diagram.ob
      [(Sum.inl i : I ⊕ Fin ℓ), .inl i]))) from rfl, map_sub, map_sub, map_one, map_mul,
    map_mul, sub_eq_zero]
  rw [downEndAlg_apply _ _ _ _ (LinDiagram.of (KLR.Diagram.X2 (Sum.inl i : I ⊕ Fin ℓ) (.inl i)))]
  erw [admissibleMap_X2_ij S red upIso Sc m i i rfl rfl ha ha h₁ h₂ h₁ h₂ (𝟙 _) (𝟙 _)]
  erw [downEndAlg_D0_ij S red upIso Sc m i i rfl ha h₁ h₂ (𝟙 _) (𝟙 _),
    downEndAlg_D1_ij S red upIso Sc m i i rfl ha h₁ h₂ (𝟙 _) (𝟙 _)]
  simp only [PrelaxFunctor.map₂_id, Category.id_comp, End.mul_def]
  erw [Category.comp_id, Category.comp_id, Category.comp_id]
  exact (S.loc i h₁ h₂).slide_right

/-- **The downward nilHecke dot slide** `x₀ ψ - ψ x₁ = 1` on two black strands of one colour
is killed by the generator images. -/
theorem admissibleMap_slideREq_ii (i : I) (m : X) {x y : X}
    (ha : Cond x y (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inl i, .inl i])))
    (hb : Cond x y (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inl i, .inl i]))) :
    admissibleMap (genImg S red upIso Sc) ha hb (downLinear RD Λ k m [] []
      (KLR.Diagram.relation k Q (.slideREq (.inl i)))) = 0 := by
  obtain rfl : m = x := ha.2.2
  obtain rfl : (m + (wD i)) + (wD i) = y := ha.2.1
  obtain rfl : ha = hb := rfl
  have h₁ : ((m + (wD i)) + (wD i)) + RD.iX i = m + (wD i) := by double_regions
  have h₂ : (m + (wD i)) + RD.iX i = m := by double_regions
  change downEndAlg (genImg S red upIso Sc) m [.inl i, .inl i] ha
    (KLR.Diagram.relation k Q (.slideREq (.inl i))) = 0
  rw [relation_slideREq, LinDiagram.of_comp, LinDiagram.of_comp, ← End.mul_def,
    ← End.mul_def, show LinDiagram.of (𝟙 _) = (1 : End (Free.of k (KLR.Diagram.ob
      [(Sum.inl i : I ⊕ Fin ℓ), .inl i]))) from rfl, map_sub, map_sub, map_one, map_mul,
    map_mul, sub_eq_zero]
  rw [downEndAlg_apply _ _ _ _ (LinDiagram.of (KLR.Diagram.X2 (Sum.inl i : I ⊕ Fin ℓ) (.inl i)))]
  erw [admissibleMap_X2_ij S red upIso Sc m i i rfl rfl ha ha h₁ h₂ h₁ h₂ (𝟙 _) (𝟙 _)]
  erw [downEndAlg_D0_ij S red upIso Sc m i i rfl ha h₁ h₂ (𝟙 _) (𝟙 _),
    downEndAlg_D1_ij S red upIso Sc m i i rfl ha h₁ h₂ (𝟙 _) (𝟙 _)]
  simp only [PrelaxFunctor.map₂_id, Category.id_comp, End.mul_def]
  erw [Category.comp_id, Category.comp_id, Category.comp_id]
  exact (S.loc i h₁ h₂).slide_left

end Quadratic

section Distinct

variable {S red upIso}

variable (Q : I ⊕ Fin ℓ → I ⊕ Fin ℓ → MvPolynomial (Fin 2) k)
  {Qb : I → I → MvPolynomial (Fin 2) k} (H : RouqUpKLR S Qb)
include H

/-- **The downward KLR quadratic relation** `ψ² = Q_ij(x₀, x₁)` on two black strands of
distinct colours is killed by the generator images, when the family satisfies the mixed KLR
relations for the same polynomials. -/
theorem admissibleMap_sqNe_ij (hQ : ∀ i j : I, Q (.inl i) (.inl j) = Qb i j) (i j : I)
    (hij : i ≠ j) (m : X) {x y : X}
    (ha : Cond x y (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inl i, .inl j])))
    (hb : Cond x y (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inl i, .inl j]))) :
    admissibleMap (genImg S red upIso Sc) ha hb (downLinear RD Λ k m [] []
      (KLR.Diagram.relation k Q (.sqNe (.inl i) (.inl j) (Sum.inl_injective.ne hij)))) = 0 := by
  obtain rfl : m = x := ha.2.2
  obtain rfl : (m + (wD i)) + (wD j) = y := ha.2.1
  have he : (m + (wD j)) + (wD i) = (m + (wD i)) + (wD j) := add_right_comm m (wD j) (wD i)
  have hm : Cond m ((m + (wD i)) + (wD j))
      (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inl j, .inl i])) :=
    ⟨colours_ok .., he, rfl⟩
  have h₁ : ((m + (wD i)) + (wD j)) + RD.iX j = m + (wD i) := by double_regions
  have h₂ : (m + (wD i)) + RD.iX i = m := by double_regions
  have h₃ : ((m + (wD i)) + (wD j)) + RD.iX i = m + (wD j) := by double_regions
  have h₄ : (m + (wD j)) + RD.iX j = m := by double_regions
  rw [relation_sqNe, map_sub, map_sub, sub_eq_zero, LinDiagram.of_comp, downLinear_comp]
  erw [admissibleMap_comp _ ha hm hb]
  erw [admissibleMap_X2_ij S red upIso Sc m i j rfl he ha hm h₁ h₂ h₃ h₄ (𝟙 _) (𝟙 _),
    admissibleMap_X2_ij S red upIso Sc m j i he rfl hm hb h₃ h₄ h₁ h₂ (𝟙 _) (𝟙 _)]
  change _ = downEndAlg (genImg S red upIso Sc) m [.inl i, .inl j] ha _
  rw [KLR.Diagram.lpoly, AlgHom.map_ncEval, hQ]
  simp only [PrelaxFunctor.map₂_id, Category.id_comp]
  erw [Category.comp_id, Category.comp_id, H.square i j hij h₁ h₂ h₃ h₄]
  congr 1
  funext a
  fin_cases a
  · erw [downEndAlg_D0_ij S red upIso Sc m i j rfl ha h₁ h₂ (𝟙 _) (𝟙 _)]
    simp only [PrelaxFunctor.map₂_id, Category.id_comp]
    erw [Category.comp_id]
    rfl
  · erw [downEndAlg_D1_ij S red upIso Sc m i j rfl ha h₁ h₂ (𝟙 _) (𝟙 _)]
    simp only [PrelaxFunctor.map₂_id, Category.id_comp]
    erw [Category.comp_id]
    rfl

/-- **The downward dot slide** `ψ x₁ = x₀ ψ` across a crossing of black strands of distinct
colours is killed by the generator images. -/
theorem admissibleMap_slideLNe_ij (i j : I)
    (hij : i ≠ j) (m : X) {x y : X}
    (ha : Cond x y (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inl i, .inl j])))
    (hb : Cond x y (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inl j, .inl i]))) :
    admissibleMap (genImg S red upIso Sc) ha hb (downLinear RD Λ k m [] []
      (KLR.Diagram.relation k Q (.slideLNe (.inl i) (.inl j) (Sum.inl_injective.ne hij)))) = 0 := by
  obtain rfl : m = x := ha.2.2
  obtain rfl : (m + (wD i)) + (wD j) = y := ha.2.1
  have he : (m + (wD j)) + (wD i) = (m + (wD i)) + (wD j) := add_right_comm m (wD j) (wD i)
  have h₁ : ((m + (wD i)) + (wD j)) + RD.iX j = m + (wD i) := by double_regions
  have h₂ : (m + (wD i)) + RD.iX i = m := by double_regions
  have h₃ : ((m + (wD i)) + (wD j)) + RD.iX i = m + (wD j) := by double_regions
  have h₄ : (m + (wD j)) + RD.iX j = m := by double_regions
  rw [relation_slideLNe, map_sub, map_sub, sub_eq_zero, LinDiagram.of_comp, LinDiagram.of_comp,
    downLinear_comp, downLinear_comp]
  erw [admissibleMap_comp _ ha hb hb, admissibleMap_comp _ ha ha hb]
  erw [admissibleMap_X2_ij S red upIso Sc m i j rfl he ha hb h₁ h₂ h₃ h₄ (𝟙 _) (𝟙 _)]
  erw [show admissibleMap (genImg S red upIso Sc) hb hb (downLinear RD Λ k m [] []
      (LinDiagram.of (KLR.Diagram.D0 (Sum.inl j : I ⊕ Fin ℓ) (.inl i)))) =
      downEndAlg (genImg S red upIso Sc) m [.inl j, .inl i] hb
        (LinDiagram.of (KLR.Diagram.D0 (Sum.inl j : I ⊕ Fin ℓ) (.inl i))) from rfl,
    show admissibleMap (genImg S red upIso Sc) ha ha (downLinear RD Λ k m [] []
      (LinDiagram.of (KLR.Diagram.D1 (Sum.inl i : I ⊕ Fin ℓ) (.inl j)))) =
      downEndAlg (genImg S red upIso Sc) m [.inl i, .inl j] ha
        (LinDiagram.of (KLR.Diagram.D1 (Sum.inl i : I ⊕ Fin ℓ) (.inl j))) from rfl]
  erw [downEndAlg_D0_ij S red upIso Sc m j i he hb h₃ h₄ (𝟙 _) (𝟙 _),
    downEndAlg_D1_ij S red upIso Sc m i j rfl ha h₁ h₂ (𝟙 _) (𝟙 _)]
  simp only [PrelaxFunctor.map₂_id, Category.id_comp]
  erw [Category.comp_id, Category.comp_id, Category.comp_id]
  exact (H.slide_right i j hij h₁ h₂ h₃ h₄).symm

/-- **The downward dot slide** `x₀ ψ = ψ x₁` across a crossing of black strands of distinct
colours is killed by the generator images. -/
theorem admissibleMap_slideRNe_ij (i j : I)
    (hij : i ≠ j) (m : X) {x y : X}
    (ha : Cond x y (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inl i, .inl j])))
    (hb : Cond x y (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inl j, .inl i]))) :
    admissibleMap (genImg S red upIso Sc) ha hb (downLinear RD Λ k m [] []
      (KLR.Diagram.relation k Q (.slideRNe (.inl i) (.inl j) (Sum.inl_injective.ne hij)))) = 0 := by
  obtain rfl : m = x := ha.2.2
  obtain rfl : (m + (wD i)) + (wD j) = y := ha.2.1
  have he : (m + (wD j)) + (wD i) = (m + (wD i)) + (wD j) := add_right_comm m (wD j) (wD i)
  have h₁ : ((m + (wD i)) + (wD j)) + RD.iX j = m + (wD i) := by double_regions
  have h₂ : (m + (wD i)) + RD.iX i = m := by double_regions
  have h₃ : ((m + (wD i)) + (wD j)) + RD.iX i = m + (wD j) := by double_regions
  have h₄ : (m + (wD j)) + RD.iX j = m := by double_regions
  rw [relation_slideRNe, map_sub, map_sub, sub_eq_zero, LinDiagram.of_comp, LinDiagram.of_comp,
    downLinear_comp, downLinear_comp]
  erw [admissibleMap_comp _ ha ha hb, admissibleMap_comp _ ha hb hb]
  erw [admissibleMap_X2_ij S red upIso Sc m i j rfl he ha hb h₁ h₂ h₃ h₄ (𝟙 _) (𝟙 _)]
  erw [show admissibleMap (genImg S red upIso Sc) ha ha (downLinear RD Λ k m [] []
      (LinDiagram.of (KLR.Diagram.D0 (Sum.inl i : I ⊕ Fin ℓ) (.inl j)))) =
      downEndAlg (genImg S red upIso Sc) m [.inl i, .inl j] ha
        (LinDiagram.of (KLR.Diagram.D0 (Sum.inl i : I ⊕ Fin ℓ) (.inl j))) from rfl,
    show admissibleMap (genImg S red upIso Sc) hb hb (downLinear RD Λ k m [] []
      (LinDiagram.of (KLR.Diagram.D1 (Sum.inl j : I ⊕ Fin ℓ) (.inl i)))) =
      downEndAlg (genImg S red upIso Sc) m [.inl j, .inl i] hb
        (LinDiagram.of (KLR.Diagram.D1 (Sum.inl j : I ⊕ Fin ℓ) (.inl i))) from rfl]
  erw [downEndAlg_D0_ij S red upIso Sc m i j rfl ha h₁ h₂ (𝟙 _) (𝟙 _),
    downEndAlg_D1_ij S red upIso Sc m j i he hb h₃ h₄ (𝟙 _) (𝟙 _)]
  simp only [PrelaxFunctor.map₂_id, Category.id_comp]
  erw [Category.comp_id, Category.comp_id, Category.comp_id]
  exact H.slide_left i j hij h₁ h₂ h₃ h₄

end Distinct

end Categorification.Stendhal.DoubleDiagram
