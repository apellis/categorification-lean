/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleRouquierRedDown
import Categorification.WeightedKLR.RedStrands.DoubleRouquierRedCup
import Categorification.WeightedKLR.RedStrands.DoubleDownRedRed
import Categorification.Diagrams.BicatInterpConj

/-!
# The downward red/black bigons in a Rouquier family

Webster, arXiv:1309.3796v3, (4.2), in the proof of Theorem 4.25. The downward translation of
the ordinary quadratic relation between a black strand and a red strand is killed by the
generator images `genImg` as soon as the two composites of the red/down crossings `a′`
(`redDownQuot`) and `b′` (`redDownDot`) are the powers of the dot recorded by the polynomials
of the relation (`DownBigon`).

The images of downward diagrams with fixed boundary form an algebra map (`downEndAlg`).
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

/-- **The images of downward diagrams on a fixed boundary**, as an algebra map. -/
def downEndAlg (m : X) (l : List (I ⊕ Fin ℓ)) {x y : X}
    (hc : Cond x y (downContextObj RD Λ m [] [] (KLR.Diagram.ob l))) :
    End (Free.of k (KLR.Diagram.ob l)) →ₐ[k]
      End (M.word x (downContextObj RD Λ m [] [] (KLR.Diagram.ob l)).word y hc.1 hc.2.1) where
  toFun f := admissibleMap G hc hc (downLinear RD Λ k m [] [] f)
  map_one' := by
    change admissibleMap G hc hc (downLinear RD Λ k m [] [] (𝟙 _)) = 𝟙 _
    rw [downLinear_id]
    change admissibleMap G hc hc (LinDiagram.of (𝟙 _)) = 𝟙 _
    rw [admissibleMap_of]
    exact (admissibleInterp G x y).map_id _
  map_mul' f g := by
    change admissibleMap G hc hc (downLinear RD Λ k m [] [] (g ≫ f)) =
      admissibleMap G hc hc (downLinear RD Λ k m [] [] g) ≫
        admissibleMap G hc hc (downLinear RD Λ k m [] [] f)
    rw [downLinear_comp, admissibleMap_comp]
  map_zero' := by
    change admissibleMap G hc hc (downLinear RD Λ k m [] [] 0) = 0
    rw [map_zero, map_zero]
  map_add' f g := by
    change admissibleMap G hc hc (downLinear RD Λ k m [] [] (f + g)) =
      admissibleMap G hc hc (downLinear RD Λ k m [] [] f) +
        admissibleMap G hc hc (downLinear RD Λ k m [] [] g)
    rw [map_add, map_add]
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    change admissibleMap G hc hc (downLinear RD Λ k m [] [] (r • 𝟙 _)) = r • 𝟙 _
    rw [map_smul, map_smul, downLinear_id]
    congr 1
    change admissibleMap G hc hc (LinDiagram.of (𝟙 _)) = 𝟙 _
    rw [admissibleMap_of]
    exact (admissibleInterp G x y).map_id _

theorem downEndAlg_apply (m : X) (l : List (I ⊕ Fin ℓ)) {x y : X}
    (hc : Cond x y (downContextObj RD Λ m [] [] (KLR.Diagram.ob l)))
    (f : End (Free.of k (KLR.Diagram.ob l))) :
    downEndAlg G m l hc f = admissibleMap G hc hc (downLinear RD Λ k m [] [] f) := rfl

/-- **The image of one downward layer** with canonical pieces, read through free 2-morphisms. -/
theorem admissibleMap_down_dl (s : X) (l r : List (I ⊕ Fin ℓ)) (g : KLR.Diagram.Gen (I ⊕ Fin ℓ))
    {mv : Move I ℓ} (hmv : downMove g = some mv) {a b : Obj (KLR.Diagram.sig (I ⊕ Fin ℓ))}
    (hda : l ++ g.dom ++ r = a.word) (hdb : l ++ g.cod ++ r = b.word) {t : X}
    (ha : Cond s t (downContextObj RD Λ s [] [] a)) (hb : Cond s t (downContextObj RD Λ s [] [] b))
    {b₁ c₁ : FB (signature RD Λ)} {p₁ : fo (S := signature RD Λ) t ⟶ b₁}
    {q₁ : c₁ ⟶ fo (S := signature RD Λ) s} {x₁ y₁ : b₁ ⟶ c₁}
    (γ₁ : M.lift.map x₁ ⟶ M.lift.map y₁)
    (N0 : fw s (downContextObj RD Λ s [] [] a).word t ha.1 ha.2.1 ⟶ p₁ ≫ (x₁ ≫ q₁))
    (N1 : p₁ ≫ (y₁ ≫ q₁) ⟶ fw s (downContextObj RD Λ s [] [] b).word t hb.1 hb.2.1)
    (hn1 : fo (S := signature RD Λ)
      ((signature RD Λ).right (layer RD Λ s ([] ++ l.map DoubleStrand.down) mv
        (r.map DoubleStrand.down ++ [])).gen) = b₁)
    (hm1 : fo (S := signature RD Λ)
      ((signature RD Λ).left (layer RD Λ s ([] ++ l.map DoubleStrand.down) mv
        (r.map DoubleStrand.down ++ [])).gen) = c₁)
    (hr1 : ∀ h e, fw ((signature RD Λ).right (layer RD Λ s ([] ++ l.map DoubleStrand.down) mv
        (r.map DoubleStrand.down ++ [])).gen)
      (layer RD Λ s ([] ++ l.map DoubleStrand.down) mv (r.map DoubleStrand.down ++ [])).right t
        h e ≍ p₁)
    (hl1 : ∀ h e, fw s (layer RD Λ s ([] ++ l.map DoubleStrand.down) mv
        (r.map DoubleStrand.down ++ [])).left
      ((signature RD Λ).left (layer RD Λ s ([] ++ l.map DoubleStrand.down) mv
        (r.map DoubleStrand.down ++ [])).gen) h e ≍ q₁)
    (hd1 : ∀ h e, fw ((signature RD Λ).left (layer RD Λ s ([] ++ l.map DoubleStrand.down) mv
        (r.map DoubleStrand.down ++ [])).gen)
      ((signature RD Λ).dom (layer RD Λ s ([] ++ l.map DoubleStrand.down) mv
        (r.map DoubleStrand.down ++ [])).gen)
      ((signature RD Λ).right (layer RD Λ s ([] ++ l.map DoubleStrand.down) mv
        (r.map DoubleStrand.down ++ [])).gen) h e ≍ x₁)
    (he1 : ∀ h e, fw ((signature RD Λ).left (layer RD Λ s ([] ++ l.map DoubleStrand.down) mv
        (r.map DoubleStrand.down ++ [])).gen)
      ((signature RD Λ).cod (layer RD Λ s ([] ++ l.map DoubleStrand.down) mv
        (r.map DoubleStrand.down ++ [])).gen)
      ((signature RD Λ).right (layer RD Λ s ([] ++ l.map DoubleStrand.down) mv
        (r.map DoubleStrand.down ++ [])).gen) h e ≍ y₁)
    (hg1 : ∀ hd hde hc hce,
      G.gen (layer RD Λ s ([] ++ l.map DoubleStrand.down) mv (r.map DoubleStrand.down ++ [])).gen
        ((signature RD Λ).left (layer RD Λ s ([] ++ l.map DoubleStrand.down) mv
          (r.map DoubleStrand.down ++ [])).gen)
        ((signature RD Λ).right (layer RD Λ s ([] ++ l.map DoubleStrand.down) mv
          (r.map DoubleStrand.down ++ [])).gen) rfl rfl hd hde hc hce ≍ γ₁) :
    admissibleMap G ha hb (downLinear RD Λ k s [] [] (LinDiagram.of (KLR.Diagram.dl l g r hda hdb))) =
      M.lift.map₂ N0 ≫ midK M p₁ q₁ γ₁ ≫ M.lift.map₂ N1 := by
  rw [KLR.Diagram.dl, downLinear_layer,
    downLinearLayer_of_move RD Λ k s [] [] (KLR.Diagram.lay l g r) hmv, LinDiagram.cast_of,
    admissibleMap_of]
  change admissibleChain _ _ _ _ _ _ _ = _
  dsimp only [ObjectProperty.homMk]
  rw [admissibleChain_congr _ (show Diagram.layers (Diagram.cast (downLayerDiagram RD Λ s [] []
      (KLR.Diagram.lay l g r) hmv) _ _) =
      [layer RD Λ s ([] ++ l.map DoubleStrand.down) mv (r.map DoubleStrand.down ++ [])] by simp)]
  exact admissibleChain₁_conj M G _ ha hb γ₁ N0 N1 hn1 hm1 hr1 hl1 hd1 he1 hg1

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

theorem blackImg_dot_dn' (z : X) (i : I) {a b : X} (ha hb hd hde hc hce) {x y : X}
    (hx : a = x) (hy : b = y) (h : y + RD.iX i = x) :
    blackImg S red Sc z (.dot (false, i)) a b ha hb hd hde hc hce ≍ S.dot i h := by
  subst hx hy; rfl

theorem downLinear_D0_ir (s : X) (i : I) (r : Fin ℓ) :
    downLinear RD Λ k s [] [] (LinDiagram.of (KLR.Diagram.D0 (Sum.inl i : I ⊕ Fin ℓ) (.inr r))) =
      LinDiagram.of (Diagram.cast (moveDiagram RD Λ s [] (.black (.dot (false, i))) [.inr r])
        rfl rfl) := by
  rw [KLR.Diagram.D0, KLR.Diagram.dl, downLinear_layer,
    downLinearLayer_of_move (g := .black (.dot (false, i))) RD Λ k s [] [] _ rfl,
    LinDiagram.cast_of]
  congr 1

theorem downEndAlg_D0_ir (s : X) (i : I) (r : Fin ℓ) {t : X} (hR : (s + (wD i)) + Λ r = t)
    (hc : Cond s t
      (downContextObj RD Λ s [] [] (KLR.Diagram.ob [.inl i, .inr r])))
    (h₁ : (s + (wD i)) + RD.iX i = s)
    (N : fwT s (downContextObj RD Λ s [] [] (KLR.Diagram.ob [.inl i, .inr r])).word
        t hc.1 hc.2.1 ⟶
      fwT (s + (wD i)) [((s + (wD i)), .inr r)] t ⟨rfl, trivial⟩ hR ≫
        fwT s [(s, .inl (false, i))] (s + (wD i)) ⟨rfl, trivial⟩ rfl)
    (N' : fwT (s + (wD i)) [((s + (wD i)), .inr r)] t ⟨rfl, trivial⟩ hR ≫
        fwT s [(s, .inl (false, i))] (s + (wD i)) ⟨rfl, trivial⟩ rfl ⟶
      fwT s (downContextObj RD Λ s [] [] (KLR.Diagram.ob [.inl i, .inr r])).word
        t hc.1 hc.2.1) :
    downEndAlg (k := k) (genImg S red upIso Sc) s [.inl i, .inr r] hc
        (LinDiagram.of (KLR.Diagram.D0 (Sum.inl i : I ⊕ Fin ℓ) (.inr r))) =
      (doubleModel S red).lift.map₂ N ≫ (red r hR ◁ S.dot i h₁) ≫
        (doubleModel S red).lift.map₂ N' := by
  subst hR
  rw [downEndAlg_apply, downLinear_D0_ir, admissibleMap_of]
  change admissibleChain _ _ _ _ _ _ _ = _
  dsimp only [ObjectProperty.homMk]
  rw [admissibleChain_congr _ (show Diagram.layers (Diagram.cast (moveDiagram RD Λ s []
      (.black (.dot (false, i))) [.inr r]) rfl rfl) =
      [layer RD Λ s [] (.black (.dot (false, i))) [.inr r]] by simp [moveDiagram])]
  let R := fwT (s + (wD i)) [((s + (wD i)), .inr r)] ((s + (wD i)) + Λ r) ⟨rfl, trivial⟩ rfl
  let Eb := fwT s [(s, .inl (false, i))] (s + (wD i)) ⟨rfl, trivial⟩ rfl
  rw [admissibleChain₁_conj (doubleModel S red) _ _ _ _ (p₁ := R) (q₁ := 𝟙 _) (x₁ := Eb)
    (y₁ := Eb) (S.dot i h₁) (N ≫ R ◁ (ρ_ Eb).inv) (R ◁ (ρ_ Eb).hom ≫ N')
    ?hn ?hm ?hr ?hl ?hd ?he ?hg]
  · simp only [midK, PrelaxFunctor.map₂_comp, lift_map₂_whiskerLeft,
      lift_map₂_rightUnitor_hom, Category.assoc]
    congr 1
    rw [← Category.assoc, ← Category.assoc, ← whiskerLeft_comp, ← whiskerLeft_comp,
      Category.assoc, lift_map₂_rightUnitor_inv]
    congr 2
    change (ρ_ _).inv ≫ S.dot i h₁ ▷ 𝟙 _ ≫ (ρ_ _).hom = _
    rw [whiskerRight_id]
    simp
  case hg =>
    intro _ _ _ _
    refine (heq_of_eq (genImg_blackOn S red upIso Sc _ _ _ _ _ _ _ _ _ _)).trans ?_
    exact blackImg_dot_dn' S red Sc _ i _ _ _ _ _ _ (by double_regions) (by double_regions) h₁
  case hn => double_regions
  case hm => double_regions
  case hr => intro _ _; double_single
  case hl => intro _ _; double_nil
  case hd => intro _ _; double_single
  case he => intro _ _; double_single

omit [∀ a b : B, Preadditive (a ⟶ b)] [AdditiveWhiskering B] in
/-- A 2-morphism conjugated by unitors. -/
theorem unit_conj {a b : B} {f g h : a ⟶ b} (γ : f ⟶ g) (κ : g ⟶ h) :
    (λ_ f).inv ≫ 𝟙 a ◁ (ρ_ f).inv ≫ 𝟙 a ◁ (γ ▷ 𝟙 b) ≫ 𝟙 a ◁ (ρ_ g).hom ≫ (λ_ g).hom ≫ κ =
      γ ≫ κ := by
  simp

theorem downLinear_X2_ir (s : X) (i : I) (r : Fin ℓ) :
    downLinear RD Λ k s [] [] (LinDiagram.of (KLR.Diagram.X2 (Sum.inl i : I ⊕ Fin ℓ) (.inr r))) =
      LinDiagram.of (Diagram.cast (moveDiagram RD Λ s [] (.blackRed (false, i) r) [])
        rfl rfl) := by
  rw [KLR.Diagram.X2, KLR.Diagram.dl, downLinear_layer,
    downLinearLayer_of_move (g := .blackRed (false, i) r) RD Λ k s [] [] _ rfl,
    LinDiagram.cast_of]
  congr 1

theorem downLinear_X2_ri (s : X) (i : I) (r : Fin ℓ) :
    downLinear RD Λ k s [] [] (LinDiagram.of (KLR.Diagram.X2 (Sum.inr r : I ⊕ Fin ℓ) (.inl i))) =
      LinDiagram.of (Diagram.cast (moveDiagram RD Λ s [] (.redBlack r (false, i)) [])
        rfl rfl) := by
  rw [KLR.Diagram.X2, KLR.Diagram.dl, downLinear_layer,
    downLinearLayer_of_move (g := .redBlack r (false, i)) RD Λ k s [] [] _ rfl,
    LinDiagram.cast_of]
  congr 1

theorem admissibleMap_X2_ir (s : X) (i : I) (r : Fin ℓ) {t : X}
    (hR : (s + (wD i)) + Λ r = t) (he : (s + Λ r) + (wD i) = t)
    (ha : Cond s t
      (downContextObj RD Λ s [] [] (KLR.Diagram.ob [.inl i, .inr r])))
    (hb : Cond s t
      (downContextObj RD Λ s [] [] (KLR.Diagram.ob [.inr r, .inl i])))
    (h₁ : (s + (wD i)) + RD.iX i = s) (h₄ : t + RD.iX i = s + Λ r)
    (N : fwT s (downContextObj RD Λ s [] [] (KLR.Diagram.ob [.inl i, .inr r])).word
        t ha.1 ha.2.1 ⟶
      fwT (s + (wD i)) [((s + (wD i)), .inr r)] t ⟨rfl, trivial⟩ hR ≫
        fwT s [(s, .inl (false, i))] (s + (wD i)) ⟨rfl, trivial⟩ rfl)
    (N' : fwT (s + Λ r) [((s + Λ r), .inl (false, i))] t ⟨rfl, trivial⟩ he ≫
        fwT s [(s, .inr r)] (s + Λ r) ⟨rfl, trivial⟩ rfl ⟶
      fwT s (downContextObj RD Λ s [] [] (KLR.Diagram.ob [.inr r, .inl i])).word
        t hb.1 hb.2.1) :
    admissibleMap (k := k) (genImg S red upIso Sc) ha hb
        (downLinear RD Λ k s [] []
          (LinDiagram.of (KLR.Diagram.X2 (Sum.inl i : I ⊕ Fin ℓ) (.inr r)))) =
      (doubleModel S red).lift.map₂ N ≫ redDownQuot S red upIso r i h₁ hR rfl h₄ ≫
        (doubleModel S red).lift.map₂ N' := by
  subst hR
  rw [downLinear_X2_ir, admissibleMap_of]
  change admissibleChain _ _ _ _ _ _ _ = _
  dsimp only [ObjectProperty.homMk]
  rw [admissibleChain_congr _ (show Diagram.layers (Diagram.cast (moveDiagram RD Λ s []
      (.blackRed (false, i) r) []) rfl rfl) =
      [layer RD Λ s [] (.blackRed (false, i) r) []] by simp [moveDiagram])]
  let R := fwT (s + (wD i)) [((s + (wD i)), .inr r)] ((s + (wD i)) + Λ r) ⟨rfl, trivial⟩ rfl
  let Eb := fwT s [(s, .inl (false, i))] (s + (wD i)) ⟨rfl, trivial⟩ rfl
  let E' := fwT (s + Λ r) [((s + Λ r), .inl (false, i))] ((s + (wD i)) + Λ r) ⟨rfl, trivial⟩ he
  let R' := fwT s [(s, .inr r)] (s + Λ r) ⟨rfl, trivial⟩ rfl
  rw [admissibleChain₁_conj (doubleModel S red) _ _ _ _ (p₁ := 𝟙 _) (q₁ := 𝟙 _)
    (x₁ := R ≫ Eb) (y₁ := E' ≫ R') (redDownQuot S red upIso r i h₁ rfl rfl h₄) (N ≫ (λ_ _).inv ≫ 𝟙 _ ◁ (ρ_ _).inv)
    (𝟙 _ ◁ (ρ_ _).hom ≫ (λ_ _).hom ≫ N') ?hn ?hm ?hr ?hl ?hd ?he ?hg]
  · simp only [midK, PrelaxFunctor.map₂_comp, lift_map₂_whiskerLeft, lift_map₂_leftUnitor_hom,
      lift_map₂_leftUnitor_inv, lift_map₂_rightUnitor_hom, lift_map₂_rightUnitor_inv,
      Category.assoc]
    congr 1
    exact unit_conj _ _
  case hg =>
    intro _ _ _ _
    exact redDownQuot_heq S red upIso r i (by double_regions) (by double_regions)
      (by double_regions) (by double_regions) _ _ _ _ _ _ _ _
  case hn => double_regions
  case hm => double_regions
  case hr => intro _ _; double_nil
  case hl => intro _ _; double_nil
  case hd => intro _ _; double_pair
  case he => intro _ _; double_pair

theorem admissibleMap_X2_ri (s : X) (i : I) (r : Fin ℓ) {t : X}
    (hR : (s + (wD i)) + Λ r = t) (he : (s + Λ r) + (wD i) = t)
    (ha : Cond s t
      (downContextObj RD Λ s [] [] (KLR.Diagram.ob [.inr r, .inl i])))
    (hb : Cond s t
      (downContextObj RD Λ s [] [] (KLR.Diagram.ob [.inl i, .inr r])))
    (h₁ : (s + (wD i)) + RD.iX i = s) (h₄ : t + RD.iX i = s + Λ r)
    (N : fwT s (downContextObj RD Λ s [] [] (KLR.Diagram.ob [.inr r, .inl i])).word
        t ha.1 ha.2.1 ⟶
      fwT (s + Λ r) [((s + Λ r), .inl (false, i))] t ⟨rfl, trivial⟩ he ≫
        fwT s [(s, .inr r)] (s + Λ r) ⟨rfl, trivial⟩ rfl)
    (N' : fwT (s + (wD i)) [((s + (wD i)), .inr r)] t ⟨rfl, trivial⟩ hR ≫
        fwT s [(s, .inl (false, i))] (s + (wD i)) ⟨rfl, trivial⟩ rfl ⟶
      fwT s (downContextObj RD Λ s [] [] (KLR.Diagram.ob [.inl i, .inr r])).word
        t hb.1 hb.2.1) :
    admissibleMap (k := k) (genImg S red upIso Sc) ha hb
        (downLinear RD Λ k s [] []
          (LinDiagram.of (KLR.Diagram.X2 (Sum.inr r : I ⊕ Fin ℓ) (.inl i)))) =
      (doubleModel S red).lift.map₂ N ≫ redDownDot S red upIso r i h₁ hR rfl h₄ ≫
        (doubleModel S red).lift.map₂ N' := by
  subst hR
  rw [downLinear_X2_ri, admissibleMap_of]
  change admissibleChain _ _ _ _ _ _ _ = _
  dsimp only [ObjectProperty.homMk]
  rw [admissibleChain_congr _ (show Diagram.layers (Diagram.cast (moveDiagram RD Λ s []
      (.redBlack r (false, i)) []) rfl rfl) =
      [layer RD Λ s [] (.redBlack r (false, i)) []] by simp [moveDiagram])]
  let R := fwT (s + (wD i)) [((s + (wD i)), .inr r)] ((s + (wD i)) + Λ r) ⟨rfl, trivial⟩ rfl
  let Eb := fwT s [(s, .inl (false, i))] (s + (wD i)) ⟨rfl, trivial⟩ rfl
  let E' := fwT (s + Λ r) [((s + Λ r), .inl (false, i))] ((s + (wD i)) + Λ r) ⟨rfl, trivial⟩ he
  let R' := fwT s [(s, .inr r)] (s + Λ r) ⟨rfl, trivial⟩ rfl
  rw [admissibleChain₁_conj (doubleModel S red) _ _ _ _ (p₁ := 𝟙 _) (q₁ := 𝟙 _)
    (x₁ := E' ≫ R') (y₁ := R ≫ Eb) (redDownDot S red upIso r i h₁ rfl rfl h₄)
    (N ≫ (λ_ _).inv ≫ 𝟙 _ ◁ (ρ_ _).inv)
    (𝟙 _ ◁ (ρ_ _).hom ≫ (λ_ _).hom ≫ N') ?hn ?hm ?hr ?hl ?hd ?he ?hg]
  · simp only [midK, PrelaxFunctor.map₂_comp, lift_map₂_whiskerLeft, lift_map₂_leftUnitor_hom,
      lift_map₂_leftUnitor_inv, lift_map₂_rightUnitor_hom, lift_map₂_rightUnitor_inv,
      Category.assoc]
    congr 1
    exact unit_conj _ _
  case hg =>
    intro _ _ _ _
    exact redDownDot_heq S red upIso r i (by double_regions) (by double_regions)
      (by double_regions) (by double_regions) _ _ _ _ _ _ _ _
  case hn => double_regions
  case hm => double_regions
  case hr => intro _ _; double_nil
  case hl => intro _ _; double_nil
  case hd => intro _ _; double_pair
  case he => intro _ _; double_pair

omit [∀ a b : B, Preadditive (a ⟶ b)] [AdditiveWhiskering B] in
/-- A 2-morphism whiskered by an identity, conjugated by the left unitor. -/
theorem lunit_conj {a b : B} {f g h : a ⟶ b} (γ : f ⟶ g) (κ : g ⟶ h) :
    (λ_ f).inv ≫ 𝟙 a ◁ γ ≫ (λ_ g).hom ≫ κ = γ ≫ κ := by
  simp

theorem downLinear_D1_ri (s : X) (i : I) (r : Fin ℓ) :
    downLinear RD Λ k s [] [] (LinDiagram.of (KLR.Diagram.D1 (Sum.inr r : I ⊕ Fin ℓ) (.inl i))) =
      LinDiagram.of (Diagram.cast (moveDiagram RD Λ s [.inr r] (.black (.dot (false, i))) [])
        rfl rfl) := by
  rw [KLR.Diagram.D1, KLR.Diagram.dl, downLinear_layer,
    downLinearLayer_of_move (g := .black (.dot (false, i))) RD Λ k s [] [] _ rfl,
    LinDiagram.cast_of]
  congr 1

theorem downEndAlg_D1_ri (s : X) (i : I) (r : Fin ℓ) {t : X} (he : (s + Λ r) + (wD i) = t)
    (hc : Cond s t
      (downContextObj RD Λ s [] [] (KLR.Diagram.ob [.inr r, .inl i])))
    (h₄ : t + RD.iX i = s + Λ r)
    (N : fwT s (downContextObj RD Λ s [] [] (KLR.Diagram.ob [.inr r, .inl i])).word
        t hc.1 hc.2.1 ⟶
      fwT (s + Λ r) [((s + Λ r), .inl (false, i))] t ⟨rfl, trivial⟩ he ≫
        fwT s [(s, .inr r)] (s + Λ r) ⟨rfl, trivial⟩ rfl)
    (N' : fwT (s + Λ r) [((s + Λ r), .inl (false, i))] t ⟨rfl, trivial⟩ he ≫
        fwT s [(s, .inr r)] (s + Λ r) ⟨rfl, trivial⟩ rfl ⟶
      fwT s (downContextObj RD Λ s [] [] (KLR.Diagram.ob [.inr r, .inl i])).word
        t hc.1 hc.2.1) :
    downEndAlg (k := k) (genImg S red upIso Sc) s [.inr r, .inl i] hc
        (LinDiagram.of (KLR.Diagram.D1 (Sum.inr r : I ⊕ Fin ℓ) (.inl i))) =
      (doubleModel S red).lift.map₂ N ≫ (S.dot i h₄ ▷ red r rfl) ≫
        (doubleModel S red).lift.map₂ N' := by
  subst he
  rw [downEndAlg_apply, downLinear_D1_ri, admissibleMap_of]
  change admissibleChain _ _ _ _ _ _ _ = _
  dsimp only [ObjectProperty.homMk]
  rw [admissibleChain_congr _ (show Diagram.layers (Diagram.cast (moveDiagram RD Λ s [.inr r]
      (.black (.dot (false, i))) []) rfl rfl) =
      [layer RD Λ s [.inr r] (.black (.dot (false, i))) []] by simp [moveDiagram])]
  let E' := fwT (s + Λ r) [((s + Λ r), .inl (false, i))] ((s + Λ r) + (wD i)) ⟨rfl, trivial⟩ rfl
  let R' := fwT s [(s, .inr r)] (s + Λ r) ⟨rfl, trivial⟩ rfl
  rw [admissibleChain₁_conj (doubleModel S red) _ _ _ _ (p₁ := 𝟙 _) (q₁ := R') (x₁ := E')
    (y₁ := E') (S.dot i h₄) (N ≫ (λ_ _).inv) ((λ_ _).hom ≫ N')
    ?hn ?hm ?hr ?hl ?hd ?he ?hg]
  · simp only [midK, PrelaxFunctor.map₂_comp, lift_map₂_leftUnitor_hom,
      lift_map₂_leftUnitor_inv, Category.assoc]
    congr 1
    exact lunit_conj _ _
  case hg =>
    intro _ _ _ _
    refine (heq_of_eq (genImg_blackOn S red upIso Sc _ _ _ _ _ _ _ _ _ _)).trans ?_
    exact blackImg_dot_dn' S red Sc _ i _ _ _ _ _ _ (by double_regions) (by double_regions) h₄
  case hn => double_regions
  case hm => double_regions
  case hr => intro _ _; double_nil
  case hl => intro _ _; double_single
  case hd => intro _ _; double_single
  case he => intro _ _; double_single

section Bigon

omit [AddCommGroup X] in
theorem ncEval_X_pow_two {A : Type*} [Ring A] [Algebra k A] (y : Fin 2 → A) (j : Fin 2) (n : ℕ) :
    KLR.ncEval y (MvPolynomial.X j ^ n : MvPolynomial (Fin 2) k) = y j ^ n := by
  rw [MvPolynomial.X_pow_eq_monomial]
  unfold KLR.ncEval
  change (Finsupp.single _ _).sum _ = _
  rw [Finsupp.sum_single_index (by simp), map_one, one_mul]
  fin_cases j <;> simp [List.ofFn_succ, Finsupp.single_apply]

omit [∀ a b : B, Preadditive (a ⟶ b)] [AdditiveWhiskering B] in
theorem whiskerLeft_pow {a b c : B} (f : a ⟶ b) {g : b ⟶ c} (γ : g ⟶ g) (n : ℕ) :
    (show End (f ≫ g) from f ◁ γ) ^ n = f ◁ ((show End g from γ) ^ n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, End.mul_def, End.mul_def, ih, whiskerLeft_comp]

omit [∀ a b : B, Preadditive (a ⟶ b)] [AdditiveWhiskering B] in
theorem whiskerRight_pow {a b c : B} {f : a ⟶ b} (γ : f ⟶ f) (g : b ⟶ c) (n : ℕ) :
    (show End (f ≫ g) from γ ▷ g) ^ n = ((show End f from γ) ^ n) ▷ g := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, End.mul_def, End.mul_def, ih, comp_whiskerRight]

/-- **The red/black bigons**, the downward form of (4.2): the composites of the red/down
crossings `a′` and `b′` are powers of the dot, with exponent `n r i` (`⟨α_i^∨, λ_r⟩` in
Webster's cyclotomic setting). -/
def DownBigon (n : Fin ℓ → I → ℕ) : Prop :=
  ∀ (r : Fin ℓ) (i : I) {μ μ₁ μ₂ μ₃ : X} (h₁ : μ + RD.iX i = μ₁) (h₂ : μ + Λ r = μ₂)
    (h₃ : μ₁ + Λ r = μ₃) (h₄ : μ₂ + RD.iX i = μ₃),
    redDownQuot S red upIso r i h₁ h₂ h₃ h₄ ≫ redDownDot S red upIso r i h₁ h₂ h₃ h₄ =
        red r h₂ ◁ ((show End (S.E i h₁) from S.dot i h₁) ^ n r i) ∧
      redDownDot S red upIso r i h₁ h₂ h₃ h₄ ≫ redDownQuot S red upIso r i h₁ h₂ h₃ h₄ =
        ((show End (S.E i h₄) from S.dot i h₄) ^ n r i) ▷ red r h₃

/-- **The bigon `[i, r]`** (downward form of (4.2) with the black strand on the left) is killed
by the generator images. -/
theorem admissibleMap_sqNe_ir (n : Fin ℓ → I → ℕ) (hB : DownBigon S red upIso n)
    (Q : I ⊕ Fin ℓ → I ⊕ Fin ℓ → MvPolynomial (Fin 2) k) (i : I) (r : Fin ℓ)
    (hQ : Q (.inl i) (.inr r) = MvPolynomial.X 0 ^ n r i) (m : X) {x y : X}
    (ha : Cond x y (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inl i, .inr r])))
    (hb : Cond x y (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inl i, .inr r]))) :
    admissibleMap (genImg S red upIso Sc) ha hb (downLinear RD Λ k m [] []
      (KLR.Diagram.relation k Q (.sqNe (.inl i) (.inr r) Sum.inl_ne_inr))) = 0 := by
  obtain rfl : m = x := ha.2.2
  obtain rfl : (m + (wD i)) + Λ r = y := ha.2.1
  have hm : Cond m ((m + (wD i)) + Λ r)
      (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inr r, .inl i])) :=
    ⟨colours_ok .., add_right_comm m (Λ r) (wD i), rfl⟩
  have h₁ : (m + (wD i)) + RD.iX i = m := by double_regions
  have h₄ : ((m + (wD i)) + Λ r) + RD.iX i = m + Λ r := by double_regions
  have he : (m + Λ r) + (wD i) = (m + (wD i)) + Λ r := by double_regions
  rw [relation_sqNe]
  rw [map_sub, map_sub, sub_eq_zero, LinDiagram.of_comp, downLinear_comp]
  erw [admissibleMap_comp _ ha hm hb]
  erw [admissibleMap_X2_ir S red upIso Sc m i r rfl he ha hm h₁ h₄ (𝟙 _) (𝟙 _),
    admissibleMap_X2_ri S red upIso Sc m i r rfl he hm hb h₁ h₄ (𝟙 _) (𝟙 _)]
  change _ = downEndAlg (genImg S red upIso Sc) m [.inl i, .inr r] ha _
  rw [KLR.Diagram.lpoly, AlgHom.map_ncEval, hQ, ncEval_X_pow_two]
  simp only [Matrix.cons_val_zero]
  rw [downEndAlg_D0_ir S red upIso Sc m i r rfl ha h₁ (𝟙 _) (𝟙 _)]
  simp only [PrelaxFunctor.map₂_id, Category.id_comp]
  erw [Category.comp_id, Category.comp_id, Category.comp_id, (hB r i h₁ rfl rfl h₄).1]
  exact (whiskerLeft_pow _ _ _).symm

/-- **The bigon `[r, i]`** (downward form of (4.2) with the black strand on the right) is
killed by the generator images. -/
theorem admissibleMap_sqNe_ri (n : Fin ℓ → I → ℕ) (hB : DownBigon S red upIso n)
    (Q : I ⊕ Fin ℓ → I ⊕ Fin ℓ → MvPolynomial (Fin 2) k) (i : I) (r : Fin ℓ)
    (hQ : Q (.inr r) (.inl i) = MvPolynomial.X 1 ^ n r i) (m : X) {x y : X}
    (ha : Cond x y (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inr r, .inl i])))
    (hb : Cond x y (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inr r, .inl i]))) :
    admissibleMap (genImg S red upIso Sc) ha hb (downLinear RD Λ k m [] []
      (KLR.Diagram.relation k Q (.sqNe (.inr r) (.inl i) Sum.inr_ne_inl))) = 0 := by
  obtain rfl : m = x := ha.2.2
  obtain rfl : (m + Λ r) + (wD i) = y := ha.2.1
  have hR : (m + (wD i)) + Λ r = (m + Λ r) + (wD i) := add_right_comm m (wD i) (Λ r)
  have hm : Cond m ((m + Λ r) + (wD i))
      (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inl i, .inr r])) :=
    ⟨colours_ok .., hR, rfl⟩
  have h₁ : (m + (wD i)) + RD.iX i = m := by double_regions
  have h₄ : ((m + Λ r) + (wD i)) + RD.iX i = m + Λ r := by double_regions
  rw [relation_sqNe]
  rw [map_sub, map_sub, sub_eq_zero, LinDiagram.of_comp, downLinear_comp]
  erw [admissibleMap_comp _ ha hm hb]
  erw [admissibleMap_X2_ri S red upIso Sc m i r hR rfl ha hm h₁ h₄ (𝟙 _) (𝟙 _),
    admissibleMap_X2_ir S red upIso Sc m i r hR rfl hm hb h₁ h₄ (𝟙 _) (𝟙 _)]
  change _ = downEndAlg (genImg S red upIso Sc) m [.inr r, .inl i] ha _
  rw [KLR.Diagram.lpoly, AlgHom.map_ncEval, hQ, ncEval_X_pow_two]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
  erw [downEndAlg_D1_ri S red upIso Sc m i r rfl ha h₄ (𝟙 _) (𝟙 _)]
  simp only [PrelaxFunctor.map₂_id, Category.id_comp]
  erw [Category.comp_id, Category.comp_id, Category.comp_id, (hB r i h₁ hR rfl h₄).2]
  exact (whiskerRight_pow _ _ _).symm

end Bigon

section Slide

variable (Q : I ⊕ Fin ℓ → I ⊕ Fin ℓ → MvPolynomial (Fin 2) k)

/-- The downward slide of a red dot under a black/red crossing translates to zero. -/
theorem downLinear_slideLNe_ir (m : X) (i : I) (r : Fin ℓ) :
    downLinear RD Λ k m [] []
      (KLR.Diagram.relation k Q (.slideLNe (.inl i) (.inr r) Sum.inl_ne_inr)) = 0 := by
  rw [relation_slideLNe, map_sub, LinDiagram.of_comp, LinDiagram.of_comp, downLinear_comp,
    downLinear_comp]
  have hD : downLinear RD Λ k m [] []
      (LinDiagram.of (KLR.Diagram.D0 (Sum.inr r : I ⊕ Fin ℓ) (.inl i))) = 0 :=
    downLinear_dl_red_dot RD Λ k _ _ _ [] r [.inl i] rfl rfl
  have hD' : downLinear RD Λ k m [] []
      (LinDiagram.of (KLR.Diagram.D1 (Sum.inl i : I ⊕ Fin ℓ) (.inr r))) = 0 :=
    downLinear_dl_red_dot RD Λ k _ _ _ [.inl i] r [] rfl rfl
  erw [hD, hD']
  simp

/-- The downward slide of a red dot under a red/black crossing translates to zero. -/
theorem downLinear_slideRNe_ri (m : X) (i : I) (r : Fin ℓ) :
    downLinear RD Λ k m [] []
      (KLR.Diagram.relation k Q (.slideRNe (.inr r) (.inl i) Sum.inr_ne_inl)) = 0 := by
  rw [relation_slideRNe, map_sub, LinDiagram.of_comp, LinDiagram.of_comp, downLinear_comp,
    downLinear_comp]
  have hD : downLinear RD Λ k m [] []
      (LinDiagram.of (KLR.Diagram.D0 (Sum.inr r : I ⊕ Fin ℓ) (.inl i))) = 0 :=
    downLinear_dl_red_dot RD Λ k _ _ _ [] r [.inl i] rfl rfl
  have hD' : downLinear RD Λ k m [] []
      (LinDiagram.of (KLR.Diagram.D1 (Sum.inl i : I ⊕ Fin ℓ) (.inr r))) = 0 :=
    downLinear_dl_red_dot RD Λ k _ _ _ [.inl i] r [] rfl rfl
  erw [hD, hD']
  simp

/-- **The downward black dot slides through the crossing `b′`** with a red strand. -/
theorem admissibleMap_slideLNe_ri (hdot : UpIsoDotNatural S red upIso) (i : I) (r : Fin ℓ)
    (m : X) {x y : X}
    (ha : Cond x y (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inr r, .inl i])))
    (hb : Cond x y (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inl i, .inr r]))) :
    admissibleMap (genImg S red upIso Sc) ha hb (downLinear RD Λ k m [] []
      (KLR.Diagram.relation k Q (.slideLNe (.inr r) (.inl i) Sum.inr_ne_inl))) = 0 := by
  obtain rfl : m = x := ha.2.2
  obtain rfl : (m + Λ r) + (wD i) = y := ha.2.1
  have hR : (m + (wD i)) + Λ r = (m + Λ r) + (wD i) := add_right_comm m (wD i) (Λ r)
  have h₁ : (m + (wD i)) + RD.iX i = m := by double_regions
  have h₄ : ((m + Λ r) + (wD i)) + RD.iX i = m + Λ r := by double_regions
  rw [relation_slideLNe, map_sub, map_sub, sub_eq_zero, LinDiagram.of_comp, LinDiagram.of_comp,
    downLinear_comp, downLinear_comp]
  erw [admissibleMap_comp _ ha hb hb, admissibleMap_comp _ ha ha hb]
  erw [admissibleMap_X2_ri S red upIso Sc m i r hR rfl ha hb h₁ h₄ (𝟙 _) (𝟙 _)]
  erw [show admissibleMap (genImg S red upIso Sc) hb hb (downLinear RD Λ k m [] []
      (LinDiagram.of (KLR.Diagram.D0 (Sum.inl i : I ⊕ Fin ℓ) (.inr r)))) =
      downEndAlg (genImg S red upIso Sc) m [.inl i, .inr r] hb
        (LinDiagram.of (KLR.Diagram.D0 (Sum.inl i : I ⊕ Fin ℓ) (.inr r))) from rfl,
    show admissibleMap (genImg S red upIso Sc) ha ha (downLinear RD Λ k m [] []
      (LinDiagram.of (KLR.Diagram.D1 (Sum.inr r : I ⊕ Fin ℓ) (.inl i)))) =
      downEndAlg (genImg S red upIso Sc) m [.inr r, .inl i] ha
        (LinDiagram.of (KLR.Diagram.D1 (Sum.inr r : I ⊕ Fin ℓ) (.inl i))) from rfl]
  erw [downEndAlg_D0_ir S red upIso Sc m i r hR hb h₁ (𝟙 _) (𝟙 _),
    downEndAlg_D1_ri S red upIso Sc m i r rfl ha h₄ (𝟙 _) (𝟙 _)]
  simp only [PrelaxFunctor.map₂_id, Category.id_comp]
  erw [Category.comp_id, Category.comp_id, Category.comp_id]
  exact (redDownDot_dot S red upIso hdot r i h₁ hR rfl h₄).symm

/-- **The downward black dot slides through the crossing `a′`** with a red strand. -/
theorem admissibleMap_slideRNe_ir (hdot : UpIsoDotNatural S red upIso) (i : I) (r : Fin ℓ)
    (m : X) {x y : X}
    (ha : Cond x y (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inl i, .inr r])))
    (hb : Cond x y (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inr r, .inl i]))) :
    admissibleMap (genImg S red upIso Sc) ha hb (downLinear RD Λ k m [] []
      (KLR.Diagram.relation k Q (.slideRNe (.inl i) (.inr r) Sum.inl_ne_inr))) = 0 := by
  obtain rfl : m = x := ha.2.2
  obtain rfl : (m + (wD i)) + Λ r = y := ha.2.1
  have he : (m + Λ r) + (wD i) = (m + (wD i)) + Λ r := add_right_comm m (Λ r) (wD i)
  have h₁ : (m + (wD i)) + RD.iX i = m := by double_regions
  have h₄ : ((m + (wD i)) + Λ r) + RD.iX i = m + Λ r := by double_regions
  rw [relation_slideRNe, map_sub, map_sub, sub_eq_zero, LinDiagram.of_comp, LinDiagram.of_comp,
    downLinear_comp, downLinear_comp]
  erw [admissibleMap_comp _ ha ha hb, admissibleMap_comp _ ha hb hb]
  erw [admissibleMap_X2_ir S red upIso Sc m i r rfl he ha hb h₁ h₄ (𝟙 _) (𝟙 _)]
  erw [show admissibleMap (genImg S red upIso Sc) ha ha (downLinear RD Λ k m [] []
      (LinDiagram.of (KLR.Diagram.D0 (Sum.inl i : I ⊕ Fin ℓ) (.inr r)))) =
      downEndAlg (genImg S red upIso Sc) m [.inl i, .inr r] ha
        (LinDiagram.of (KLR.Diagram.D0 (Sum.inl i : I ⊕ Fin ℓ) (.inr r))) from rfl,
    show admissibleMap (genImg S red upIso Sc) hb hb (downLinear RD Λ k m [] []
      (LinDiagram.of (KLR.Diagram.D1 (Sum.inr r : I ⊕ Fin ℓ) (.inl i)))) =
      downEndAlg (genImg S red upIso Sc) m [.inr r, .inl i] hb
        (LinDiagram.of (KLR.Diagram.D1 (Sum.inr r : I ⊕ Fin ℓ) (.inl i))) from rfl]
  erw [downEndAlg_D0_ir S red upIso Sc m i r rfl ha h₁ (𝟙 _) (𝟙 _),
    downEndAlg_D1_ri S red upIso Sc m i r he hb h₄ (𝟙 _) (𝟙 _)]
  simp only [PrelaxFunctor.map₂_id, Category.id_comp]
  erw [Category.comp_id, Category.comp_id, Category.comp_id]
  exact redDownQuot_dot S red upIso hdot r i h₁ rfl rfl h₄

end Slide

end Categorification.Stendhal.DoubleDiagram
