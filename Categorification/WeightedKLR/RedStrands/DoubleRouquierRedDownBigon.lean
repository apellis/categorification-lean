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

theorem downEndAlg_D0_ir (s : X) (i : I) (r : Fin ℓ)
    (hc : Cond s ((s + (wD i)) + Λ r)
      (downContextObj RD Λ s [] [] (KLR.Diagram.ob [.inl i, .inr r])))
    (h₁ : (s + (wD i)) + RD.iX i = s)
    (N : fwT s (downContextObj RD Λ s [] [] (KLR.Diagram.ob [.inl i, .inr r])).word
        ((s + (wD i)) + Λ r) hc.1 hc.2.1 ⟶
      fwT (s + (wD i)) [((s + (wD i)), .inr r)] ((s + (wD i)) + Λ r) ⟨rfl, trivial⟩ rfl ≫
        fwT s [(s, .inl (false, i))] (s + (wD i)) ⟨rfl, trivial⟩ rfl)
    (N' : fwT (s + (wD i)) [((s + (wD i)), .inr r)] ((s + (wD i)) + Λ r) ⟨rfl, trivial⟩ rfl ≫
        fwT s [(s, .inl (false, i))] (s + (wD i)) ⟨rfl, trivial⟩ rfl ⟶
      fwT s (downContextObj RD Λ s [] [] (KLR.Diagram.ob [.inl i, .inr r])).word
        ((s + (wD i)) + Λ r) hc.1 hc.2.1) :
    downEndAlg (k := k) (genImg S red upIso Sc) s [.inl i, .inr r] hc
        (LinDiagram.of (KLR.Diagram.D0 (Sum.inl i : I ⊕ Fin ℓ) (.inr r))) =
      (doubleModel S red).lift.map₂ N ≫ (red r rfl ◁ S.dot i h₁) ≫
        (doubleModel S red).lift.map₂ N' := by
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

end Categorification.Stendhal.DoubleDiagram
