/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleRouquierRedDownBraid
import Categorification.TwoRep.RouqMixedCycLeft
import Categorification.TwoRep.RouqFullCL

/-!
# Red/down crossings of two black strands by mates

Webster, arXiv:1309.3796v3, proof of Theorem 4.25. The red/down crossing `a′` is the mate of
the red/up crossing for the adjunctions `E ⊣ F`. The downward mixed crossing is, up to the
scalar `t_ij⁻¹`, the mate of the upward one for these adjunctions
(`RouqFamily.mixed_crossDn_rightMate`). So the naturality of the red/up crossing for upward
crossings (4.4d) is equivalent to the naturality of `a′` for downward crossings
(`upIsoCrossNatural_iff_downQuotCrossNatural`).
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

variable {B : Type*} [Bicategory B] [∀ a b : B, Preadditive (a ⟶ b)] [AdditiveWhiskering B]
  {k : Type w} [CommRing k] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (g : b ⟶ c), (postcomp a g).Linear k]
  (S : RouqFamily (B := B) RD) (Sc : CL.CLScalars C k)

/-- The downward crossing is `t_ij⁻¹` times the mate of the upward crossing for the
adjunctions `E ⊣ F`, for all colours. -/
theorem crossDn_eq_conjugate (H : BrundanUpKLR S Sc) (M : BrundanMixedInversion S)
    (i j : I) {a n n' b : X} (hj : n' + RD.iX j = b) (hi : a + RD.iX i = n')
    (hi' : n + RD.iX i = b) (hj' : a + RD.iX j = n) :
    S.crossDn Sc i j hj hi hi' hj' =
      (((Sc.t i j)⁻¹ : kˣ) : k) •
        conjugateEquiv ((S.adj i hi).comp (S.adj j hj)) ((S.adj j hj').comp (S.adj i hi'))
          (S.cross i j hj' hi' hi hj) := by
  by_cases hij : i = j
  · subst hij
    subst hi hj'
    rw [Sc.t_self, inv_one, Units.val_one, one_smul]
    exact S.crossDn_self Sc i (rfl : a + RD.iX i = a + RD.iX i) hj
  · have := M i j hij hj' hi' hi hj
    have := M j i (Ne.symm hij) hi hj hj' hi'
    exact S.mixed_crossDn_rightMate Sc H j i (Ne.symm hij) hj' hi' hi hj

omit [AdditiveWhiskering B] in
theorem conjugateEquiv_smul' {a b : B} {l₁ l₂ : a ⟶ b} {r₁ r₂ : b ⟶ a}
    (A : l₁ ⊣ r₁) (D : l₂ ⊣ r₂) (t : k) (f : l₂ ⟶ l₁) :
    conjugateEquiv A D (t • f) = t • conjugateEquiv A D f := by
  simp only [Bicategory.conjugateEquiv_apply', source_whiskerLeft_smul,
    source_smul_whiskerRight, Linear.smul_comp, Linear.comp_smul]

/-- The mate of the downward crossing for the adjunctions `F ⊣ E` is `t_ji⁻¹` times the upward
crossing (the definition of `RouqFamily.crossDn`). -/
theorem conjugateEquiv_adjL_crossDn (i j : I) {a n n' b : X} (hj : n' + RD.iX j = b)
    (hi : a + RD.iX i = n') (hi' : n + RD.iX i = b) (hj' : a + RD.iX j = n) :
    conjugateEquiv ((S.adjL i hi').comp (S.adjL j hj')) ((S.adjL j hj).comp (S.adjL i hi))
        (S.crossDn Sc i j hj hi hi' hj') =
      (((Sc.t j i)⁻¹ : kˣ) : k) • S.cross i j hj' hi' hi hj := by
  rw [RouqFamily.crossDn, conjugateEquiv_smul', Equiv.apply_symm_apply]

variable (red : (r : Fin ℓ) → {x y : X} → x + Λ r = y → (S.obj y ⟶ S.obj x))
  (upIso : (r : Fin ℓ) → (i : I) → {μ μ₁ μ₂ μ₃ : X} → (h₁ : μ + RD.iX i = μ₁) →
    (h₂ : μ + Λ r = μ₂) → (h₃ : μ₁ + Λ r = μ₃) → (h₄ : μ₂ + RD.iX i = μ₃) →
    (S.F i h₄ ≫ red r h₂ ≅ red r h₃ ≫ S.F i h₁))

omit [AdditiveWhiskering B] [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (g : b ⟶ c), (postcomp a g).Linear k] in
theorem upIso_hom_eq_mate (r : Fin ℓ) (i : I) {μ μ₁ μ₂ μ₃ : X} (h₁ : μ + RD.iX i = μ₁)
    (h₂ : μ + Λ r = μ₂) (h₃ : μ₁ + Λ r = μ₃) (h₄ : μ₂ + RD.iX i = μ₃) :
    (upIso r i h₁ h₂ h₃ h₄).hom =
      mateEquiv (S.adj i h₄) (S.adj i h₁) (redDownQuot S red upIso r i h₁ h₂ h₃ h₄) := by
  rw [redDownQuot, Equiv.apply_symm_apply]

/-- **One instance of (4.4d) is the mate of one instance of the downward naturality of `a′`.**
-/
theorem upIsoCross_iff_downQuotCross (H : BrundanUpKLR S Sc) (M : BrundanMixedInversion S)
    (r : Fin ℓ) (i j : I) {μ ρ ρi ρj ν μi μj μij : X} (hr : μ + Λ r = ρ)
    (hi : ρ + RD.iX i = ρi) (hj : ρi + RD.iX j = ν) (hi' : ρj + RD.iX i = ν)
    (hj' : ρ + RD.iX j = ρj) (h₁ : μ + RD.iX j = μj) (h₃ : μj + Λ r = ρj)
    (h₁' : μj + RD.iX i = μij) (h₃' : μij + Λ r = ν) (g₁ : μ + RD.iX i = μi)
    (g₃ : μi + Λ r = ρi) (g₁' : μi + RD.iX j = μij) :
    ((α_ _ _ _).inv ≫ S.crossDn Sc i j hj hi hi' hj' ▷ red r hr ≫ (α_ _ _ _).hom ≫
        S.F i hi' ◁ (upIso r j h₁ hr h₃ hj').hom ≫ (α_ _ _ _).inv ≫
        (upIso r i h₁' h₃ h₃' hi').hom ▷ S.F j h₁ ≫ (α_ _ _ _).hom =
      S.F j hj ◁ (upIso r i g₁ hr g₃ hi).hom ≫ (α_ _ _ _).inv ≫
        (upIso r j g₁' g₃ h₃' hj).hom ▷ S.F i g₁ ≫ (α_ _ _ _).hom ≫
        red r h₃' ◁ S.crossDn Sc i j g₁' g₁ h₁' h₁) ↔
    ((α_ _ _ _).inv ≫ redDownQuot S red upIso r j h₁ hr h₃ hj' ▷ S.E i h₁' ≫ (α_ _ _ _).hom ≫
        S.E j hj' ◁ redDownQuot S red upIso r i h₁' h₃ h₃' hi' ≫ (α_ _ _ _).inv ≫
        S.cross i j hj' hi' hi hj ▷ red r h₃' ≫ (α_ _ _ _).hom =
      red r hr ◁ S.cross i j h₁ h₁' g₁ g₁' ≫ (α_ _ _ _).inv ≫
        redDownQuot S red upIso r i g₁ hr g₃ hi ▷ S.E j g₁' ≫ (α_ _ _ _).hom ≫
        S.E i hi ◁ redDownQuot S red upIso r j g₁' g₃ h₃' hj) := by
  have hc : IsUnit (((Sc.t i j)⁻¹ : kˣ) : k) := Units.isUnit _
  set A₁ := (S.adj i hi).comp (S.adj j hj)
  set A₃ := (S.adj j h₁).comp (S.adj i h₁')
  set X₁ := leftAdjointConjugateSquare.vcomp (S.cross i j hj' hi' hi hj)
    (leftAdjointSquare.hcomp (redDownQuot S red upIso r j h₁ hr h₃ hj')
      (redDownQuot S red upIso r i h₁' h₃ h₃' hi'))
  set Y₁ := leftAdjointSquareConjugate.vcomp
    (leftAdjointSquare.hcomp (redDownQuot S red upIso r i g₁ hr g₃ hi)
      (redDownQuot S red upIso r j g₁' g₃ h₃' hj)) (S.cross i j h₁ h₁' g₁ g₁')
  have hL : mateEquiv A₁ A₃ X₁ = _ :=
    conjugateEquiv_mateEquiv_vcomp A₁ ((S.adj j hj').comp (S.adj i hi')) A₃
    (S.cross i j hj' hi' hi hj)
    (leftAdjointSquare.hcomp (redDownQuot S red upIso r j h₁ hr h₃ hj')
      (redDownQuot S red upIso r i h₁' h₃ h₃' hi'))
  have hR : mateEquiv A₁ A₃ Y₁ = _ :=
    mateEquiv_conjugateEquiv_vcomp A₁ ((S.adj i g₁).comp (S.adj j g₁')) A₃
    (leftAdjointSquare.hcomp (redDownQuot S red upIso r i g₁ hr g₃ hi)
      (redDownQuot S red upIso r j g₁' g₃ h₃' hj)) (S.cross i j h₁ h₁' g₁ g₁')
  rw [Bicategory.mateEquiv_hcomp] at hL hR
  have eL : (α_ _ _ _).inv ≫ S.crossDn Sc i j hj hi hi' hj' ▷ red r hr ≫ (α_ _ _ _).hom ≫
        S.F i hi' ◁ (upIso r j h₁ hr h₃ hj').hom ≫ (α_ _ _ _).inv ≫
        (upIso r i h₁' h₃ h₃' hi').hom ▷ S.F j h₁ ≫ (α_ _ _ _).hom =
      (α_ _ _ _).inv ≫ ((((Sc.t i j)⁻¹ : kˣ) : k) • mateEquiv A₁ A₃ X₁) := by
    rw [hL, crossDn_eq_conjugate S Sc H M, upIso_hom_eq_mate S red upIso,
      upIso_hom_eq_mate S red upIso]
    simp only [rightAdjointConjugateSquare.vcomp, rightAdjointSquare.hcomp,
      source_smul_whiskerRight, Linear.smul_comp, Linear.comp_smul]
    rfl
  have eR : S.F j hj ◁ (upIso r i g₁ hr g₃ hi).hom ≫ (α_ _ _ _).inv ≫
        (upIso r j g₁' g₃ h₃' hj).hom ▷ S.F i g₁ ≫ (α_ _ _ _).hom ≫
        red r h₃' ◁ S.crossDn Sc i j g₁' g₁ h₁' h₁ =
      (α_ _ _ _).inv ≫ ((((Sc.t i j)⁻¹ : kˣ) : k) • mateEquiv A₁ A₃ Y₁) := by
    rw [hR, crossDn_eq_conjugate S Sc H M, upIso_hom_eq_mate S red upIso,
      upIso_hom_eq_mate S red upIso]
    simp only [rightAdjointSquareConjugate.vcomp, rightAdjointSquare.hcomp,
      source_whiskerLeft_smul, Linear.comp_smul, Category.assoc, Iso.inv_hom_id_assoc]
    rfl
  rw [eL, eR, cancel_epi, hc.smul_left_cancel, (mateEquiv A₁ A₃).apply_eq_iff_eq,
    ← cancel_mono (α_ _ _ _).hom]
  simp only [X₁, Y₁, leftAdjointConjugateSquare.vcomp, leftAdjointSquareConjugate.vcomp,
    leftAdjointSquare.hcomp, Category.assoc, Iso.inv_hom_id, Category.comp_id]

omit [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (g : b ⟶ c), (postcomp a g).Linear k] in
theorem upIso_inv_eq_mate (r : Fin ℓ) (i : I) {μ μ₁ μ₂ μ₃ : X} (h₁ : μ + RD.iX i = μ₁)
    (h₂ : μ + Λ r = μ₂) (h₃ : μ₁ + Λ r = μ₃) (h₄ : μ₂ + RD.iX i = μ₃) :
    redDownDot S red upIso r i h₁ h₂ h₃ h₄ =
      mateEquiv (S.adjL i h₄) (S.adjL i h₁) (upIso r i h₁ h₂ h₃ h₄).inv := rfl

/-- **One instance of (4.4d) is the mate of one instance of the downward naturality of `b′`.**
-/
theorem upIsoCross_iff_downDotCross (r : Fin ℓ) (i j : I) {μ ρ ρi ρj ν μi μj μij : X}
    (hr : μ + Λ r = ρ)
    (hi : ρ + RD.iX i = ρi) (hj : ρi + RD.iX j = ν) (hi' : ρj + RD.iX i = ν)
    (hj' : ρ + RD.iX j = ρj) (h₁ : μ + RD.iX j = μj) (h₃ : μj + Λ r = ρj)
    (h₁' : μj + RD.iX i = μij) (h₃' : μij + Λ r = ν) (g₁ : μ + RD.iX i = μi)
    (g₃ : μi + Λ r = ρi) (g₁' : μi + RD.iX j = μij) :
    ((α_ _ _ _).inv ≫ S.crossDn Sc i j hj hi hi' hj' ▷ red r hr ≫ (α_ _ _ _).hom ≫
        S.F i hi' ◁ (upIso r j h₁ hr h₃ hj').hom ≫ (α_ _ _ _).inv ≫
        (upIso r i h₁' h₃ h₃' hi').hom ▷ S.F j h₁ ≫ (α_ _ _ _).hom =
      S.F j hj ◁ (upIso r i g₁ hr g₃ hi).hom ≫ (α_ _ _ _).inv ≫
        (upIso r j g₁' g₃ h₃' hj).hom ▷ S.F i g₁ ≫ (α_ _ _ _).hom ≫
        red r h₃' ◁ S.crossDn Sc i j g₁' g₁ h₁' h₁) ↔
    ((α_ _ _ _).inv ≫ S.cross i j hj' hi' hi hj ▷ red r h₃' ≫ (α_ _ _ _).hom ≫
        S.E i hi ◁ redDownDot S red upIso r j g₁' g₃ h₃' hj ≫ (α_ _ _ _).inv ≫
        redDownDot S red upIso r i g₁ hr g₃ hi ▷ S.E j g₁' ≫ (α_ _ _ _).hom =
      S.E j hj' ◁ redDownDot S red upIso r i h₁' h₃ h₃' hi' ≫ (α_ _ _ _).inv ≫
        redDownDot S red upIso r j h₁ hr h₃ hj' ▷ S.E i h₁' ≫ (α_ _ _ _).hom ≫
        red r hr ◁ S.cross i j h₁ h₁' g₁ g₁') := by
  have hc : IsUnit (((Sc.t j i)⁻¹ : kˣ) : k) := Units.isUnit _
  set A₁ := (S.adjL i hi').comp (S.adjL j hj')
  set A₃ := (S.adjL j g₁').comp (S.adjL i g₁)
  set Hc := (α_ _ _ _).hom ≫ S.F i hi' ◁ (upIso r j h₁ hr h₃ hj').hom ≫ (α_ _ _ _).inv ≫
    (upIso r i h₁' h₃ h₃' hi').hom ▷ S.F j h₁ ≫ (α_ _ _ _).hom
  set Hc' := (α_ _ _ _).hom ≫ S.F j hj ◁ (upIso r i g₁ hr g₃ hi).hom ≫ (α_ _ _ _).inv ≫
    (upIso r j g₁' g₃ h₃' hj).hom ▷ S.F i g₁ ≫ (α_ _ _ _).hom
  set Hi := leftAdjointSquare.hcomp (upIso r i h₁' h₃ h₃' hi').inv (upIso r j h₁ hr h₃ hj').inv
  set Hi' := leftAdjointSquare.hcomp (upIso r j g₁' g₃ h₃' hj).inv (upIso r i g₁ hr g₃ hi).inv
  have e₁ : Hc ≫ Hi = 𝟙 _ := by
    simp [Hc, Hi, leftAdjointSquare.hcomp, ← whiskerLeft_comp_assoc, ← comp_whiskerRight_assoc]
  have e₂ : Hi ≫ Hc = 𝟙 _ := by
    simp [Hc, Hi, leftAdjointSquare.hcomp, ← whiskerLeft_comp_assoc, ← comp_whiskerRight_assoc]
  have e₁' : Hc' ≫ Hi' = 𝟙 _ := by
    simp [Hc', Hi', leftAdjointSquare.hcomp, ← whiskerLeft_comp_assoc, ← comp_whiskerRight_assoc]
  have e₂' : Hi' ≫ Hc' = 𝟙 _ := by
    simp [Hc', Hi', leftAdjointSquare.hcomp, ← whiskerLeft_comp_assoc, ← comp_whiskerRight_assoc]
  set P := S.crossDn Sc i j hj hi hi' hj' ▷ red r hr
  set Q := red r h₃' ◁ S.crossDn Sc i j g₁' g₁ h₁' h₁
  have hU : ((α_ _ _ _).inv ≫ S.crossDn Sc i j hj hi hi' hj' ▷ red r hr ≫ (α_ _ _ _).hom ≫
        S.F i hi' ◁ (upIso r j h₁ hr h₃ hj').hom ≫ (α_ _ _ _).inv ≫
        (upIso r i h₁' h₃ h₃' hi').hom ▷ S.F j h₁ ≫ (α_ _ _ _).hom =
      S.F j hj ◁ (upIso r i g₁ hr g₃ hi).hom ≫ (α_ _ _ _).inv ≫
        (upIso r j g₁' g₃ h₃' hj).hom ▷ S.F i g₁ ≫ (α_ _ _ _).hom ≫
        red r h₃' ◁ S.crossDn Sc i j g₁' g₁ h₁' h₁) ↔ P ≫ Hc = Hc' ≫ Q := by
    rw [← cancel_epi (α_ _ _ _).inv]
    simp only [P, Q, Hc, Hc', Category.assoc, Iso.inv_hom_id_assoc]
  have hconv : P ≫ Hc = Hc' ≫ Q ↔ Hi' ≫ P = Q ≫ Hi := by
    constructor
    · intro h
      calc Hi' ≫ P = Hi' ≫ (P ≫ Hc) ≫ Hi := by rw [Category.assoc, e₁, Category.comp_id]
        _ = Q ≫ Hi := by rw [h, Category.assoc, reassoc_of% e₂']
    · intro h
      calc P ≫ Hc = Hc' ≫ (Hi' ≫ P) ≫ Hc := by
            simp only [Category.assoc, reassoc_of% e₁']
        _ = Hc' ≫ Q := by simp only [h, Category.assoc, e₂, Category.comp_id]
  have hY : mateEquiv A₁ A₃ (leftAdjointConjugateSquare.vcomp
      (S.crossDn Sc i j hj hi hi' hj') Hi') = _ :=
    conjugateEquiv_mateEquiv_vcomp A₁ ((S.adjL j hj).comp (S.adjL i hi)) A₃ _ _
  have hX : mateEquiv A₁ A₃ (leftAdjointSquareConjugate.vcomp Hi
      (S.crossDn Sc i j g₁' g₁ h₁' h₁)) = _ :=
    mateEquiv_conjugateEquiv_vcomp A₁ ((S.adjL i h₁').comp (S.adjL j h₁)) A₃ _ _
  rw [Bicategory.mateEquiv_hcomp, conjugateEquiv_adjL_crossDn] at hY hX
  have hD : (Hi' ≫ P = Q ≫ Hi) ↔
      (α_ _ _ _).inv ≫ mateEquiv A₁ A₃ (leftAdjointConjugateSquare.vcomp
        (S.crossDn Sc i j hj hi hi' hj') Hi') =
      (α_ _ _ _).inv ≫ mateEquiv A₁ A₃ (leftAdjointSquareConjugate.vcomp Hi
        (S.crossDn Sc i j g₁' g₁ h₁' h₁)) := by
    rw [cancel_epi, (mateEquiv A₁ A₃).apply_eq_iff_eq]
    rfl
  rw [hU, hconv, hD, hY, hX, ← upIso_inv_eq_mate, ← upIso_inv_eq_mate, ← upIso_inv_eq_mate,
    ← upIso_inv_eq_mate]
  simp only [rightAdjointConjugateSquare.vcomp, rightAdjointSquareConjugate.vcomp,
    rightAdjointSquare.hcomp, source_smul_whiskerRight, source_whiskerLeft_smul,
    Linear.smul_comp, Linear.comp_smul, Category.assoc, Iso.inv_hom_id_assoc]
  exact hc.smul_left_cancel

/-- **The red/up crossings are natural for upward crossings (4.4d) if and only if `a′` is
natural for downward crossings.** -/
theorem upIsoCrossNatural_iff_downQuotCrossNatural (H : BrundanUpKLR S Sc)
    (M : BrundanMixedInversion S) :
    UpIsoCrossNatural S red upIso Sc ↔ DownQuotCrossNatural S red upIso := by
  constructor
  · intro h r i j _ _ _ _ _ _ _ _ f₁ f₂ hR q₁ q₂ hr q₃ q₄ q₅ g₁ g₂ g₃
    exact (upIsoCross_iff_downQuotCross S Sc red upIso H M r i j hR q₅ q₄ q₃ q₂ f₂ q₁ f₁ hr
      g₂ g₃ g₁).1 (h r i j hR q₅ q₄ q₃ q₂ f₂ q₁ f₁ hr g₂ g₃ g₁)
  · intro h r i j _ _ _ _ _ _ _ _ hr hi hj hi' hj' h₁ h₃ h₁' h₃' g₁ g₃ g₁'
    exact (upIsoCross_iff_downQuotCross S Sc red upIso H M r i j hr hi hj hi' hj' h₁ h₃ h₁' h₃'
      g₁ g₃ g₁').2 (h r i j h₁' h₁ hr h₃ hj' h₃' hi' hj hi g₁' g₁ g₃)

/-- **The red/up crossings are natural for upward crossings (4.4d) if and only if `b′` is
natural for downward crossings.** -/
theorem upIsoCrossNatural_iff_downDotCrossNatural :
    UpIsoCrossNatural S red upIso Sc ↔ DownDotCrossNatural S red upIso := by
  constructor
  · intro h r i j _ _ _ _ _ _ _ _ hr hi hj hi' hj' g₁ g₃ k₁ k₃ f₁ f₃ f₁'
    exact (upIsoCross_iff_downDotCross S Sc red upIso r i j k₃ hi' hj' hi hj f₁' f₃ f₁ hr k₁ g₃
      g₁).1 (h r i j k₃ hi' hj' hi hj f₁' f₃ f₁ hr k₁ g₃ g₁)
  · intro h r i j _ _ _ _ _ _ _ _ hr hi hj hi' hj' h₁ h₃ h₁' h₃' g₁ g₃ g₁'
    exact (upIsoCross_iff_downDotCross S Sc red upIso r i j hr hi hj hi' hj' h₁ h₃ h₁' h₃' g₁
      g₃ g₁').2 (h r i j h₃' hi' hj' hi hj g₁' g₃ g₁ hr h₁' h₃ h₁)

end Categorification.Stendhal.DoubleDiagram
