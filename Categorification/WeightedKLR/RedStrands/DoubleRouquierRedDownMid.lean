/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleRouquierRedDownMates

/-!
# A red strand between two downward strands, by mates

Webster, arXiv:1309.3796v3, proof of Theorem 4.25. For distinct colours `i ≠ j`, the condition
that a red strand between two downward strands commutes with their crossing
(`DownMidCrossNatural`) is the double mate of (4.4d) for the colours `(j, i)`: bending the
strand `j` through `F_j ⊣ E_j` turns `b′` into the inverse red/up crossing and the downward
crossing into the inverse of a sideways crossing (`RouqFamily.mixed_mate`); these sideways
crossings are invertible (`BrundanMixedInversion`), and bending the strand `i` through
`E_i ⊣ F_i` then turns `a′` into the red/up crossing and the sideways crossing into the
downward crossing of upward strands (`crossDn_eq_conjugate`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory CategoryTheory.Bicategory QuantumGroup QuantumGroup.UDot KL3.Diagram
  StringDiagrams TwoRep Diagrams.BicatInterp

universe w u v

/-- Conjugating a commuting square by isomorphisms on both sides. -/
theorem comp_eq_comp_iff_of_inv {C : Type*} [Category C] {a b c d : C} {A : a ⟶ b}
    {A' : b ⟶ a} {P : b ⟶ d} {Q : a ⟶ c} {Bk : c ⟶ d} {B' : d ⟶ c} (hA : A ≫ A' = 𝟙 _)
    (hA' : A' ≫ A = 𝟙 _) (hB : Bk ≫ B' = 𝟙 _) (hB' : B' ≫ Bk = 𝟙 _) :
    A ≫ P = Q ≫ Bk ↔ P ≫ B' = A' ≫ Q := by
  constructor
  · intro h
    calc P ≫ B' = A' ≫ (A ≫ P) ≫ B' := by simp only [Category.assoc, reassoc_of% hA']
      _ = A' ≫ Q := by simp only [h, Category.assoc, hB, Category.comp_id]
  · intro h
    calc A ≫ P = A ≫ (P ≫ B') ≫ Bk := by rw [Category.assoc, hB', Category.comp_id]
      _ = Q ≫ Bk := by simp only [h, Category.assoc, reassoc_of% hA]

variable {I : Type u} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {ℓ : ℕ} {Λ : Fin ℓ → X}

variable {B : Type*} [Bicategory B] [∀ a b : B, Preadditive (a ⟶ b)] [AdditiveWhiskering B]
  {k : Type w} [CommRing k] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (g : b ⟶ c), (postcomp a g).Linear k]
  (S : RouqFamily (B := B) RD) (Sc : CL.CLScalars C k)
  (red : (r : Fin ℓ) → {x y : X} → x + Λ r = y → (S.obj y ⟶ S.obj x))
  (upIso : (r : Fin ℓ) → (i : I) → {μ μ₁ μ₂ μ₃ : X} → (h₁ : μ + RD.iX i = μ₁) →
    (h₂ : μ + Λ r = μ₂) → (h₃ : μ₁ + Λ r = μ₃) → (h₄ : μ₂ + RD.iX i = μ₃) →
    (S.F i h₄ ≫ red r h₂ ≅ red r h₃ ≫ S.F i h₁))

omit [AdditiveWhiskering B] in
theorem mateEquiv_smul' {a b c d : B} {l₁ : a ⟶ b} {r₁ : b ⟶ a} {l₂ : c ⟶ d} {r₂ : d ⟶ c}
    (A : l₁ ⊣ r₁) (D : l₂ ⊣ r₂) {g : a ⟶ c} {h : b ⟶ d} (s : k) (f : g ≫ l₂ ⟶ l₁ ≫ h) :
    mateEquiv A D (s • f) = s • mateEquiv A D f := by
  simp only [Bicategory.mateEquiv_apply, Adjunction.homEquiv₁_apply,
    Adjunction.homEquiv₂_apply, source_whiskerLeft_smul, source_smul_whiskerRight,
    Linear.smul_comp, Linear.comp_smul]

/-- **One instance of `DownMidCrossNatural` for `(i, j)` is the double mate of one instance of
(4.4d) for `(j, i)`.** -/
theorem upIsoCross_iff_downMidCross (H : BrundanUpKLR S Sc) (M : BrundanMixedInversion S)
    (r : Fin ℓ) (i j : I) (hij : i ≠ j) {μ μi μj μij ρ ρi ρj T : X} (f₁ : μi + RD.iX i = μ)
    (f₂ : μij + RD.iX j = μi) (hR : μi + Λ r = ρi) (e₁ : μij + Λ r = T) (q : T + RD.iX j = ρi)
    (g₁ : μj + RD.iX j = μ) (g₂ : μij + RD.iX i = μj) (hRj : μj + Λ r = ρj)
    (q₅ : T + RD.iX i = ρj) (hr : μ + Λ r = ρ) (q₃ : ρi + RD.iX i = ρ)
    (q₄ : ρj + RD.iX j = ρ) :
    ((α_ _ _ _).inv ≫ S.crossDn Sc j i q₃ q q₄ q₅ ▷ red r e₁ ≫ (α_ _ _ _).hom ≫
        S.F j q₄ ◁ (upIso r i g₂ e₁ hRj q₅).hom ≫ (α_ _ _ _).inv ≫
        (upIso r j g₁ hRj hr q₄).hom ▷ S.F i g₂ ≫ (α_ _ _ _).hom =
      S.F i q₃ ◁ (upIso r j f₂ e₁ hR q).hom ≫ (α_ _ _ _).inv ≫
        (upIso r i f₁ hR hr q₃).hom ▷ S.F j f₂ ≫ (α_ _ _ _).hom ≫
        red r hr ◁ S.crossDn Sc j i f₁ f₂ g₁ g₂) ↔
    ((α_ _ _ _).inv ≫ redDownDot S red upIso r j f₂ e₁ hR q ▷ S.E i f₁ ≫ (α_ _ _ _).hom ≫
        red r e₁ ◁ S.cross i j f₂ f₁ g₂ g₁ ≫ (α_ _ _ _).inv ≫
        redDownQuot S red upIso r i g₂ e₁ hRj q₅ ▷ S.E j g₁ ≫ (α_ _ _ _).hom =
      S.E j q ◁ redDownQuot S red upIso r i f₁ hR hr q₃ ≫ (α_ _ _ _).inv ≫
        S.cross i j q q₃ q₅ q₄ ▷ red r hr ≫ (α_ _ _ _).hom ≫
        S.E i q₅ ◁ redDownDot S red upIso r j g₁ hRj hr q₄) := by
  have := M j i hij.symm g₂ g₁ f₂ f₁
  have := M j i hij.symm q₅ q₄ q q₃
  set t : k := ((Sc.t j i : kˣ) : k)
  set t' : k := (((Sc.t j i)⁻¹ : kˣ) : k)
  have htt : t * t' = 1 := Units.mul_inv _
  have htt' : t' * t = 1 := Units.inv_mul _
  set σ₀ := S.mixedSigma j i g₂ g₁ f₂ f₁
  set σ₁ := S.mixedSigma j i q₅ q₄ q q₃
  set Sg := t • inv σ₀
  set Sg' := t • inv σ₁
  set Tg := t' • σ₀
  set Tg' := t' • σ₁
  have hST : Sg ≫ Tg = 𝟙 _ := by
    simp only [Sg, Tg, Linear.smul_comp, Linear.comp_smul, smul_smul, IsIso.inv_hom_id, htt',
      one_smul]
  have hTS : Tg ≫ Sg = 𝟙 _ := by
    simp only [Sg, Tg, Linear.smul_comp, Linear.comp_smul, smul_smul, IsIso.hom_inv_id, htt,
      one_smul]
  have hST' : Sg' ≫ Tg' = 𝟙 _ := by
    simp only [Sg', Tg', Linear.smul_comp, Linear.comp_smul, smul_smul, IsIso.inv_hom_id, htt',
      one_smul]
  have hTS' : Tg' ≫ Sg' = 𝟙 _ := by
    simp only [Sg', Tg', Linear.smul_comp, Linear.comp_smul, smul_smul, IsIso.hom_inv_id, htt,
      one_smul]
  -- The mates of the sideways crossings.
  have hm₀ : mateEquiv (S.adjL j f₂) (S.adjL j g₁) Sg = S.cross i j f₂ f₁ g₂ g₁ :=
    S.mixed_mate Sc H j i hij.symm f₂ f₁ g₂ g₁
  have hm₁ : mateEquiv (S.adjL j q) (S.adjL j q₄) Sg' = S.cross i j q q₃ q₅ q₄ :=
    S.mixed_mate Sc H j i hij.symm q q₃ q₅ q₄
  have hn₀ : mateEquiv (S.adj i f₁) (S.adj i g₂) Tg = S.crossDn Sc j i f₁ f₂ g₁ g₂ := by
    rw [crossDn_eq_conjugate S Sc H M, ← Bicategory.iterated_mateEquiv_conjugateEquiv,
      mateEquiv_smul']
    rfl
  have hn₁ : mateEquiv (S.adj i q₃) (S.adj i q₅) Tg' = S.crossDn Sc j i q₃ q q₄ q₅ := by
    rw [crossDn_eq_conjugate S Sc H M, ← Bicategory.iterated_mateEquiv_conjugateEquiv,
      mateEquiv_smul']
    rfl
  set a₁ := redDownQuot S red upIso r i g₂ e₁ hRj q₅
  set a₂ := redDownQuot S red upIso r i f₁ hR hr q₃
  set u := upIso r j f₂ e₁ hR q
  set u' := upIso r j g₁ hRj hr q₄
  -- Bending the strand `i`.
  have step₁ : ((α_ _ _ _).inv ≫ S.crossDn Sc j i q₃ q q₄ q₅ ▷ red r e₁ ≫ (α_ _ _ _).hom ≫
        S.F j q₄ ◁ (upIso r i g₂ e₁ hRj q₅).hom ≫ (α_ _ _ _).inv ≫
        u'.hom ▷ S.F i g₂ ≫ (α_ _ _ _).hom =
      S.F i q₃ ◁ u.hom ≫ (α_ _ _ _).inv ≫
        (upIso r i f₁ hR hr q₃).hom ▷ S.F j f₂ ≫ (α_ _ _ _).hom ≫
        red r hr ◁ S.crossDn Sc j i f₁ f₂ g₁ g₂) ↔
      leftAdjointSquare.vcomp Tg' a₁ ≫ S.E i q₃ ◁ u'.hom =
        u.hom ▷ S.E i g₂ ≫ leftAdjointSquare.vcomp a₂ Tg := by
    rw [← (mateEquiv (S.adj i q₃) (S.adj i g₂)).apply_eq_iff_eq, rightMate_post, rightMate_pre,
      Bicategory.mateEquiv_vcomp _ (S.adj i q₅) _, Bicategory.mateEquiv_vcomp _ (S.adj i f₁) _,
      hn₀, hn₁, ← upIso_hom_eq_mate, ← upIso_hom_eq_mate, ← cancel_mono (α_ _ _ _).hom]
    simp only [rightAdjointSquare.vcomp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  -- Bending the strand `j`.
  have step₄ : leftAdjointSquare.vcomp u.inv Sg ≫ S.F j q ◁ a₁ =
        a₂ ▷ S.F j g₁ ≫ leftAdjointSquare.vcomp Sg' u'.inv ↔
      ((α_ _ _ _).inv ≫ redDownDot S red upIso r j f₂ e₁ hR q ▷ S.E i f₁ ≫ (α_ _ _ _).hom ≫
        red r e₁ ◁ S.cross i j f₂ f₁ g₂ g₁ ≫ (α_ _ _ _).inv ≫
        a₁ ▷ S.E j g₁ ≫ (α_ _ _ _).hom =
      S.E j q ◁ a₂ ≫ (α_ _ _ _).inv ≫
        S.cross i j q q₃ q₅ q₄ ▷ red r hr ≫ (α_ _ _ _).hom ≫
        S.E i q₅ ◁ redDownDot S red upIso r j g₁ hRj hr q₄) := by
    rw [← (mateEquiv (S.adjL j q) (S.adjL j g₁)).apply_eq_iff_eq, rightMate_post, rightMate_pre,
      Bicategory.mateEquiv_vcomp _ (S.adjL j f₂) _, Bicategory.mateEquiv_vcomp _ (S.adjL j q₄) _,
      hm₀, hm₁, ← upIso_inv_eq_mate, ← upIso_inv_eq_mate, ← cancel_mono (α_ _ _ _).hom]
    simp only [rightAdjointSquare.vcomp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  -- Moving the red/up crossings of `j` to the other side.
  have step₂ := comp_eq_comp_iff_of_inv (A := u.inv ▷ S.E i g₂) (A' := u.hom ▷ S.E i g₂)
    (P := leftAdjointSquare.vcomp Tg' a₁) (Q := leftAdjointSquare.vcomp a₂ Tg)
    (Bk := S.E i q₃ ◁ u'.inv) (B' := S.E i q₃ ◁ u'.hom)
    (by rw [← comp_whiskerRight, Iso.inv_hom_id, id_whiskerRight])
    (by rw [← comp_whiskerRight, Iso.hom_inv_id, id_whiskerRight])
    (by rw [← whiskerLeft_comp, Iso.inv_hom_id, whiskerLeft_id])
    (by rw [← whiskerLeft_comp, Iso.hom_inv_id, whiskerLeft_id])
  -- Moving the sideways crossings to the other side.
  have step₃ := comp_eq_comp_iff_of_inv
    (A := (α_ _ _ _).hom ≫ red r hR ◁ Sg ≫ (α_ _ _ _).inv)
    (A' := (α_ _ _ _).hom ≫ red r hR ◁ Tg ≫ (α_ _ _ _).inv)
    (P := u.inv ▷ S.E i g₂ ≫ (α_ _ _ _).hom ≫ S.F j q ◁ a₁)
    (Q := a₂ ▷ S.F j g₁ ≫ (α_ _ _ _).hom ≫ S.E i q₃ ◁ u'.inv)
    (Bk := (α_ _ _ _).inv ≫ Sg' ▷ red r hRj ≫ (α_ _ _ _).hom)
    (B' := (α_ _ _ _).inv ≫ Tg' ▷ red r hRj ≫ (α_ _ _ _).hom)
    (by simp [← whiskerLeft_comp_assoc, hST])
    (by simp [← whiskerLeft_comp_assoc, hTS])
    (by simp [← comp_whiskerRight_assoc, hST'])
    (by simp [← comp_whiskerRight_assoc, hTS'])
  rw [step₁, ← step₄, ← step₂]
  simp only [leftAdjointSquare.vcomp, Category.assoc] at step₃ ⊢
  exact step₃.symm

/-- **A red strand between two downward strands of distinct colours commutes with their
crossing** once the red/up crossings are natural for upward crossings (4.4d). -/
theorem downMidCrossNatural_of_upIsoCrossNatural (H : BrundanUpKLR S Sc)
    (M : BrundanMixedInversion S) (h : UpIsoCrossNatural S red upIso Sc) :
    DownMidCrossNatural S red upIso :=
  fun r i j hij _ _ _ _ _ _ _ _ f₁ f₂ hR e₁ q g₁ g₂ hRj q₅ hr q₃ q₄ =>
    (upIsoCross_iff_downMidCross S Sc red upIso H M r i j hij f₁ f₂ hR e₁ q g₁ g₂ hRj q₅ hr q₃
      q₄).1 (h r j i e₁ q q₃ q₄ q₅ g₂ hRj g₁ hr f₂ hR f₁)

end Categorification.Stendhal.DoubleDiagram
