/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqModel

/-!
# Vanishing of `E` at weight zero next to a vanishing `F`

J. Brundan, *On the definition of Kac–Moody 2-category*, arXiv:1501.00350v1, (1.8): at weight
`h = 0`, Rouquier's map `σ : E F 1_λ → F E 1_λ` is invertible. If `F 1_λ = 0`, then
`F E 1_λ = 0`, and the adjunction `E ⊣ F` then gives `E 1_λ = 0` and `F 1_{λ+α} = 0`
(`RouqLoc.isZero_of_isZero_of_weight_zero`).

B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3, proof of the
theorem with label `nondegenerate`. The labels of the unfurled graph over a colour are infinite
in number. At a given weight, only finitely many of them act by nonzero 1-morphisms. For a
label `a` that does not occur in the block, carries no weight, and has no arrows to the labels
of the block, `F_a` vanishes and the pairing is zero, so `E_a` vanishes as well
(`RouqFamily.isZero_E_of_isZero_F`).
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits

universe w v u u₁

section Whisker

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [AdditiveWhiskering B] {a b c : B}

theorem isZero_whiskerComp_left {f : a ⟶ b} (hf : IsZero f) (g : b ⟶ c) : IsZero (f ≫ g) := by
  rw [IsZero.iff_id_eq_zero, ← Bicategory.id_whiskerRight, hf.eq_of_src (𝟙 f) 0,
    AdditiveWhiskering.zero_whiskerRight]

theorem isZero_whiskerComp_right (f : a ⟶ b) {g : b ⟶ c} (hg : IsZero g) : IsZero (f ≫ g) := by
  rw [IsZero.iff_id_eq_zero, ← Bicategory.whiskerLeft_id, hg.eq_of_src (𝟙 g) 0,
    AdditiveWhiskering.whiskerLeft_zero]

/-- If `E ⊣ R` and `E ≫ R` is zero, then `E` and `R` are zero (the triangle identities). -/
theorem isZero_of_adjunction {E : a ⟶ b} {R : b ⟶ a} (adj : E ⊣ R) (h : IsZero (E ≫ R)) :
    IsZero E ∧ IsZero R := by
  constructor
  · have hz : adj.unit ▷ E = 0 := (isZero_whiskerComp_left h E).eq_of_tgt _ _
    have h0 : (λ_ E).hom ≫ (ρ_ E).inv = 0 := by
      rw [← adj.left_triangle]
      simp [leftZigzag, bicategoricalComp, hz]
    rw [IsZero.iff_id_eq_zero]
    calc 𝟙 E = (λ_ E).inv ≫ ((λ_ E).hom ≫ (ρ_ E).inv) ≫ (ρ_ E).hom := by simp
      _ = 0 := by rw [h0]; simp
  · have hz : R ◁ adj.unit = 0 := (isZero_whiskerComp_right R h).eq_of_tgt _ _
    have h0 : (ρ_ R).hom ≫ (λ_ R).inv = 0 := by
      rw [← adj.right_triangle]
      simp [rightZigzag, bicategoricalComp, hz]
    rw [IsZero.iff_id_eq_zero]
    calc 𝟙 R = (ρ_ R).inv ≫ ((ρ_ R).hom ≫ (λ_ R).inv) ≫ (λ_ R).hom := by simp
      _ = 0 := by rw [h0]; simp

end Whisker

namespace RouqLoc

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [AdditiveWhiskering B] {a b c : B} {E₁ : a ⟶ b} {R₁ : b ⟶ a} {E₂ : b ⟶ c} {R₂ : c ⟶ b}
  {adj₁ : E₁ ⊣ R₁} {adj₂ : E₂ ⊣ R₂} {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂}
  {τ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂} {h : ℤ} (L : RouqLoc adj₁ adj₂ x₁ x₂ τ h)

include L in
/-- **At weight zero, `F 1_λ = 0` forces `E 1_λ = 0` and `F 1_{λ+α} = 0`** (Brundan,
arXiv:1501.00350v1, (1.8) with `h = 0`, and the adjunction `E ⊣ F`). -/
theorem isZero_of_isZero_of_weight_zero (hh : h = 0) (hR : IsZero R₁) :
    IsZero E₂ ∧ IsZero R₂ := by
  have I := L.invPos hh.ge
  have hRE : IsZero (R₁ ≫ E₁) := isZero_whiskerComp_left hR E₁
  have hER : IsZero (E₂ ≫ R₂) := by
    rw [IsZero.iff_id_eq_zero, ← I.ff, hRE.eq_of_tgt I.f' 0, zero_comp]
  exact isZero_of_adjunction adj₂ hER

end RouqLoc

namespace RouqFamily

open QuantumGroup UDot

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [AdditiveWhiskering B] {I : Type*} {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X]
  [AddCommGroup Y] {RD : WeightDatum C X Y} (S : RouqFamily (B := B) RD)

/-- **At a weight `b` with `⟨i, b⟩ = 0`, if `F_i` out of `b` vanishes then so do `E_i` out of `b`
and `F_i` into `b`.** -/
theorem isZero_E_of_isZero_F (i : I) {a b c : X} (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX i = c)
    (hb : RD.pair (RD.iY i) b = 0) (hF : IsZero (S.F i h₁)) :
    IsZero (S.E i h₂) ∧ IsZero (S.F i h₂) :=
  (S.loc i h₁ h₂).isZero_of_isZero_of_weight_zero hb hF

end RouqFamily

end Categorification.TwoRep
