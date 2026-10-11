/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqDottedCurls

/-!
# Ungraded curl expansions

Closing Brundan's capped-crossing expansions gives the two finite bubble sums.
The indices are those used by the CL right and left curls, including empty ranges.
These identities feed the actual diagram consumers in `RouqCurls`.

Brundan, *On the definition of Kac–Moody 2-category*, arXiv:1501.00350v1,
Corollary 3.5, (3.18).
-/

noncomputable section
namespace Categorification.TwoRep
open CategoryTheory CategoryTheory.Bicategory
universe w v u
namespace RouqLoc
variable {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [AdditiveWhiskering B]
  {a b c : B} {E₁ : a ⟶ b} {R₁ : b ⟶ a} {E₂ : b ⟶ c} {R₂ : c ⟶ b}
  {adj₁ : E₁ ⊣ R₁} {adj₂ : E₂ ⊣ R₂} {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂}
  {τ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂} {h : ℤ} (L : RouqLoc adj₁ adj₂ x₁ x₂ τ h)

omit [AdditiveWhiskering B] in
private theorem close_cupD (z : 𝟙 b ⟶ 𝟙 b) (n : ℕ) :
    (λ_ E₂).inv ≫ (z ≫ L.cupD n) ▷ E₂ ≫ (α_ E₂ R₂ E₂).hom ≫
      E₂ ◁ adj₂.counit ≫ (ρ_ E₂).hom =
    ((λ_ E₂).inv ≫ z ▷ E₂ ≫ (λ_ E₂).hom) ≫ powComp x₂ n := by
  calc _ = ((λ_ E₂).inv ≫ z ▷ E₂ ≫ (λ_ E₂).hom) ≫
        ((λ_ E₂).inv ≫ leftZigzag adj₂.unit adj₂.counit ≫ (ρ_ E₂).hom) ≫ powComp x₂ n := by
          dsimp only [cupD, leftZigzag]
          simp only [comp_whiskerRight, Category.assoc]
          rw [associator_naturality_left_assoc, ← whisker_exchange_assoc, rightUnitor_naturality]
          bicategory
    _ = _ := by rw [adj₂.left_triangle]; simp

omit [AdditiveWhiskering B] in
private theorem close_capD (z : 𝟙 b ⟶ 𝟙 b) (n : ℕ) :
    (λ_ E₁).inv ≫ adj₁.unit ▷ E₁ ≫ (α_ E₁ R₁ E₁).hom ≫
      E₁ ◁ (L.capD n ≫ z) ≫ (ρ_ E₁).hom =
    powComp x₁ n ≫ ((ρ_ E₁).inv ≫ E₁ ◁ z ≫ (ρ_ E₁).hom) := by
  calc _ = powComp x₁ n ≫
        ((λ_ E₁).inv ≫ leftZigzag adj₁.unit adj₁.counit ≫ (ρ_ E₁).hom) ≫
          ((ρ_ E₁).inv ≫ E₁ ◁ z ≫ (ρ_ E₁).hom) := by
          dsimp only [capD, leftZigzag]
          simp only [whiskerLeft_comp, Category.assoc]
          rw [← associator_naturality_right_assoc, ← whisker_exchange_assoc,
            ← leftUnitor_inv_naturality_assoc]
          bicategory
    _ = _ := by rw [adj₁.left_triangle]; simp

private def closeRight : (𝟙 b ⟶ E₂ ≫ R₂) →+ (E₂ ⟶ E₂) where
  toFun u := (λ_ E₂).inv ≫ u ▷ E₂ ≫ (α_ E₂ R₂ E₂).hom ≫ E₂ ◁ adj₂.counit ≫ (ρ_ E₂).hom
  map_zero' := by simp [AdditiveWhiskering.zero_whiskerRight]
  map_add' u v := by simp [AdditiveWhiskering.add_whiskerRight, Preadditive.comp_add]

private def closeLeft : (R₁ ≫ E₁ ⟶ 𝟙 b) →+ (E₁ ⟶ E₁) where
  toFun d := (λ_ E₁).inv ≫ adj₁.unit ▷ E₁ ≫ (α_ E₁ R₁ E₁).hom ≫ E₁ ◁ d ≫ (ρ_ E₁).hom
  map_zero' := by simp [AdditiveWhiskering.whiskerLeft_zero]
  map_add' u v := by simp [AdditiveWhiskering.whiskerLeft_add, Preadditive.comp_add]

/-- The right curl as its signed finite sum, at every local weight. -/
theorem curlG_bubble_sum :
    curlG L.cupL adj₁.counit τ =
      -(∑ j ∈ Finset.range (-h + 1).toNat,
        ((λ_ E₂).inv ≫ L.ccw (h - 1 + j) ▷ E₂ ≫ (λ_ E₂).hom) ≫
          powComp x₂ (-h - j).toNat) := by
  rw [← L.close_cup_sig, L.cupL_sig_expansion]
  change closeRight (-∑ j ∈ Finset.range (-h + 1).toNat, L.ccw (-(j : ℤ) - 1) ≫ L.cupD j) = _
  rw [map_neg, map_sum]
  congr 1
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  change (λ_ E₂).inv ≫ (_ ≫ L.cupD _) ▷ E₂ ≫ _ = _
  rw [L.close_cupD, show -(((-h + 1).toNat - 1 - j : ℕ) : ℤ) - 1 = h - 1 + j by omega,
    show (-h + 1).toNat - 1 - j = (-h - j).toNat by omega]

/-- The left curl as its finite sum, at every local weight. -/
theorem curlEG_bubble_sum :
    curlEG adj₂.unit L.capL τ =
      ∑ j ∈ Finset.range (h + 1).toNat,
        powComp x₁ (h - j).toNat ≫
          ((ρ_ E₁).inv ≫ E₁ ◁ L.cw (-h - 1 + j) ≫ (ρ_ E₁).hom) := by
  rw [← L.close_sig_cap, L.sig_capL_expansion]
  change closeLeft (∑ j ∈ Finset.range (h + 1).toNat, L.capD j ≫ L.cw (-(j : ℤ) - 1)) = _
  rw [map_sum]
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  change (λ_ E₁).inv ≫ adj₁.unit ▷ E₁ ≫ (α_ E₁ R₁ E₁).hom ≫ E₁ ◁ (L.capD _ ≫ _) ≫ _ = _
  rw [L.close_capD, show -(((h + 1).toNat - 1 - j : ℕ) : ℤ) - 1 = -h - 1 + j by omega,
    show (h + 1).toNat - 1 - j = (h - j).toNat by omega]
end RouqLoc
end Categorification.TwoRep
