/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqCurl
import Categorification.TwoRep.BetaCoeffNeg

/-!
# Dotted curls from Rouquier's data

Brundan, *On the definition of Kac–Moody 2-category*, arXiv:1501.00350v1, Lemma 4.1.
The dotted curls of small degree are computed from the inverse components and right adjunctions.
These identities are used in the left-adjunction relations; no grading is assumed.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Bicategory Opposite

universe w v u

namespace RouqLoc

variable {C : Type u} [Bicategory.{w, v} C] [∀ a b : C, Preadditive (a ⟶ b)] [AdditiveWhiskering C]
  {a b c : C} {E₁ : a ⟶ b} {R₁ : b ⟶ a} {E₂ : b ⟶ c} {R₂ : c ⟶ b}
  {adj₁ : E₁ ⊣ R₁} {adj₂ : E₂ ⊣ R₂} {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂}
  {τ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂} {h : ℤ} (L : RouqLoc adj₁ adj₂ x₁ x₂ τ h)

/-- The dotted left cup against the rightward crossing, through the boundary degree. -/
theorem cupL_powComp_sig_of_le {n : ℕ} (hn : (n : ℤ) ≤ h) :
    L.cupL ≫ R₁ ◁ powComp x₁ n ≫ L.sig = if (n : ℤ) = h then -adj₂.unit else 0 := by
  have hh : 0 ≤ h := by omega
  rcases eq_or_lt_of_le hh with hz | hp
  · have hn0 : n = 0 := by omega
    subst n
    subst h
    simp only [powComp_zero, whiskerLeft_id, Category.id_comp]
    rw [L.cupL_sig_expansion]
    simp only [neg_zero, zero_add, Int.toNat_one, Finset.sum_range_one,
      Nat.cast_zero, zero_sub]
    rw [L.ccw_of_neg_of_eq (by omega) (by omega), Category.id_comp]
    simp [cupD]
  · rcases lt_or_eq_of_le hn with hlt | heq
    · rw [L.cupL_powComp_sig hp (by omega), ite_eq_right (by omega)]
    · rw [ite_eq_left heq, L.powComp_sig, Preadditive.comp_sub,
        ← Category.assoc, L.cupL_sig hp, Limits.zero_comp, zero_sub, Preadditive.comp_sum]
      congr 1
      rw [Finset.sum_eq_single (n - 1)]
      · rw [← Category.assoc, L.cupL_capD hp (by omega), ite_eq_left (by omega),
          Category.id_comp, Nat.sub_self]
        simp [cupD]
      · intro j hj hjn
        have hj' := Finset.mem_range.mp hj
        rw [← Category.assoc, L.cupL_capD hp (by omega), ite_eq_right (by omega), Limits.zero_comp]
      · intro hj
        exact False.elim (hj (Finset.mem_range.mpr (by omega)))

omit [AdditiveWhiskering C] in
/-- Closing the output of the rightward crossing gives the curl on `E₂`. -/
theorem close_cup_sig (u : 𝟙 b ⟶ R₁ ≫ E₁) :
    (λ_ E₂).inv ≫ (u ≫ L.sig) ▷ E₂ ≫ (α_ E₂ R₂ E₂).hom ≫
      E₂ ◁ adj₂.counit ≫ (ρ_ E₂).hom = curlG u adj₁.counit τ := by
  calc _ = 𝟙 _ ⊗≫ u ▷ E₂ ⊗≫ (L.sig ▷ E₂ ⊗≫ E₂ ◁ adj₂.counit) ⊗≫ 𝟙 _ := by
        bicategory
    _ = _ := by
        rw [L.sig_counit_pitchfork]
        unfold curlG
        bicategory

/-- **Brundan, Lemma 4.1, (4.2)**: the right curl with at most `h` dots is zero except in
its boundary degree, where it is minus the identity. -/
theorem curlG_dotted {n : ℕ} (hn : (n : ℤ) ≤ h) :
    curlG (L.cupL ≫ R₁ ◁ powComp x₁ n) adj₁.counit τ =
      if (n : ℤ) = h then -𝟙 E₂ else 0 := by
  rw [← L.close_cup_sig, Category.assoc, L.cupL_powComp_sig_of_le hn]
  split_ifs with heq
  · rw [AdditiveWhiskering.neg_whiskerRight]
    simp only [Preadditive.comp_neg, Preadditive.neg_comp]
    congr 1
    calc _ = (λ_ E₂).inv ≫ leftZigzag adj₂.unit adj₂.counit ≫ (ρ_ E₂).hom := by
          unfold leftZigzag
          bicategory
      _ = 𝟙 E₂ := by rw [adj₂.left_triangle]; simp
  · rw [AdditiveWhiskering.zero_whiskerRight]
    simp

/-- The rightward crossing against a dotted left cap, through the boundary degree. -/
theorem sig_powComp_capL_of_le {n : ℕ} (hn : (n : ℤ) ≤ -h) :
    L.sig ≫ powComp x₂ n ▷ R₂ ≫ L.capL = if (n : ℤ) = -h then adj₁.counit else 0 := by
  have hd := L.dual.cupL_powComp_sig_of_le hn
  simp only [dual_cupL, dual_sig] at hd
  split_ifs at hd ⊢ with heq
  · have hu := congrArg Quiver.Hom.unop hd
    change ((-L.sig) ≫ (powComp x₂.op n).unop ▷ R₂) ≫ L.capL = -adj₁.counit at hu
    rw [unop_powComp, Category.assoc, Preadditive.neg_comp] at hu
    exact neg_injective hu
  · have hu := congrArg Quiver.Hom.unop hd
    change ((-L.sig) ≫ (powComp x₂.op n).unop ▷ R₂) ≫ L.capL = 0 at hu
    rw [unop_powComp, Category.assoc, Preadditive.neg_comp] at hu
    exact neg_eq_zero.mp hu

omit [AdditiveWhiskering C] in
/-- Closing the input of the rightward crossing gives the curl on `E₁`. -/
theorem close_sig_cap (d : E₂ ≫ R₂ ⟶ 𝟙 b) :
    (λ_ E₁).inv ≫ adj₁.unit ▷ E₁ ≫ (α_ E₁ R₁ E₁).hom ≫
      E₁ ◁ (L.sig ≫ d) ≫ (ρ_ E₁).hom = curlEG adj₂.unit d τ := by
  calc _ = 𝟙 _ ⊗≫ (adj₁.unit ▷ E₁ ⊗≫ E₁ ◁ L.sig) ⊗≫ E₁ ◁ d ⊗≫ 𝟙 _ := by
        bicategory
    _ = _ := by
        rw [L.unit_sig_pitchfork]
        unfold curlEG
        bicategory

/-- **Brundan, Lemma 4.1, (4.1)**: the left curl with at most `-h` dots is zero except in
its boundary degree, where it is the identity. Here `h` is the weight after `E₁`, so the
weight of its source in the paper is `h - 2`. -/
theorem curlEG_dotted {n : ℕ} (hn : (n : ℤ) ≤ -h) :
    curlEG adj₂.unit (powComp x₂ n ▷ R₂ ≫ L.capL) τ =
      if (n : ℤ) = -h then 𝟙 E₁ else 0 := by
  rw [← L.close_sig_cap, L.sig_powComp_capL_of_le hn]
  split_ifs with heq
  · calc _ = (λ_ E₁).inv ≫ leftZigzag adj₁.unit adj₁.counit ≫ (ρ_ E₁).hom := by
          unfold leftZigzag
          bicategory
      _ = 𝟙 E₁ := by rw [adj₁.left_triangle]; simp
  · rw [AdditiveWhiskering.whiskerLeft_zero]
    simp

end RouqLoc

end Categorification.TwoRep
