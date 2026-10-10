/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqPitchfork

/-!
# The upward left-adjunction triangle

The upward-strand triangle in Brundan, *On the definition of Kac–Moody 2-category*,
arXiv:1501.00350v1, Theorem 4.3, follows from the pitchforks and dotted curls. We prove it
at all weights from adjacent Rouquier data, with no grading or scalar-endomorphism hypothesis.

The headline result `RouqLoc.rightZigzag_left` is the right triangle for the candidate
adjunction `R₂ ⊣ E₂`. It is one of the two identities needed to construct that adjunction;
this module does not assert the other triangle. The proof treats nonnegative weights,
weights at most `-2`, and the correction at weight `-1` separately.
-/

noncomputable section
namespace Categorification.TwoRep
open CategoryTheory CategoryTheory.Bicategory
universe w v u

namespace RouqSl2Generic
variable {C : Type u} [Bicategory.{w, v} C] [∀ a b : C, Preadditive (a ⟶ b)]
  [AdditiveWhiskering C] {a b c : C} {E₁ : a ⟶ b} {E₂ : b ⟶ c} {R₁ : b ⟶ a}

/-- Closing the first strand of a crossing is additive. -/
def curlGMap (u : 𝟙 b ⟶ R₁ ≫ E₁) (e : R₁ ≫ E₁ ⟶ 𝟙 b) :
    (E₁ ≫ E₂ ⟶ E₁ ≫ E₂) →+ (E₂ ⟶ E₂) where
  toFun := curlG u e
  map_zero' := by simp only [curlG, AdditiveWhiskering.whiskerLeft_zero,
    Limits.comp_zero, Limits.zero_comp]
  map_add' _ _ := by simp only [curlG, AdditiveWhiskering.whiskerLeft_add,
    Preadditive.comp_add, Preadditive.add_comp]

omit [∀ a b : C, Preadditive (a ⟶ b)] [AdditiveWhiskering C] in
/-- Dots on the first strand at the top are absorbed into its cap. -/
theorem curlG_comp_whiskerRight_cap (u : 𝟙 b ⟶ R₁ ≫ E₁) (e : R₁ ≫ E₁ ⟶ 𝟙 b)
    (t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) (x : E₁ ⟶ E₁) :
    curlG u e (t ≫ x ▷ E₂) = curlG u (R₁ ◁ x ≫ e) t := by
  unfold curlG
  bicategory
end RouqSl2Generic

namespace RouqLoc
variable {C : Type u} [Bicategory.{w, v} C] [∀ a b : C, Preadditive (a ⟶ b)] [AdditiveWhiskering C]
  {a b c d : C} {E₁ : a ⟶ b} {R₁ : b ⟶ a} {E₂ : b ⟶ c} {R₂ : c ⟶ b}
  {E₃ : c ⟶ d} {R₃ : d ⟶ c}
  {adj₁ : E₁ ⊣ R₁} {adj₂ : E₂ ⊣ R₂} {adj₃ : E₃ ⊣ R₃}
  {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂} {x₃ : E₃ ⟶ E₃}
  {τ₁₂ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂} {τ₂₃ : E₂ ≫ E₃ ⟶ E₂ ≫ E₃} {h h' : ℤ}
  (L : RouqLoc adj₁ adj₂ x₁ x₂ τ₁₂ h) (U : RouqLoc adj₂ adj₃ x₂ x₃ τ₂₃ h')

/-- The boundary right curl with all dots on the cap side. -/
theorem curlG_capD_self (hh : 0 ≤ h) : curlG L.cupL (L.capD h.toNat) τ₁₂ = -𝟙 E₂ := by
  rcases eq_or_lt_of_le hh with hz | hp
  · subst h
    simpa only [Int.toNat_zero, capD, powComp_zero, whiskerLeft_id, Category.id_comp,
      Category.comp_id, Nat.cast_zero, ite_true] using L.curlG_dotted (n := 0) (by omega)
  · have hN : (h.toNat : ℤ) = h := Int.toNat_of_nonneg hh
    have hb : curlG L.cupL adj₁.counit τ₁₂ = 0 := by
      simpa only [powComp_zero, whiskerLeft_id, Category.comp_id, Nat.cast_zero,
        ite_eq_right (by omega : (0 : ℤ) ≠ h)] using L.curlG_dotted (n := 0) (by omega)
    have hx : τ₁₂ ≫ powComp (x₁ ▷ E₂) h.toNat =
        powComp (E₁ ◁ x₂) h.toNat ≫ τ₁₂ -
          ∑ j ∈ Finset.range h.toNat, powComp (E₁ ◁ x₂) j ≫
            powComp (x₁ ▷ E₂) (h.toNat - 1 - j) := by
      rw [qpow_tau _ _ _ L.slide_left h.toNat, add_sub_cancel_right]
    change curlG L.cupL (R₁ ◁ powComp x₁ h.toNat ≫ adj₁.counit) τ₁₂ = _
    rw [← RouqSl2Generic.curlG_comp_whiskerRight_cap, powComp_whiskerRight]
    change (RouqSl2Generic.curlGMap L.cupL adj₁.counit) _ = _
    rw [hx, map_sub, map_sum]
    change curlG L.cupL adj₁.counit (powComp (E₁ ◁ x₂) h.toNat ≫ τ₁₂) -
      (∑ j ∈ Finset.range h.toNat, curlG L.cupL adj₁.counit
        (powComp (E₁ ◁ x₂) j ≫ powComp (x₁ ▷ E₂) (h.toNat - 1 - j))) = _
    rw [← whiskerLeft_powComp, curlG_whiskerLeft_comp, hb, Limits.comp_zero, zero_sub]
    congr 1
    have ht : ∀ j ∈ Finset.range h.toNat, curlG L.cupL adj₁.counit
        (powComp (E₁ ◁ x₂) j ≫ powComp (x₁ ▷ E₂) (h.toNat - 1 - j)) =
        if j = 0 then 𝟙 E₂ else 0 := by
      intro j hj
      have hj' := Finset.mem_range.mp hj
      rw [← whiskerLeft_powComp, ← powComp_whiskerRight, curlG_whiskerLeft_comp,
        curlG_whiskerRight]
      have hc := L.cupL_capD hp (n := h.toNat - 1 - j) (by omega)
      change L.cupL ≫ R₁ ◁ powComp x₁ (h.toNat - 1 - j) ≫ adj₁.counit = _ at hc
      rw [hc]
      by_cases heq : j = 0
      · subst j
        simp
      · rw [ite_eq_right (by omega), AdditiveWhiskering.zero_whiskerRight,
          ite_eq_right heq]
        simp
    rw [Finset.sum_congr rfl ht]
    simp [show 0 < h.toNat by omega]

/-- The boundary left curl with all dots on the cup side. -/
theorem curlEG_cupD_self (hh : h ≤ 0) : curlEG (L.cupD (-h).toNat) L.capL τ₁₂ = 𝟙 E₁ := by
  rcases lt_or_eq_of_le hh with hn | hz
  · have hN : ((-h).toNat : ℤ) = -h := Int.toNat_of_nonneg (by omega)
    have hb : curlEG adj₂.unit L.capL τ₁₂ = 0 := by
      simpa only [powComp_zero, id_whiskerRight, Category.id_comp, Nat.cast_zero,
        ite_eq_right (by omega : (0 : ℤ) ≠ -h)] using L.curlEG_dotted (n := 0) (by omega)
    change curlEG (adj₂.unit ≫ powComp x₂ (-h).toNat ▷ R₂) L.capL τ₁₂ = _
    rw [← curlEG_whiskerLeft_comp, whiskerLeft_powComp]
    change (RouqSl2Generic.curlEGMap adj₂.unit L.capL) _ = _
    rw [qpow_tau _ _ _ L.slide_left (-h).toNat, map_add, map_sum]
    change curlEG adj₂.unit L.capL (τ₁₂ ≫ powComp (x₁ ▷ E₂) (-h).toNat) +
      (∑ j ∈ Finset.range (-h).toNat, curlEG adj₂.unit L.capL
        (powComp (E₁ ◁ x₂) j ≫ powComp (x₁ ▷ E₂) ((-h).toNat - 1 - j))) = _
    rw [← powComp_whiskerRight, curlEG_comp_whiskerRight, hb, Limits.zero_comp, zero_add]
    have ht : ∀ j ∈ Finset.range (-h).toNat, curlEG adj₂.unit L.capL
        (powComp (E₁ ◁ x₂) j ≫ powComp (x₁ ▷ E₂) ((-h).toNat - 1 - j)) =
        if j = (-h).toNat - 1 then 𝟙 E₁ else 0 := by
      intro j hj
      have hj' := Finset.mem_range.mp hj
      rw [← whiskerLeft_powComp, ← powComp_whiskerRight, curlEG_comp_whiskerRight,
        curlEG_whiskerLeft]
      have hc := L.cupD_capL hn (n := j) hj'
      change (adj₂.unit ≫ powComp x₂ j ▷ R₂) ≫ L.capL = _ at hc
      rw [Category.assoc] at hc
      rw [hc, show (-h - 1).toNat = (-h).toNat - 1 by omega]
      by_cases heq : j = (-h).toNat - 1
      · subst j
        simp
      · rw [ite_eq_right heq, AdditiveWhiskering.whiskerLeft_zero]
        simp [heq]
    rw [Finset.sum_congr rfl ht]
    simp [show (-h).toNat - 1 < (-h).toNat by omega]
  · subst h
    simpa only [neg_zero, Int.toNat_zero, cupD, powComp_zero, id_whiskerRight,
      Category.comp_id, Category.id_comp, Nat.cast_zero, ite_true] using
      L.curlEG_dotted (n := 0) (by omega)

/-- The left-adjunction triangle on the upward strand, at every weight. -/
theorem leftAdj_triangle_E (hw : h' = h + 2)
    (hsq : τ₁₂ ≫ τ₁₂ = 0) (hsq' : τ₂₃ ≫ τ₂₃ = 0)
    (hB : E₁ ◁ τ₂₃ ≫ ((α_ E₁ E₂ E₃).inv ≫ τ₁₂ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom) ≫ E₁ ◁ τ₂₃ =
      ((α_ E₁ E₂ E₃).inv ≫ τ₁₂ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom) ≫ E₁ ◁ τ₂₃ ≫
        ((α_ E₁ E₂ E₃).inv ≫ τ₁₂ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom)) :
    (ρ_ E₂).inv ≫ E₂ ◁ U.cupL ≫ (α_ E₂ R₂ E₂).inv ≫ L.capL ▷ E₂ ≫ (λ_ E₂).hom = 𝟙 E₂ := by
  rcases le_or_gt 0 h with hh | hh
  · have hp := L.cupL_pitchfork_of_gt_neg_two U hw (by omega) hsq hsq' hB
    have hc : curlG L.cupL (L.capD h.toNat) τ₁₂ =
        (ρ_ E₂).inv ≫ E₂ ◁ U.cupL ≫ (α_ E₂ R₂ E₂).inv ≫
          (L.sigL ≫ L.capD h.toNat) ▷ E₂ ≫ (λ_ E₂).hom := by
      calc _ = ((λ_ E₂).inv ≫ L.cupL ▷ E₂ ≫ (α_ R₁ E₁ E₂).hom ≫
          R₁ ◁ τ₁₂ ≫ (α_ R₁ E₁ E₂).inv) ≫ L.capD h.toNat ▷ E₂ ≫ (λ_ E₂).hom := by
            unfold curlG
            simp only [Category.assoc]
        _ = _ := by rw [hp]; bicategory
    rw [L.capL_of_nonneg hh, AdditiveWhiskering.neg_whiskerRight]
    simp only [Preadditive.neg_comp, Preadditive.comp_neg]
    rw [← hc, L.curlG_capD_self hh, neg_neg]
  · by_cases heq : h = -1
    · have hu : 0 < h' := by omega
      have hs : U.cupL ≫ U.sig = 0 := U.cupL_sig hu
      have hb : U.cupL ≫ adj₂.counit = 𝟙 (𝟙 c) := by
        simpa only [capD, powComp_zero, whiskerLeft_id, Category.id_comp,
          show (h' - 1).toNat = 0 by omega, ite_true] using U.cupL_capD hu (n := 0) (by omega)
      let z := (ρ_ E₂).inv ≫ E₂ ◁ U.cupL ≫ (α_ E₂ R₂ E₂).inv ≫ L.capL ▷ E₂ ≫ (λ_ E₂).hom
      change z = 𝟙 E₂
      have hz : (ρ_ E₂).inv ≫ E₂ ◁ U.cupL ≫ (α_ E₂ R₂ E₂).inv ≫ U.capCross = 0 := by
        unfold capCross
        rw [Iso.inv_hom_id_assoc, ← whiskerLeft_comp_assoc, hs,
          AdditiveWhiskering.whiskerLeft_zero, Limits.zero_comp, Limits.comp_zero]
      have he : 0 = -z + 𝟙 E₂ := by
        calc 0 = (ρ_ E₂).inv ≫ E₂ ◁ U.cupL ≫ (α_ E₂ R₂ E₂).inv ≫ U.capCross := hz.symm
          _ = -z + 𝟙 E₂ := by
            rw [L.capCross_eq_of_neg U hw hh hsq hsq' hB, ite_eq_left heq]
            simp only [Preadditive.comp_add, Preadditive.comp_neg]
            change -z + (ρ_ E₂).inv ≫ E₂ ◁ U.cupL ≫ (α_ E₂ R₂ E₂).inv ≫
              (α_ E₂ R₂ E₂).hom ≫ E₂ ◁ adj₂.counit ≫ (ρ_ E₂).hom = -z + 𝟙 E₂
            rw [Iso.inv_hom_id_assoc, ← whiskerLeft_comp_assoc, hb, whiskerLeft_id,
              Category.id_comp, Iso.inv_hom_id]
      exact (eq_of_sub_eq_zero (by
        simpa only [sub_eq_add_neg, add_comm] using he.symm) : 𝟙 E₂ = z).symm
    · have hu : h' ≤ 0 := by omega
      have hp := L.capL_pitchfork_of_neg U hw hh hsq hsq' hB
      calc _ = (ρ_ E₂).inv ≫ E₂ ◁ U.cupD (-h').toNat ≫
          (E₂ ◁ U.sigL ≫ (α_ E₂ R₂ E₂).inv ≫ L.capL ▷ E₂ ≫ (λ_ E₂).hom) := by
            rw [U.cupL_of_nonpos hu]
            bicategory
        _ = curlEG (U.cupD (-h').toNat) U.capL τ₂₃ := by
            rw [← hp]
            rfl
        _ = 𝟙 E₂ := U.curlEG_cupD_self hu

/-- The upward-strand triangle in the standard bicategorical form. -/
theorem rightZigzag_left (hw : h' = h + 2)
    (hsq : τ₁₂ ≫ τ₁₂ = 0) (hsq' : τ₂₃ ≫ τ₂₃ = 0)
    (hB : E₁ ◁ τ₂₃ ≫ ((α_ E₁ E₂ E₃).inv ≫ τ₁₂ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom) ≫ E₁ ◁ τ₂₃ =
      ((α_ E₁ E₂ E₃).inv ≫ τ₁₂ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom) ≫ E₁ ◁ τ₂₃ ≫
        ((α_ E₁ E₂ E₃).inv ≫ τ₁₂ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom)) :
    rightZigzag U.cupL L.capL = (ρ_ E₂).hom ≫ (λ_ E₂).inv := by
  have ht := L.leftAdj_triangle_E U hw hsq hsq' hB
  have he := congrArg (fun z => (ρ_ E₂).hom ≫ z ≫ (λ_ E₂).inv) ht
  calc rightZigzag U.cupL L.capL = E₂ ◁ U.cupL ≫ (α_ E₂ R₂ E₂).inv ≫ L.capL ▷ E₂ := by
        unfold rightZigzag
        bicategory
    _ = _ := by
        simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
          Category.comp_id, Category.id_comp] using he

end RouqLoc
end Categorification.TwoRep
