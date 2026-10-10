/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqCyclicDot

/-!
# Same-colour crossing cyclicity from Rouquier data

Brundan, *On the definition of Kac–Moody 2-category*, arXiv:1501.00350v1,
Theorem 5.3, the same-colour part of (5.8), and the final deduction of cyclicity in §5.

The headline theorem `RouqLoc.cyclic_cross` identifies the left mate of the right mate
of the upward crossing with the original crossing. The intermediate `mate_sigL` identifies
the leftward crossing with a partial left mate. `cupL_pitchfork` and `capL_pitchfork`
remove the weight restrictions from the leftward pitchforks.

The proof uses the cup criterion above weight `-2` and the cap criterion one weight below
in the remaining range. Applying the same result to right-mate-reflected Rouquier data
proves full cyclicity. These relations supply the same-colour crossing identities for the
diagrammatic interpretation. No grading, finiteness, or scalar-endomorphism assumption occurs.
-/

noncomputable section
namespace Categorification.TwoRep
open CategoryTheory CategoryTheory.Bicategory
universe w v u

section MateCriterion
variable {C : Type u} [Bicategory.{w, v} C]
  {a b c d : C} {l₁ : a ⟶ b} {r₁ : b ⟶ a} {l₂ : c ⟶ d} {r₂ : d ⟶ c}
  (A : l₁ ⊣ r₁) (B : l₂ ⊣ r₂) {g : a ⟶ c} {h : b ⟶ d}
/-- Compute partial mates by closing the other side first. -/
theorem mateEquiv_other_order (φ : g ≫ l₂ ⟶ l₁ ≫ h) :
    mateEquiv A B φ = B.homEquiv₂ ((α_ r₁ g l₂).hom ≫ A.homEquiv₁ φ) := by
  simp only [Bicategory.mateEquiv_apply, Adjunction.homEquiv₁_apply, Adjunction.homEquiv₂_apply]
  bicategory
/-- A cap pitchfork characterizes a partial mate. -/
theorem mateEquiv_eq_iff_counit (φ : g ≫ l₂ ⟶ l₁ ≫ h) (ψ : r₁ ≫ g ⟶ h ≫ r₂) :
    mateEquiv A B φ = ψ ↔
      A.homEquiv₁ φ = (α_ r₁ g l₂).inv ≫ B.homEquiv₂.symm ψ := by
  rw [mateEquiv_other_order, ← Equiv.eq_symm_apply]
  constructor
  · intro hh
    rw [← hh, Iso.inv_hom_id_assoc]
  · intro hh
    rw [hh, Iso.hom_inv_id_assoc]
end MateCriterion

namespace RouqLoc
variable {C : Type u} [Bicategory.{w, v} C] [∀ a b : C, Preadditive (a ⟶ b)] [AdditiveWhiskering C]
  {a b c d : C} {E₁ : a ⟶ b} {R₁ : b ⟶ a} {E₂ : b ⟶ c} {R₂ : c ⟶ b}
  {E₃ : c ⟶ d} {R₃ : d ⟶ c}
  {adj₁ : E₁ ⊣ R₁} {adj₂ : E₂ ⊣ R₂} {adj₃ : E₃ ⊣ R₃}
  {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂} {x₃ : E₃ ⟶ E₃}
  {τ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂} {τ₂₃ : E₂ ≫ E₃ ⟶ E₂ ≫ E₃} {h h' : ℤ}
  (L : RouqLoc adj₁ adj₂ x₁ x₂ τ h) (U : RouqLoc adj₂ adj₃ x₂ x₃ τ₂₃ h')

/-- The cup pitchfork identifies the partial left mate above weight `-2`. -/
theorem mate_sigL_of_gt_neg_two (A₁ : R₁ ⊣ E₁) (A₂ : R₂ ⊣ E₂)
    (hu₁ : A₁.unit = L.cupL) (hu₂ : A₂.unit = U.cupL)
    (hw : h' = h + 2) (hh : -2 < h)
    (hsq : τ ≫ τ = 0) (hsq' : τ₂₃ ≫ τ₂₃ = 0)
    (hB : E₁ ◁ τ₂₃ ≫ ((α_ E₁ E₂ E₃).inv ≫ τ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom) ≫ E₁ ◁ τ₂₃ =
      ((α_ E₁ E₂ E₃).inv ≫ τ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom) ≫ E₁ ◁ τ₂₃ ≫
        ((α_ E₁ E₂ E₃).inv ≫ τ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom)) :
    mateEquiv A₁ A₂ L.sigL = τ := by
  apply (mateEquiv_eq_iff A₁ A₂ _ _).mpr
  simp only [Adjunction.homEquiv₁_symm_apply, Adjunction.homEquiv₂_apply, hu₁, hu₂]
  have hp := L.cupL_pitchfork_of_gt_neg_two U hw hh hsq hsq' hB
  have ht := congrArg (fun z => z ≫ (α_ R₁ E₁ E₂).hom) hp
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using ht

/-- The cap pitchfork identifies the upper partial left mate below weight zero. -/
theorem mate_sigL_of_neg (A₂ : R₂ ⊣ E₂) (A₃ : R₃ ⊣ E₃)
    (he₂ : A₂.counit = L.capL) (he₃ : A₃.counit = U.capL)
    (hw : h' = h + 2) (hh : h < 0)
    (hsq : τ ≫ τ = 0) (hsq' : τ₂₃ ≫ τ₂₃ = 0)
    (hB : E₁ ◁ τ₂₃ ≫ ((α_ E₁ E₂ E₃).inv ≫ τ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom) ≫ E₁ ◁ τ₂₃ =
      ((α_ E₁ E₂ E₃).inv ≫ τ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom) ≫ E₁ ◁ τ₂₃ ≫
        ((α_ E₁ E₂ E₃).inv ≫ τ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom)) :
    mateEquiv A₂ A₃ U.sigL = τ₂₃ := by
  apply (mateEquiv_eq_iff_counit A₂ A₃ _ _).mpr
  simp only [Adjunction.homEquiv₁_apply, Adjunction.homEquiv₂_symm_apply, he₂, he₃]
  exact (L.capL_pitchfork_of_neg U hw hh hsq hsq' hB).symm
end RouqLoc

namespace RouqLoc
variable {C : Type u} [Bicategory.{w, v} C] [∀ a b : C, Preadditive (a ⟶ b)] [AdditiveWhiskering C]
  {a₀ a₁ a₂ a₃ a₄ : C}
  {E₀ : a₀ ⟶ a₁} {R₀ : a₁ ⟶ a₀} {E₁ : a₁ ⟶ a₂} {R₁ : a₂ ⟶ a₁}
  {E₂ : a₂ ⟶ a₃} {R₂ : a₃ ⟶ a₂} {E₃ : a₃ ⟶ a₄} {R₃ : a₄ ⟶ a₃}
  {adj₀ : E₀ ⊣ R₀} {adj₁ : E₁ ⊣ R₁} {adj₂ : E₂ ⊣ R₂} {adj₃ : E₃ ⊣ R₃}
  {x₀ : E₀ ⟶ E₀} {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂} {x₃ : E₃ ⟶ E₃}
  {τ₀ : E₀ ≫ E₁ ⟶ E₀ ≫ E₁} {τ₁ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂}
  {τ₂ : E₂ ≫ E₃ ⟶ E₂ ≫ E₃} {h₀ h₁ h₂ : ℤ}
  (K : RouqLoc adj₀ adj₁ x₀ x₁ τ₀ h₀) (L : RouqLoc adj₁ adj₂ x₁ x₂ τ₁ h₁)
  (U : RouqLoc adj₂ adj₃ x₂ x₃ τ₂ h₂)
  (hw₀ : h₁ = h₀ + 2) (hw₁ : h₂ = h₁ + 2)
  (hsq₀ : τ₀ ≫ τ₀ = 0) (hsq₁ : τ₁ ≫ τ₁ = 0) (hsq₂ : τ₂ ≫ τ₂ = 0)
  (hb₀ : E₀ ◁ τ₁ ≫ ((α_ E₀ E₁ E₂).inv ≫ τ₀ ▷ E₂ ≫ (α_ E₀ E₁ E₂).hom) ≫ E₀ ◁ τ₁ =
    ((α_ E₀ E₁ E₂).inv ≫ τ₀ ▷ E₂ ≫ (α_ E₀ E₁ E₂).hom) ≫ E₀ ◁ τ₁ ≫
      ((α_ E₀ E₁ E₂).inv ≫ τ₀ ▷ E₂ ≫ (α_ E₀ E₁ E₂).hom))
  (hb₁ : E₁ ◁ τ₂ ≫ ((α_ E₁ E₂ E₃).inv ≫ τ₁ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom) ≫ E₁ ◁ τ₂ =
    ((α_ E₁ E₂ E₃).inv ≫ τ₁ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom) ≫ E₁ ◁ τ₂ ≫
      ((α_ E₁ E₂ E₃).inv ≫ τ₁ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom))

include K U hw₀ hw₁ hsq₀ hsq₁ hsq₂ hb₀ hb₁ in
/-- The mate identity depends only on the prescribed units and counits. -/
theorem mate_sigL_of_units_counits (A₁ : R₁ ⊣ E₁) (A₂ : R₂ ⊣ E₂)
    (hu₁ : A₁.unit = L.cupL) (hu₂ : A₂.unit = U.cupL)
    (he₁ : A₁.counit = K.capL) (he₂ : A₂.counit = L.capL) :
    mateEquiv A₁ A₂ L.sigL = τ₁ := by
  by_cases hh : -2 < h₁
  · exact L.mate_sigL_of_gt_neg_two U A₁ A₂ hu₁ hu₂ hw₁ hh hsq₁ hsq₂ hb₁
  · exact K.mate_sigL_of_neg L A₁ A₂ he₁ he₂ hw₀ (by omega) hsq₀ hsq₁ hb₀

/-- At every weight, the leftward crossing is the partial left mate of the upward crossing. -/
theorem mate_sigL : mateEquiv (K.leftAdjunction L hw₀ hsq₀ hsq₁ hb₀)
    (L.leftAdjunction U hw₁ hsq₁ hsq₂ hb₁) L.sigL = τ₁ := by
  by_cases hh : -2 < h₁
  · exact L.mate_sigL_of_gt_neg_two U _ _ rfl rfl hw₁ hh hsq₁ hsq₂ hb₁
  · exact K.mate_sigL_of_neg L _ _ rfl rfl hw₀ (by omega) hsq₀ hsq₁ hb₀

include K U hw₀ hw₁ hsq₀ hsq₁ hsq₂ hb₀ hb₁ in
/-- The leftward cup pitchfork holds without a weight restriction. -/
theorem cupL_pitchfork :
    (λ_ E₂).inv ≫ L.cupL ▷ E₂ ≫ (α_ R₁ E₁ E₂).hom ≫
      R₁ ◁ τ₁ ≫ (α_ R₁ E₁ E₂).inv =
    (ρ_ E₂).inv ≫ E₂ ◁ U.cupL ≫ (α_ E₂ R₂ E₂).inv ≫ L.sigL ▷ E₂ := by
  have ht := (mateEquiv_eq_iff (K.leftAdjunction L hw₀ hsq₀ hsq₁ hb₀)
    (L.leftAdjunction U hw₁ hsq₁ hsq₂ hb₁) L.sigL τ₁).mp
      (K.mate_sigL L U hw₀ hw₁ hsq₀ hsq₁ hsq₂ hb₀ hb₁)
  simp only [Adjunction.homEquiv₁_symm_apply, Adjunction.homEquiv₂_apply,
    leftAdjunction] at ht
  have ht' := congrArg (fun z => z ≫ (α_ R₁ E₁ E₂).inv) ht
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using ht'

include K U hw₀ hw₁ hsq₀ hsq₁ hsq₂ hb₀ hb₁ in
/-- The leftward cap pitchfork holds without a weight restriction. -/
theorem capL_pitchfork :
    (α_ E₁ E₂ R₂).inv ≫ τ₁ ▷ R₂ ≫ (α_ E₁ E₂ R₂).hom ≫
      E₁ ◁ L.capL ≫ (ρ_ E₁).hom =
    E₁ ◁ L.sigL ≫ (α_ E₁ R₁ E₁).inv ≫ K.capL ▷ E₁ ≫ (λ_ E₁).hom := by
  have ht := (mateEquiv_eq_iff_counit (K.leftAdjunction L hw₀ hsq₀ hsq₁ hb₀)
    (L.leftAdjunction U hw₁ hsq₁ hsq₂ hb₁) L.sigL τ₁).mp
      (K.mate_sigL L U hw₀ hw₁ hsq₀ hsq₁ hsq₂ hb₀ hb₁)
  simpa only [Adjunction.homEquiv₁_apply, Adjunction.homEquiv₂_symm_apply,
    leftAdjunction] using ht.symm

/-- Full same-colour crossing cyclicity: the left mate of the right mate is the crossing. -/
theorem cyclic_cross :
    conjugateEquiv ((L.leftAdjunction U hw₁ hsq₁ hsq₂ hb₁).comp
        (K.leftAdjunction L hw₀ hsq₀ hsq₁ hb₀))
      ((L.leftAdjunction U hw₁ hsq₁ hsq₂ hb₁).comp
        (K.leftAdjunction L hw₀ hsq₀ hsq₁ hb₀))
      (conjugateEquiv (adj₁.comp adj₂) (adj₁.comp adj₂) τ₁) = τ₁ := by
  let A₁ := K.leftAdjunction L hw₀ hsq₀ hsq₁ hb₀
  let A₂ := L.leftAdjunction U hw₁ hsq₁ hsq₂ hb₁
  have hm : mateEquiv (HOp.adjunction A₁) (HOp.adjunction A₂) L.mirror.sigL = L.mirrorTau :=
    K.mirror.mate_sigL_of_units_counits L.mirror U.mirror hw₀ hw₁
      (K.mirror_square hsq₀) (L.mirror_square hsq₁) (U.mirror_square hsq₂)
      (K.mirror_braid L hb₀) (L.mirror_braid U hb₁)
      (HOp.adjunction A₁) (HOp.adjunction A₂)
      (by exact L.mirror_cupL.symm) (by exact U.mirror_cupL.symm)
      (by exact K.mirror_capL.symm) (by exact L.mirror_capL.symm)
  rw [HOp.mateEquiv_reflect, L.mirror_sigL] at hm
  change (mateEquiv A₂ A₁).symm L.sigL =
    conjugateEquiv (adj₁.comp adj₂) (adj₁.comp adj₂) τ₁ at hm
  have hm' : mateEquiv A₂ A₁ (conjugateEquiv (adj₁.comp adj₂) (adj₁.comp adj₂) τ₁) = L.sigL := by
    rw [← hm, Equiv.apply_symm_apply]
  change conjugateEquiv (A₂.comp A₁) (A₂.comp A₁) _ = _
  rw [RouqSl2Generic.rightMate_eq_iterated, hm']
  exact K.mate_sigL L U hw₀ hw₁ hsq₀ hsq₁ hsq₂ hb₀ hb₁
end RouqLoc
end Categorification.TwoRep
