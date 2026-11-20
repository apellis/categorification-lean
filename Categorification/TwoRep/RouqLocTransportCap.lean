/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqLocTransport

/-!
# Leftward cups and caps of transported Rouquier data

Brundan, arXiv:1501.00350v1, (1.14)–(1.18): the leftward cup and cap of local Rouquier
data are built from the components of the inverses (1.8), (1.9), the rightward crossing and
the rightward cups and caps. Transporting the data along isomorphisms of 1-cells
(`AdditiveCat.RouqLoc.transport`) conjugates all of them, so the leftward cap of the
transported data is the original one precomposed with `E₂' R₂' ≅ E₂ R₂`, and the leftward
cup is the original one followed by `R₁ E₁ ≅ R₁' E₁'`.
-/

noncomputable section
namespace Categorification.TwoRep
open CategoryTheory CategoryTheory.Bicategory

namespace AdditiveCat

universe v u

variable {A B C : AdditiveCat.{v, u}}
  {E₁ E₁' : A ⟶ B} {R₁ R₁' : B ⟶ A} {E₂ E₂' : B ⟶ C} {R₂ R₂' : C ⟶ B}
  {adj₁ : E₁ ⊣ R₁} {adj₂ : E₂ ⊣ R₂} {adj₁' : E₁' ⊣ R₁'} {adj₂' : E₂' ⊣ R₂'}
  {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂} {τ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂}
  {x₁' : E₁' ⟶ E₁'} {x₂' : E₂' ⟶ E₂'} {τ' : E₁' ≫ E₂' ⟶ E₁' ≫ E₂'} {h : ℤ}
  (L : RouqLoc adj₁ adj₂ x₁ x₂ τ h) (e₁ : E₁' ≅ E₁) (e₂ : E₂' ≅ E₂) (r₁ : R₁' ≅ R₁)
  (r₂ : R₂' ≅ R₂) (hη : adj₂'.unit ≫ (e₂.hom ▷ R₂' ≫ E₂ ◁ r₂.hom) = adj₂.unit)
  (hκ : (r₁.hom ▷ E₁' ≫ R₁ ◁ e₁.hom) ≫ adj₁.counit = adj₁'.counit)
  (hx₁ : x₁' ≫ e₁.hom = e₁.hom ≫ x₁) (hx₂ : x₂' ≫ e₂.hom = e₂.hom ≫ x₂)
  (hτ : τ' ≫ (e₁.hom ▷ E₂' ≫ E₁ ◁ e₂.hom) = (e₁.hom ▷ E₂' ≫ E₁ ◁ e₂.hom) ≫ τ)

/-- The rightward cap with dots of transported data is conjugated. -/
theorem transport_capD (n : ℕ) :
    (RouqLoc.transport L e₁ e₂ r₁ r₂ hη hκ hx₁ hx₂ hτ).capD n =
      (r₁.hom ▷ E₁' ≫ R₁ ◁ e₁.hom) ≫ L.capD n :=
  capD_conj e₁.hom r₁.hom hκ (powComp_conj e₁ hx₁ n)

/-- The rightward cup with dots of transported data is conjugated. -/
theorem transport_cupD (n : ℕ) :
    (RouqLoc.transport L e₁ e₂ r₁ r₂ hη hκ hx₁ hx₂ hτ).cupD n ≫ (e₂.hom ▷ R₂' ≫ E₂ ◁ r₂.hom) =
      L.cupD n :=
  cupD_conj e₂.hom r₂.hom hη (powComp_conj e₂ hx₂ n)

/-- **The leftward crossing of transported data** is `ψ₂ ≫ σ' ≫ ψ₁⁻¹`. -/
theorem transport_sigL :
    (RouqLoc.transport L e₁ e₂ r₁ r₂ hη hκ hx₁ hx₂ hτ).sigL ≫ (r₁.hom ▷ E₁' ≫ R₁ ◁ e₁.hom) =
      (e₂.hom ▷ R₂' ≫ E₂ ◁ r₂.hom) ≫ L.sigL := by
  unfold RouqLoc.sigL
  split_ifs with hh
  · change (-((e₂.hom ▷ R₂' ≫ E₂ ◁ r₂.hom) ≫ (L.ip hh).f' ≫
        (whiskerRightIso r₁ E₁' ≪≫ whiskerLeftIso R₁ e₁).inv)) ≫ _ = _
    simp [Category.assoc]
  · change (-((e₂.hom ▷ R₂' ≫ E₂ ◁ r₂.hom) ≫ (L.iN _).f' ≫
        (whiskerRightIso r₁ E₁' ≪≫ whiskerLeftIso R₁ e₁).inv)) ≫ _ = _
    simp [Category.assoc]

/-- **The leftward cap of transported data** (Brundan (1.15), (1.17)) is the original leftward
cap precomposed with `E₂' R₂' ≅ E₂ R₂`. -/
theorem transport_capL :
    (RouqLoc.transport L e₁ e₂ r₁ r₂ hη hκ hx₁ hx₂ hτ).capL =
      (e₂.hom ▷ R₂' ≫ E₂ ◁ r₂.hom) ≫ L.capL := by
  unfold RouqLoc.capL
  split_ifs with hh
  · unfold RouqLoc.capN
    split_ifs with h'
    · change (e₂.hom ▷ R₂' ≫ E₂ ◁ r₂.hom) ≫ (L.iN h').g' _ ≫ 𝟙 _ = _
      rw [Category.comp_id]
    · exact absurd hh.le h'
  · rw [transport_capD, ← Category.assoc, transport_sigL, Category.assoc,
      Preadditive.comp_neg]

/-- **The leftward cup of transported data** (Brundan (1.14), (1.18)) is the original leftward
cup followed by `R₁ E₁ ≅ R₁' E₁'`. -/
theorem transport_cupL :
    (RouqLoc.transport L e₁ e₂ r₁ r₂ hη hκ hx₁ hx₂ hτ).cupL ≫ (r₁.hom ▷ E₁' ≫ R₁ ◁ e₁.hom) =
      L.cupL := by
  unfold RouqLoc.cupL
  split_ifs with hh
  · unfold RouqLoc.cupN
    split_ifs with h'
    · change (𝟙 _ ≫ (L.ip h').g' _ ≫
        (whiskerRightIso r₁ E₁' ≪≫ whiskerLeftIso R₁ e₁).inv) ≫ _ = _
      simp
    · exact absurd hh.le h'
  · rw [Category.assoc, transport_sigL, ← Category.assoc, transport_cupD]

end AdditiveCat

end Categorification.TwoRep
