/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqAdjunction

/-!
# Dot cyclicity from Rouquier data

Brundan, *On the definition of Kac–Moody 2-category*, arXiv:1501.00350v1,
Lemma 5.1 and Theorem 5.3, equation (5.6).

The headline theorem `RouqLoc.cyclic_dot` identifies the left mate of the right mate
of the dot with the original dot. The equivalent cup/cap slides `cupL_dot` and `capL_dot`
hold at every weight and supply the dot relations needed for the diagrammatic interpretation.

Inverse-component cancellation first proves the cup slide at positive weights and the cap
slide at negative weights. The left adjunction then extends these identities to every weight,
with no assumptions on grading or endomorphism dimensions.
-/

noncomputable section
namespace Categorification.TwoRep
open CategoryTheory CategoryTheory.Bicategory
universe w v u

section InverseDetection
variable {D : Type*} [Category D] [Preadditive D] {X Y Z W : D}
/-- An explicit column inverse detects incoming morphisms. -/
theorem SumInvTo.hom_ext {f : X ⟶ Y} {g : ℕ → (X ⟶ Z)} {n : ℕ} (I : SumInvTo f g n)
    (p q : W ⟶ X) (hf : p ≫ f = q ≫ f) (hg : ∀ m, m < n → p ≫ g m = q ≫ g m) : p = q := by
  calc p = p ≫ (f ≫ I.f' + ∑ m ∈ Finset.range n, g m ≫ I.g' m) := by rw [I.total, Category.comp_id]
    _ = q ≫ (f ≫ I.f' + ∑ m ∈ Finset.range n, g m ≫ I.g' m) := by
      simp only [Preadditive.comp_add, Preadditive.comp_sum, ← Category.assoc]
      rw [hf]
      congr 1
      apply Finset.sum_congr rfl
      intro m hm
      rw [hg m (Finset.mem_range.mp hm)]
    _ = q := by rw [I.total, Category.comp_id]
/-- An explicit row inverse detects outgoing morphisms. -/
theorem SumInvFrom.hom_ext {f : Y ⟶ X} {g : ℕ → (Z ⟶ X)} {n : ℕ} (I : SumInvFrom f g n)
    (p q : X ⟶ W) (hf : f ≫ p = f ≫ q) (hg : ∀ m, m < n → g m ≫ p = g m ≫ q) : p = q := by
  apply Quiver.Hom.op_inj
  apply I.op.hom_ext p.op q.op
  · exact congrArg Quiver.Hom.op hf
  · intro m hm
    exact congrArg Quiver.Hom.op (hg m hm)
end InverseDetection

section MateDetection
variable {C : Type u} [Bicategory.{w, v} C] {a b : C} {E : a ⟶ b} {R : b ⟶ a}
/-- The unit of an adjunction detects endomorphisms of its right adjoint. -/
theorem eq_of_unit_whiskerLeft (A : E ⊣ R) (x y : R ⟶ R)
    (h : A.unit ≫ E ◁ x = A.unit ≫ E ◁ y) : x = y := by
  have hc (z : R ⟶ R) : (ρ_ R).inv ≫ R ◁ (A.unit ≫ E ◁ z) ≫
      (α_ R E R).inv ≫ A.counit ▷ R ≫ (λ_ R).hom = z := by
    calc _ = (ρ_ R).inv ≫ R ◁ A.unit ≫ (α_ R E R).inv ≫
        ((R ≫ E) ◁ z ≫ A.counit ▷ R) ≫ (λ_ R).hom := by bicategory
      _ = (ρ_ R).inv ≫ rightZigzag A.unit A.counit ≫ (λ_ R).hom ≫ z := by
        rw [whisker_exchange]
        unfold rightZigzag
        bicategory
      _ = z := by rw [A.right_triangle]; simp
  rw [← hc x, h, hc]
/-- The counit of an adjunction detects endomorphisms of its right adjoint. -/
theorem eq_of_whiskerRight_counit (A : E ⊣ R) (x y : R ⟶ R)
    (h : x ▷ E ≫ A.counit = y ▷ E ≫ A.counit) : x = y := by
  have hc (z : R ⟶ R) : (ρ_ R).inv ≫ R ◁ A.unit ≫
      (α_ R E R).inv ≫ (z ▷ E ≫ A.counit) ▷ R ≫ (λ_ R).hom = z := by
    calc _ = (ρ_ R).inv ≫ (R ◁ A.unit ≫ z ▷ (E ≫ R)) ≫
        (α_ R E R).inv ≫ A.counit ▷ R ≫ (λ_ R).hom := by bicategory
      _ = z ≫ (ρ_ R).inv ≫ rightZigzag A.unit A.counit ≫ (λ_ R).hom := by
        rw [whisker_exchange]
        unfold rightZigzag
        bicategory
      _ = z := by rw [A.right_triangle]; simp
  rw [← hc x, h, hc]
end MateDetection

namespace RouqLoc
variable {C : Type u} [Bicategory.{w, v} C] [∀ a b : C, Preadditive (a ⟶ b)] [AdditiveWhiskering C]
  {a b c : C} {E₁ : a ⟶ b} {R₁ : b ⟶ a} {E₂ : b ⟶ c} {R₂ : c ⟶ b}
  {adj₁ : E₁ ⊣ R₁} {adj₂ : E₂ ⊣ R₂}
  {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂} {τ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂} {h : ℤ}
  (L : RouqLoc adj₁ adj₂ x₁ x₂ τ h)

/-- Brundan Lemma 5.1: a dot slides around the leftward cup at positive weight. -/
theorem cupL_dot_of_pos (hh : 0 < h) : L.cupL ≫ R₁ ◁ x₁ = L.cupL ≫ L.dotD₁ ▷ E₁ := by
  apply (L.ip (le_of_lt hh)).hom_ext
  · have h₁ := congrArg (fun z => L.cupL ≫ z) L.sig_dot_sub
    have h₂ := congrArg (fun z => L.cupL ≫ z) L.sig_dotD_sub
    simp only [Preadditive.comp_sub, ← Category.assoc, L.cupL_sig hh, Limits.zero_comp,
      zero_sub] at h₁ h₂
    exact neg_injective (h₁.trans h₂.symm)
  · intro n _
    simp only [capD, Category.assoc]
    rw [← whisker_exchange_assoc, L.dotD₁_counit, ← whiskerLeft_comp_assoc,
      ← whiskerLeft_comp_assoc, comp_powComp, powComp_succ]

/-- The reflected cup-dot relation: a dot slides around the leftward cap at negative weight. -/
theorem capL_dot_of_neg (hh : h < 0) : x₂ ▷ R₂ ≫ L.capL = E₂ ◁ L.dotD₂ ≫ L.capL := by
  apply (L.iN (le_of_lt hh)).hom_ext
  · change L.sig ≫ x₂ ▷ R₂ ≫ L.capL = L.sig ≫ E₂ ◁ L.dotD₂ ≫ L.capL
    have h₁ := congrArg (fun z => z ≫ L.capL) L.sig_dot_sub
    have h₂ := congrArg (fun z => z ≫ L.capL) L.sig_dotD_sub
    simp only [Preadditive.sub_comp, Category.assoc, L.sig_capL hh, Limits.comp_zero,
      sub_zero] at h₁ h₂
    exact h₁.trans h₂.symm
  · intro n _
    change L.cupD n ≫ x₂ ▷ R₂ ≫ L.capL = L.cupD n ≫ E₂ ◁ L.dotD₂ ≫ L.capL
    simp only [cupD, Category.assoc]
    rw [← whisker_exchange_assoc, ← Category.assoc adj₂.unit (E₂ ◁ L.dotD₂), L.unit_dotD₂,
      Category.assoc, ← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc,
      comp_powComp, powComp_succ]

variable {d : C} {E₃ : c ⟶ d} {R₃ : d ⟶ c} {adj₃ : E₃ ⊣ R₃} {x₃ : E₃ ⟶ E₃}
  {τ₂₃ : E₂ ≫ E₃ ⟶ E₂ ≫ E₃} {h' : ℤ}
  (U : RouqLoc adj₂ adj₃ x₂ x₃ τ₂₃ h')
  (hw : h' = h + 2) (hsq : τ ≫ τ = 0) (hsq' : τ₂₃ ≫ τ₂₃ = 0)
  (hB : E₁ ◁ τ₂₃ ≫ ((α_ E₁ E₂ E₃).inv ≫ τ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom) ≫ E₁ ◁ τ₂₃ =
    ((α_ E₁ E₂ E₃).inv ≫ τ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom) ≫ E₁ ◁ τ₂₃ ≫
      ((α_ E₁ E₂ E₃).inv ≫ τ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom))

/-- Dot cyclicity: the left mate of the right mate is the original dot, at every weight. -/
theorem cyclic_dot : conjugateEquiv (L.leftAdjunction U hw hsq hsq' hB)
    (L.leftAdjunction U hw hsq hsq' hB) L.dotD₂ = x₂ := by
  let A := L.leftAdjunction U hw hsq hsq' hB
  change conjugateEquiv A A L.dotD₂ = x₂
  by_cases hp : 0 < h'
  · apply eq_of_unit_whiskerLeft A
    rw [unit_whiskerLeft_conjugateEquiv]
    exact (U.cupL_dot_of_pos hp).symm
  · apply eq_of_whiskerRight_counit A
    rw [conjugateEquiv_whiskerRight_counit]
    exact (L.capL_dot_of_neg (by omega)).symm

include U hw hsq hsq' hB in
/-- A dot slides around the prescribed leftward cup at every weight. -/
theorem cupL_dot : U.cupL ≫ R₂ ◁ x₂ = U.cupL ≫ L.dotD₂ ▷ E₂ := by
  have ht := unit_whiskerLeft_conjugateEquiv (L.leftAdjunction U hw hsq hsq' hB) L.dotD₂
  rw [L.cyclic_dot U hw hsq hsq' hB] at ht
  exact ht

include U hw hsq hsq' hB in
/-- A dot slides around the prescribed leftward cap at every weight. -/
theorem capL_dot : x₂ ▷ R₂ ≫ L.capL = E₂ ◁ L.dotD₂ ≫ L.capL := by
  have ht := conjugateEquiv_whiskerRight_counit (L.leftAdjunction U hw hsq hsq' hB) L.dotD₂
  rw [L.cyclic_dot U hw hsq hsq' hB] at ht
  exact ht
end RouqLoc
end Categorification.TwoRep
