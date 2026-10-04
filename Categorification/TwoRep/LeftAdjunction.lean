/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.AdjointWeightNegOne

/-!
# The left adjunction of `E 1_n` in the graded-Hom bicategory

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, §3.4 (Proposition 3.9, Corollary 3.10) and §4.1 ("Fixing adjunction maps").

Under (3.2) at the weight `n` (`StrongSl2.AdjHyp`), `1_n F ⟨-n-1⟩` is left adjoint to `E 1_n`.
In the graded-Hom bicategory `GradedHomBicat B`, where `1_n F ⟨-n-1⟩ ≅ R_n` by a homogeneous
isomorphism, this is an adjunction `R_n ⊣ E 1_n` (`StrongSl2.leftAdj`). Its unit and counit are
homogeneous of degrees `-2n-2` and `2n+2` (`isHomogeneous_leftAdj_unit`,
`isHomogeneous_leftAdj_counit`). They are determined up to a scalar: every homogeneous 2-morphism
`𝟙 ⟶ R_n E_n` of degree `-2n-2` is a multiple of the unit, and every homogeneous 2-morphism
`E_n R_n ⟶ 𝟙` of degree `2n+2` is a multiple of the counit (CL Corollary 3.10;
`exists_eq_smul_leftAdj_unit`, `exists_eq_smul_leftAdj_counit`). These are the cups and caps
that CL §4.1 rescales.

* `adjunctionOfIsoLeft`: transport of an adjunction `f ⊣ g` along an isomorphism `f ≅ f'` (any
  bicategory).
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Module
open KrullSchmidtCat (HomFinite)

universe w v u

section Transport

variable {C : Type u} [Bicategory.{w, v} C] {a b : C}

/-- **An adjunction transported along an isomorphism of the left adjoint**: from `f ⊣ g` and
`θ : f ≅ f'`, the adjunction `f' ⊣ g` with unit `η ≫ θ g` and counit `(g θ⁻¹) ≫ ε`. -/
def adjunctionOfIsoLeft {f f' : a ⟶ b} {g : b ⟶ a} (adj : f ⊣ g) (θ : f ≅ f') : f' ⊣ g where
  unit := adj.unit ≫ θ.hom ▷ g
  counit := g ◁ θ.inv ≫ adj.counit
  left_triangle := by
    calc leftZigzag (adj.unit ≫ θ.hom ▷ g) (g ◁ θ.inv ≫ adj.counit)
        = 𝟙 _ ⊗≫ adj.unit ▷ f' ⊗≫ (θ.hom ▷ (g ≫ f') ≫ f' ◁ g ◁ θ.inv) ⊗≫
            f' ◁ adj.counit ⊗≫ 𝟙 _ := by
          rw [leftZigzag]; bicategory
      _ = 𝟙 _ ⊗≫ adj.unit ▷ f' ⊗≫ (f ◁ g ◁ θ.inv ≫ θ.hom ▷ (g ≫ f)) ⊗≫
            f' ◁ adj.counit ⊗≫ 𝟙 _ := by
          rw [← whisker_exchange]
      _ = 𝟙 _ ⊗≫ (adj.unit ▷ f' ≫ (f ≫ g) ◁ θ.inv) ⊗≫
            (θ.hom ▷ (g ≫ f) ≫ f' ◁ adj.counit) ⊗≫ 𝟙 _ := by
          bicategory
      _ = 𝟙 _ ⊗≫ (𝟙 a ◁ θ.inv ≫ adj.unit ▷ f) ⊗≫ (f ◁ adj.counit ≫ θ.hom ▷ 𝟙 b) ⊗≫ 𝟙 _ := by
          rw [← whisker_exchange, ← whisker_exchange]
      _ = 𝟙 _ ⊗≫ 𝟙 a ◁ θ.inv ⊗≫ leftZigzag adj.unit adj.counit ⊗≫ θ.hom ▷ 𝟙 b ⊗≫ 𝟙 _ := by
          rw [leftZigzag]; bicategory
      _ = (λ_ f').hom ≫ θ.inv ≫ θ.hom ≫ (ρ_ f').inv := by
          rw [adj.left_triangle]; bicategory
      _ = (λ_ f').hom ≫ (ρ_ f').inv := by
          rw [Iso.inv_hom_id_assoc]
  right_triangle := by
    calc rightZigzag (adj.unit ≫ θ.hom ▷ g) (g ◁ θ.inv ≫ adj.counit)
        = g ◁ adj.unit ⊗≫ g ◁ (θ.hom ≫ θ.inv) ▷ g ⊗≫ adj.counit ▷ g := by
          rw [rightZigzag]; bicategory
      _ = rightZigzag adj.unit adj.counit := by
          rw [Iso.hom_inv_id, Bicategory.id_whiskerRight, Bicategory.whiskerLeft_id, rightZigzag]
          bicategory
      _ = (ρ_ g).hom ≫ (λ_ g).inv := adj.right_triangle

end Transport

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [GradedBicategory.ShiftCoherence B]

namespace StrongSl2

open GradedHomBicat GradedHomCat RightwardCrossing

variable (S : StrongSl2 k B)

/-- The homogeneous isomorphism `1_n F ⟨-n-1⟩ ≅ R_n = 1_n F ⟨n+1⟩` of the graded-Hom bicategory
(of degree `-2n-2`). -/
def leftAdjIso (r : ℤ) : of₁ ((S.F r)⟦-(S.wt r + 1)⟧) ≅ S.grR r :=
  shiftIso₁ (S.F r) (-(S.wt r + 1)) ≪≫ (shiftIso₁ (S.F r) (S.n₀ + 2 * r + 1)).symm

/-- **The left adjunction `R_n ⊣ E 1_n`** in the graded-Hom bicategory, from (3.2) at `n`. -/
def leftAdj {r : ℤ} (h : S.AdjHyp r) : S.grR r ⊣ S.grE r :=
  adjunctionOfIsoLeft (GradedHomBicat.mapAdjunction h.some) (S.leftAdjIso r)

theorem leftAdj_unit {r : ℤ} (h : S.AdjHyp r) :
    (S.leftAdj h).unit = incl₂ h.some.unit ≫ (S.leftAdjIso r).hom ▷ S.grE r := rfl

theorem leftAdj_counit {r : ℤ} (h : S.AdjHyp r) :
    (S.leftAdj h).counit = S.grE r ◁ (S.leftAdjIso r).inv ≫ incl₂ h.some.counit := rfl

theorem isHomogeneous_leftAdj_unit {r : ℤ} (h : S.AdjHyp r) :
    IsHomogeneous (S.leftAdj h).unit (-(2 * S.wt r + 2)) :=
  ((isHomogeneous_incl₂ _).comp (isHomogeneous_whiskerRight
    ((shiftIso₁_hom_isHomogeneous _ _).comp (shiftIso₁_inv_isHomogeneous _ _) rfl) _)
      rfl).of_eq (by simp only [wt]; ring)

theorem isHomogeneous_leftAdj_counit {r : ℤ} (h : S.AdjHyp r) :
    IsHomogeneous (S.leftAdj h).counit (2 * S.wt r + 2) :=
  ((isHomogeneous_whiskerLeft _ ((shiftIso₁_hom_isHomogeneous _ _).comp
    (shiftIso₁_inv_isHomogeneous _ _) rfl)).comp (isHomogeneous_incl₂ _) rfl).of_eq
      (by simp only [wt]; ring)

variable [GradedBicategory.IsLinear B k]

omit [GradedBicategory.IsLinear B k] in
theorem leftAdj_unit_ne_zero {r : ℤ} (h : S.AdjHyp r) (hE : ¬ IsZero (S.E r)) :
    (S.leftAdj h).unit ≠ 0 := by
  intro h0
  have hz := (S.leftAdj h).right_triangle
  rw [h0, rightZigzag, GradedHomBicat.whiskerLeft_zero] at hz
  simp only [bicategoricalComp, zero_comp] at hz
  apply id_ne_zero_of_not_isZero hE
  have e : 𝟙 (S.grE r) = (ρ_ (S.grE r)).inv ≫ ((ρ_ (S.grE r)).hom ≫ (λ_ (S.grE r)).inv) ≫
      (λ_ (S.grE r)).hom := by simp
  rw [← hz, zero_comp, comp_zero] at e
  exact e

omit [GradedBicategory.IsLinear B k] in
theorem leftAdj_counit_ne_zero {r : ℤ} (h : S.AdjHyp r) (hE : ¬ IsZero (S.E r)) :
    (S.leftAdj h).counit ≠ 0 := by
  intro h0
  have hz := (S.leftAdj h).right_triangle
  rw [h0, rightZigzag, GradedHomBicat.zero_whiskerRight] at hz
  simp only [bicategoricalComp, comp_zero] at hz
  apply id_ne_zero_of_not_isZero hE
  have e : 𝟙 (S.grE r) = (ρ_ (S.grE r)).inv ≫ ((ρ_ (S.grE r)).hom ≫ (λ_ (S.grE r)).inv) ≫
      (λ_ (S.grE r)).hom := by simp
  rw [← hz, zero_comp, comp_zero] at e
  exact e

/-- **Uniqueness of the left cup** (CL Corollary 3.10): a homogeneous `𝟙 ⟶ R_n E_n` of degree
`-2n-2` is a multiple of the unit of the left adjunction, provided `End(E 1_n) = k`. -/
theorem exists_eq_smul_leftAdj_unit {r : ℤ} (h : S.AdjHyp r)
    (hend : finrank k (S.E r ⟶ S.E r) = 1) {u : 𝟙 (of (S.obj (r + 1))) ⟶ S.grR r ≫ S.grE r}
    (hu : IsHomogeneous u (-(2 * S.wt r + 2))) : ∃ c : k, u = c • (S.leftAdj h).unit := by
  have hE : ¬ IsZero (S.E r) := fun hz => by
    rw [finrank_hom_of_isZero_left k hz] at hend; exact zero_ne_one hend
  refine GradedHomBicat.exists_smul_of_isHomogeneous hu (S.isHomogeneous_leftAdj_unit h)
    (S.leftAdj_unit_ne_zero h hE) ?_
  rw [finrank_hom_congr_right k _ ((shiftFunctor _ _).mapIso (whiskerRightShiftIso _ _ _) ≪≫
      ((shiftFunctorAdd' _ (S.n₀ + 2 * r + 1) (-(2 * S.wt r + 2)) (-(S.wt r + 1))
        (by simp only [wt]; ring)).app _).symm),
    finrank_hom_shift_right k _ _ (b := S.wt r + 1) (by ring)]
  exact (S.finrank_EF_unit h).trans hend

/-- **Uniqueness of the left cap** (CL Corollary 3.10): a homogeneous `E_n R_n ⟶ 𝟙` of degree
`2n+2` is a multiple of the counit of the left adjunction, provided `End(E 1_n) = k`. -/
theorem exists_eq_smul_leftAdj_counit {r : ℤ} (h : S.AdjHyp r)
    (hend : finrank k (S.E r ⟶ S.E r) = 1) {c : S.grE r ≫ S.grR r ⟶ 𝟙 (of (S.obj r))}
    (hc : IsHomogeneous c (2 * S.wt r + 2)) : ∃ t : k, c = t • (S.leftAdj h).counit := by
  have hE : ¬ IsZero (S.E r) := fun hz => by
    rw [finrank_hom_of_isZero_left k hz] at hend; exact zero_ne_one hend
  refine GradedHomBicat.exists_smul_of_isHomogeneous hc (S.isHomogeneous_leftAdj_counit h)
    (S.leftAdj_counit_ne_zero h hE) ?_
  rw [finrank_hom_congr_left k (whiskerLeftShiftIso _ _ _),
    finrank_hom_shift_shift k _ _ (c := S.wt r + 1) (by simp only [wt]; ring)]
  exact (S.finrank_FE_counit h).trans hend

end StrongSl2

end Categorification.TwoRep
