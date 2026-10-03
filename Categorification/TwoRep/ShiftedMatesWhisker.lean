/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.ShiftedMates

/-!
# Composite adjunctions and shifted whiskering

The degree-zero inclusion into the actual finite-sum graded-Hom bicategory preserves
Mathlib's composite adjunction, including its unit and counit. The ordinary conjugate-mate
whiskering theorems therefore imply both shifted whiskering equations in every integer
degree. Left and right tensor factors are exchanged; the degree is unchanged.

The `StrongSl2` consumer identifies the degree-two tensor-factor dots and degree-minus-two
tensor-factor crossings on the supplied right adjoints, and transports square-zero and
both two-strand dot-slide relations. These right adjoints are the weight-shifted `F`s in
`S.adj`, not unshifted `F`s. The triple crossing formulas retain their distinct, exact
parenthesizations. No downward braid relation, removal of the shifts, cyclicity, automatic
biadjointness, or low-weight foothold is claimed here.
-/

noncomputable section
namespace Categorification.TwoRep
open CategoryTheory CategoryTheory.Bicategory
universe w v u

private theorem comp_unit_explicit {D : Type*} [Bicategory D] {a b c : D}
    {f₁ : a ⟶ b} {g₁ : b ⟶ a} {f₂ : b ⟶ c} {g₂ : c ⟶ b}
    (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) :
    (adj₁.comp adj₂).unit = adj₁.unit ≫ f₁ ◁ (λ_ g₁).inv ≫
      f₁ ◁ (adj₂.unit ▷ g₁) ≫ f₁ ◁ (α_ f₂ g₂ g₁).hom ≫
      (α_ f₁ f₂ (g₂ ≫ g₁)).inv := by
  dsimp only [Bicategory.Adjunction.comp, Bicategory.Adjunction.compUnit]
  bicategory

private theorem comp_counit_explicit {D : Type*} [Bicategory D] {a b c : D}
    {f₁ : a ⟶ b} {g₁ : b ⟶ a} {f₂ : b ⟶ c} {g₂ : c ⟶ b}
    (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) :
    (adj₁.comp adj₂).counit = (α_ (g₂ ≫ g₁) f₁ f₂).inv ≫
      (α_ g₂ g₁ f₁).hom ▷ f₂ ≫ (g₂ ◁ adj₁.counit) ▷ f₂ ≫
      (ρ_ g₂).hom ▷ f₂ ≫ adj₂.counit := by
  dsimp only [Bicategory.Adjunction.comp, Bicategory.Adjunction.compCounit]
  bicategory

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [GradedBicategory.ShiftCoherence B]
open GradedHomBicat
variable {a b c : B} {f₁ : a ⟶ b} {g₁ : b ⟶ a} {f₂ : b ⟶ c} {g₂ : c ⟶ b}
    (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂)

/-- The actual graded-Hom inclusion preserves the supplied composite adjunction. -/
theorem GradedHomBicat.mapAdjunction_comp :
    mapAdjunction (adj₁.comp adj₂) = (mapAdjunction adj₁).comp (mapAdjunction adj₂) := by
  apply Bicategory.Adjunction.ext
  · change incl₂ (adj₁.comp adj₂).unit = _
    rw [comp_unit_explicit, comp_unit_explicit]
    simp only [incl₂_comp, ← whiskerLeft_incl₂, ← incl₂_whiskerRight,
      ← leftUnitor_inv_eq, ← associator_hom_eq, ← associator_inv_eq, mapAdjunction, of₁_comp]
  · change incl₂ (adj₁.comp adj₂).counit = _
    rw [comp_counit_explicit, comp_counit_explicit]
    simp only [incl₂_comp, ← whiskerLeft_incl₂, ← incl₂_whiskerRight,
      ← rightUnitor_hom_eq, ← associator_hom_eq, ← associator_inv_eq, mapAdjunction, of₁_comp]

/-- A mate under the composite adjunction turns left whiskering into right whiskering,
without changing the integer degree. -/
theorem mateSh_comp_shWhiskerLeft {d : ℤ} (φ : ShiftedHom f₂ f₂ d) :
    mateSh (adj₁.comp adj₂) (shWhiskerLeft f₁ φ) =
      shWhiskerRight (mateSh adj₂ φ) g₁ := by
  apply of₂_injective d
  rw [of₂_mateSh, mapAdjunction_comp, ← whiskerLeft_of₂,
    Bicategory.conjugateEquiv_whiskerLeft, ← of₂_mateSh, of₂_whiskerRight]

/-- A mate under the composite adjunction turns right whiskering into left whiskering,
without changing the integer degree. -/
theorem mateSh_comp_shWhiskerRight {d : ℤ} (φ : ShiftedHom f₁ f₁ d) :
    mateSh (adj₁.comp adj₂) (shWhiskerRight φ f₂) =
      shWhiskerLeft g₂ (mateSh adj₁ φ) := by
  apply of₂_injective d
  rw [of₂_mateSh, mapAdjunction_comp, ← of₂_whiskerRight,
    Bicategory.conjugateEquiv_whiskerRight, ← of₂_mateSh, whiskerLeft_of₂]

namespace StrongSl2

open CategoryTheory.Limits
variable {k : Type*} [Field k] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  (S : StrongSl2 k B)

/-- The supplied right adjoint, retaining CL's weight-dependent shift on `F`. -/
abbrev adjointF (r : ℤ) : S.obj (r + 1) ⟶ S.obj r :=
  (S.F r)⟦S.n₀ + 2 * r + 1⟧

/-- The degree-two dot on the supplied right adjoint of `E r`. -/
def mateDot (r : ℤ) : ShiftedHom (S.adjointF r) (S.adjointF r) (2 : ℤ) :=
  mateSh (S.adj r) (S.dot r)

/-- The degree-minus-two crossing on the reversed composite of supplied right adjoints. -/
def mateCross (r : ℤ) :
    ShiftedHom (S.adjointF (r + 1) ≫ S.adjointF r)
      (S.adjointF (r + 1) ≫ S.adjointF r) (-2 : ℤ) :=
  mateSh ((S.adj r).comp (S.adj (r + 1))) (S.cross r)

/-- The dot on the second upward factor becomes the dot on the first downward factor. -/
theorem mateDot_tensor_first (r : ℤ) :
    mateSh ((S.adj r).comp (S.adj (r + 1)))
        (shWhiskerLeft (S.E r) (S.dot (r + 1))) =
      shWhiskerRight (S.mateDot (r + 1)) (S.adjointF r) :=
  mateSh_comp_shWhiskerLeft (S.adj r) (S.adj (r + 1)) (S.dot (r + 1))

/-- The dot on the first upward factor becomes the dot on the second downward factor. -/
theorem mateDot_tensor_second (r : ℤ) :
    mateSh ((S.adj r).comp (S.adj (r + 1)))
        (shWhiskerRight (S.dot r) (S.E (r + 1))) =
      shWhiskerLeft (S.adjointF (r + 1)) (S.mateDot r) :=
  mateSh_comp_shWhiskerRight (S.adj r) (S.adj (r + 1)) (S.dot r)

/-- A negative-degree crossing on the second upward pair becomes one on the first
 downward pair. The right adjoint is parenthesized `(F₂ F₁) F₀`, with shifts retained. -/
theorem mateCross_tensor_first (r : ℤ) :
    mateSh ((S.adj r).comp ((S.adj (r + 1)).comp (S.adj (r + 1 + 1))))
        (shWhiskerLeft (S.E r) (S.cross (r + 1))) =
      shWhiskerRight (S.mateCross (r + 1)) (S.adjointF r) :=
  mateSh_comp_shWhiskerLeft (S.adj r) ((S.adj (r + 1)).comp (S.adj (r + 1 + 1)))
    (S.cross (r + 1))

/-- The opposite negative-degree factor identity, with right adjoint `F₂ (F₁ F₀)`.
No equality between the two triple parenthesizations is being silently imposed. -/
theorem mateCross_tensor_second (r : ℤ) :
    mateSh (((S.adj r).comp (S.adj (r + 1))).comp (S.adj (r + 1 + 1)))
        (shWhiskerRight (S.cross r) (S.E (r + 1 + 1))) =
      shWhiskerLeft (S.adjointF (r + 1 + 1)) (S.mateCross r) :=
  mateSh_comp_shWhiskerRight ((S.adj r).comp (S.adj (r + 1))) (S.adj (r + 1 + 1))
    (S.cross r)

/-- Square-zero descends in degree `-4`, not just at the level of an ungraded end ring. -/
theorem mateCross_sq (r : ℤ) :
    (S.mateCross r).comp (S.mateCross r) (by norm_num : (-2 : ℤ) + -2 = -4) = 0 := by
  have h := congrArg (mateSh ((S.adj r).comp (S.adj (r + 1)))) (S.cross_sq r)
  simpa only [mateSh_comp, mateSh_zero, mateCross] using h

/-- A nonzero upward crossing gives a nonzero negative-degree downward crossing. -/
theorem mateCross_eq_zero_iff (r : ℤ) : S.mateCross r = 0 ↔ S.cross r = 0 :=
  mateSh_eq_zero_iff ((S.adj r).comp (S.adj (r + 1))) (S.cross r)

section Linear
variable [GradedBicategory.IsLinear B k]

/-- Transport of the first dot-slide relation: vertical order and tensor factors both
reverse. This uses explicit linearity, not cyclicity or a new adjunction. -/
theorem mate_dot_slide_left (r : ℤ) :
    ShiftedHom.mk₀ (0 : ℤ) rfl
        ((S.rQ : k) • 𝟙 (S.adjointF (r + 1) ≫ S.adjointF r)) =
      (S.mateCross r).comp (shWhiskerRight (S.mateDot (r + 1)) (S.adjointF r))
          (by norm_num : (2 : ℤ) + -2 = 0) -
        (shWhiskerLeft (S.adjointF (r + 1)) (S.mateDot r)).comp (S.mateCross r)
          (by norm_num : (-2 : ℤ) + 2 = 0) := by
  have h := congrArg (mateSh ((S.adj r).comp (S.adj (r + 1)))) (S.dot_slide_left r)
  simpa only [ShiftedHom.mk₀_smul, mateSh_smul, mateSh_mk₀_id, mateSh_sub, mateSh_comp,
    mateDot_tensor_first, mateDot_tensor_second, mateCross] using h

/-- The second two-strand dot-slide relation with the transported orientation. -/
theorem mate_dot_slide_right (r : ℤ) :
    ShiftedHom.mk₀ (0 : ℤ) rfl
        ((S.rQ : k) • 𝟙 (S.adjointF (r + 1) ≫ S.adjointF r)) =
      (shWhiskerRight (S.mateDot (r + 1)) (S.adjointF r)).comp (S.mateCross r)
          (by norm_num : (-2 : ℤ) + 2 = 0) -
        (S.mateCross r).comp (shWhiskerLeft (S.adjointF (r + 1)) (S.mateDot r))
          (by norm_num : (2 : ℤ) + -2 = 0) := by
  have h := congrArg (mateSh ((S.adj r).comp (S.adj (r + 1)))) (S.dot_slide_right r)
  simpa only [ShiftedHom.mk₀_smul, mateSh_smul, mateSh_mk₀_id, mateSh_sub, mateSh_comp,
    mateDot_tensor_first, mateDot_tensor_second, mateCross] using h

end Linear
end StrongSl2
end Categorification.TwoRep
