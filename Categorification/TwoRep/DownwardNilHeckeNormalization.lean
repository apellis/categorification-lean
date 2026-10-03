import Categorification.TwoRep.DownwardNilHeckeAction

/-!
# Normalizing the actual two-strand downward crossing

Right-counted dots and the reverse-composition multiplication in `End` require
`D = -rQ⁻¹ C`. The two mixed relations below certify this sign using the actual
unshifted `FF` operators. The scalar is already a unit in `StrongSl2`; no new
nonvanishing assumption is needed. This is not yet an all-width action.
-/

noncomputable section
namespace Categorification.TwoRep
open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits
open GradedHomBicat
universe w v u
variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [GradedBicategory.ShiftCoherence B]
namespace StrongSl2
variable {k : Type*} [Field k] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [GradedBicategory.IsLinear B k] (S : StrongSl2 k B)

/-- The degree-minus-two crossing with the native right-counted nilHecke normalization. -/
def ffNormalizedCross (r : ℤ) :
    ShiftedHom (S.F (r + 1) ≫ S.F r) (S.F (r + 1) ≫ S.F r) (-2 : ℤ) :=
  -((S.rQ : k)⁻¹) • S.ffCross r

/-- Scalar normalization preserves the actual homogeneous square-zero relation. -/
theorem ffNormalizedCross_sq (r : ℤ) :
    (S.ffNormalizedCross r).comp (S.ffNormalizedCross r)
      (by norm_num : (-2 : ℤ) + -2 = -4) = 0 := by
  rw [ffNormalizedCross, ShiftedHom.smul_comp', ShiftedHom.comp_smul', S.ffCross_sq]
  simp

/-- First mixed relation in the order induced by right-counted dots and End multiplication. -/
theorem ffNormalizedCross_x_d (r : ℤ) :
    (S.ffNormalizedCross r).comp (S.ffDotSecond r) (by norm_num : (2 : ℤ) + -2 = 0) -
      (S.ffDotFirst r).comp (S.ffNormalizedCross r) (by norm_num : (-2 : ℤ) + 2 = 0) =
        ShiftedHom.mk₀ (0 : ℤ) rfl (𝟙 (S.F (r + 1) ≫ S.F r)) := by
  rw [ffNormalizedCross, ShiftedHom.smul_comp', ShiftedHom.comp_smul', ← smul_sub,
    ← neg_sub, ← S.ff_dot_slide_right, ShiftedHom.mk₀_smul]
  simp [smul_smul, Units.ne_zero S.rQ]

/-- The other mixed relation has the same certified negative normalization. -/
theorem ffNormalizedCross_d_x (r : ℤ) :
    (S.ffDotSecond r).comp (S.ffNormalizedCross r) (by norm_num : (-2 : ℤ) + 2 = 0) -
      (S.ffNormalizedCross r).comp (S.ffDotFirst r) (by norm_num : (2 : ℤ) + -2 = 0) =
        ShiftedHom.mk₀ (0 : ℤ) rfl (𝟙 (S.F (r + 1) ≫ S.F r)) := by
  rw [ffNormalizedCross, ShiftedHom.comp_smul', ShiftedHom.smul_comp', ← smul_sub,
    ← neg_sub, ← S.ff_dot_slide_left, ShiftedHom.mk₀_smul]
  simp [smul_smul, Units.ne_zero S.rQ]

/-- The literal native `x_d_sub` equation on actual `FF`, with the right dot indexed first. -/
theorem ffNormalizedCross_end_x_d (r : ℤ) :
    let X₀ : End (of₁ (S.F (r + 1) ≫ S.F r)) := of₂ 2 (S.ffDotSecond r)
    let X₁ : End (of₁ (S.F (r + 1) ≫ S.F r)) := of₂ 2 (S.ffDotFirst r)
    let D : End (of₁ (S.F (r + 1) ≫ S.F r)) := of₂ (-2) (S.ffNormalizedCross r)
    X₀ * D - D * X₁ = 1 := by
  change of₂ (-2) (S.ffNormalizedCross r) ≫ of₂ 2 (S.ffDotSecond r) -
    of₂ 2 (S.ffDotFirst r) ≫ of₂ (-2) (S.ffNormalizedCross r) = 𝟙 _
  rw [of₂_comp_of₂ _ _ (by norm_num : (2 : ℤ) + -2 = 0),
    of₂_comp_of₂ _ _ (by norm_num : (-2 : ℤ) + 2 = 0), ← of₂_sub,
    S.ffNormalizedCross_x_d, ← incl₂_eq_of₂, incl₂_id]

/-- The literal native `d_x_sub` equation with the same actual generators. -/
theorem ffNormalizedCross_end_d_x (r : ℤ) :
    let X₀ : End (of₁ (S.F (r + 1) ≫ S.F r)) := of₂ 2 (S.ffDotSecond r)
    let X₁ : End (of₁ (S.F (r + 1) ≫ S.F r)) := of₂ 2 (S.ffDotFirst r)
    let D : End (of₁ (S.F (r + 1) ≫ S.F r)) := of₂ (-2) (S.ffNormalizedCross r)
    D * X₀ - X₁ * D = 1 := by
  change of₂ 2 (S.ffDotSecond r) ≫ of₂ (-2) (S.ffNormalizedCross r) -
    of₂ (-2) (S.ffNormalizedCross r) ≫ of₂ 2 (S.ffDotFirst r) = 𝟙 _
  rw [of₂_comp_of₂ _ _ (by norm_num : (-2 : ℤ) + 2 = 0),
    of₂_comp_of₂ _ _ (by norm_num : (2 : ℤ) + -2 = 0), ← of₂_sub,
    S.ffNormalizedCross_d_x, ← incl₂_eq_of₂, incl₂_id]

end StrongSl2
end Categorification.TwoRep
