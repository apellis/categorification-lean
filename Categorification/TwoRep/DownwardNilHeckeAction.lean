import Categorification.TwoRep.DownwardNilHeckeFarComm

/-!
# Square-zero on actual downward words

This is a local-relation propagation step toward the native nilHecke action, not a
completed action. Every crossing on every actual nonempty left-associated `F` word
squares to zero. In particular, the bottom-pair proof uses the actual associator
conjugation, not an assumed all-width relation. No scalar normalization is needed
for this relation. Mixed slides, braid propagation, and the algebra lift remain open.
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
  (S : StrongSl2 k B)

/-- Every actual local crossing squares to zero, including out-of-range positions. -/
theorem fWordCross_sq (n j : ℕ) (r : ℤ) :
    (S.fWordCross n r j).comp (S.fWordCross n r j)
      (by norm_num : (-2 : ℤ) + -2 = -4) = 0 := by
  induction n generalizing r j with
  | zero =>
    change (0 : ShiftedHom (S.fWord 0 r) (S.fWord 0 r) (-2 : ℤ)).comp _ _ = 0
    simp only [fWordCross, ShiftedHom.zero_comp]
  | succ n ih =>
    cases j with
    | succ j =>
      simp only [fWordCross, fWord]
      rw [← shWhiskerRight_comp, ih]
      exact ShiftedHom.map_zero _
    | zero =>
      cases n with
      | zero => exact S.ffCross_sq r
      | succ n =>
        apply of₂_injective (-4)
        rw [of₂_zero]
        simp only [fWordCross, fWordBottomCross, fWord, ← of₂_comp_of₂,
          ← incl₂_eq_of₂, ← associator_hom_eq, ← associator_inv_eq,
          ← whiskerLeft_of₂, Category.assoc, Iso.inv_hom_id_assoc]
        rw [← Category.assoc (of₁ (S.fWord n (r + 1 + 1)) ◁ of₂ (-2) (S.ffCross r)),
          ← whiskerLeft_comp, of₂_comp_of₂ _ _ (by norm_num : (-2 : ℤ) + -2 = -4),
          S.ffCross_sq, of₂_zero]
        change _ ≫ whiskerLeftHom _ _ _ 0 ≫ _ = 0
        simp

/-- The new relation in exactly the native nilHecke `d_sq` endomorphism-ring shape. -/
theorem fWordCross_end_sq (n j : ℕ) (r : ℤ) :
    let C : End (of₁ (S.fWord n r)) := of₂ (-2) (S.fWordCross n r j)
    C * C = 0 := by
  change of₂ (-2) (S.fWordCross n r j) ≫ of₂ (-2) (S.fWordCross n r j) = 0
  rw [of₂_comp_of₂ _ _ (by norm_num : (-2 : ℤ) + -2 = -4), S.fWordCross_sq, of₂_zero]

end StrongSl2
end Categorification.TwoRep
