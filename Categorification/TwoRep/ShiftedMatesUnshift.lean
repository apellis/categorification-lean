/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.ShiftedMatesWhisker

/-! # Removing the weight shifts from downward mates

The shifts of objects are removed by homogeneous isomorphisms, never by identifying
shifted and unshifted objects definitionally. The resulting `fDot` and `ffCross`
live on the actual `F` and `FF`; square-zero and both scalar dot-slides hold on
`FF` with the transported dots `ffDotFirst` and `ffDotSecond`. Shift removal is
injective and preserves degrees, composition, subtraction and scalars.

`removeIso_tensor` identifies the conjugating isomorphism with the tensor product
of the one-factor homogeneous shift isomorphisms. The consequences identifying
`ffDotFirst` and `ffDotSecond` with whiskerings of `fDot` are not proved here.
No triple braid or all-strand unshifted nilHecke action is asserted.
-/

noncomputable section
namespace Categorification.TwoRep
open CategoryTheory CategoryTheory.Bicategory
universe w v u

namespace ShiftRemoval
variable {C : Type*} [Category C] [HasShift C ℤ]

/-- The canonical homogeneous map from an object to its shift, of degree `-n`. -/
def up (X : C) (n : ℤ) : ShiftedHom X (X⟦n⟧) (-n) :=
  (shiftFunctorCompIsoId C n (-n) (add_neg_cancel n)).inv.app X

/-- The inverse homogeneous map has degree `n`. -/
def down (X : C) (n : ℤ) : ShiftedHom (X⟦n⟧) X n := 𝟙 _

@[simp] theorem up_down (X : C) (n : ℤ) :
    (up X n).comp (down X n) (by omega : n + -n = 0) =
      ShiftedHom.mk₀ (0 : ℤ) rfl (𝟙 X) := by
  simp [up, down, ShiftedHom.comp, ShiftedHom.mk₀, shiftFunctorCompIsoId,
    shiftFunctorZero']

@[simp] theorem down_up (X : C) (n : ℤ) :
    (down X n).comp (up X n) (by omega : -n + n = 0) =
      ShiftedHom.mk₀ (0 : ℤ) rfl (𝟙 (X⟦n⟧)) := by
  apply (cancel_mono ((shiftFunctorZero C ℤ).hom.app (X⟦n⟧))).mp
  have h := (shiftEquiv C n).functor_unitIso_comp X
  change (shiftFunctor C n).map ((shiftFunctorCompIsoId C n (-n) _).inv.app X) ≫
    (shiftFunctorCompIsoId C (-n) n _).hom.app (X⟦n⟧) = 𝟙 _ at h
  simpa [up, down, ShiftedHom.comp, ShiftedHom.mk₀, shiftFunctorCompIsoId,
    shiftFunctorZero', Category.assoc] using h

variable [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]

open GradedHomCat

/-- A shift is an isomorphism in the graded-Hom category, not in the original category. -/
def shiftIso (X : C) (n : ℤ) : mk X ≅ mk (X⟦n⟧) where
  hom := homOf (-n) (up X n)
  inv := homOf n (down X n)
  hom_inv_id := by
    rw [homOf_comp_homOf _ _ (by omega : n + -n = 0), up_down, ← GradedHomCat.id_eq]
  inv_hom_id := by
    rw [homOf_comp_homOf _ _ (by omega : -n + n = 0), down_up, ← GradedHomCat.id_eq]

/-- Remove an object shift, preserving the degree of its endomorphism. -/
def unshift {X : C} (n : ℤ) {d : ℤ} (f : ShiftedHom (X⟦n⟧) (X⟦n⟧) d) :
    ShiftedHom X X d :=
  ((up X n).comp f (rfl : d + -n = d + -n)).comp (down X n) (by omega)

theorem homOf_unshift {X : C} (n : ℤ) {d : ℤ}
    (f : ShiftedHom (X⟦n⟧) (X⟦n⟧) d) :
    homOf d (unshift n f) = (shiftIso X n).hom ≫ homOf d f ≫ (shiftIso X n).inv := by
  simp only [unshift, shiftIso, ← homOf_comp_homOf, Category.assoc]

/-- Transport along an actual object isomorphism, followed by shift removal. -/
def remove {X Y : C} {n : ℤ} (e : X ≅ Y⟦n⟧) {d : ℤ}
    (f : ShiftedHom X X d) : ShiftedHom Y Y d :=
  unshift n (e.inv ≫ f ≫ e.hom⟦d⟧')

/-- The conjugating isomorphism used by `remove`. -/
def removeIso {X Y : C} {n : ℤ} (e : X ≅ Y⟦n⟧) : mk Y ≅ mk X :=
  shiftIso Y n ≪≫ (incl C).mapIso e.symm

theorem homOf_remove {X Y : C} {n : ℤ} (e : X ≅ Y⟦n⟧) {d : ℤ}
    (f : ShiftedHom X X d) :
    homOf d (remove e f) = (removeIso e).hom ≫ homOf d f ≫ (removeIso e).inv := by
  rw [remove, homOf_unshift]
  have h : e.inv ≫ f ≫ e.hom⟦d⟧' =
      (ShiftedHom.mk₀ (0 : ℤ) rfl e.inv).comp
        (f.comp (ShiftedHom.mk₀ (0 : ℤ) rfl e.hom) (zero_add d)) (add_zero d) := by
    simp [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀]
  rw [h, ← homOf_comp_homOf, ← homOf_comp_homOf]
  simp [removeIso, Category.assoc]

theorem remove_comp {X Y : C} {n d t s : ℤ} (e : X ≅ Y⟦n⟧)
    (f : ShiftedHom X X d) (g : ShiftedHom X X t) (h : t + d = s) :
    remove e (f.comp g h) = (remove e f).comp (remove e g) h := by
  apply homOf_injective s
  simp only [homOf_remove, ← homOf_comp_homOf]
  simp [Category.assoc]

@[simp] theorem remove_zero {X Y : C} {n d : ℤ} (e : X ≅ Y⟦n⟧) :
    remove e (0 : ShiftedHom X X d) = 0 := by
  apply homOf_injective d
  simp [homOf_remove]

@[simp] theorem remove_id {X Y : C} {n : ℤ} (e : X ≅ Y⟦n⟧) :
    remove e (ShiftedHom.mk₀ (0 : ℤ) rfl (𝟙 X)) =
      ShiftedHom.mk₀ (0 : ℤ) rfl (𝟙 Y) := by
  apply homOf_injective (0 : ℤ)
  simp [homOf_remove, ← GradedHomCat.id_eq]

theorem remove_injective {X Y : C} {n d : ℤ} (e : X ≅ Y⟦n⟧) :
    Function.Injective (remove e (d := d)) := by
  intro f g h
  have h' := congrArg (homOf d) h
  rw [homOf_remove, homOf_remove] at h'
  apply homOf_injective d
  have h'' := congrArg (fun t => (removeIso e).inv ≫ t ≫ (removeIso e).hom) h'
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id, Category.comp_id] using h''

theorem remove_sub {X Y : C} {n d : ℤ} (e : X ≅ Y⟦n⟧)
    (f g : ShiftedHom X X d) : remove e (f - g) = remove e f - remove e g := by
  apply homOf_injective d
  simp [homOf_remove, homOf_sub, Preadditive.comp_sub, Preadditive.sub_comp]

section Linear
variable {k : Type*} [Field k] [Linear k C]
  [∀ n : ℤ, (shiftFunctor C n).Linear k]

omit [∀ n : ℤ, (shiftFunctor C n).Additive] in
theorem remove_smul {X Y : C} {n d : ℤ} (e : X ≅ Y⟦n⟧)
    (r : k) (f : ShiftedHom X X d) : remove e (r • f) = r • remove e f := by
  simp [remove, unshift, ShiftedHom.comp_smul, ShiftedHom.smul_comp]

end Linear
end ShiftRemoval

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [GradedBicategory.ShiftCoherence B]

namespace ShiftRemoval
open GradedHomBicat
variable {a b c : B}

/-- Shift removal on a composite uses the tensor product of the canonical homogeneous
shift isomorphisms. This is a coherence theorem, not an extra hypothesis. -/
theorem removeIso_tensor_inv (f : a ⟶ b) (g : b ⟶ c) (p q : ℤ) :
    (removeIso (shiftCompShiftIso f g (rfl : q + p = q + p))).inv =
      (shiftIso f p).inv ▷ of₁ (g⟦q⟧) ≫ of₁ f ◁ (shiftIso g q).inv := by
  change (GradedHomCat.incl (a ⟶ c)).map (shiftCompShiftIso f g rfl).hom ≫
      GradedHomCat.homOf (q + p) (down (f ≫ g) (q + p)) = _
  rw [GradedHomCat.incl_map, GradedHomCat.homOf_comp_homOf _ _ (add_zero (q + p)),
    ShiftedHom.mk₀_comp]
  change of₂ (q + p) ((shiftCompShiftIso f g rfl).hom ≫ down (f ≫ g) (q + p)) =
    of₂ p (down f p) ▷ of₁ (g⟦q⟧) ≫ of₁ f ◁ of₂ q (down g q)
  rw [of₂_whiskerRight, whiskerLeft_of₂, of₂_comp_of₂ _ _ rfl]
  congr 1
  simp [down, ShiftedHom.comp, shWhiskerRight_eq, shWhiskerLeft_eq,
    shiftCompShiftIso]

theorem removeIso_tensor (f : a ⟶ b) (g : b ⟶ c) (p q : ℤ) :
    removeIso (shiftCompShiftIso f g (rfl : q + p = q + p)) =
      (whiskerLeftIso (B := GradedHomBicat B) (c := of c) (of₁ f) (shiftIso g q)) ≪≫
        whiskerRightIso (B := GradedHomBicat B) (a := of a) (b := of b) (shiftIso f p) (of₁ (g⟦q⟧)) := by
  apply Iso.ext_inv
  exact removeIso_tensor_inv f g p q


end ShiftRemoval

namespace StrongSl2
open CategoryTheory.Limits
variable {k : Type*} [Field k] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  (S : StrongSl2 k B)

/-- The actual degree-two dot on the unshifted `F r`. -/
def fDot (r : ℤ) : ShiftedHom (S.F r) (S.F r) (2 : ℤ) :=
  ShiftRemoval.remove (Iso.refl (S.adjointF r)) (S.mateDot r)

/-- The supplied composite right adjoint is isomorphic to a shift of actual `FF`. -/
def ffShiftIso (r : ℤ) : S.adjointF (r + 1) ≫ S.adjointF r ≅
    (S.F (r + 1) ≫ S.F r)⟦(S.n₀ + 2 * r + 1) + (S.n₀ + 2 * (r + 1) + 1)⟧ :=
  shiftCompShiftIso (S.F (r + 1)) (S.F r) rfl

/-- The actual degree-minus-two crossing on unshifted `FF`. -/
def ffCross (r : ℤ) :
    ShiftedHom (S.F (r + 1) ≫ S.F r) (S.F (r + 1) ≫ S.F r) (-2 : ℤ) :=
  ShiftRemoval.remove (S.ffShiftIso r) (S.mateCross r)

/-- The transported first dot on actual `FF`. Tensor-factor identification is separate. -/
def ffDotFirst (r : ℤ) :
    ShiftedHom (S.F (r + 1) ≫ S.F r) (S.F (r + 1) ≫ S.F r) (2 : ℤ) :=
  ShiftRemoval.remove (S.ffShiftIso r)
    (shWhiskerRight (S.mateDot (r + 1)) (S.adjointF r))

/-- The transported second dot on actual `FF`. Tensor-factor identification is separate. -/
def ffDotSecond (r : ℤ) :
    ShiftedHom (S.F (r + 1) ≫ S.F r) (S.F (r + 1) ≫ S.F r) (2 : ℤ) :=
  ShiftRemoval.remove (S.ffShiftIso r)
    (shWhiskerLeft (S.adjointF (r + 1)) (S.mateDot r))

/-- Square-zero on actual unshifted `FF`, retaining degree `-4`. -/
theorem ffCross_sq (r : ℤ) :
    (S.ffCross r).comp (S.ffCross r) (by norm_num : (-2 : ℤ) + -2 = -4) = 0 := by
  simp only [ffCross, ← ShiftRemoval.remove_comp, S.mateCross_sq,
    ShiftRemoval.remove_zero]

/-- Shift removal does not lose information about the crossing. -/
theorem ffCross_eq_zero_iff (r : ℤ) : S.ffCross r = 0 ↔ S.cross r = 0 := by
  rw [ffCross, ← ShiftRemoval.remove_zero (S.ffShiftIso r),
    (ShiftRemoval.remove_injective (S.ffShiftIso r)).eq_iff, S.mateCross_eq_zero_iff]

theorem fDot_eq_zero_iff (r : ℤ) : S.fDot r = 0 ↔ S.dot r = 0 := by
  rw [fDot, ← ShiftRemoval.remove_zero (Iso.refl (S.adjointF r)),
    (ShiftRemoval.remove_injective (Iso.refl (S.adjointF r))).eq_iff,
    mateDot, mateSh_eq_zero_iff]

section Linear
variable [GradedBicategory.IsLinear B k]

/-- First dot-slide on actual `FF` with its original CL scalar. -/
theorem ff_dot_slide_left (r : ℤ) :
    ShiftedHom.mk₀ (0 : ℤ) rfl ((S.rQ : k) • 𝟙 (S.F (r + 1) ≫ S.F r)) =
      (S.ffCross r).comp (S.ffDotFirst r) (by norm_num : (2 : ℤ) + -2 = 0) -
        (S.ffDotSecond r).comp (S.ffCross r) (by norm_num : (-2 : ℤ) + 2 = 0) := by
  have h := congrArg (ShiftRemoval.remove (S.ffShiftIso r)) (S.mate_dot_slide_left r)
  simpa only [ShiftedHom.mk₀_smul, ShiftRemoval.remove_smul, ShiftRemoval.remove_id,
    ShiftRemoval.remove_sub, ShiftRemoval.remove_comp, ffCross, ffDotFirst, ffDotSecond] using h

/-- Second dot-slide on actual `FF` with its original CL scalar. -/
theorem ff_dot_slide_right (r : ℤ) :
    ShiftedHom.mk₀ (0 : ℤ) rfl ((S.rQ : k) • 𝟙 (S.F (r + 1) ≫ S.F r)) =
      (S.ffDotFirst r).comp (S.ffCross r) (by norm_num : (-2 : ℤ) + 2 = 0) -
        (S.ffCross r).comp (S.ffDotSecond r) (by norm_num : (2 : ℤ) + -2 = 0) := by
  have h := congrArg (ShiftRemoval.remove (S.ffShiftIso r)) (S.mate_dot_slide_right r)
  simpa only [ShiftedHom.mk₀_smul, ShiftRemoval.remove_smul, ShiftRemoval.remove_id,
    ShiftRemoval.remove_sub, ShiftRemoval.remove_comp, ffCross, ffDotFirst, ffDotSecond] using h

end Linear
end StrongSl2
end Categorification.TwoRep
