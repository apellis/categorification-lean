import Categorification.TwoRep.ShiftedMatesUnshift
import Categorification.TwoRep.ShiftedMatesReassociate

/-! # Local nilHecke relations on the unshifted downward factors

Shift removal is compatible with each tensor factor by ordinary bicategorical
interchange. No super sign or extra adjunction is introduced.
-/

noncomputable section
namespace Categorification.TwoRep
open CategoryTheory CategoryTheory.Bicategory
universe w v u

private theorem tensor_conjugate_right {D : Type*} [Bicategory D]
    {a b c : D} {f f' : a ⟶ b} {g g' : b ⟶ c}
    (e : f ≅ f') (h : g ≅ g') (t : f' ⟶ f') :
    (f ◁ h.hom ≫ e.hom ▷ g') ≫ (t ▷ g') ≫
      (e.inv ▷ g' ≫ f ◁ h.inv) = (e.hom ≫ t ≫ e.inv) ▷ g := by
  rw [Category.assoc, ← Category.assoc (e.hom ▷ g'),
    ← Category.assoc (e.hom ▷ g' ≫ t ▷ g'),
    ← comp_whiskerRight, ← comp_whiskerRight,
    whisker_exchange_assoc]
  rw [← whiskerLeft_comp, Iso.hom_inv_id, whiskerLeft_id, Category.comp_id]
  rw [Category.assoc]

private theorem tensor_conjugate_left {D : Type*} [Bicategory D]
    {a b c : D} {f f' : a ⟶ b} {g g' : b ⟶ c}
    (e : f ≅ f') (h : g ≅ g') (t : g' ⟶ g') :
    (f ◁ h.hom ≫ e.hom ▷ g') ≫ (f' ◁ t) ≫
      (e.inv ▷ g' ≫ f ◁ h.inv) = f ◁ (h.hom ≫ t ≫ h.inv) := by
  rw [Category.assoc, ← whisker_exchange_assoc e.hom t,
    ← comp_whiskerRight_assoc, Iso.hom_inv_id, id_whiskerRight,
    Category.id_comp, ← whiskerLeft_comp, ← whiskerLeft_comp]

private def tensorIso {D : Type*} [Bicategory D]
    {a b c : D} {f f' : a ⟶ b} {g g' : b ⟶ c}
    (e : f ≅ f') (h : g ≅ g') : f ≫ g ≅ f' ≫ g' :=
  whiskerLeftIso f h ≪≫ whiskerRightIso e g'

private theorem tensorIso_associator {D : Type*} [Bicategory D]
    {a b c d : D} {f f' : a ⟶ b} {g g' : b ⟶ c} {h h' : c ⟶ d}
    (e : f ≅ f') (i : g ≅ g') (j : h ≅ h') :
    tensorIso (tensorIso e i) j ≪≫ (α_ f' g' h') =
      (α_ f g h) ≪≫ tensorIso e (tensorIso i j) := by
  apply Iso.ext
  simp only [tensorIso, Iso.trans_hom, whiskerLeftIso_hom, whiskerRightIso_hom,
    comp_whiskerRight, Category.assoc, associator_naturality_left,
    associator_naturality_middle_assoc, associator_naturality_right_assoc,
    whiskerLeft_comp]

private theorem tensor_conjugate_triple_right {D : Type*} [Bicategory D]
    {a b c d : D} {f f' : a ⟶ b} {g g' : b ⟶ c} {h h' : c ⟶ d}
    (e : f ≅ f') (i : g ≅ g') (j : h ≅ h') (t : g' ≫ h' ⟶ g' ≫ h') :
    (tensorIso (tensorIso e i) j).hom ≫
      ((α_ f' g' h').hom ≫ (f' ◁ t) ≫ (α_ f' g' h').inv) ≫
      (tensorIso (tensorIso e i) j).inv =
    (α_ f g h).hom ≫
      (f ◁ ((tensorIso i j).hom ≫ t ≫ (tensorIso i j).inv)) ≫
      (α_ f g h).inv := by
  have hh := congrArg Iso.hom (tensorIso_associator e i j)
  have hi := congrArg Iso.inv (tensorIso_associator e i j)
  simp only [Iso.trans_hom] at hh
  simp only [Iso.trans_inv] at hi
  simp only [Category.assoc]
  rw [← Category.assoc, hh]
  simp only [Category.assoc]
  rw [hi]
  have ht := tensor_conjugate_left e (tensorIso i j) t
  simpa only [tensorIso, Iso.trans_hom, Iso.trans_inv, whiskerLeftIso_hom,
    whiskerRightIso_hom, whiskerLeftIso_inv, whiskerRightIso_inv, Category.assoc] using
    congrArg (fun x => (α_ f g h).hom ≫ x ≫ (α_ f g h).inv) ht

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [GradedBicategory.ShiftCoherence B]

namespace ShiftRemoval
open GradedHomBicat
variable {a b c : B}

/-- Shift removal commutes with the first tensor factor in every degree. -/
theorem remove_whiskerRight (f : a ⟶ b) (g : b ⟶ c) (p q : ℤ) {d : ℤ}
    (t : ShiftedHom (f⟦p⟧) (f⟦p⟧) d) :
    remove (shiftCompShiftIso f g (rfl : q + p = q + p)) (shWhiskerRight t (g⟦q⟧)) =
      shWhiskerRight (remove (Iso.refl (f⟦p⟧)) t) g := by
  apply of₂_injective d
  change GradedHomCat.homOf d (remove _ _) = _
  rw [homOf_remove, removeIso_tensor]
  change _ ≫ of₂ d (shWhiskerRight t (g⟦q⟧)) ≫ _ = _
  rw [← of₂_whiskerRight, ← of₂_whiskerRight]
  change _ = of₂ d (remove (Iso.refl (f⟦p⟧)) t) ▷ of₁ g
  rw [show of₂ d (remove (Iso.refl (f⟦p⟧)) t) =
      (shiftIso f p).hom ≫ of₂ d t ≫ (shiftIso f p).inv by
    simpa [removeIso, of₂] using homOf_remove (Iso.refl (f⟦p⟧)) t]
  exact tensor_conjugate_right (D := GradedHomBicat B) (shiftIso f p) (shiftIso g q) (of₂ d t)

/-- Shift removal commutes with the second tensor factor in every degree. -/
theorem remove_whiskerLeft (f : a ⟶ b) (g : b ⟶ c) (p q : ℤ) {d : ℤ}
    (t : ShiftedHom (g⟦q⟧) (g⟦q⟧) d) :
    remove (shiftCompShiftIso f g (rfl : q + p = q + p)) (shWhiskerLeft (f⟦p⟧) t) =
      shWhiskerLeft f (remove (Iso.refl (g⟦q⟧)) t) := by
  apply of₂_injective d
  change GradedHomCat.homOf d (remove _ _) = _
  rw [homOf_remove, removeIso_tensor]
  change _ ≫ of₂ d (shWhiskerLeft (f⟦p⟧) t) ≫ _ = _
  rw [← whiskerLeft_of₂, ← whiskerLeft_of₂]
  change _ = of₁ f ◁ of₂ d (remove (Iso.refl (g⟦q⟧)) t)
  rw [show of₂ d (remove (Iso.refl (g⟦q⟧)) t) =
      (shiftIso g q).hom ≫ of₂ d t ≫ (shiftIso g q).inv by
    simpa [removeIso, of₂] using homOf_remove (Iso.refl (g⟦q⟧)) t]
  exact tensor_conjugate_left (D := GradedHomBicat B) (shiftIso f p) (shiftIso g q) (of₂ d t)

end ShiftRemoval

namespace StrongSl2
open CategoryTheory.Limits
variable {k : Type*} [Field k] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  (S : StrongSl2 k B)

/-- The first transported dot is the dot on the actual first `F` factor. -/
theorem ffDotFirst_eq (r : ℤ) :
    S.ffDotFirst r = shWhiskerRight (S.fDot (r + 1)) (S.F r) :=
  ShiftRemoval.remove_whiskerRight _ _ _ _ _

/-- The second transported dot is the dot on the actual second `F` factor. -/
theorem ffDotSecond_eq (r : ℤ) :
    S.ffDotSecond r = shWhiskerLeft (S.F (r + 1)) (S.fDot r) :=
  ShiftRemoval.remove_whiskerLeft _ _ _ _ _

open GradedHomBicat ShiftRemoval

/-- The first crossing on the actual left-associated unshifted triple. -/
def fffCrossLeft (r : ℤ) :
    ShiftedHom ((S.F (r + 1 + 1) ≫ S.F (r + 1)) ≫ S.F r)
      ((S.F (r + 1 + 1) ≫ S.F (r + 1)) ≫ S.F r) (-2 : ℤ) :=
  shWhiskerRight (S.ffCross (r + 1)) (S.F r)

/-- The second crossing, conjugated by the actual unshifted associator. -/
def fffCrossRight (r : ℤ) :
    ShiftedHom ((S.F (r + 1 + 1) ≫ S.F (r + 1)) ≫ S.F r)
      ((S.F (r + 1 + 1) ≫ S.F (r + 1)) ≫ S.F r) (-2 : ℤ) :=
  (ShiftedHom.mk₀ (0 : ℤ) rfl (α_ (S.F (r + 1 + 1)) (S.F (r + 1)) (S.F r)).hom).comp
    ((shWhiskerLeft (S.F (r + 1 + 1)) (S.ffCross r)).comp
      (ShiftedHom.mk₀ (0 : ℤ) rfl (α_ (S.F (r + 1 + 1)) (S.F (r + 1)) (S.F r)).inv)
      (by norm_num : (0 : ℤ) + -2 = -2)) (by norm_num : (-2 : ℤ) + 0 = -2)

/-- The homogeneous tensor conjugator from actual `FFF` to supplied right adjoints.
The parenthesization is left-associated on both sides. -/
def fffShiftHomIso (r : ℤ) :
    of₁ ((S.F (r + 1 + 1) ≫ S.F (r + 1)) ≫ S.F r) ≅
      of₁ ((S.adjointF (r + 1 + 1) ≫ S.adjointF (r + 1)) ≫ S.adjointF r) :=
  tensorIso (D := GradedHomBicat B)
    (a := of (S.obj (r + 1 + 1 + 1))) (b := of (S.obj (r + 1))) (c := of (S.obj r))
    (tensorIso (D := GradedHomBicat B)
      (a := of (S.obj (r + 1 + 1 + 1))) (b := of (S.obj (r + 1 + 1)))
      (c := of (S.obj (r + 1)))
      (shiftIso (S.F (r + 1 + 1)) (S.n₀ + 2 * (r + 1 + 1) + 1))
      (shiftIso (S.F (r + 1)) (S.n₀ + 2 * (r + 1) + 1)))
    (shiftIso (S.F r) (S.n₀ + 2 * r + 1))

private theorem of₂_ffCross (r : ℤ) :
    of₂ (-2) (S.ffCross r) =
      (tensorIso (D := GradedHomBicat B)
        (a := of (S.obj (r + 1 + 1))) (b := of (S.obj (r + 1))) (c := of (S.obj r))
        (shiftIso (S.F (r + 1)) (S.n₀ + 2 * (r + 1) + 1))
        (shiftIso (S.F r) (S.n₀ + 2 * r + 1))).hom ≫
      of₂ (-2) (S.mateCross r) ≫
      (tensorIso (D := GradedHomBicat B)
        (a := of (S.obj (r + 1 + 1))) (b := of (S.obj (r + 1))) (c := of (S.obj r))
        (shiftIso (S.F (r + 1)) (S.n₀ + 2 * (r + 1) + 1))
        (shiftIso (S.F r) (S.n₀ + 2 * r + 1))).inv := by
  change GradedHomCat.homOf (-2) (ShiftRemoval.remove _ _) = _
  rw [ShiftRemoval.homOf_remove]
  simp only [ffShiftIso, ShiftRemoval.removeIso_tensor]
  rfl

/-- The first genuine local crossing is transported by the triple tensor conjugator. -/
theorem of₂_fffCrossLeft (r : ℤ) :
    of₂ (-2) (S.fffCrossLeft r) = (S.fffShiftHomIso r).hom ≫
      of₂ (-2) (S.mateCrossTripleLeft r) ≫ (S.fffShiftHomIso r).inv := by
  simp only [fffCrossLeft, mateCrossTripleLeft, ← of₂_whiskerRight, of₂_ffCross]
  exact (tensor_conjugate_right (D := GradedHomBicat B) _ _ _).symm

/-- The second genuine local crossing is transported by the same conjugator. -/
theorem of₂_fffCrossRight (r : ℤ) :
    of₂ (-2) (S.fffCrossRight r) = (S.fffShiftHomIso r).hom ≫
      of₂ (-2) (S.mateCrossTripleRight r) ≫ (S.fffShiftHomIso r).inv := by
  simp only [fffCrossRight, mateCrossTripleRight, ← of₂_comp_of₂, ← incl₂_eq_of₂,
    ← associator_hom_eq, ← associator_inv_eq, ← whiskerLeft_of₂, of₂_ffCross]
  exact (tensor_conjugate_triple_right (D := GradedHomBicat B) _ _ _ _).symm

/-- The degree-minus-six braid on actual unshifted `FFF`, using genuine local crossings. -/
theorem fffCross_braid (r : ℤ) :
    ((S.fffCrossLeft r).comp (S.fffCrossRight r)
      (by norm_num : (-2 : ℤ) + -2 = -4)).comp (S.fffCrossLeft r)
      (by norm_num : (-2 : ℤ) + -4 = -6) =
    ((S.fffCrossRight r).comp (S.fffCrossLeft r)
      (by norm_num : (-2 : ℤ) + -2 = -4)).comp (S.fffCrossRight r)
      (by norm_num : (-2 : ℤ) + -4 = -6) := by
  apply of₂_injective (-6)
  have h := congrArg (fun t => (S.fffShiftHomIso r).hom ≫ of₂ (-6) t ≫
    (S.fffShiftHomIso r).inv) (S.mateCross_braid r)
  simpa only [← of₂_comp_of₂, of₂_fffCrossLeft, of₂_fffCrossRight,
    Category.assoc, Iso.inv_hom_id_assoc] using h

section Linear
variable [GradedBicategory.IsLinear B k]

/-- The first scalar dot-slide, now with genuine tensor-factor dots. -/
theorem f_dot_slide_left (r : ℤ) :
    ShiftedHom.mk₀ (0 : ℤ) rfl ((S.rQ : k) • 𝟙 (S.F (r + 1) ≫ S.F r)) =
      (S.ffCross r).comp (shWhiskerRight (S.fDot (r + 1)) (S.F r))
        (by norm_num : (2 : ℤ) + -2 = 0) -
      (shWhiskerLeft (S.F (r + 1)) (S.fDot r)).comp (S.ffCross r)
        (by norm_num : (-2 : ℤ) + 2 = 0) := by
  rw [← S.ffDotFirst_eq, ← S.ffDotSecond_eq]
  exact S.ff_dot_slide_left r

/-- The second scalar dot-slide, with the original `rQ` and subtraction order. -/
theorem f_dot_slide_right (r : ℤ) :
    ShiftedHom.mk₀ (0 : ℤ) rfl ((S.rQ : k) • 𝟙 (S.F (r + 1) ≫ S.F r)) =
      (shWhiskerRight (S.fDot (r + 1)) (S.F r)).comp (S.ffCross r)
        (by norm_num : (-2 : ℤ) + 2 = 0) -
      (S.ffCross r).comp (shWhiskerLeft (S.F (r + 1)) (S.fDot r))
        (by norm_num : (2 : ℤ) + -2 = 0) := by
  rw [← S.ffDotFirst_eq, ← S.ffDotSecond_eq]
  exact S.ff_dot_slide_right r

end Linear
end StrongSl2
end Categorification.TwoRep
