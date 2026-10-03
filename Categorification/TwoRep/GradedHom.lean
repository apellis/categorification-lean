/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.DirectSum.Module
import Categorification.TwoRep.Basic

/-!
# Finite-sum graded Hom categories

For CL §2.1.2 (arXiv:1111.1431v3), construct `Hom^•(X,Y) = ⨁ d, Hom(X,Y⟦d⟧)`.
Composition extends the existing `ShiftedHom.comp` biadditively; its unit and associativity
laws are proved by finite-sum induction. The degree-zero inclusion is faithful and additive.
This is the categorical kernel for `GradedHomBicategory` and its shifted-adjunction consumer.

Only an additive shift on a preadditive category is needed. No boundedness of graded
endomorphisms, weight bound, finite-dimensionality, or adjunction is assumed. In particular
this infrastructure neither proves CL Prop. 3.9 nor removes the extra hypothesis of issue #6.
The core definitions follow the ungated `cl-sc` lead; additional homogeneous inverse,
linearity, and low-weight claims from that branch are deliberately not imported.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits

universe v u

/-- **The graded-Hom category** of a category with shift (CL §2.1.2): the same objects, and
morphisms the graded Hom spaces `Hom^•(X, Y) = ⨁ d, Hom(X, Y⟦d⟧)`. -/
structure GradedHomCat (C : Type u) where
  /-- The underlying object of `C`. -/
  as : C

namespace GradedHomCat

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]

/-- The graded Hom space `Hom^•(X, Y) = ⨁ d, Hom(X, Y⟦d⟧)`. -/
abbrev GHom (X Y : C) : Type v := DirectSum ℤ fun d : ℤ => ShiftedHom X Y d

/-- Composition of homogeneous morphisms, as a biadditive map into the graded Hom space. -/
def compOf (X Y Z : C) (a b : ℤ) : ShiftedHom X Y a →+ ShiftedHom Y Z b →+ GHom X Z :=
  AddMonoidHom.mk'
    (fun f => AddMonoidHom.mk'
      (fun g => DirectSum.of (fun d : ℤ => ShiftedHom X Z d) (b + a) (f.comp g rfl))
      (fun g g' => by rw [ShiftedHom.comp_add, map_add]))
    (fun f f' => by
      ext g
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
      rw [ShiftedHom.add_comp, map_add])

/-- Composition of graded morphisms, as a biadditive map. -/
def compHom (X Y Z : C) : GHom X Y →+ GHom Y Z →+ GHom X Z :=
  DirectSum.toAddMonoid fun a =>
    (DirectSum.toAddMonoid fun b => (compOf X Y Z a b).flip).flip

theorem compHom_of_of {X Y Z : C} {a b c : ℤ} (f : ShiftedHom X Y a) (g : ShiftedHom Y Z b)
    (h : b + a = c) :
    compHom X Y Z (DirectSum.of (fun d : ℤ => ShiftedHom X Y d) a f)
        (DirectSum.of (fun d : ℤ => ShiftedHom Y Z d) b g) =
      DirectSum.of (fun d : ℤ => ShiftedHom X Z d) c (f.comp g h) := by
  subst h
  simp [compHom, compOf]

instance categoryStruct : CategoryStruct.{v} (GradedHomCat C) where
  Hom X Y := GHom X.as Y.as
  id X := DirectSum.of (fun d : ℤ => ShiftedHom X.as X.as d) 0
    (ShiftedHom.mk₀ (0 : ℤ) rfl (𝟙 X.as))
  comp {X Y Z} f g := compHom X.as Y.as Z.as f g

instance homAddCommGroup (X Y : GradedHomCat C) : AddCommGroup (X ⟶ Y) :=
  inferInstanceAs (AddCommGroup (GHom X.as Y.as))

/-- The homogeneous morphism of degree `d` given by `f : X ⟶ Y⟦d⟧`. -/
def homOf {X Y : C} (d : ℤ) (f : ShiftedHom X Y d) : (mk X : GradedHomCat C) ⟶ mk Y :=
  DirectSum.of (fun d : ℤ => ShiftedHom X Y d) d f

theorem id_eq (X : C) :
    𝟙 (mk X : GradedHomCat C) = homOf 0 (ShiftedHom.mk₀ (0 : ℤ) rfl (𝟙 X)) := rfl

/-- **Composition of homogeneous morphisms**: degrees add. -/
theorem homOf_comp_homOf {X Y Z : C} {a b c : ℤ} (f : ShiftedHom X Y a) (g : ShiftedHom Y Z b)
    (h : b + a = c) : homOf a f ≫ homOf b g = homOf c (f.comp g h) :=
  compHom_of_of f g h

@[simp] theorem homOf_zero {X Y : C} (d : ℤ) :
    homOf d (0 : ShiftedHom X Y d) = (0 : (mk X : GradedHomCat C) ⟶ mk Y) :=
  map_zero (DirectSum.of (fun d : ℤ => ShiftedHom X Y d) d)

theorem homOf_add {X Y : C} (d : ℤ) (f g : ShiftedHom X Y d) :
    homOf d (f + g) = homOf d f + homOf d g :=
  map_add (DirectSum.of (fun d : ℤ => ShiftedHom X Y d) d) f g

theorem homOf_neg {X Y : C} (d : ℤ) (f : ShiftedHom X Y d) : homOf d (-f) = -homOf d f :=
  map_neg (DirectSum.of (fun d : ℤ => ShiftedHom X Y d) d) f

theorem homOf_sub {X Y : C} (d : ℤ) (f g : ShiftedHom X Y d) :
    homOf d (f - g) = homOf d f - homOf d g :=
  map_sub (DirectSum.of (fun d : ℤ => ShiftedHom X Y d) d) f g

theorem homOf_injective {X Y : C} (d : ℤ) :
    Function.Injective (homOf d : ShiftedHom X Y d → ((mk X : GradedHomCat C) ⟶ mk Y)) :=
  DirectSum.of_injective d

/-- Transport of a homogeneous morphism along an equality of degrees. -/
theorem homOf_congr {X Y : C} {d d' : ℤ} (h : d = d') (f : ShiftedHom X Y d) :
    homOf d f = homOf d' (h ▸ f) := by
  subst h; rfl

protected theorem add_comp' {X Y Z : GradedHomCat C} (f f' : X ⟶ Y) (g : Y ⟶ Z) :
    (f + f') ≫ g = f ≫ g + f' ≫ g := by
  change compHom _ _ _ (f + f') g = compHom _ _ _ f g + compHom _ _ _ f' g
  rw [map_add, AddMonoidHom.add_apply]

protected theorem comp_add' {X Y Z : GradedHomCat C} (f : X ⟶ Y) (g g' : Y ⟶ Z) :
    f ≫ (g + g') = f ≫ g + f ≫ g' :=
  map_add (compHom X.as Y.as Z.as f) g g'

protected theorem zero_comp' {X Y Z : GradedHomCat C} (g : Y ⟶ Z) : (0 : X ⟶ Y) ≫ g = 0 := by
  change compHom _ _ _ 0 g = 0
  rw [map_zero, AddMonoidHom.zero_apply]

protected theorem comp_zero' {X Y Z : GradedHomCat C} (f : X ⟶ Y) : f ≫ (0 : Y ⟶ Z) = 0 :=
  map_zero (compHom X.as Y.as Z.as f)

/-- Induction on a graded morphism: zero, homogeneous morphisms, sums. -/
@[elab_as_elim]
theorem hom_induction {X Y : C} {motive : ((mk X : GradedHomCat C) ⟶ mk Y) → Prop}
    (φ : (mk X : GradedHomCat C) ⟶ mk Y) (zero : motive 0)
    (homOf : ∀ (d : ℤ) (f : ShiftedHom X Y d), motive (homOf d f))
    (add : ∀ φ ψ, motive φ → motive ψ → motive (φ + ψ)) : motive φ :=
  DirectSum.induction_on φ zero homOf add

instance category : Category.{v} (GradedHomCat C) where
  toCategoryStruct := categoryStruct
  id_comp := by
    rintro ⟨X⟩ ⟨Y⟩ f
    induction f using hom_induction with
    | zero => exact GradedHomCat.comp_zero' _
    | homOf d f => rw [id_eq, homOf_comp_homOf _ _ (add_zero d), ShiftedHom.mk₀_id_comp]
    | add φ ψ hφ hψ => rw [GradedHomCat.comp_add', hφ, hψ]
  comp_id := by
    rintro ⟨X⟩ ⟨Y⟩ f
    induction f using hom_induction with
    | zero => exact GradedHomCat.zero_comp' _
    | homOf d f => rw [id_eq, homOf_comp_homOf _ _ (zero_add d), ShiftedHom.comp_mk₀_id]
    | add φ ψ hφ hψ => rw [GradedHomCat.add_comp', hφ, hψ]
  assoc := by
    rintro ⟨W⟩ ⟨X⟩ ⟨Y⟩ ⟨Z⟩ f g h
    induction f using hom_induction with
    | zero => simp only [GradedHomCat.zero_comp']
    | add φ ψ hφ hψ => simp only [GradedHomCat.add_comp', hφ, hψ]
    | homOf a f =>
      induction g using hom_induction with
      | zero => simp only [GradedHomCat.zero_comp', GradedHomCat.comp_zero']
      | add φ ψ hφ hψ => simp only [GradedHomCat.add_comp', GradedHomCat.comp_add', hφ, hψ]
      | homOf b g =>
        induction h using hom_induction with
        | zero => simp only [GradedHomCat.comp_zero']
        | add φ ψ hφ hψ => simp only [GradedHomCat.comp_add', hφ, hψ]
        | homOf c h =>
          rw [homOf_comp_homOf f g rfl,
            homOf_comp_homOf _ h (show c + (b + a) = c + b + a by ring),
            homOf_comp_homOf g h rfl, homOf_comp_homOf f _ rfl,
            ShiftedHom.comp_assoc f g h rfl rfl rfl]

instance preadditive : Preadditive (GradedHomCat C) where
  homGroup X Y := homAddCommGroup X Y
  add_comp _ _ _ f f' g := GradedHomCat.add_comp' f f' g
  comp_add _ _ _ f g g' := GradedHomCat.comp_add' f g g'

variable (C) in
/-- **The inclusion `C ⥤ GradedHomCat C`** in degree `0`: the identity on objects, and a morphism
`f` is sent to the homogeneous morphism of degree `0` it defines. -/
abbrev incl : C ⥤ GradedHomCat C where
  obj X := mk X
  map f := homOf 0 (ShiftedHom.mk₀ (0 : ℤ) rfl f)
  map_id _ := rfl
  map_comp f g := by
    rw [homOf_comp_homOf _ _ (add_zero (0 : ℤ)), ShiftedHom.mk₀_comp_mk₀]

@[simp] theorem incl_obj (X : C) : (incl C).obj X = mk X := rfl

theorem incl_map {X Y : C} (f : X ⟶ Y) :
    (incl C).map f = homOf 0 (ShiftedHom.mk₀ (0 : ℤ) rfl f) := rfl

instance incl_faithful : (incl C).Faithful where
  map_injective {_ _} _ _ h := (ShiftedHom.homEquiv (0 : ℤ) rfl).injective (homOf_injective 0 h)

instance incl_additive : (incl C).Additive where
  map_add {_ _ f g} := by
    rw [incl_map, incl_map, incl_map, ShiftedHom.mk₀_add, homOf_add]

end GradedHomCat

end Categorification.TwoRep
