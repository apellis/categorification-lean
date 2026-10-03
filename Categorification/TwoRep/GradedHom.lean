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
laws are proved by finite-sum induction. The degree-zero inclusion is faithful, additive and
(for a linear shift) linear. This is the categorical kernel for `GradedHomBicategory`.

## Main declarations

* `GradedHomCat C`, its `Category`, `Preadditive` and `Linear` instances;
* `GradedHomCat.homOf d f`: the homogeneous morphism of degree `d` given by `f : X ⟶ Y⟦d⟧`;
* `GradedHomCat.incl C : C ⥤ GradedHomCat C`: the inclusion in degree `0`;
* `GradedHomCat.shiftIso X d : mk (X⟦d⟧) ≅ mk X`, homogeneous of degree `d`; `isIso_homOf`;
* `GradedHomCat.component e`: the component of degree `e`;
* `GradedHomCat.IsHomogeneous φ d`, with `IsHomogeneous.comp`, `IsHomogeneous.inv` (the inverse
  of a homogeneous isomorphism of degree `d` is homogeneous of degree `-d`),
  `IsHomogeneous.exists_incl_map` (degree `0` means in the image of `incl`), and
  `isHomogeneous_of_comp_eq`, `isHomogeneous_of_eq_comp` (homogeneity of a component of the
  inverse of a map into or out of a sum of three objects).

Only an additive shift on a preadditive category is needed. No boundedness of graded
endomorphisms, weight bound, finite-dimensionality, or adjunction is assumed.
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

/-! ### Linearity -/

section Linear

variable {k : Type*} [Field k] [Linear k C]

/-- The componentwise scalar action on finite sums of homogeneous morphisms. -/
instance homModule (X Y : GradedHomCat C) : Module k (X ⟶ Y) :=
  inferInstanceAs (Module k (GHom X.as Y.as))

/-- Homogeneous inclusion respects the scalar action. -/
theorem homOf_smul {X Y : C} (d : ℤ) (r : k) (f : ShiftedHom X Y d) :
    homOf d (r • f) = r • (homOf d f : (mk X : GradedHomCat C) ⟶ mk Y) :=
  DirectSum.of_smul (M := fun d : ℤ => ShiftedHom X Y d) k d r f

variable [∀ n : ℤ, (shiftFunctor C n).Linear k]

/-- Composition is bilinear for a linear shift. -/
instance linear : Linear k (GradedHomCat C) where
  homModule X Y := homModule X Y
  smul_comp := by
    rintro ⟨X⟩ ⟨Y⟩ ⟨Z⟩ r f g
    induction f using hom_induction with
    | zero => rw [smul_zero, Limits.zero_comp, smul_zero]
    | add φ ψ hφ hψ => rw [smul_add, Preadditive.add_comp, Preadditive.add_comp, hφ, hψ, smul_add]
    | homOf a f =>
      induction g using hom_induction with
      | zero => rw [Limits.comp_zero, Limits.comp_zero, smul_zero]
      | add φ ψ hφ hψ =>
        rw [Preadditive.comp_add, Preadditive.comp_add, hφ, hψ, smul_add]
      | homOf b g =>
        rw [← homOf_smul, homOf_comp_homOf _ _ rfl, homOf_comp_homOf _ _ rfl,
          ShiftedHom.smul_comp, homOf_smul]
  comp_smul := by
    rintro ⟨X⟩ ⟨Y⟩ ⟨Z⟩ f r g
    induction f using hom_induction with
    | zero => rw [Limits.zero_comp, Limits.zero_comp, smul_zero]
    | add φ ψ hφ hψ => rw [Preadditive.add_comp, Preadditive.add_comp, hφ, hψ, smul_add]
    | homOf a f =>
      induction g using hom_induction with
      | zero => rw [smul_zero, Limits.comp_zero, smul_zero]
      | add φ ψ hφ hψ =>
        rw [smul_add, Preadditive.comp_add, Preadditive.comp_add, hφ, hψ, smul_add]
      | homOf b g =>
        rw [← homOf_smul, homOf_comp_homOf _ _ rfl, homOf_comp_homOf _ _ rfl,
          ShiftedHom.comp_smul, homOf_smul]

end Linear

/-! ### The inclusion in degree zero -/

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

instance incl_linear {k : Type*} [Field k] [Linear k C] [∀ n : ℤ, (shiftFunctor C n).Linear k] :
    (incl C).Linear k where
  map_smul {_ _} f r := by rw [incl_map, incl_map, ShiftedHom.mk₀_smul, homOf_smul]

/-! ### An object is isomorphic to its shifts -/

/-- **`X⟦d⟧ ≅ X` in the graded-Hom category**, by the homogeneous isomorphism of degree `d` given
by the identity of `X⟦d⟧`. -/
def shiftIso (X : C) (d : ℤ) : (mk (X⟦d⟧) : GradedHomCat C) ≅ mk X where
  hom := homOf d (𝟙 (X⟦d⟧) : ShiftedHom (X⟦d⟧) X d)
  inv := homOf (-d)
    ((shiftFunctorCompIsoId C d (-d) (add_neg_cancel d)).inv.app X : ShiftedHom X (X⟦d⟧) (-d))
  hom_inv_id := by
    rw [homOf_comp_homOf _ _ (neg_add_cancel d), id_eq]
    congr 1
    dsimp only [ShiftedHom.comp, ShiftedHom.mk₀]
    rw [Category.id_comp, Category.id_comp, shift_shiftFunctorCompIsoId_inv_app]
    simp [shiftFunctorCompIsoId, shiftFunctorZero']
  inv_hom_id := by
    rw [homOf_comp_homOf _ _ (add_neg_cancel d), id_eq]
    congr 1
    dsimp only [ShiftedHom.comp, ShiftedHom.mk₀]
    simp [shiftFunctorCompIsoId, shiftFunctorZero']

theorem shiftIso_hom (X : C) (d : ℤ) :
    (shiftIso X d).hom = homOf d (𝟙 (X⟦d⟧) : ShiftedHom (X⟦d⟧) X d) := rfl

/-- A homogeneous morphism of degree `d` is the degree-`0` morphism `X ⟶ Y⟦d⟧` followed by the
isomorphism `Y⟦d⟧ ≅ Y` of degree `d`. -/
theorem homOf_eq_incl_map_comp_shiftIso {X Y : C} (d : ℤ) (f : ShiftedHom X Y d) :
    homOf d f = (incl C).map (f : X ⟶ Y⟦d⟧) ≫ (shiftIso Y d).hom := by
  rw [incl_map, shiftIso_hom, homOf_comp_homOf _ _ (add_zero d), ShiftedHom.mk₀_comp,
    Category.comp_id]

/-- If `f : X ⟶ Y⟦d⟧` is an isomorphism of `C`, the homogeneous morphism `homOf d f : X ⟶ Y` is an
isomorphism of the graded-Hom category. -/
theorem isIso_homOf {X Y : C} (d : ℤ) (f : ShiftedHom X Y d) [IsIso (f : X ⟶ Y⟦d⟧)] :
    IsIso (homOf d f) := by
  rw [homOf_eq_incl_map_comp_shiftIso]
  have : IsIso ((incl C).map (f : X ⟶ Y⟦d⟧)) := Functor.map_isIso _ _
  infer_instance

/-! ### Homogeneous components -/

/-- The component of degree `e` of a graded morphism. -/
def component {X Y : GradedHomCat C} (e : ℤ) : (X ⟶ Y) →+ ShiftedHom X.as Y.as e :=
  (Pi.evalAddMonoidHom (fun d : ℤ => ShiftedHom X.as Y.as d) e).comp
    (DirectSum.coeFnAddMonoidHom fun d : ℤ => ShiftedHom X.as Y.as d)

theorem component_homOf_self {X Y : C} (d : ℤ) (f : ShiftedHom X Y d) :
    component d (homOf d f) = f :=
  DirectSum.of_eq_same d f

theorem component_homOf_of_ne {X Y : C} {d e : ℤ} (h : e ≠ d) (f : ShiftedHom X Y d) :
    component e (homOf d f) = 0 :=
  DirectSum.of_eq_of_ne d e f h

/-- The components of `φ ≫ g` for `g` homogeneous of degree `d`. -/
theorem component_comp_homOf {X Y Z : C} (φ : (mk X : GradedHomCat C) ⟶ mk Y) {d e e' : ℤ}
    (g : ShiftedHom Y Z d) (h : d + e' = e) :
    component e (φ ≫ homOf d g) = (component e' φ).comp g h := by
  induction φ using hom_induction with
  | zero => rw [Limits.zero_comp, map_zero, map_zero, ShiftedHom.zero_comp]
  | add φ ψ hφ hψ => rw [Preadditive.add_comp, map_add, map_add, hφ, hψ, ShiftedHom.add_comp]
  | homOf a f =>
    by_cases ha : a = e'
    · subst ha
      rw [homOf_comp_homOf f g h, component_homOf_self, component_homOf_self]
    · rw [homOf_comp_homOf f g rfl, component_homOf_of_ne (by omega),
        component_homOf_of_ne (Ne.symm ha), ShiftedHom.zero_comp]

/-- The components of `f ≫ φ` for `f` homogeneous of degree `d`. -/
theorem component_homOf_comp {X Y Z : C} {d e e' : ℤ} (f : ShiftedHom X Y d)
    (φ : (mk Y : GradedHomCat C) ⟶ mk Z) (h : e' + d = e) :
    component e (homOf d f ≫ φ) = f.comp (component e' φ) h := by
  induction φ using hom_induction with
  | zero => rw [Limits.comp_zero, map_zero, map_zero, ShiftedHom.comp_zero]
  | add φ ψ hφ hψ => rw [Preadditive.comp_add, map_add, map_add, hφ, hψ, ShiftedHom.comp_add]
  | homOf a g =>
    by_cases ha : a = e'
    · subst ha
      rw [homOf_comp_homOf f g h, component_homOf_self, component_homOf_self]
    · rw [homOf_comp_homOf f g rfl, component_homOf_of_ne (by omega),
        component_homOf_of_ne (Ne.symm ha), ShiftedHom.comp_zero]

/-! ### Homogeneous morphisms -/

/-- A graded morphism is **homogeneous of degree `d`** if it is `homOf d f` for some
`f : X ⟶ Y⟦d⟧`. -/
def IsHomogeneous {X Y : GradedHomCat C} (φ : X ⟶ Y) (d : ℤ) : Prop :=
  ∃ f : ShiftedHom X.as Y.as d, φ = homOf d f

theorem isHomogeneous_homOf {X Y : C} (d : ℤ) (f : ShiftedHom X Y d) :
    IsHomogeneous (homOf d f) d :=
  ⟨f, rfl⟩

theorem isHomogeneous_incl_map {X Y : C} (f : X ⟶ Y) : IsHomogeneous ((incl C).map f) 0 :=
  ⟨_, rfl⟩

theorem isHomogeneous_id (X : GradedHomCat C) : IsHomogeneous (𝟙 X) 0 :=
  ⟨_, rfl⟩

theorem isHomogeneous_zero {X Y : GradedHomCat C} (d : ℤ) : IsHomogeneous (0 : X ⟶ Y) d :=
  ⟨0, (homOf_zero d).symm⟩

theorem IsHomogeneous.comp {X Y Z : GradedHomCat C} {φ : X ⟶ Y} {ψ : Y ⟶ Z} {a b c : ℤ}
    (hφ : IsHomogeneous φ a) (hψ : IsHomogeneous ψ b) (h : b + a = c) :
    IsHomogeneous (φ ≫ ψ) c := by
  obtain ⟨f, rfl⟩ := hφ
  obtain ⟨g, rfl⟩ := hψ
  exact ⟨f.comp g h, homOf_comp_homOf f g h⟩

theorem IsHomogeneous.neg {X Y : GradedHomCat C} {φ : X ⟶ Y} {d : ℤ} (hφ : IsHomogeneous φ d) :
    IsHomogeneous (-φ) d := by
  obtain ⟨f, rfl⟩ := hφ
  exact ⟨-f, (homOf_neg d f).symm⟩

theorem IsHomogeneous.add {X Y : GradedHomCat C} {φ ψ : X ⟶ Y} {d : ℤ} (hφ : IsHomogeneous φ d)
    (hψ : IsHomogeneous ψ d) : IsHomogeneous (φ + ψ) d := by
  obtain ⟨f, rfl⟩ := hφ
  obtain ⟨g, rfl⟩ := hψ
  exact ⟨f + g, (homOf_add d f g).symm⟩

theorem IsHomogeneous.smul {k : Type*} [Field k] [Linear k C]
    [∀ n : ℤ, (shiftFunctor C n).Linear k] {X Y : GradedHomCat C} {φ : X ⟶ Y} {d : ℤ}
    (hφ : IsHomogeneous φ d) (r : k) : IsHomogeneous (r • φ) d := by
  obtain ⟨f, rfl⟩ := hφ
  exact ⟨r • f, (homOf_smul d r f).symm⟩

theorem IsHomogeneous.of_eq {X Y : GradedHomCat C} {φ : X ⟶ Y} {d d' : ℤ}
    (hφ : IsHomogeneous φ d) (h : d = d') : IsHomogeneous φ d' :=
  h ▸ hφ

/-- A homogeneous morphism is recovered from its component. -/
theorem IsHomogeneous.eq_homOf_component {X Y : GradedHomCat C} {φ : X ⟶ Y} {d : ℤ}
    (hφ : IsHomogeneous φ d) : φ = homOf d (component d φ) := by
  obtain ⟨f, rfl⟩ := hφ
  rw [component_homOf_self]

/-- A homogeneous morphism of degree `0` comes from a morphism of `C`. -/
theorem IsHomogeneous.exists_incl_map {X Y : GradedHomCat C} {φ : X ⟶ Y}
    (hφ : IsHomogeneous φ 0) : ∃ f : X.as ⟶ Y.as, φ = (incl C).map f := by
  obtain ⟨f, rfl⟩ := hφ
  refine ⟨(ShiftedHom.homEquiv (0 : ℤ) rfl).symm f, ?_⟩
  rw [incl_map]
  congr 1
  exact ((ShiftedHom.homEquiv (0 : ℤ) rfl).apply_symm_apply f).symm

theorem shiftIso_hom_isHomogeneous (X : C) (d : ℤ) : IsHomogeneous (shiftIso X d).hom d :=
  ⟨_, rfl⟩

theorem shiftIso_inv_isHomogeneous (X : C) (d : ℤ) : IsHomogeneous (shiftIso X d).inv (-d) :=
  ⟨_, rfl⟩

/-- **The inverse of a homogeneous isomorphism** of degree `d` is homogeneous of degree `-d`. -/
theorem IsHomogeneous.inv {X Y : GradedHomCat C} {φ : X ⟶ Y} {d : ℤ} (hφ : IsHomogeneous φ d)
    [IsIso φ] : IsHomogeneous (CategoryTheory.inv φ) (-d) := by
  obtain ⟨X⟩ := X
  obtain ⟨Y⟩ := Y
  obtain ⟨f, rfl⟩ := hφ
  refine ⟨component (-d) (CategoryTheory.inv (homOf d f)), ?_⟩
  refine IsIso.inv_eq_of_hom_inv_id ?_
  rw [homOf_comp_homOf _ _ (neg_add_cancel d), id_eq]
  congr 1
  rw [← component_homOf_comp f (CategoryTheory.inv (homOf d f)) (neg_add_cancel d),
    IsIso.hom_inv_id, id_eq,
    component_homOf_self]

/-- If `(f₁, f₂, f₃) : X ⟶ Y₁ ⊕ Y₂ ⊕ Y₃` has homogeneous components and a left inverse
`(g₁, g₂, g₃)`, and `g₃` is a section of `f₃` killed by `f₁` and `f₂`, then `g₃` is homogeneous,
of degree opposite to that of `f₃`. -/
theorem isHomogeneous_of_comp_eq {X Y₁ Y₂ Y₃ : GradedHomCat C} {f₁ : X ⟶ Y₁} {f₂ : X ⟶ Y₂}
    {f₃ : X ⟶ Y₃} {g₁ : Y₁ ⟶ X} {g₂ : Y₂ ⟶ X} {g₃ : Y₃ ⟶ X} {d₁ d₂ d₃ : ℤ}
    (h₁ : IsHomogeneous f₁ d₁) (h₂ : IsHomogeneous f₂ d₂) (h₃ : IsHomogeneous f₃ d₃)
    (hsum : f₁ ≫ g₁ + f₂ ≫ g₂ + f₃ ≫ g₃ = 𝟙 X) (e₁ : g₃ ≫ f₁ = 0) (e₂ : g₃ ≫ f₂ = 0)
    (e₃ : g₃ ≫ f₃ = 𝟙 Y₃) : IsHomogeneous g₃ (-d₃) := by
  obtain ⟨X⟩ := X
  obtain ⟨Y₁⟩ := Y₁
  obtain ⟨Y₂⟩ := Y₂
  obtain ⟨Y₃⟩ := Y₃
  obtain ⟨φ₁, rfl⟩ := h₁
  obtain ⟨φ₂, rfl⟩ := h₂
  obtain ⟨φ₃, rfl⟩ := h₃
  refine ⟨component (-d₃) g₃, ?_⟩
  have k₁ : homOf (-d₃) (component (-d₃) g₃) ≫ homOf d₁ φ₁ = 0 := by
    rw [homOf_comp_homOf _ _ rfl, ← component_comp_homOf g₃ φ₁ rfl, e₁, map_zero, homOf_zero]
  have k₂ : homOf (-d₃) (component (-d₃) g₃) ≫ homOf d₂ φ₂ = 0 := by
    rw [homOf_comp_homOf _ _ rfl, ← component_comp_homOf g₃ φ₂ rfl, e₂, map_zero, homOf_zero]
  have k₃ : homOf (-d₃) (component (-d₃) g₃) ≫ homOf d₃ φ₃ = 𝟙 _ := by
    rw [homOf_comp_homOf _ _ (add_neg_cancel d₃),
      ← component_comp_homOf g₃ φ₃ (add_neg_cancel d₃), e₃, id_eq, component_homOf_self]
  calc g₃ = (homOf (-d₃) (component (-d₃) g₃) ≫ homOf d₃ φ₃) ≫ g₃ := by
        rw [k₃, Category.id_comp]
    _ = homOf (-d₃) (component (-d₃) g₃) ≫
          (homOf d₁ φ₁ ≫ g₁ + homOf d₂ φ₂ ≫ g₂ + homOf d₃ φ₃ ≫ g₃) := by
        rw [Preadditive.comp_add, Preadditive.comp_add, ← Category.assoc, ← Category.assoc,
          ← Category.assoc, k₁, k₂, Limits.zero_comp, Limits.zero_comp, zero_add, zero_add]
    _ = homOf (-d₃) (component (-d₃) g₃) := by
        rw [hsum, Category.comp_id]

/-- If `(f₁, f₂, f₃) : Y₁ ⊕ Y₂ ⊕ Y₃ ⟶ X` has homogeneous components and a right inverse
`(g₁, g₂, g₃)`, and `g₃` is a retraction of `f₃` killing `f₁` and `f₂`, then `g₃` is homogeneous,
of degree opposite to that of `f₃`. -/
theorem isHomogeneous_of_eq_comp {X Y₁ Y₂ Y₃ : GradedHomCat C} {f₁ : Y₁ ⟶ X} {f₂ : Y₂ ⟶ X}
    {f₃ : Y₃ ⟶ X} {g₁ : X ⟶ Y₁} {g₂ : X ⟶ Y₂} {g₃ : X ⟶ Y₃} {d₁ d₂ d₃ : ℤ}
    (h₁ : IsHomogeneous f₁ d₁) (h₂ : IsHomogeneous f₂ d₂) (h₃ : IsHomogeneous f₃ d₃)
    (hsum : g₁ ≫ f₁ + g₂ ≫ f₂ + g₃ ≫ f₃ = 𝟙 X) (e₁ : f₁ ≫ g₃ = 0) (e₂ : f₂ ≫ g₃ = 0)
    (e₃ : f₃ ≫ g₃ = 𝟙 Y₃) : IsHomogeneous g₃ (-d₃) := by
  obtain ⟨X⟩ := X
  obtain ⟨Y₁⟩ := Y₁
  obtain ⟨Y₂⟩ := Y₂
  obtain ⟨Y₃⟩ := Y₃
  obtain ⟨φ₁, rfl⟩ := h₁
  obtain ⟨φ₂, rfl⟩ := h₂
  obtain ⟨φ₃, rfl⟩ := h₃
  refine ⟨component (-d₃) g₃, ?_⟩
  have k₁ : homOf d₁ φ₁ ≫ homOf (-d₃) (component (-d₃) g₃) = 0 := by
    rw [homOf_comp_homOf _ _ rfl, ← component_homOf_comp φ₁ g₃ rfl, e₁, map_zero, homOf_zero]
  have k₂ : homOf d₂ φ₂ ≫ homOf (-d₃) (component (-d₃) g₃) = 0 := by
    rw [homOf_comp_homOf _ _ rfl, ← component_homOf_comp φ₂ g₃ rfl, e₂, map_zero, homOf_zero]
  have k₃ : homOf d₃ φ₃ ≫ homOf (-d₃) (component (-d₃) g₃) = 𝟙 _ := by
    rw [homOf_comp_homOf _ _ (neg_add_cancel d₃),
      ← component_homOf_comp φ₃ g₃ (neg_add_cancel d₃), e₃, id_eq, component_homOf_self]
  calc g₃ = g₃ ≫ homOf d₃ φ₃ ≫ homOf (-d₃) (component (-d₃) g₃) := by
        rw [k₃, Category.comp_id]
    _ = (g₁ ≫ homOf d₁ φ₁ + g₂ ≫ homOf d₂ φ₂ + g₃ ≫ homOf d₃ φ₃) ≫
          homOf (-d₃) (component (-d₃) g₃) := by
        rw [Preadditive.add_comp, Preadditive.add_comp, Category.assoc, Category.assoc,
          Category.assoc, k₁, k₂, Limits.comp_zero, Limits.comp_zero, zero_add, zero_add]
    _ = homOf (-d₃) (component (-d₃) g₃) := by
        rw [hsum, Category.id_comp]

end GradedHomCat

end Categorification.TwoRep
