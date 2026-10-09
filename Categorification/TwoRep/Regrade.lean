/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.GradedHomBicategory
import Mathlib.CategoryTheory.Shift.Pullback
import Mathlib.CategoryTheory.Bicategory.Functor.StrictPseudofunctor
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic

/-!
# Rescaling the grading of a graded bicategory

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, §2.6.1 and the first paragraph of §5: for a vertex `i` with `d_i ≠ 1` the
relations involving only the label `i` are reduced to the case `d_i = 1` "by rescaling degrees".
This file makes the rescaling precise on the side of the 2-representation.

For a graded bicategory `B` and an integer `d`, `Regrade B d` is `B` with the grading shift of
every Hom category pulled back along `n ↦ d n` (Mathlib's `PullbackShift`): the shift `⟨n⟩` of
`Regrade B d` is the shift `⟨d n⟩` of `B`. All other structure (composition, additive and linear
structure, zero objects, biproducts, idempotent completeness, Hom-finiteness) is that of `B`.

* `Regrade B d` is again a graded bicategory satisfying the shift coherence conditions
  (`GradedBicategory.ShiftCoherence`) and linearity when `B` does.
* `Regrade.toB`: a shifted 2-morphism of degree `n` of `Regrade B d` *is* a shifted 2-morphism
  of degree `d n` of `B`; `toB_comp`, `toB_shWhiskerLeft`, `toB_shWhiskerRight`, `toB_mk₀`
  compare composition, whiskering and degree-zero 2-morphisms.
* `Regrade.comparison`: the strict pseudofunctor `K^•(Regrade B d) → K^•(B)` of graded-Hom
  bicategories (`GradedHomBicat`), the identity on objects and 1-morphisms, sending a homogeneous
  2-morphism of degree `n` to the same 2-morphism of degree `d n` (`comparison_map₂_of₂`); it is
  `k`-linear on 2-morphisms (`comparison_map₂_smul`).
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory

universe w v u

/-- **`B` with its grading rescaled by `d`**: the shift `⟨n⟩` of the Hom categories is the shift
`⟨d n⟩` of `B`. -/
def Regrade (B : Type u) (_d : ℤ) : Type u := B

namespace Regrade

variable {B : Type u} [Bicategory.{w, v} B] (d : ℤ)

instance bicategory : Bicategory.{w, v} (Regrade B d) := inferInstanceAs (Bicategory.{w, v} B)

/-- An object of `B` as an object of `Regrade B d`. -/
abbrev of (a : B) : Regrade B d := a

/-- An object of `Regrade B d` as an object of `B`. -/
abbrev as {d : ℤ} (a : Regrade B d) : B := a

/-- A 1-morphism of `B` as a 1-morphism of `Regrade B d`. -/
abbrev up {a b : B} (f : a ⟶ b) : of d a ⟶ of d b := f

/-- A 1-morphism of `Regrade B d` as a 1-morphism of `B`. -/
abbrev as₁ {d : ℤ} {a b : Regrade B d} (f : a ⟶ b) : as a ⟶ as b := f

/-- A 2-morphism of `Regrade B d` as a 2-morphism of `B`. -/
abbrev as₂ {d : ℤ} {a b : Regrade B d} {f g : a ⟶ b} (η : f ⟶ g) : as₁ f ⟶ as₁ g := η

/-- The additive map `n ↦ d n`. -/
abbrev scale : ℤ →+ ℤ := AddMonoidHom.mulLeft d

theorem scale_apply (n : ℤ) : scale d n = d * n := rfl

section Instances

variable [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, HasShift (a ⟶ b) ℤ]

instance homPreadditive (a b : Regrade B d) : Preadditive (a ⟶ b) :=
  inferInstanceAs (Preadditive (as a ⟶ as b))

instance homHasShift (a b : Regrade B d) : HasShift (a ⟶ b) ℤ :=
  inferInstanceAs (HasShift (PullbackShift (as a ⟶ as b) (scale d)) ℤ)

instance homLinear (k : Type*) [Field k] [∀ a b : B, Linear k (a ⟶ b)] (a b : Regrade B d) :
    Linear k (a ⟶ b) :=
  inferInstanceAs (Linear k (as a ⟶ as b))

instance homHasZeroObject [∀ a b : B, HasZeroObject (a ⟶ b)] (a b : Regrade B d) :
    HasZeroObject (a ⟶ b) :=
  inferInstanceAs (HasZeroObject (as a ⟶ as b))

instance homHasBinaryBiproducts [∀ a b : B, HasBinaryBiproducts (a ⟶ b)] (a b : Regrade B d) :
    HasBinaryBiproducts (a ⟶ b) :=
  inferInstanceAs (HasBinaryBiproducts (as a ⟶ as b))

instance homIsIdempotentComplete [∀ a b : B, IsIdempotentComplete (a ⟶ b)] (a b : Regrade B d) :
    IsIdempotentComplete (a ⟶ b) :=
  inferInstanceAs (IsIdempotentComplete (as a ⟶ as b))

instance homFinite (k : Type*) [Field k] [∀ a b : B, Linear k (a ⟶ b)]
    [∀ a b : B, KrullSchmidtCat.HomFinite k (a ⟶ b)] (a b : Regrade B d) :
    KrullSchmidtCat.HomFinite k (a ⟶ b) :=
  inferInstanceAs (KrullSchmidtCat.HomFinite k (as a ⟶ as b))

/-- The shift of a 1-morphism of `Regrade B d` by `n` is its shift by `d n` in `B`. -/
theorem shift_obj {a b : B} (f : a ⟶ b) (n : ℤ) :
    (up d f)⟦n⟧ = (f⟦d * n⟧ : a ⟶ b) := rfl

theorem shiftFunctor_map {a b : B} {f g : a ⟶ b} (η : f ⟶ g) (n : ℤ) :
    (shiftFunctor (of d a ⟶ of d b) n).map (η : up d f ⟶ up d g) = (shiftFunctor (a ⟶ b) (d * n)).map η := rfl

variable [GradedBicategory B]

instance gradedBicategory : GradedBicategory (Regrade B d) where
  precomp_additive := fun {_ _} c f => inferInstanceAs (precomp (B := B) (as c) (as₁ f)).Additive
  postcomp_additive := fun a {_ _} g =>
    inferInstanceAs (postcomp (B := B) (as a) (as₁ g)).Additive
  shift_additive := fun a b n => inferInstanceAs (shiftFunctor (as a ⟶ as b) (d * n)).Additive
  precomp_commShift := fun {_ _} c f =>
    inferInstanceAs ((PullbackShift.functor (scale d) (precomp (B := B) (as c) (as₁ f))).CommShift ℤ)
  postcomp_commShift := fun a {_ _} g =>
    inferInstanceAs
      ((PullbackShift.functor (scale d) (postcomp (B := B) (as a) (as₁ g))).CommShift ℤ)

instance isLinear (k : Type*) [Field k] [∀ a b : B, Linear k (a ⟶ b)]
    [GradedBicategory.IsLinear B k] : GradedBicategory.IsLinear (Regrade B d) k where
  precomp_linear := fun {_ _} c f => inferInstanceAs ((precomp (B := B) (as c) (as₁ f)).Linear k)
  postcomp_linear := fun a {_ _} g =>
    inferInstanceAs ((postcomp (B := B) (as a) (as₁ g)).Linear k)
  shift_linear := fun a b n => inferInstanceAs ((shiftFunctor (as a ⟶ as b) (d * n)).Linear k)

/-! ### Shifted 2-morphisms -/

section ShiftedHoms

variable {a b c : Regrade B d}

/-- A shifted 2-morphism of degree `n` of `Regrade B d` is a shifted 2-morphism of degree `d n`
of `B`. -/
abbrev toB {X Y : a ⟶ b} {n : ℤ} (f : ShiftedHom X Y n) :
    ShiftedHom (as₁ X) (as₁ Y) (d * n) := f

/-- A shifted 2-morphism of degree `d n` of `B` as one of degree `n` of `Regrade B d`. -/
abbrev ofB {X Y : a ⟶ b} {n : ℤ} (f : ShiftedHom (as₁ X) (as₁ Y) (d * n)) :
    ShiftedHom X Y n := f

theorem shiftFunctorAdd'_inv_app (Z : a ⟶ b) (m n p : ℤ) (h : m + n = p)
    (h' : d * m + d * n = d * p) :
    ((shiftFunctorAdd' (a ⟶ b) m n p h).inv.app Z : Z⟦m⟧⟦n⟧ ⟶ Z⟦p⟧) =
      ((shiftFunctorAdd' (as a ⟶ as b) (d * m) (d * n) (d * p) h').inv.app (as₁ Z) :
        (as₁ Z)⟦d * m⟧⟦d * n⟧ ⟶ (as₁ Z)⟦d * p⟧) := by
  set_option backward.isDefEq.respectTransparency false in
  have := pullbackShiftFunctorAdd'_inv_app (C := (as a ⟶ as b)) (scale d) (as₁ Z) m n p h (d * m)
    (d * n) (d * p) rfl rfl rfl
  set_option backward.isDefEq.respectTransparency false in
  erw [this]
  simp only [pullbackShiftIso, eqToIso.hom, eqToIso.inv, eqToHom_refl]
  erw [NatTrans.id_app, NatTrans.id_app, NatTrans.id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.id_comp, Category.comp_id]

theorem toB_comp {X Y Z : a ⟶ b} {m n p : ℤ} (f : ShiftedHom X Y m)
    (g : ShiftedHom Y Z n) (h : n + m = p) :
    toB d (f.comp g h) = (toB d f).comp (toB d g) (by rw [← h]; ring) := by
  unfold ShiftedHom.comp
  erw [shiftFunctorAdd'_inv_app d Z n m p h (by rw [← h]; ring)]
  rfl

theorem toB_inj {X Y : a ⟶ b} {n : ℤ} {f g : ShiftedHom X Y n} (h : toB d f = toB d g) :
    f = g := h

theorem toB_ofB {X Y : a ⟶ b} {n : ℤ} (f : ShiftedHom (as₁ X) (as₁ Y) (d * n)) :
    toB d (ofB d f) = f := rfl

theorem toB_mk₀ {X Y : a ⟶ b} (x : X ⟶ Y) :
    toB d (ShiftedHom.mk₀ (X := X) (Y := Y) (0 : ℤ) rfl x) =
      ShiftedHom.mk₀ (X := as₁ X) (Y := as₁ Y) (d * 0) (by ring) x := by
  unfold ShiftedHom.mk₀
  simp only [shiftFunctorZero', Iso.trans_inv, NatTrans.comp_app]
  set_option backward.isDefEq.respectTransparency false in
  erw [pullbackShiftFunctorZero_inv_app (C := (as a ⟶ as b)) (scale d) (as₁ Y)]
  simp only [pullbackShiftIso, eqToIso.inv, eqToHom_app, eqToHom_trans, Category.assoc]

theorem toB_smul (k : Type*) [Field k] [∀ a b : B, Linear k (a ⟶ b)]
    {X Y : a ⟶ b} {n : ℤ} (r : k) (f : ShiftedHom X Y n) :
    toB d (r • f) = r • toB d f := rfl

theorem toB_sub {X Y : a ⟶ b} {n : ℤ} (f g : ShiftedHom X Y n) :
    toB d (f - g) = toB d f - toB d g := rfl

theorem precomp_commShiftIso_hom_app (f : a ⟶ b) (g : b ⟶ c) (n : ℤ) :
    (((precomp c f).commShiftIso n).hom.app g : f ≫ g⟦n⟧ ⟶ (f ≫ g)⟦n⟧) =
      (((precomp (as c) (as₁ f)).commShiftIso (d * n)).hom.app (as₁ g) :
        as₁ f ≫ (as₁ g)⟦d * n⟧ ⟶ (as₁ f ≫ as₁ g)⟦d * n⟧) := by
  set_option backward.isDefEq.respectTransparency false in
  erw [Functor.commShiftPullback_iso_eq (scale d) (precomp (as c) (as₁ f)) n (d * n) rfl]
  simp only [pullbackShiftIso, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, eqToIso.hom, eqToHom_refl]
  erw [NatTrans.id_app, NatTrans.id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.comp_id]

theorem postcomp_commShiftIso_hom_app (f : a ⟶ b) (g : b ⟶ c) (n : ℤ) :
    (((postcomp a g).commShiftIso n).hom.app f : f⟦n⟧ ≫ g ⟶ (f ≫ g)⟦n⟧) =
      (((postcomp (as a) (as₁ g)).commShiftIso (d * n)).hom.app (as₁ f) :
        (as₁ f)⟦d * n⟧ ≫ as₁ g ⟶ (as₁ f ≫ as₁ g)⟦d * n⟧) := by
  set_option backward.isDefEq.respectTransparency false in
  erw [Functor.commShiftPullback_iso_eq (scale d) (postcomp (as a) (as₁ g)) n (d * n) rfl]
  simp only [pullbackShiftIso, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, eqToIso.hom, eqToHom_refl]
  erw [NatTrans.id_app, NatTrans.id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.comp_id]

theorem whiskerLeftShiftIso_hom (f : a ⟶ b) (g : b ⟶ c) (n : ℤ) :
    ((whiskerLeftShiftIso f g n).hom : f ≫ g⟦n⟧ ⟶ (f ≫ g)⟦n⟧) =
      ((whiskerLeftShiftIso (as₁ f) (as₁ g) (d * n)).hom :
        as₁ f ≫ (as₁ g)⟦d * n⟧ ⟶ (as₁ f ≫ as₁ g)⟦d * n⟧) :=
  precomp_commShiftIso_hom_app d f g n

theorem whiskerRightShiftIso_hom (f : a ⟶ b) (g : b ⟶ c) (n : ℤ) :
    ((whiskerRightShiftIso f g n).hom : f⟦n⟧ ≫ g ⟶ (f ≫ g)⟦n⟧) =
      ((whiskerRightShiftIso (as₁ f) (as₁ g) (d * n)).hom :
        (as₁ f)⟦d * n⟧ ≫ as₁ g ⟶ (as₁ f ≫ as₁ g)⟦d * n⟧) :=
  postcomp_commShiftIso_hom_app d f g n

theorem toB_shWhiskerLeft (f : a ⟶ b) {g h : b ⟶ c} {n : ℤ}
    (η : ShiftedHom g h n) :
    toB d (shWhiskerLeft f η) = shWhiskerLeft (as₁ f) (toB d η) := by
  unfold shWhiskerLeft ShiftedHom.map
  erw [precomp_commShiftIso_hom_app d f h n]
  rfl

theorem toB_shWhiskerRight {f g : a ⟶ b} {n : ℤ} (η : ShiftedHom f g n)
    (h : b ⟶ c) :
    toB d (shWhiskerRight η h) = shWhiskerRight (toB d η) (as₁ h) := by
  unfold shWhiskerRight ShiftedHom.map
  erw [postcomp_commShiftIso_hom_app d g h n]
  rfl

end ShiftedHoms

/-! ### Shift coherence -/

section Coherence

instance shiftInterchange [GradedBicategory.ShiftInterchange B] :
    GradedBicategory.ShiftInterchange (Regrade B d) where
  whiskerRightShiftIso_natural := fun {_ _ _} f {g g'} θ m => by
    erw [whiskerRightShiftIso_hom d f g m, whiskerRightShiftIso_hom d f g' m]
    exact GradedBicategory.ShiftInterchange.whiskerRightShiftIso_natural (B := B) (as₁ f) θ (d * m)
  whiskerLeftShiftIso_natural := fun {_ _ _} {f f'} η g n => by
    erw [whiskerLeftShiftIso_hom d f g n, whiskerLeftShiftIso_hom d f' g n]
    exact GradedBicategory.ShiftInterchange.whiskerLeftShiftIso_natural (B := B) η (as₁ g) (d * n)
  shift_shift := fun {_ _ _} f g m n => by
    have key : ∀ (p : ℤ) (hp : d * n + d * m = p) (hp' : d * m + d * n = p),
        (whiskerRightShiftIso (as₁ f) ((as₁ g)⟦d * n⟧) (d * m)).hom ≫
            (whiskerLeftShiftIso (as₁ f) (as₁ g) (d * n)).hom⟦d * m⟧' ≫
            (shiftFunctorAdd' _ (d * n) (d * m) p hp).inv.app (as₁ f ≫ as₁ g) =
          (whiskerLeftShiftIso ((as₁ f)⟦d * m⟧) (as₁ g) (d * n)).hom ≫
            (whiskerRightShiftIso (as₁ f) (as₁ g) (d * m)).hom⟦d * n⟧' ≫
            (shiftFunctorAdd' _ (d * m) (d * n) p hp').inv.app (as₁ f ≫ as₁ g) := by
      intro p hp hp'
      subst hp
      exact GradedBicategory.ShiftInterchange.shift_shift (B := B) (as₁ f) (as₁ g) (d * m) (d * n)
    erw [whiskerRightShiftIso_hom d f (g⟦n⟧) m, whiskerLeftShiftIso_hom d f g n,
      whiskerLeftShiftIso_hom d (f⟦m⟧) g n, whiskerRightShiftIso_hom d f g m,
      shiftFunctorAdd'_inv_app d (f ≫ g) n m (n + m) rfl (by ring),
      shiftFunctorAdd'_inv_app d (f ≫ g) m n (n + m) (add_comm m n) (by ring)]
    exact key _ _ _

instance shiftAssoc [GradedBicategory.ShiftAssoc B] : GradedBicategory.ShiftAssoc (Regrade B d) where
  assoc_shift := fun {_ _ _ _} f g h n => by
    erw [whiskerLeftShiftIso_hom d g h n, whiskerLeftShiftIso_hom d f (g ≫ h) n,
      whiskerLeftShiftIso_hom d (f ≫ g) h n]
    exact GradedBicategory.ShiftAssoc.assoc_shift (B := B) (as₁ f) (as₁ g) (as₁ h) (d * n)

instance shiftAssocMid [GradedBicategory.ShiftAssocMid B] :
    GradedBicategory.ShiftAssocMid (Regrade B d) where
  assoc_shift_mid := fun {_ _ _ _} f g h n => by
    erw [whiskerRightShiftIso_hom d g h n, whiskerLeftShiftIso_hom d f (g ≫ h) n,
      whiskerLeftShiftIso_hom d f g n, whiskerRightShiftIso_hom d (f ≫ g) h n]
    exact GradedBicategory.ShiftAssocMid.assoc_shift_mid (B := B) (as₁ f) (as₁ g) (as₁ h) (d * n)

instance shiftAssocRight [GradedBicategory.ShiftAssocRight B] :
    GradedBicategory.ShiftAssocRight (Regrade B d) where
  assoc_shift_right := fun {_ _ _ _} f g h n => by
    erw [whiskerRightShiftIso_hom d f g n, whiskerRightShiftIso_hom d (f ≫ g) h n,
      whiskerRightShiftIso_hom d f (g ≫ h) n]
    exact GradedBicategory.ShiftAssocRight.assoc_shift_right (B := B) (as₁ f) (as₁ g) (as₁ h)
      (d * n)

instance shiftUnitor [GradedBicategory.ShiftUnitor B] :
    GradedBicategory.ShiftUnitor (Regrade B d) where
  leftUnitor_shift := fun {a _} g n => by
    erw [whiskerLeftShiftIso_hom d (𝟙 a) g n]
    exact GradedBicategory.ShiftUnitor.leftUnitor_shift (B := B) (as₁ g) (d * n)
  rightUnitor_shift := fun {_ b} f n => by
    erw [whiskerRightShiftIso_hom d f (𝟙 b) n]
    exact GradedBicategory.ShiftUnitor.rightUnitor_shift (B := B) (as₁ f) (d * n)

instance shiftCoherence [GradedBicategory.ShiftCoherence B] :
    GradedBicategory.ShiftCoherence (Regrade B d) where

end Coherence

/-! ### The comparison of graded-Hom bicategories -/

section Comparison

open GradedHomCat

variable {a b : Regrade B d}

/-- `toB` as an additive map. -/
def toBHom (X Y : a ⟶ b) (n : ℤ) :
    ShiftedHom X Y n →+ ShiftedHom (as₁ X) (as₁ Y) (d * n) where
  toFun := toB d
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The comparison on graded 2-morphisms: the homogeneous component of degree `n` goes to
degree `d n`. -/
def compMap₂ (X Y : a ⟶ b) :
    ((mk X : GradedHomCat (a ⟶ b)) ⟶ mk Y) →+
      ((mk (as₁ X) : GradedHomCat (as a ⟶ as b)) ⟶ mk (as₁ Y)) :=
  DirectSum.toAddMonoid fun n =>
    (DirectSum.of (fun m : ℤ => ShiftedHom (as₁ X) (as₁ Y) m) (d * n)).comp (toBHom d X Y n)

theorem compMap₂_homOf {X Y : a ⟶ b} (n : ℤ) (f : ShiftedHom X Y n) :
    compMap₂ d X Y (homOf n f) = homOf (d * n) (toB d f) :=
  DirectSum.toAddMonoid_of _ _ _

theorem homOf_mk₀ {X Y : as a ⟶ as b} {m : ℤ} (hm : m = 0) (x : X ⟶ Y) :
    (homOf m (ShiftedHom.mk₀ m hm x) : (mk X : GradedHomCat (as a ⟶ as b)) ⟶ mk Y) =
      homOf 0 (ShiftedHom.mk₀ (0 : ℤ) rfl x) := by
  subst hm; rfl

theorem compMap₂_incl {X Y : a ⟶ b} (x : X ⟶ Y) :
    compMap₂ d X Y ((incl (a ⟶ b)).map x) = (incl (as a ⟶ as b)).map (as₂ x) := by
  rw [incl_map, compMap₂_homOf, toB_mk₀ d x]
  exact homOf_mk₀ d (X := as₁ X) (Y := as₁ Y) _ (as₂ x)

theorem compMap₂_id (X : a ⟶ b) :
    compMap₂ d X X (𝟙 (mk X : GradedHomCat (a ⟶ b))) = 𝟙 (mk (as₁ X)) := by
  rw [GradedHomCat.id_eq, compMap₂_homOf, toB_mk₀ d (𝟙 X)]
  exact homOf_mk₀ d (X := as₁ X) (Y := as₁ X) _ (𝟙 (as₁ X))

theorem compMap₂_comp {X Y Z : a ⟶ b}
    (η : (mk X : GradedHomCat (a ⟶ b)) ⟶ mk Y)
    (θ : (mk Y : GradedHomCat (a ⟶ b)) ⟶ mk Z) :
    compMap₂ d X Z (η ≫ θ) = compMap₂ d X Y η ≫ compMap₂ d Y Z θ := by
  induction η using hom_induction with
  | zero => rw [Limits.zero_comp, map_zero, map_zero, Limits.zero_comp]
  | add φ ψ hφ hψ => rw [Preadditive.add_comp, map_add, map_add, hφ, hψ, Preadditive.add_comp]
  | homOf m f =>
    induction θ using hom_induction with
    | zero => rw [Limits.comp_zero, map_zero, map_zero, Limits.comp_zero]
    | add φ ψ hφ hψ => rw [Preadditive.comp_add, map_add, map_add, hφ, hψ, Preadditive.comp_add]
    | homOf n g =>
      rw [homOf_comp_homOf f g rfl, compMap₂_homOf, compMap₂_homOf, compMap₂_homOf,
        homOf_comp_homOf (toB d f) (toB d g) (by ring : d * n + d * m = d * (n + m)),
        toB_comp d f g rfl]

theorem compMap₂_smul (k : Type*) [Field k] [∀ a b : B, Linear k (a ⟶ b)]
    [GradedBicategory.IsLinear B k] {X Y : a ⟶ b} (r : k)
    (η : (mk X : GradedHomCat (a ⟶ b)) ⟶ mk Y) :
    compMap₂ d X Y (r • η) = r • compMap₂ d X Y η := by
  induction η using hom_induction with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add φ ψ hφ hψ => rw [smul_add, map_add, map_add, hφ, hψ, smul_add]
  | homOf n f =>
    rw [← homOf_smul, compMap₂_homOf, compMap₂_homOf, ← homOf_smul]
    rfl

theorem compMap₂_whiskerLeft {c : Regrade B d} (f : a ⟶ b) {g h : b ⟶ c}
    (η : (mk g : GradedHomCat (b ⟶ c)) ⟶ mk h) :
    compMap₂ d (f ≫ g) (f ≫ h) (GradedHomBicat.whiskerLeftHom f g h η) =
      GradedHomBicat.whiskerLeftHom (as₁ f) (as₁ g) (as₁ h) (compMap₂ d g h η) := by
  induction η using hom_induction with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]; rfl
  | add φ ψ hφ hψ => rw [map_add, map_add, map_add, map_add, hφ, hψ]; rfl
  | homOf n e =>
    rw [GradedHomBicat.whiskerLeftHom_homOf, compMap₂_homOf, compMap₂_homOf,
      GradedHomBicat.whiskerLeftHom_homOf, toB_shWhiskerLeft]
    rfl

theorem compMap₂_whiskerRight {c : Regrade B d} {f g : a ⟶ b} (h : b ⟶ c)
    (η : (mk f : GradedHomCat (a ⟶ b)) ⟶ mk g) :
    compMap₂ d (f ≫ h) (g ≫ h) (GradedHomBicat.whiskerRightHom f g h η) =
      GradedHomBicat.whiskerRightHom (as₁ f) (as₁ g) (as₁ h) (compMap₂ d f g η) := by
  induction η using hom_induction with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]; rfl
  | add φ ψ hφ hψ => rw [map_add, map_add, map_add, map_add, hφ, hψ]; rfl
  | homOf n e =>
    rw [GradedHomBicat.whiskerRightHom_homOf, compMap₂_homOf, compMap₂_homOf,
      GradedHomBicat.whiskerRightHom_homOf, toB_shWhiskerRight]
    rfl

variable [GradedBicategory.ShiftCoherence B]

omit [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [GradedBicategory.ShiftCoherence B] in
theorem eqToHom_conj_self {C : Type*} [Category C] {X Y : C} (p : X = X) (q : Y = Y) (x : X ⟶ Y) :
    eqToHom p ≫ x ≫ eqToHom q = x := by
  simp

omit [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [GradedBicategory.ShiftCoherence B] in
theorem eqToHom_comp_self {C : Type*} [Category C] {X Y : C} (p : X = X) (x : X ⟶ Y) :
    eqToHom p ≫ x = x := by
  simp

/-- **The comparison strict pseudofunctor** `K^•(Regrade B d) → K^•(B)`: the identity on objects
and 1-morphisms; a homogeneous 2-morphism of degree `n` goes to the same 2-morphism, of degree
`d n`. -/
def comparison : StrictPseudofunctor (GradedHomBicat (Regrade B d)) (GradedHomBicat B) :=
  StrictPseudofunctor.mk' {
    obj := fun a => GradedHomBicat.of (B := B) (as (GradedHomBicat.as a))
    map := fun {a b} f =>
      GradedHomCat.mk (as₁ (a := GradedHomBicat.as a) (b := GradedHomBicat.as b) f.as)
    map₂ := fun {_ _} {f g} η => compMap₂ d f.as g.as η
    map₂_id := fun {_ _} f => compMap₂_id d f.as
    map₂_comp := fun {_ _} {_ _ _} η θ => compMap₂_comp d η θ
    map₂_whisker_left := fun {_ _ _} f {g h} η => by
      exact (compMap₂_whiskerLeft d f.as η).trans (eqToHom_conj_self _ _ _).symm
    map₂_whisker_right := fun {_ _ _} {f g} η h => by
      exact (compMap₂_whiskerRight d h.as η).trans (eqToHom_conj_self _ _ _).symm
    map₂_left_unitor := fun {_ _} f => by
      exact (compMap₂_incl d (λ_ f.as).hom).trans (eqToHom_comp_self _ _).symm
    map₂_right_unitor := fun {_ _} f => by
      exact (compMap₂_incl d (ρ_ f.as).hom).trans (eqToHom_comp_self _ _).symm
    map₂_associator := fun {_ _ _ _} f g h => by
      exact (compMap₂_incl d (α_ f.as g.as h.as).hom).trans (eqToHom_conj_self _ _ _).symm }

theorem comparison_map {a b : GradedHomBicat (Regrade B d)} (f : a ⟶ b) :
    (comparison d).map f =
      GradedHomCat.mk (as₁ (a := GradedHomBicat.as a) (b := GradedHomBicat.as b) f.as) := rfl

theorem comparison_map₂_of₂ {f g : a ⟶ b} (n : ℤ) (η : ShiftedHom f g n) :
    (comparison d).map₂ (GradedHomBicat.of₂ n η) = GradedHomBicat.of₂ (d * n) (toB d η) :=
  compMap₂_homOf d n η

theorem comparison_map₂_smul (k : Type*) [Field k] [∀ a b : B, Linear k (a ⟶ b)]
    [GradedBicategory.IsLinear B k] {a b : GradedHomBicat (Regrade B d)} {f g : a ⟶ b} (r : k)
    (η : f ⟶ g) : (comparison d).map₂ (r • η) = r • (comparison d).map₂ η :=
  compMap₂_smul d k r η

end Comparison

end Instances

end Regrade

end Categorification.TwoRep
