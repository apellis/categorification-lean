/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Shift.ShiftedHomOpposite
import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
import Categorification.TwoRep.ShiftInterchange

/-!
# The bidual `Bᶜᵒᵒᵖ` of a graded bicategory

The *bidual* (or `coop`) of a bicategory `B` has the same objects, 1-morphisms `a ⟶ b` the
1-morphisms `b ⟶ a` of `B`, and 2-morphisms `f ⟶ g` the 2-morphisms `g ⟶ f` of `B`: both 1-cells
and 2-cells are reversed, and horizontal composition is `f ≫' g = g ≫ f`. (Mathlib has the 1-cell
dual `Bᵒᵖ`, `Mathlib.CategoryTheory.Bicategory.Opposites`, whose docstring lists `Bᶜᵒᵒᵖ` as a TODO.)
Its Hom categories are the opposite categories `(B(b, a))ᵒᵖ`.

For a graded bicategory (`GradedBicategory`, CL §2.1.2) the Hom categories of the bidual carry the
**inverted** grading shift: `X⟨d⟩' = X⟨-d⟩` (the shift on `Cᵒᵖ` of
`Mathlib.CategoryTheory.Triangulated.Opposite.Basic`, "shifting by `n` on `Cᵒᵖ` corresponds to the
shift by `-n` on `C`"). With this choice degrees are preserved and only the direction of maps
flips: `Hom'(X, Y⟨d⟩') = Hom(Y, X⟨d⟩)` (`Coop.finrank_hom_shift`). With the uninverted shift all
degrees would change sign.

This is the duality `D(K) = K^coop` used to transport statements about the weights `n ≤ 0` of a
strong 2-representation of `sl₂` to statements about the weights `n ≥ 0` (`Duality.lean`):
`Hom'^d(X, Y) = Hom^d(Y, X)`.

## Main declarations

* `oppositeLinear`, `oppositeHomFinite`: the opposite of a `k`-linear (Hom-finite) category;
* `unop_shift_map`, `unop_shiftFunctorAdd'_inv_app`, `unop_op_commShiftIso_hom_app`: the inverted
  shift of an opposite category in terms of the shift of the category;
* `shiftedHom_opEquiv_comp`, `shiftedHom_opEquiv_mk₀`, `shiftedHom_opEquiv_map`,
  `shiftedHomOpAddEquiv`: Mathlib's `ShiftedHom.opEquiv` reverses composition, preserves degree-zero
  morphisms and sums, and commutes with functors commuting with the shift;
* `shConj`, `shConj_comp`: conjugation of shifted endomorphisms by an isomorphism;
* `nonempty_lsum_iso_of_perm`, `opLsumIso`, `nonempty_qsum_op_iso`: `⊕_{[n]}` commutes with the
  passage to the opposite category (the shifts of `[n]` are symmetric);
* `Coop B`, `Coop.bicategory`: the bidual bicategory; `Coop.op1`, `Coop.op2`;
* the Hom-category instances of `Coop B` (preadditive, `k`-linear, inverted shift, zero object,
  binary biproducts, idempotent completeness, Hom-finiteness);
* `Coop.gradedBicategory`, `Coop.isLinear`, `Coop.shiftInterchange`: the graded structure and its
  mixins transfer to the bidual;
* `Coop.adjunction`: an adjunction `u ⊣ v` in `B` gives `op u ⊣ op v` in `Coop B`, with unit the
  counit of `u ⊣ v` and counit its unit; `Coop.adjunctionUnop` is the converse;
* `Coop.finrank_hom`, `Coop.finrank_hom_shift`: dimensions of Hom spaces in the bidual (degrees
  are preserved);
* `Coop.shOp` (shifted 2-morphisms of the bidual), `Coop.shOp_comp`, `Coop.shOp_mk₀`,
  `Coop.shOp_shWhiskerLeft`, `Coop.shOp_shWhiskerRight`, `Coop.shOp_shConj_symm`.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Module Opposite
open KrullSchmidtCat (HomFinite)

universe w v u

/-! ## Opposites of `k`-linear categories -/

section OppositeLinear

variable (k : Type*) [Field k] (C : Type*) [Category C] [Preadditive C] [Linear k C]

/-- The opposite of a `k`-linear category is `k`-linear, with `r • f = (r • f.unop).op`. -/
instance oppositeLinear : Linear k Cᵒᵖ where
  homModule X Y :=
    { smul := fun r f => (r • f.unop).op
      one_smul := fun f => Quiver.Hom.unop_inj (one_smul k f.unop)
      mul_smul := fun r s f => Quiver.Hom.unop_inj (mul_smul r s f.unop)
      smul_zero := fun r => Quiver.Hom.unop_inj (smul_zero (A := Y.unop ⟶ X.unop) r)
      smul_add := fun r f g => Quiver.Hom.unop_inj (smul_add r f.unop g.unop)
      add_smul := fun r s f => Quiver.Hom.unop_inj (add_smul r s f.unop)
      zero_smul := fun f => Quiver.Hom.unop_inj (zero_smul k f.unop) }
  smul_comp _ _ _ r f g := Quiver.Hom.unop_inj (Linear.comp_smul _ _ _ g.unop r f.unop)
  comp_smul _ _ _ f r g := Quiver.Hom.unop_inj (Linear.smul_comp _ _ _ r g.unop f.unop)

variable {k C}

@[simp] theorem unop_smul' {X Y : Cᵒᵖ} (r : k) (f : X ⟶ Y) : (r • f).unop = r • f.unop := rfl

@[simp] theorem op_smul' {X Y : C} (r : k) (f : X ⟶ Y) : (r • f).op = r • f.op := rfl

variable (k) in
/-- `Hom_{Cᵒᵖ}(op Y, op X) ≅ Hom_C(X, Y)`, `k`-linearly. -/
def opHomLinearEquiv (X Y : C) : (X ⟶ Y) ≃ₗ[k] (op Y ⟶ op X) where
  toFun f := f.op
  invFun f := f.unop
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

instance oppositeHomFinite [HomFinite k C] : HomFinite k Cᵒᵖ where
  finiteDimensional X Y :=
    LinearEquiv.finiteDimensional (opHomLinearEquiv k Y.unop X.unop)

variable (k) in
theorem finrank_op_hom (X Y : C) : finrank k (op Y ⟶ op X) = finrank k (X ⟶ Y) :=
  (opHomLinearEquiv k X Y).finrank_eq.symm

/-- The opposite of a `k`-linear functor is `k`-linear. -/
instance functor_op_linear {D : Type*} [Category D] [Preadditive D] [Linear k D] (F : C ⥤ D)
    [F.Linear k] : F.op.Linear k where
  map_smul := by intros; exact Quiver.Hom.unop_inj (by simp)

end OppositeLinear

/-! ## The inverted shift on an opposite category -/

section OppositeShift

open Pretriangulated Pretriangulated.Opposite

variable {C : Type*} [Category C] [HasShift C ℤ]

theorem shiftFunctorOpIso_hom_app_neg (X : Cᵒᵖ) (n : ℤ) :
    (shiftFunctorOpIso C n (-n) (add_neg_cancel n)).hom.app X = 𝟙 _ := rfl

theorem shiftFunctorOpIso_inv_app_neg (X : Cᵒᵖ) (n : ℤ) :
    (shiftFunctorOpIso C n (-n) (add_neg_cancel n)).inv.app X = 𝟙 _ := rfl

/-- The shift of a morphism of `Cᵒᵖ` (inverted shift) is the opposite of its shift in `C`. -/
theorem unop_shift_map {X Y : Cᵒᵖ} (φ : X ⟶ Y) (n : ℤ) : (φ⟦n⟧').unop = (φ.unop)⟦-n⟧' := rfl

theorem unop_shiftFunctorAdd'_inv_app (X : Cᵒᵖ) (a₁ a₂ a₃ : ℤ) (h : a₁ + a₂ = a₃) :
    ((shiftFunctorAdd' Cᵒᵖ a₁ a₂ a₃ h).inv.app X).unop =
      (shiftFunctorAdd' C (-a₁) (-a₂) (-a₃) (by omega)).hom.app X.unop := by
  rw [shiftFunctorAdd'_op_inv_app X a₁ a₂ a₃ h (-a₁) (-a₂) (-a₃) (add_neg_cancel _)
    (add_neg_cancel _) (add_neg_cancel _), shiftFunctorOpIso_hom_app_neg,
    shiftFunctorOpIso_hom_app_neg, shiftFunctorOpIso_inv_app_neg]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp, Category.comp_id]
  rfl

/-- The commutation isomorphism of `F.op` with the inverted shifts is the inverse of that of
`F`. -/
theorem unop_op_commShiftIso_hom_app {D : Type*} [Category D] [HasShift D ℤ] (F : C ⥤ D)
    [F.CommShift ℤ] (X : Cᵒᵖ) (n : ℤ) :
    ((F.op.commShiftIso n).hom.app X).unop = (F.commShiftIso (-n)).inv.app X.unop := by
  rw [F.op_commShiftIso_hom_app X n (-n) (add_neg_cancel n), shiftFunctorOpIso_hom_app_neg,
    shiftFunctorOpIso_inv_app_neg]
  erw [unop_id, CategoryTheory.Functor.map_id, op_id, Category.id_comp, Category.comp_id]
  rfl

/-! ### Shifted morphisms of an opposite category -/

/-- `ShiftedHom.opEquiv` reverses composition. -/
theorem shiftedHom_opEquiv_comp {X Y Z : C} {a b c : ℤ} (f : ShiftedHom X Y a)
    (g : ShiftedHom Y Z b) (h : b + a = c) :
    ShiftedHom.opEquiv c (f.comp g h) =
      (ShiftedHom.opEquiv b g).comp (ShiftedHom.opEquiv a f) (by omega) := by
  apply (ShiftedHom.opEquiv c).symm.injective
  rw [Equiv.symm_apply_apply, ShiftedHom.opEquiv_symm_comp _ _ (by omega : a + b = c),
    Equiv.symm_apply_apply, Equiv.symm_apply_apply]

theorem shiftedHom_opEquiv_symm_mk₀ {X Y : C} (f : X ⟶ Y) :
    (ShiftedHom.opEquiv (0 : ℤ)).symm (ShiftedHom.mk₀ (0 : ℤ) rfl f.op) =
      ShiftedHom.mk₀ (0 : ℤ) rfl f := by
  rw [ShiftedHom.opEquiv_symm_apply, opShiftFunctorEquivalence_zero_unitIso_inv_app]
  simp only [ShiftedHom.mk₀, shiftFunctorZero', unop_comp, Quiver.Hom.unop_op, Opposite.unop_op,
    Functor.map_comp, eqToIso_refl, Iso.refl_trans, Category.assoc]
  rw [← Functor.map_comp_assoc, ← unop_comp, Iso.inv_hom_id_app]
  simpa using ((shiftFunctorZero C ℤ).inv.naturality f).symm

/-- `ShiftedHom.opEquiv` preserves morphisms of degree zero. -/
theorem shiftedHom_opEquiv_mk₀ {X Y : C} (f : X ⟶ Y) :
    ShiftedHom.opEquiv (0 : ℤ) (ShiftedHom.mk₀ (0 : ℤ) rfl f) =
      ShiftedHom.mk₀ (0 : ℤ) rfl f.op := by
  apply (ShiftedHom.opEquiv (0 : ℤ)).symm.injective
  rw [Equiv.symm_apply_apply, shiftedHom_opEquiv_symm_mk₀]

theorem shiftedHom_opEquiv_symm_map {D : Type*} [Category D] [HasShift D ℤ] (F : C ⥤ D)
    [F.CommShift ℤ] {X Y : C} {n : ℤ} (η : ShiftedHom (op Y) (op X) n) :
    (ShiftedHom.opEquiv n).symm (η.map F.op) = ((ShiftedHom.opEquiv n).symm η).map F := by
  rw [ShiftedHom.opEquiv_symm_apply, ShiftedHom.opEquiv_symm_apply]
  simp only [ShiftedHom.map, Functor.map_comp, unop_comp, Functor.op_map, Quiver.Hom.unop_op,
    Category.assoc]
  rw [F.map_opShiftFunctorEquivalence_unitIso_inv_app_unop (op X) n]
  simp only [Category.assoc]
  congr 2
  rw [F.commShiftIso_hom_naturality]
  exact (Iso.inv_hom_id_app_assoc (F.commShiftIso n) _ _).symm

/-- `ShiftedHom.opEquiv` is compatible with the action of a functor commuting with the shift. -/
theorem shiftedHom_opEquiv_map {D : Type*} [Category D] [HasShift D ℤ] (F : C ⥤ D)
    [F.CommShift ℤ] {X Y : C} {n : ℤ} (η : ShiftedHom X Y n) :
    ShiftedHom.opEquiv n (η.map F) = (ShiftedHom.opEquiv n η).map F.op := by
  apply (ShiftedHom.opEquiv n).symm.injective
  rw [Equiv.symm_apply_apply, shiftedHom_opEquiv_symm_map, Equiv.symm_apply_apply]

/-- `ShiftedHom.opEquiv` as an additive equivalence. -/
def shiftedHomOpAddEquiv [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] (X Y : C)
    (n : ℤ) : ShiftedHom X Y n ≃+ ShiftedHom (op Y) (op X) n :=
  AddEquiv.symm
    { (ShiftedHom.opEquiv n).symm with
      map_add' := fun x y => ShiftedHom.opEquiv_symm_add x y }

@[simp] theorem shiftedHomOpAddEquiv_apply [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    {X Y : C} {n : ℤ} (f : ShiftedHom X Y n) :
    shiftedHomOpAddEquiv X Y n f = ShiftedHom.opEquiv n f := rfl

/-! ### Conjugation of shifted endomorphisms -/

/-- Conjugation of a shifted endomorphism of `X` by an isomorphism `e : X ≅ Y`: first `e⁻¹`, then
`f`, then `e`. -/
def shConj {X Y : C} (e : X ≅ Y) {n : ℤ} (f : ShiftedHom X X n) : ShiftedHom Y Y n :=
  (ShiftedHom.mk₀ (0 : ℤ) rfl e.inv).comp (f.comp (ShiftedHom.mk₀ (0 : ℤ) rfl e.hom) (zero_add n))
    (add_zero n)

theorem shConj_eq {X Y : C} (e : X ≅ Y) {n : ℤ} (f : ShiftedHom X X n) :
    shConj e f = e.inv ≫ f ≫ e.hom⟦n⟧' := by
  rw [shConj, ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀]

/-- Conjugation is multiplicative. -/
theorem shConj_comp {X Y : C} (e : X ≅ Y) {a b c : ℤ} (f : ShiftedHom X X a)
    (g : ShiftedHom X X b) (h : b + a = c) :
    shConj e (f.comp g h) = (shConj e f).comp (shConj e g) h := by
  simp only [shConj_eq, ShiftedHom.comp, Category.assoc, Functor.map_comp]
  have nat := (shiftFunctorAdd' C b a c h).inv.naturality e.hom
  simp only [Functor.comp_map] at nat
  rw [← nat]
  simp

theorem shConj_symm_shConj {X Y : C} (e : X ≅ Y) {n : ℤ} (f : ShiftedHom X X n) :
    shConj e.symm (shConj e f) = f := by
  simp [shConj_eq]

theorem shConj_neg [Preadditive C] {X Y : C} (e : X ≅ Y) {n : ℤ} (f : ShiftedHom X X n) :
    shConj e (-f) = -shConj e f := by
  simp [shConj_eq]

end OppositeShift

/-! ## Direct sums in an opposite category -/

section OpSums

open Pretriangulated Pretriangulated.Opposite

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]

/-- Permuted lists have isomorphic sums. -/
theorem nonempty_lsum_iso_of_perm {L L' : List C} (h : L.Perm L') :
    Nonempty (lsum L ≅ lsum L') := by
  induction h with
  | nil => exact ⟨Iso.refl _⟩
  | cons X _ ih =>
    obtain ⟨e⟩ := ih
    exact ⟨biprod.mapIso (Iso.refl X) e⟩
  | swap X Y L =>
    exact ⟨(biprod.associator Y X (lsum L)).symm ≪≫
      biprod.mapIso (biprod.braiding Y X) (Iso.refl _) ≪≫ biprod.associator X Y (lsum L)⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨e₁⟩ := ih₁
    obtain ⟨e₂⟩ := ih₂
    exact ⟨e₁ ≪≫ e₂⟩

/-- `op (X₁ ⊕ ⋯ ⊕ Xₙ) ≅ op X₁ ⊕ ⋯ ⊕ op Xₙ`. -/
def opLsumIso : ∀ L : List C, op (lsum L) ≅ lsum (L.map op)
  | [] => (isZero_zero C).op.isoZero
  | X :: L => biprod.opIso X (lsum L) ≪≫ biprod.mapIso (Iso.refl _) (opLsumIso L)

variable [HasShift C ℤ]

omit [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C] in
theorem qsum_list_reverse (d : ℤ) (n : ℕ) (X : C) :
    ((List.range n).map fun j : ℕ => X⟦d * ((n : ℤ) - 1 - 2 * (j : ℤ))⟧).reverse =
      (List.range n).map fun j : ℕ => X⟦-(d * ((n : ℤ) - 1 - 2 * (j : ℤ)))⟧ := by
  rw [← List.map_reverse, List.range_eq_range', List.reverse_range', List.map_map,
    ← List.range_eq_range']
  apply List.map_congr_left
  intro i hi
  have hi' : i < n := by simpa using hi
  have h : ((0 + n - 1 - i : ℕ) : ℤ) = (n : ℤ) - 1 - i := by omega
  simp only [Function.comp_apply]
  exact congrArg (fun m : ℤ => X⟦m⟧) (by rw [h]; ring)

/-- **`⊕_{[n]}` commutes with the passage to the opposite category** (with the inverted shift):
the multiset of shifts of `[n]` is symmetric. -/
theorem nonempty_qsum_op_iso (d : ℤ) (n : ℕ) (X : C) :
    Nonempty (qsum d n (op X) ≅ op (qsum d n X)) := by
  obtain ⟨e⟩ := nonempty_lsum_iso_of_perm
    (List.reverse_perm ((List.range n).map fun j : ℕ => X⟦d * ((n : ℤ) - 1 - 2 * (j : ℤ))⟧))
  rw [qsum_list_reverse] at e
  have h1 : qsum d n (op X) =
      lsum (((List.range n).map fun j : ℕ => X⟦-(d * ((n : ℤ) - 1 - 2 * (j : ℤ)))⟧).map op) := by
    rw [List.map_map]; rfl
  exact ⟨eqToIso h1 ≪≫ (opLsumIso _).symm ≪≫ e.symm.op⟩

end OpSums

/-! ## The bidual bicategory -/

/-- **The bidual `Bᶜᵒᵒᵖ` of a bicategory** (type synonym): 1-morphisms and 2-morphisms reversed. -/
def Coop (B : Type u) : Type u := B

namespace Coop

variable {B : Type u} [Bicategory.{w, v} B]

/-- An object of `B` as an object of the bidual. -/
def toCoop (a : B) : Coop B := a

/-- An object of the bidual as an object of `B`. -/
def ofCoop (a : Coop B) : B := a

omit [Bicategory B] in
@[simp] theorem ofCoop_toCoop (a : B) : ofCoop (toCoop a) = a := rfl

omit [Bicategory B] in
@[simp] theorem toCoop_ofCoop (a : Coop B) : toCoop (ofCoop a) = a := rfl

/-- **The bidual bicategory.** A 1-morphism `a ⟶ b` is `op f` for `f : b ⟶ a` in `B`; `f ≫' g`
is `op (g.unop ≫ f.unop)`; the Hom category `a ⟶ b` is `(b ⟶ a)ᵒᵖ`, so a 2-morphism
`op f ⟶ op g` is `η.op` for `η : g ⟶ f` in `B`. Whiskering and the coherence isomorphisms are
the opposites of those of `B`, with left and right exchanged. -/
instance bicategory : Bicategory.{w, v} (Coop B) where
  Hom a b := (ofCoop b ⟶ ofCoop a)ᵒᵖ
  id a := op (𝟙 (ofCoop a))
  comp f g := op (g.unop ≫ f.unop)
  homCategory a b := inferInstanceAs (Category (ofCoop b ⟶ ofCoop a)ᵒᵖ)
  whiskerLeft f _ _ η := (η.unop ▷ f.unop).op
  whiskerRight η h := (h.unop ◁ η.unop).op
  associator f g h := (α_ h.unop g.unop f.unop).op
  leftUnitor f := (ρ_ f.unop).symm.op
  rightUnitor f := (λ_ f.unop).symm.op
  whiskerLeft_id _ _ := Quiver.Hom.unop_inj (by simp)
  whiskerLeft_comp _ _ _ _ _ _ := Quiver.Hom.unop_inj (by simp)
  id_whiskerLeft _ := Quiver.Hom.unop_inj (by simp)
  comp_whiskerLeft _ _ _ _ _ := Quiver.Hom.unop_inj (by simp)
  id_whiskerRight _ _ := Quiver.Hom.unop_inj (by simp)
  comp_whiskerRight _ _ _ := Quiver.Hom.unop_inj (by simp)
  whiskerRight_id _ := Quiver.Hom.unop_inj (by simp)
  whiskerRight_comp _ _ _ := Quiver.Hom.unop_inj (by simp)
  whisker_assoc _ _ _ _ _ := Quiver.Hom.unop_inj (by simp)
  whisker_exchange _ _ := Quiver.Hom.unop_inj (by simp [whisker_exchange])
  pentagon _ _ _ _ := Quiver.Hom.unop_inj (by simp)
  triangle _ _ := Quiver.Hom.unop_inj (by simp)

/-- A 1-morphism `f : a ⟶ b` of `B` as a 1-morphism `b ⟶ a` of the bidual. -/
abbrev op1 {a b : B} (f : a ⟶ b) : toCoop b ⟶ toCoop a := op f

/-- A 2-morphism `η : f ⟶ g` of `B` as a 2-morphism `op1 g ⟶ op1 f` of the bidual. -/
abbrev op2 {a b : B} {f g : a ⟶ b} (η : f ⟶ g) : op1 g ⟶ op1 f := η.op

@[simp] theorem id_def (a : Coop B) : 𝟙 a = op (𝟙 (ofCoop a)) := rfl

@[simp] theorem comp_def {a b c : Coop B} (f : a ⟶ b) (g : b ⟶ c) : f ≫ g = op (g.unop ≫ f.unop) :=
  rfl

@[simp] theorem unop_comp₂ {a b : Coop B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) :
    (η ≫ θ).unop = θ.unop ≫ η.unop := rfl

@[simp] theorem unop_id₂ {a b : Coop B} (f : a ⟶ b) : (𝟙 f : f ⟶ f).unop = 𝟙 f.unop := rfl

@[simp] theorem op_comp₂ {a b : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) :
    op2 (η ≫ θ) = op2 θ ≫ op2 η := rfl

theorem whiskerLeft_def {a b c : Coop B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) :
    f ◁ η = (η.unop ▷ f.unop).op := rfl

theorem whiskerRight_def {a b c : Coop B} {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) :
    η ▷ h = (h.unop ◁ η.unop).op := rfl

@[simp] theorem unop_whiskerLeft {a b c : Coop B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) :
    (f ◁ η).unop = η.unop ▷ f.unop := rfl

@[simp] theorem unop_whiskerRight {a b c : Coop B} {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) :
    (η ▷ h).unop = h.unop ◁ η.unop := rfl

@[simp] theorem associator_hom_unop {a b c d : Coop B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (α_ f g h).hom.unop = (α_ h.unop g.unop f.unop).hom := rfl

@[simp] theorem associator_inv_unop {a b c d : Coop B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (α_ f g h).inv.unop = (α_ h.unop g.unop f.unop).inv := rfl

@[simp] theorem leftUnitor_hom_unop {a b : Coop B} (f : a ⟶ b) :
    (λ_ f).hom.unop = (ρ_ f.unop).inv := rfl

@[simp] theorem leftUnitor_inv_unop {a b : Coop B} (f : a ⟶ b) :
    (λ_ f).inv.unop = (ρ_ f.unop).hom := rfl

@[simp] theorem rightUnitor_hom_unop {a b : Coop B} (f : a ⟶ b) :
    (ρ_ f).hom.unop = (λ_ f.unop).inv := rfl

@[simp] theorem rightUnitor_inv_unop {a b : Coop B} (f : a ⟶ b) :
    (ρ_ f).inv.unop = (λ_ f.unop).hom := rfl

/-- Left whiskering in the bidual is the opposite of right whiskering in `B`. -/
theorem precomp_eq {a b : Coop B} (c : Coop B) (f : a ⟶ b) :
    precomp c f = (postcomp (ofCoop c) f.unop).op := rfl

/-- Right whiskering in the bidual is the opposite of left whiskering in `B`. -/
theorem postcomp_eq (a : Coop B) {b c : Coop B} (g : b ⟶ c) :
    postcomp a g = (precomp (ofCoop a) g.unop).op := rfl

/-! ### The Hom categories of the bidual -/

section HomInstances

open Pretriangulated Pretriangulated.Opposite

instance homPreadditive [∀ a b : B, Preadditive (a ⟶ b)] (a b : Coop B) :
    Preadditive (a ⟶ b) :=
  inferInstanceAs (Preadditive (ofCoop b ⟶ ofCoop a)ᵒᵖ)

instance homLinear (k : Type*) [Field k] [∀ a b : B, Preadditive (a ⟶ b)]
    [∀ a b : B, Linear k (a ⟶ b)] (a b : Coop B) : Linear k (a ⟶ b) :=
  inferInstanceAs (Linear k (ofCoop b ⟶ ofCoop a)ᵒᵖ)

instance homHomFinite (k : Type*) [Field k] [∀ a b : B, Preadditive (a ⟶ b)]
    [∀ a b : B, Linear k (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)] (a b : Coop B) :
    HomFinite k (a ⟶ b) :=
  inferInstanceAs (HomFinite k (ofCoop b ⟶ ofCoop a)ᵒᵖ)

instance homHasZeroObject [∀ a b : B, HasZeroObject (a ⟶ b)] (a b : Coop B) :
    HasZeroObject (a ⟶ b) :=
  inferInstanceAs (HasZeroObject (ofCoop b ⟶ ofCoop a)ᵒᵖ)

instance homHasBinaryBiproducts [∀ a b : B, Preadditive (a ⟶ b)]
    [∀ a b : B, HasBinaryBiproducts (a ⟶ b)] (a b : Coop B) : HasBinaryBiproducts (a ⟶ b) :=
  inferInstanceAs (HasBinaryBiproducts (ofCoop b ⟶ ofCoop a)ᵒᵖ)

instance homIsIdempotentComplete [∀ a b : B, IsIdempotentComplete (a ⟶ b)] (a b : Coop B) :
    IsIdempotentComplete (a ⟶ b) :=
  inferInstanceAs (IsIdempotentComplete (ofCoop b ⟶ ofCoop a)ᵒᵖ)

/-- The **inverted** grading shift on the Hom categories of the bidual: `(op X)⟨n⟩ = op (X⟨-n⟩)`
(the shift of `Mathlib.CategoryTheory.Triangulated.Opposite.Basic`). -/
instance homHasShift [∀ a b : B, HasShift (a ⟶ b) ℤ] (a b : Coop B) : HasShift (a ⟶ b) ℤ :=
  inferInstanceAs (HasShift (ofCoop b ⟶ ofCoop a)ᵒᵖ ℤ)

variable [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, HasShift (a ⟶ b) ℤ]

/-- **The bidual of a graded additive bicategory is graded**, with the inverted shift. -/
instance gradedBicategory [GradedBicategory B] : GradedBicategory (Coop B) where
  precomp_additive c f := inferInstanceAs ((postcomp (ofCoop c) f.unop).op.Additive)
  postcomp_additive a _ _ g := inferInstanceAs ((precomp (ofCoop a) g.unop).op.Additive)
  shift_additive a b n := inferInstanceAs ((shiftFunctor (ofCoop b ⟶ ofCoop a)ᵒᵖ n).Additive)
  precomp_commShift c f := inferInstanceAs ((postcomp (ofCoop c) f.unop).op.CommShift ℤ)
  postcomp_commShift a _ _ g := inferInstanceAs ((precomp (ofCoop a) g.unop).op.CommShift ℤ)

instance isLinear [GradedBicategory B] (k : Type*) [Field k] [∀ a b : B, Linear k (a ⟶ b)]
    [GradedBicategory.IsLinear B k] : GradedBicategory.IsLinear (Coop B) k where
  precomp_linear c f := inferInstanceAs ((postcomp (ofCoop c) f.unop).op.Linear k)
  postcomp_linear a _ _ g := inferInstanceAs ((precomp (ofCoop a) g.unop).op.Linear k)
  shift_linear a b n := inferInstanceAs ((shiftFunctor (ofCoop b ⟶ ofCoop a) (-n)).op.Linear k)

end HomInstances

/-! ### Adjunctions in the bidual -/

section Adjunction

/-- The left zigzag with the coherence isomorphism made explicit. -/
theorem _root_.Categorification.TwoRep.leftZigzag_eq {C : Type*} [Bicategory C] {a b : C}
    {f : a ⟶ b} {g : b ⟶ a} (unit : 𝟙 a ⟶ f ≫ g) (counit : g ≫ f ⟶ 𝟙 b) :
    leftZigzag unit counit = unit ▷ f ≫ (α_ f g f).hom ≫ f ◁ counit := by
  simp [bicategoricalComp]

/-- The right zigzag with the coherence isomorphism made explicit. -/
theorem _root_.Categorification.TwoRep.rightZigzag_eq {C : Type*} [Bicategory C] {a b : C}
    {f : a ⟶ b} {g : b ⟶ a} (unit : 𝟙 a ⟶ f ≫ g) (counit : g ≫ f ⟶ 𝟙 b) :
    rightZigzag unit counit = g ◁ unit ≫ (α_ g f g).inv ≫ counit ▷ g := by
  simp [bicategoricalComp]

/-- **Adjunctions pass to the bidual**: `u ⊣ v` in `B` gives `op u ⊣ op v` in `Bᶜᵒᵒᵖ`, with unit
the counit of `u ⊣ v` and counit its unit. -/
def adjunction {a b : B} {u : a ⟶ b} {v : b ⟶ a} (adj : u ⊣ v) : op1 u ⊣ op1 v where
  unit := op2 adj.counit
  counit := op2 adj.unit
  left_triangle := by
    rw [leftZigzag_eq]
    apply Quiver.Hom.unop_inj
    simp only [unop_comp₂, unop_whiskerLeft, unop_whiskerRight, associator_hom_unop,
      leftUnitor_hom_unop, rightUnitor_inv_unop]
    have h := adj.left_triangle
    rw [leftZigzag_eq] at h
    exact (Category.assoc _ _ _).trans h
  right_triangle := by
    rw [rightZigzag_eq]
    apply Quiver.Hom.unop_inj
    simp only [unop_comp₂, unop_whiskerLeft, unop_whiskerRight, associator_inv_unop,
      rightUnitor_hom_unop, leftUnitor_inv_unop]
    have h := adj.right_triangle
    rw [rightZigzag_eq] at h
    exact (Category.assoc _ _ _).trans h

/-- An adjunction `u ⊣ v` in the bidual is an adjunction `u.unop ⊣ v.unop` in `B`. -/
def adjunctionUnop {a b : Coop B} {u : a ⟶ b} {v : b ⟶ a} (adj : u ⊣ v) : u.unop ⊣ v.unop where
  unit := adj.counit.unop
  counit := adj.unit.unop
  left_triangle := by
    have := congrArg Quiver.Hom.unop adj.left_triangle
    rw [leftZigzag_eq] at this
    simp only [unop_comp₂, unop_whiskerLeft, unop_whiskerRight, associator_hom_unop,
      leftUnitor_hom_unop, rightUnitor_inv_unop] at this
    exact (leftZigzag_eq _ _).trans ((Category.assoc _ _ _).symm.trans this)
  right_triangle := by
    have := congrArg Quiver.Hom.unop adj.right_triangle
    rw [rightZigzag_eq] at this
    simp only [unop_comp₂, unop_whiskerLeft, unop_whiskerRight, associator_inv_unop,
      rightUnitor_hom_unop, leftUnitor_inv_unop] at this
    exact (rightZigzag_eq _ _).trans ((Category.assoc _ _ _).symm.trans this)

end Adjunction

/-! ### Zero objects and dimensions of Hom spaces -/

section Dim

variable {a b : B}

theorem isZero_op1_iff [∀ a b : B, HasZeroObject (a ⟶ b)] (f : a ⟶ b) :
    IsZero (op1 f) ↔ IsZero f :=
  ⟨fun h => h.unop, fun h => h.op⟩

variable (k : Type*) [Field k] [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]

/-- `Hom'(X, Y) = Hom(Y, X)`. -/
theorem finrank_hom (f g : a ⟶ b) : finrank k (op1 f ⟶ op1 g) = finrank k (g ⟶ f) :=
  finrank_op_hom k g f

variable [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B] [GradedBicategory.IsLinear B k]

/-- **Degrees are preserved by the duality**: `Hom'(X, Y⟨d⟩') = Hom(Y, X⟨d⟩)`. -/
theorem finrank_hom_shift (f g : a ⟶ b) (d : ℤ) :
    finrank k (op1 f ⟶ (op1 g)⟦d⟧) = finrank k (g ⟶ f⟦d⟧) := by
  change finrank k (op1 f ⟶ op1 (g⟦-d⟧)) = _
  rw [finrank_hom]
  exact finrank_hom_shift_left k g f (by ring)

end Dim

/-! ### Shifted 2-morphisms of the bidual -/

section Shifted

open Pretriangulated Pretriangulated.Opposite

variable [∀ a b : B, HasShift (a ⟶ b) ℤ] {a b c : B}

/-- The shift of the bidual is the inverted shift. -/
theorem shift_op1 (f : a ⟶ b) (n : ℤ) : (op1 f)⟦n⟧ = op1 (f⟦-n⟧) := rfl

/-- A shifted 2-morphism `f ⟶ g⟨n⟩` of `B` as a shifted 2-morphism `op g ⟶ (op f)⟨n⟩'` of the
bidual (Mathlib's `ShiftedHom.opEquiv`): the degree is preserved. -/
def shOp {f g : a ⟶ b} {n : ℤ} (η : ShiftedHom f g n) : ShiftedHom (op1 g) (op1 f) n :=
  ShiftedHom.opEquiv n η

theorem shOp_injective {f g : a ⟶ b} {n : ℤ} :
    Function.Injective (shOp : ShiftedHom f g n → ShiftedHom (op1 g) (op1 f) n) :=
  (ShiftedHom.opEquiv n).injective

/-- `shOp` reverses the composition of shifted 2-morphisms. -/
theorem shOp_comp {f g h : a ⟶ b} {m n s : ℤ} (η : ShiftedHom f g m) (θ : ShiftedHom g h n)
    (hs : n + m = s) (hs' : m + n = s) :
    shOp (η.comp θ hs) = (shOp θ).comp (shOp η) hs' :=
  shiftedHom_opEquiv_comp η θ hs

theorem shOp_mk₀ {f g : a ⟶ b} (η : f ⟶ g) :
    shOp (ShiftedHom.mk₀ (0 : ℤ) rfl η) = ShiftedHom.mk₀ (0 : ℤ) rfl (op2 η) :=
  shiftedHom_opEquiv_mk₀ η

/-- `shOp` exchanges conjugation by `e⁻¹` with conjugation by the opposite isomorphism. -/
theorem shOp_shConj_symm {f g : a ⟶ b} (e : f ≅ g) {n : ℤ} (η : ShiftedHom g g n) :
    shOp (shConj e.symm η) = shConj e.op (shOp η) := by
  unfold shConj
  rw [shOp_comp _ _ (add_zero n) (zero_add n),
    shOp_comp _ _ (zero_add n) (add_zero n), shOp_mk₀, shOp_mk₀]
  exact ShiftedHom.comp_assoc _ _ _ (add_zero n) (zero_add n) (by omega)

variable [∀ a b : B, Preadditive (a ⟶ b)] [GradedBicategory B]

@[simp] theorem shOp_zero {f g : a ⟶ b} {n : ℤ} : shOp (0 : ShiftedHom f g n) = 0 :=
  map_zero (shiftedHomOpAddEquiv f g n)

theorem shOp_add {f g : a ⟶ b} {n : ℤ} (η θ : ShiftedHom f g n) :
    shOp (η + θ) = shOp η + shOp θ :=
  map_add (shiftedHomOpAddEquiv f g n) η θ

theorem shOp_neg {f g : a ⟶ b} {n : ℤ} (η : ShiftedHom f g n) : shOp (-η) = -shOp η :=
  map_neg (shiftedHomOpAddEquiv f g n) η

theorem shOp_sub {f g : a ⟶ b} {n : ℤ} (η θ : ShiftedHom f g n) :
    shOp (η - θ) = shOp η - shOp θ :=
  map_sub (shiftedHomOpAddEquiv f g n) η θ

/-- Left whiskering in `B` is right whiskering in the bidual. -/
theorem shOp_shWhiskerLeft (f : a ⟶ b) {g h : b ⟶ c} {n : ℤ} (θ : ShiftedHom g h n) :
    shOp (shWhiskerLeft f θ) = shWhiskerRight (shOp θ) (op1 f) :=
  shiftedHom_opEquiv_map (precomp c f) θ

/-- Right whiskering in `B` is left whiskering in the bidual. -/
theorem shOp_shWhiskerRight {f g : a ⟶ b} {n : ℤ} (η : ShiftedHom f g n) (h : b ⟶ c) :
    shOp (shWhiskerRight η h) = shWhiskerLeft (op1 h) (shOp η) :=
  shiftedHom_opEquiv_map (postcomp a h) η

end Shifted

/-! ### Coherence of the shift with composition in the bidual -/

section ShiftIsos

open Pretriangulated Pretriangulated.Opposite

variable [∀ a b : B, HasShift (a ⟶ b) ℤ]

/-- The shift of a 2-morphism of the bidual is the opposite of its inverted shift. -/
theorem unop_shift_map₂ {a b : Coop B} {f g : a ⟶ b} (φ : f ⟶ g) (n : ℤ) :
    (φ⟦n⟧').unop = (φ.unop)⟦-n⟧' := rfl

theorem unop_shiftFunctorAdd'_inv_app₂ {a b : Coop B} (f : a ⟶ b) (a₁ a₂ a₃ : ℤ)
    (h : a₁ + a₂ = a₃) :
    ((shiftFunctorAdd' (a ⟶ b) a₁ a₂ a₃ h).inv.app f).unop =
      (shiftFunctorAdd' (ofCoop b ⟶ ofCoop a) (-a₁) (-a₂) (-a₃) (by omega)).hom.app f.unop :=
  unop_shiftFunctorAdd'_inv_app f a₁ a₂ a₃ h

variable [∀ a b : B, Preadditive (a ⟶ b)] [GradedBicategory B]

/-- The left whiskering shift isomorphism of the bidual is the inverse of the right whiskering
shift isomorphism of `B`. -/
theorem whiskerLeftShiftIso_hom_unop {a b c : Coop B} (f : a ⟶ b) (g : b ⟶ c) (n : ℤ) :
    (whiskerLeftShiftIso f g n).hom.unop = (whiskerRightShiftIso g.unop f.unop (-n)).inv :=
  unop_op_commShiftIso_hom_app (postcomp (ofCoop c) f.unop) g n

/-- The right whiskering shift isomorphism of the bidual is the inverse of the left whiskering
shift isomorphism of `B`. -/
theorem whiskerRightShiftIso_hom_unop {a b c : Coop B} (f : a ⟶ b) (g : b ⟶ c) (n : ℤ) :
    (whiskerRightShiftIso f g n).hom.unop = (whiskerLeftShiftIso g.unop f.unop (-n)).inv :=
  unop_op_commShiftIso_hom_app (precomp (ofCoop a) g.unop) f n

/-- Moving isomorphisms across a commutative square. -/
theorem _root_.Categorification.TwoRep.comp_inv_eq_inv_comp_of_hom_comp {C : Type*} [Category C]
    {W X Y Z : C} (i : Y ≅ Z) (j : W ≅ X) {A : X ⟶ Z} {B : W ⟶ Y}
    (h : j.hom ≫ A = B ≫ i.hom) : A ≫ i.inv = j.inv ≫ B := by
  rw [Iso.eq_inv_comp, ← Category.assoc, h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- `ShiftInterchange.shift_shift` with an arbitrary name for the total shift. -/
theorem shift_shift' [GradedBicategory.ShiftInterchange B] {a b c : B} (f : a ⟶ b) (g : b ⟶ c)
    (m n s : ℤ) (h : n + m = s) :
    (whiskerRightShiftIso f (g⟦n⟧) m).hom ≫ (whiskerLeftShiftIso f g n).hom⟦m⟧' ≫
        (shiftFunctorAdd' (a ⟶ c) n m s h).inv.app (f ≫ g) =
      (whiskerLeftShiftIso (f⟦m⟧) g n).hom ≫ (whiskerRightShiftIso f g m).hom⟦n⟧' ≫
        (shiftFunctorAdd' (a ⟶ c) m n s (by omega)).inv.app (f ≫ g) := by
  subst h
  exact GradedBicategory.ShiftInterchange.shift_shift f g m n

/-- **The bidual of a graded bicategory with coherent shifts has coherent shifts.** -/
instance shiftInterchange [GradedBicategory.ShiftInterchange B] :
    GradedBicategory.ShiftInterchange (Coop B) where
  whiskerRightShiftIso_natural {a b c} f g g' θ m := by
    apply Quiver.Hom.unop_inj
    have h := GradedBicategory.ShiftInterchange.whiskerLeftShiftIso_natural θ.unop f.unop (-m)
    rw [unop_comp₂, unop_comp₂, whiskerRightShiftIso_hom_unop, whiskerRightShiftIso_hom_unop,
      unop_shift_map₂, unop_whiskerLeft]
    exact comp_inv_eq_inv_comp_of_hom_comp _ _ h
  whiskerLeftShiftIso_natural {a b c} f f' η g n := by
    apply Quiver.Hom.unop_inj
    have h := GradedBicategory.ShiftInterchange.whiskerRightShiftIso_natural g.unop η.unop (-n)
    rw [unop_comp₂, unop_comp₂, whiskerLeftShiftIso_hom_unop, whiskerLeftShiftIso_hom_unop,
      unop_shift_map₂, unop_whiskerRight]
    exact comp_inv_eq_inv_comp_of_hom_comp _ _ h
  shift_shift {a b c} f g m n := by
    apply Quiver.Hom.unop_inj
    have h := shift_shift' g.unop f.unop (-n) (-m) (-(n + m)) (by omega)
    let isoL : g.unop⟦-n⟧ ≫ f.unop⟦-m⟧ ≅ (g.unop ≫ f.unop)⟦-(n + m)⟧ :=
      whiskerLeftShiftIso (g.unop⟦-n⟧) f.unop (-m) ≪≫
        (shiftFunctor _ (-m)).mapIso (whiskerRightShiftIso g.unop f.unop (-n)) ≪≫
        ((shiftFunctorAdd' _ (-n) (-m) (-(n + m)) (by omega)).app (g.unop ≫ f.unop)).symm
    let isoR : g.unop⟦-n⟧ ≫ f.unop⟦-m⟧ ≅ (g.unop ≫ f.unop)⟦-(n + m)⟧ :=
      whiskerRightShiftIso g.unop (f.unop⟦-m⟧) (-n) ≪≫
        (shiftFunctor _ (-n)).mapIso (whiskerLeftShiftIso g.unop f.unop (-m)) ≪≫
        ((shiftFunctorAdd' _ (-m) (-n) (-(n + m)) (by omega)).app (g.unop ≫ f.unop)).symm
    have hiso : isoR = isoL := Iso.ext (by simpa [isoL, isoR] using h)
    have hinv := congrArg Iso.inv hiso
    rw [unop_comp₂, unop_comp₂, unop_comp₂, unop_comp₂, unop_shiftFunctorAdd'_inv_app₂,
      unop_shiftFunctorAdd'_inv_app₂, unop_shift_map₂, unop_shift_map₂,
      whiskerLeftShiftIso_hom_unop, whiskerLeftShiftIso_hom_unop,
      whiskerRightShiftIso_hom_unop, whiskerRightShiftIso_hom_unop]
    have h2 := hinv.symm
    simp only [isoL, isoR, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Iso.app_hom,
      Category.assoc] at h2
    refine (Category.assoc _ _ _).trans (h2.trans ?_)
    exact (Category.assoc (obj := (ofCoop c ⟶ ofCoop a)) _ _ _).symm

end ShiftIsos

end Coop

end Categorification.TwoRep
