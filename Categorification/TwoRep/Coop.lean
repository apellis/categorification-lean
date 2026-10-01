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
flips: `Hom'(X, Y⟨d⟩') = Hom(Y, X⟨d⟩)` (`finrank_coop_hom_shift`). With the uninverted shift all
degrees would change sign.

This is the duality `D(K) = K^coop` used to transport statements about the weights `n ≤ 0` of a
strong 2-representation of `sl₂` to statements about the weights `n ≥ 0` (`Duality.lean`).

## Main declarations

* `oppositeLinear`, `oppositeHomFinite`: the opposite of a `k`-linear (Hom-finite) category;
* `Coop B`, `Coop.bicategory`: the bidual bicategory;
* the Hom-category instances of `Coop B` (preadditive, `k`-linear, inverted shift, zero object,
  binary biproducts, idempotent completeness, Hom-finiteness);
* `Coop.gradedBicategory`, `Coop.isLinear`, `Coop.shiftInterchange`: the graded structure and its
  mixins transfer to the bidual;
* `Bicategory.Adjunction.coop`: an adjunction `u ⊣ v` in `B` gives `op u ⊣ op v` in `Coop B`, with
  unit the counit of `u ⊣ v` and counit its unit; `Adjunction.ofIsoRight`;
* `finrank_coop_hom`, `finrank_coop_hom_shift`: dimensions of Hom spaces in the bidual;
* `ShiftedHom.opEquiv_symm_map`, `opEquiv_symm_mk₀`, ...: shifted 2-morphisms of the bidual.
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

@[simp] theorem id_def (a : Coop B) : 𝟙 a = op (𝟙 (ofCoop a)) := rfl

@[simp] theorem comp_def {a b c : Coop B} (f : a ⟶ b) (g : b ⟶ c) : f ≫ g = op (g.unop ≫ f.unop) :=
  rfl

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

open Pretriangulated.Opposite

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

end Coop

end Categorification.TwoRep
