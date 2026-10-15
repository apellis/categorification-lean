/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Module.Pi
import Mathlib.CategoryTheory.Pi.Basic
import Categorification.TwoRep.LinearCat

/-!
# Products of preadditive `k`-linear categories

A product `∀ j, C j` of preadditive (`k`-linear) categories is preadditive (`k`-linear), with
morphisms added and scaled componentwise. Evaluation at a factor and functors assembled from
components (`Functor.pi'`, `Functor.pi`) are additive and `k`-linear when their components are.
`LinearCat.pi` is the resulting product of objects of `TwoRep.LinearCat`.

These products are the weight spaces of the weight-indexed cyclotomic Rouquier family of
KL III Thm. 1.2: the category at weight `x` is the product of the block categories
`R^Λ(β)-mod` over the multisets `β` of weight `x`.
-/

open CategoryTheory

namespace Categorification.TwoRep

universe w v u v₁ u₁ u₀

section Pi

variable {J : Type u₀} {C : J → Type u₁} [∀ j, Category.{v₁} (C j)]

instance piPreadditive [∀ j, Preadditive (C j)] : Preadditive (∀ j, C j) where
  homGroup X Y := inferInstanceAs (AddCommGroup (∀ j, X j ⟶ Y j))
  add_comp _ _ _ f f' g := funext fun j => Preadditive.add_comp _ _ _ (f j) (f' j) (g j)
  comp_add _ _ _ f g g' := funext fun j => Preadditive.comp_add _ _ _ (f j) (g j) (g' j)

variable [∀ j, Preadditive (C j)]

@[simp] theorem pi_add_apply {X Y : ∀ j, C j} (f g : X ⟶ Y) (j : J) :
    (f + g) j = f j + g j := rfl

@[simp] theorem pi_neg_apply {X Y : ∀ j, C j} (f : X ⟶ Y) (j : J) : (-f) j = -f j := rfl

@[simp] theorem pi_sub_apply {X Y : ∀ j, C j} (f g : X ⟶ Y) (j : J) :
    (f - g) j = f j - g j := rfl

@[simp] theorem pi_zero_apply {X Y : ∀ j, C j} (j : J) : (0 : X ⟶ Y) j = 0 := rfl

omit [∀ j, Preadditive (C j)] in
@[simp] theorem pi_comp_apply {X Y Z : ∀ j, C j} (f : X ⟶ Y) (g : Y ⟶ Z) (j : J) :
    (f ≫ g) j = f j ≫ g j := rfl

omit [∀ j, Preadditive (C j)] in
@[simp] theorem pi_id_apply (X : ∀ j, C j) (j : J) : (𝟙 X : X ⟶ X) j = 𝟙 (X j) := rfl

instance piLinear (R : Type w) [Semiring R] [∀ j, Linear R (C j)] : Linear R (∀ j, C j) where
  homModule X Y := inferInstanceAs (Module R (∀ j, X j ⟶ Y j))
  smul_comp _ _ _ r f g := funext fun j => Linear.smul_comp _ _ _ r (f j) (g j)
  comp_smul _ _ _ f r g := funext fun j => Linear.comp_smul _ _ _ (f j) r (g j)

@[simp] theorem pi_smul_apply {R : Type w} [Semiring R] [∀ j, Linear R (C j)]
    {X Y : ∀ j, C j} (r : R) (f : X ⟶ Y) (j : J) : (r • f) j = r • f j := rfl

instance eval_additive (j : J) : (Pi.eval C j).Additive where

instance eval_linear (R : Type w) [Semiring R] [∀ j, Linear R (C j)] (j : J) :
    (Pi.eval C j).Linear R where

variable {A : Type*} [Category A] [Preadditive A]

instance pi'_additive (F : ∀ j, A ⥤ C j) [∀ j, (F j).Additive] : (Functor.pi' F).Additive where
  map_add := funext fun _ => Functor.map_add _

instance pi'_linear (R : Type w) [Semiring R] [Linear R A] [∀ j, Linear R (C j)]
    (F : ∀ j, A ⥤ C j) [∀ j, (F j).Linear R] : (Functor.pi' F).Linear R where
  map_smul _ _ := funext fun j => Functor.map_smul (F j) _ _

end Pi

namespace LinearCat

variable {k : Type w} [CommRing k]

/-- The product of a family of objects of `LinearCat k`. -/
def pi {J : Type u₀} (C : J → LinearCat.{w, v, u} k) : LinearCat.{w, max u₀ v, max u₀ u} k :=
  LinearCat.of k (∀ j, C j)

end LinearCat

end Categorification.TwoRep
