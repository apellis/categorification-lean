/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.CategoryTheory.Pi.Basic

/-!
# Shift functors on towers of categories

For a family of categories `C 0, C 1, …`, functors `Fₘ : C m ⥤ C (m + 1)` and
`Eₘ : C (m + 1) ⥤ C m` assemble to endofunctors of the product `∀ m, C m`: `F` moves the
level-`m` component to level `m + 1` (with zero at level `0`), and `E` moves it down. Levelwise
adjunctions `Fₘ ⊣ Eₘ` or `Eₘ ⊣ Fₘ` give adjunctions `F ⊣ E` or `E ⊣ F`.

This is the shape of Chuang–Rouquier's weak `𝔰𝔩₂`-categorification on the modules over a tower
of algebras along one `i`-string (arXiv:math/0407205v2, §5.1.1; Webster, arXiv:1309.3796v2,
§5), where `Fₘ` adds a strand and `Eₘ` removes one.

## Main definitions

* `CategoryTheory.Adjunction.pi`: levelwise adjunctions give an adjunction of `Functor.pi`.
* `CategoryTheory.PiShift.ins`, `CategoryTheory.PiShift.drop`: insertion of a zero object at
  level `0`, and forgetting level `0`; they are adjoint on both sides.
* `CategoryTheory.PiShift.up`, `CategoryTheory.PiShift.down` and the adjunctions
  `PiShift.upDownAdj`, `PiShift.downUpAdj`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CategoryTheory

open Limits

universe w v u

section PiAdjunction

variable {I : Type w} {C : I → Type u} [∀ i, Category.{v} (C i)]
  {D : I → Type u} [∀ i, Category.{v} (D i)]

/-- Levelwise adjunctions give an adjunction between the product functors. -/
def Adjunction.pi {F : ∀ i, C i ⥤ D i} {G : ∀ i, D i ⥤ C i} (adj : ∀ i, F i ⊣ G i) :
    Functor.pi F ⊣ Functor.pi G :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f i => (adj i).homEquiv _ _ (f i)
          invFun := fun g i => ((adj i).homEquiv _ _).symm (g i)
          left_inv := fun f => funext fun i => by simp
          right_inv := fun g => funext fun i => by simp }
      homEquiv_naturality_left_symm := fun f g => funext fun i =>
        (adj i).homEquiv_naturality_left_symm (f i) (g i)
      homEquiv_naturality_right := fun f g => funext fun i =>
        (adj i).homEquiv_naturality_right (f i) (g i) }

end PiAdjunction

namespace PiShift

variable {C : ℕ → Type u} [∀ m, Category.{v} (C m)]

/-- Forget level `0`. -/
abbrev drop : (∀ m, C m) ⥤ (∀ m, C (m + 1)) :=
  Pi.comap C (fun m => m + 1)

variable [HasZeroMorphisms (C 0)] [HasZeroObject (C 0)]

open ZeroObject

/-- The object of the product with a zero object at level `0` and `X m` at level `m + 1`. -/
def insObj (X : ∀ m, C (m + 1)) : ∀ m, C m
  | 0 => 0
  | m + 1 => X m

/-- The morphism with zero at level `0` and `f m` at level `m + 1`. -/
def insMap {X Y : ∀ m, C (m + 1)} (f : X ⟶ Y) : insObj X ⟶ insObj Y
  | 0 => (0 : (0 : C 0) ⟶ 0)
  | m + 1 => f m

/-- Insert a zero object at level `0`. -/
@[simps]
def ins : (∀ m, C (m + 1)) ⥤ (∀ m, C m) where
  obj := insObj
  map := insMap
  map_id X := funext fun m => by
    cases m
    · exact (isZero_zero (C 0)).eq_of_src _ _
    · rfl
  map_comp f g := funext fun m => by
    cases m
    · exact (isZero_zero (C 0)).eq_of_src _ _
    · rfl

/-- Insertion of zero at level `0` is left adjoint to forgetting level `0`. -/
def insDropAdj : (ins : (∀ m, C (m + 1)) ⥤ (∀ m, C m)) ⊣ drop :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f m => f (m + 1)
          invFun := fun g m => match m with
            | 0 => (0 : (0 : C 0) ⟶ Y 0)
            | m + 1 => g m
          left_inv := fun f => funext fun m => by
            cases m
            · exact (isZero_zero (C 0)).eq_of_src _ _
            · rfl
          right_inv := fun g => rfl }
      homEquiv_naturality_left_symm := fun f g => funext fun m => by
        cases m
        · exact (isZero_zero (C 0)).eq_of_src _ _
        · rfl
      homEquiv_naturality_right := fun f g => rfl }

/-- Forgetting level `0` is left adjoint to insertion of zero at level `0`. -/
def dropInsAdj : drop ⊣ (ins : (∀ m, C (m + 1)) ⥤ (∀ m, C m)) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f m => match m with
            | 0 => (0 : X 0 ⟶ (0 : C 0))
            | m + 1 => f m
          invFun := fun g m => g (m + 1)
          left_inv := fun f => rfl
          right_inv := fun g => funext fun m => by
            cases m
            · exact (isZero_zero (C 0)).eq_of_tgt _ _
            · rfl }
      homEquiv_naturality_left_symm := fun f g => rfl
      homEquiv_naturality_right := fun f g => funext fun m => by
        cases m
        · exact (isZero_zero (C 0)).eq_of_tgt _ _
        · rfl }

variable (Fm : ∀ m, C m ⥤ C (m + 1)) (Em : ∀ m, C (m + 1) ⥤ C m)

/-- The functor raising every component by one level. -/
abbrev up : (∀ m, C m) ⥤ (∀ m, C m) :=
  Functor.pi Fm ⋙ ins

/-- The functor lowering every component by one level. -/
abbrev down : (∀ m, C m) ⥤ (∀ m, C m) :=
  drop ⋙ Functor.pi Em

variable {Fm Em}

/-- Levelwise adjunctions `Fₘ ⊣ Eₘ` give `up ⊣ down`. -/
def upDownAdj (adj : ∀ m, Fm m ⊣ Em m) : up Fm ⊣ down Em :=
  (Adjunction.pi adj).comp insDropAdj

/-- Levelwise adjunctions `Eₘ ⊣ Fₘ` give `down ⊣ up`. -/
def downUpAdj (adj : ∀ m, Em m ⊣ Fm m) : down Em ⊣ up Fm :=
  dropInsAdj.comp (Adjunction.pi adj)

end PiShift

end CategoryTheory
