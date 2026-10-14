/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Category.ModuleCat.Algebra

/-!
# Modules over an algebra over a commutative ring form a linear category

Mathlib provides `Linear k (ModuleCat A)` for an algebra `A` over a field `k`
(`ModuleCat.linearOverField`). The same construction works over any commutative ring: a
module over `A` is a `k`-module by restriction of scalars along `algebraMap k A`, and since
`algebraMap k A` is central, `A`-linear maps form a `k`-module, `(c • f) m = c • f m`.
For a field the two instances agree definitionally.

This is used for the `k`-linear structure of categories of modules over cyclotomic KLR
algebras, which are algebras over an arbitrary commutative ring.
-/

open CategoryTheory

universe v u w

namespace ModuleCat

variable {k : Type u} [CommRing k] {A : Type w} [Ring A] [Algebra k A]

/-- A module over a `k`-algebra, as a `k`-module by restriction of scalars. -/
@[instance_reducible]
def moduleOfAlgebraModuleCommRing (M : ModuleCat.{v} A) : Module k M :=
  Module.restrictScalars k A M

attribute [local instance] moduleOfAlgebraModuleCommRing

theorem isScalarTower_of_algebraModuleCommRing (M : ModuleCat.{v} A) : IsScalarTower k A M :=
  IsScalarTower.restrictScalars k A M

attribute [local instance] isScalarTower_of_algebraModuleCommRing

/-- `ModuleCat A` is `k`-linear for an algebra `A` over a commutative ring `k`. -/
instance (priority := 100) linearOverCommRing : Linear k (ModuleCat.{v} A) where
  homModule _ _ := inferInstance

theorem smul_hom_apply {M N : ModuleCat.{v} A} (c : k) (f : M ⟶ N) (m : M) :
    (c • f).hom m = algebraMap k A c • f.hom m :=
  rfl

end ModuleCat
