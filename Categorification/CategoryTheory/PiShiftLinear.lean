/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.CategoryTheory.PiShift
import Categorification.CategoryTheory.PiAbelian

/-!
# Linearity of level shifts and of lifts to full subcategories

If `Fₘ : C m ⥤ C (m + 1)` and `Eₘ : C (m + 1) ⥤ C m` are `k`-linear functors between
`k`-linear categories, the functors `PiShift.up` and `PiShift.down` on `∀ m, C m` which they
induce are `k`-linear (`PiShift.up_linear`, `PiShift.down_linear`). A `k`-linear functor with
values in a full subcategory is `k`-linear as a functor into that subcategory
(`ObjectProperty.lift_linear`). These are used for the `k`-linear structure of the weak
`𝔰𝔩₂`-categorification along an `i`-string (Webster, arXiv:1309.3796v2, §5;
Chuang–Rouquier, arXiv:math/0407205v2, §5.2).
-/

set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory

universe u v

namespace PiShift

variable {C : ℕ → Type u} [∀ m, Category.{v} (C m)] [∀ m, Preadditive (C m)] (k : Type*)
  [Semiring k] [∀ m, Linear k (C m)]

instance down_additive (Em : ∀ m, C (m + 1) ⥤ C m) [∀ m, (Em m).Additive] :
    (down Em).Additive where
  map_add {_ _ f g} := funext fun m => (Em m).map_add (f := f (m + 1)) (g := g (m + 1))

open Limits in
instance up_additive [HasZeroObject (C 0)] (Fm : ∀ m, C m ⥤ C (m + 1))
    [∀ m, (Fm m).Additive] : (up Fm).Additive where
  map_add {_ _ f g} := funext fun m => by
    cases m with
    | zero => exact (isZero_zero (C 0)).eq_of_src _ _
    | succ m => exact (Fm m).map_add (f := f m) (g := g m)

theorem down_linear (Em : ∀ m, C (m + 1) ⥤ C m) [∀ m, (Em m).Linear k] :
    (down Em).Linear k where
  map_smul f c := funext fun m => (Em m).map_smul c (f (m + 1))

open Limits in
theorem up_linear [HasZeroObject (C 0)] (Fm : ∀ m, C m ⥤ C (m + 1)) [∀ m, (Fm m).Linear k] :
    (up Fm).Linear k where
  map_smul f c := funext fun m => by
    cases m with
    | zero => exact (isZero_zero (C 0)).eq_of_src _ _
    | succ m => exact (Fm m).map_smul c (f m)

end PiShift

theorem ObjectProperty.lift_linear {C D : Type*} [Category* C] [Category* D] [Preadditive C]
    [Preadditive D] (k : Type*) [Semiring k] [Linear k C] [Linear k D] (P : ObjectProperty D)
    (F : C ⥤ D) (hF : ∀ X, P (F.obj X)) [F.Linear k] : (P.lift F hF).Linear k where
  map_smul f c := P.hom_ext (F.map_smul c f)

end CategoryTheory
