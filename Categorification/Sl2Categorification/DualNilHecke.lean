/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.Sl2Categorification.NilHeckeAction
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# The nilHecke action on a right adjoint

Chuang and Rouquier (arXiv:math/0407205v2, §5.2.1) note that if `E ⊣ F`, then the mates of
`X ∈ End(E)` and `T ∈ End(E²)` give endomorphisms of `F` and `F²` satisfying the same relations,
up to the sign of `X`. This file proves the nilHecke version: `(-X^∨, T^∨)` is nilHecke data
on `F`, where `(-)^∨` is the conjugation of natural transformations along `E ⊣ F`
(`conjugateEquiv`).

## Main definitions

* `Sl2.mateEnd`: the conjugation `End(L) → End(R)` along `L ⊣ R`, an anti-homomorphism.
* `Sl2.NilHeckeData.dual`: the nilHecke data `(-X^∨, T^∨)` on `F`.
-/

namespace Categorification.Sl2

open CategoryTheory CategoryTheory.Functor

universe v u

variable {C : Type u} [Category.{v} C]

section Mate

variable {L R : C ⥤ C} (adj : L ⊣ R)

/-- Conjugation of endomorphisms along `L ⊣ R`. -/
def mateEnd (a : End L) : End R := conjugateEquiv adj adj a

theorem mateEnd_mul (a b : End L) : mateEnd adj (a * b) = mateEnd adj b * mateEnd adj a := by
  simp only [mateEnd, End.mul_def]
  exact (conjugateEquiv_comp adj adj adj a b).symm

theorem mateEnd_one : mateEnd adj (1 : End L) = 1 := conjugateEquiv_id adj

variable [Preadditive C]

theorem mateEnd_add [L.Additive] (a b : End L) :
    mateEnd adj (a + b) = mateEnd adj a + mateEnd adj b := by
  refine NatTrans.ext (funext fun d ↦ ?_)
  apply (adj.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  change L.map ((conjugateEquiv adj adj (a + b)).app d) ≫ _ =
    L.map ((conjugateEquiv adj adj a).app d + (conjugateEquiv adj adj b).app d) ≫ _
  rw [L.map_add, Preadditive.add_comp, conjugateEquiv_counit, conjugateEquiv_counit,
    conjugateEquiv_counit]
  exact Preadditive.add_comp _ _ _ _ _ _

/-- `mateEnd` as an additive map. -/
def mateEndAdd [L.Additive] : End L →+ End R where
  toFun := mateEnd adj
  map_zero' := by
    have h : mateEnd adj 0 + mateEnd adj 0 = mateEnd adj 0 + 0 := by
      rw [← mateEnd_add, add_zero, add_zero]
    exact add_left_cancel h
  map_add' := mateEnd_add adj

theorem mateEnd_sub [L.Additive] (a b : End L) :
    mateEnd adj (a - b) = mateEnd adj a - mateEnd adj b := map_sub (mateEndAdd adj) a b

theorem mateEnd_zero [L.Additive] : mateEnd adj (0 : End L) = 0 := map_zero (mateEndAdd adj)

theorem mateEnd_neg [L.Additive] (a : End L) : mateEnd adj (-a) = -mateEnd adj a :=
  map_neg (mateEndAdd adj) a

end Mate

section Whisker

variable {E F : C ⥤ C} (adj : E ⊣ F)

theorem mateEnd_wR (a : End E) : mateEnd (adj.comp adj) (wR a E) = wL F (mateEnd adj a) :=
  conjugateEquiv_whiskerRight adj adj adj a

theorem mateEnd_wL (a : End E) : mateEnd (adj.comp adj) (wL E a) = wR (mateEnd adj a) F :=
  conjugateEquiv_whiskerLeft adj adj adj a

theorem mateEnd_comp_assoc (a : End ((E ⋙ E) ⋙ E)) :
    mateEnd ((adj.comp adj).comp adj) a = mateEnd (adj.comp (adj.comp adj)) a := by
  refine NatTrans.ext (funext fun X ↦ ?_)
  simp [mateEnd, conjugateEquiv_apply_app]

theorem mateEnd_wR₂ (b : End (E ⋙ E)) :
    mateEnd ((adj.comp adj).comp adj) (wR b E) = wL₂ F (mateEnd (adj.comp adj) b) :=
  conjugateEquiv_whiskerRight (adj.comp adj) (adj.comp adj) adj b

theorem mateEnd_wL₂ (b : End (E ⋙ E)) :
    mateEnd ((adj.comp adj).comp adj) (wL₂ E b) = wR (mateEnd (adj.comp adj) b) F := by
  rw [mateEnd_comp_assoc]
  exact conjugateEquiv_whiskerLeft (adj.comp adj) (adj.comp adj) adj b

end Whisker

namespace NilHeckeData

variable [Preadditive C]

variable {E F : C ⥤ C} [E.Additive] (D : NilHeckeData E) (adj : E ⊣ F)

omit [E.Additive] in
theorem wR_neg [F.Additive] (a : End F) : wR (-a) F = -wR a F := by
  refine NatTrans.ext (funext fun X ↦ ?_)
  change F.map (-(a.app X)) = -F.map (a.app X)
  exact F.map_neg

omit [E.Additive] in
theorem wL_neg (a : End F) : wL F (-a) = -wL F a := by
  rfl

/-- The nilHecke data `(-X^∨, T^∨)` on a right adjoint `F` of `E` (Chuang–Rouquier,
arXiv:math/0407205v2, §5.2.1, nilHecke version). -/
def dual : NilHeckeData F :=
  have : F.Additive := adj.right_adjoint_additive
  { X := -mateEnd adj D.X
    T := mateEnd (adj.comp adj) D.T
    T_mul_T := by rw [← mateEnd_mul, D.T_mul_T, mateEnd_zero]
    braid := by
      rw [← mateEnd_wR₂, ← mateEnd_wL₂, ← mateEnd_mul, ← mateEnd_mul, ← mateEnd_mul,
        ← mateEnd_mul, ← mul_assoc, ← mul_assoc, D.braid]
    x_T_sub := by
      rw [wR_neg, wL_neg,
        ← mateEnd_wR, ← mateEnd_wL, neg_mul, mul_neg, ← mateEnd_mul, ← mateEnd_mul,
        sub_neg_eq_add, neg_add_eq_sub, ← mateEnd_sub, D.x_T_sub, mateEnd_one]
    T_x_sub := by
      rw [wR_neg, wL_neg,
        ← mateEnd_wR, ← mateEnd_wL, neg_mul, mul_neg, ← mateEnd_mul, ← mateEnd_mul,
        sub_neg_eq_add, neg_add_eq_sub, ← mateEnd_sub, D.T_x_sub, mateEnd_one] }

theorem dual_X : (D.dual adj).X = -mateEnd adj D.X := rfl

theorem dual_T : (D.dual adj).T = mateEnd (adj.comp adj) D.T := rfl

end NilHeckeData

end Categorification.Sl2
