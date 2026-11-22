/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Sl2Categorification.DualNilHecke

/-!
# Restricting a nilHecke action to a full subcategory

If `E` preserves a full subcategory `P` of `C`, a nilHecke action on `E` (Chuang–Rouquier,
arXiv:math/0407205v2, §5.2.1) restricts to one on the induced endofunctor of `P`
(`NilHeckeData.lift`). Nilpotence of the dot is preserved by this restriction and by passing to
the action on a right adjoint (`NilHeckeData.dual`).
-/

set_option backward.isDefEq.respectTransparency false

namespace Categorification.Sl2

open CategoryTheory CategoryTheory.Functor

universe v u

variable {C : Type u} [Category.{v} C]

section Pow

variable {L R : C ⥤ C} (adj : L ⊣ R)

theorem mateEnd_pow (a : End L) (N : ℕ) : mateEnd adj (a ^ N) = mateEnd adj a ^ N := by
  induction N with
  | zero => rw [pow_zero, pow_zero, mateEnd_one]
  | succ N ih => rw [pow_succ, mateEnd_mul, ih, pow_succ']

end Pow

namespace NilHeckeData

section Lift

variable (P : ObjectProperty C) {E : C ⥤ C} (hE : ∀ X : P.FullSubcategory, P (E.obj X.obj))

/-- The endofunctor of the full subcategory `P` induced by `E`. -/
abbrev liftFunctor : P.FullSubcategory ⥤ P.FullSubcategory := P.lift (P.ι ⋙ E) hE

/-- The restriction of an endomorphism of `E` to `P`. -/
def liftEnd (a : End E) : End (liftFunctor P hE) where
  app M := P.homMk (a.app M.obj)
  naturality _ _ f := P.hom_ext (a.naturality f.hom)

/-- The restriction of an endomorphism of `E²` to `P`. -/
def liftEnd₂ (b : End (E ⋙ E)) : End (liftFunctor P hE ⋙ liftFunctor P hE) where
  app M := P.homMk (b.app M.obj)
  naturality _ _ f := P.hom_ext (b.naturality f.hom)

theorem liftEnd_pow (a : End E) (N : ℕ) : liftEnd P hE a ^ N = liftEnd P hE (a ^ N) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [pow_succ, ih, pow_succ]
    rfl

variable [Preadditive C] (D : NilHeckeData E)

/-- **The nilHecke action on the restriction of `E` to a full subcategory.** -/
def lift : NilHeckeData (liftFunctor P hE) where
  X := liftEnd P hE D.X
  T := liftEnd₂ P hE D.T
  T_mul_T := NatTrans.ext (funext fun M =>
    P.hom_ext (congrArg (fun t : End (E ⋙ E) => t.app M.obj) D.T_mul_T))
  braid := NatTrans.ext (funext fun M =>
    P.hom_ext (congrArg (fun t : End ((E ⋙ E) ⋙ E) => t.app M.obj) D.braid))
  x_T_sub := NatTrans.ext (funext fun M =>
    P.hom_ext (congrArg (fun t : End (E ⋙ E) => t.app M.obj) D.x_T_sub))
  T_x_sub := NatTrans.ext (funext fun M =>
    P.hom_ext (congrArg (fun t : End (E ⋙ E) => t.app M.obj) D.T_x_sub))

theorem lift_X : (D.lift P hE).X = liftEnd P hE D.X := rfl

theorem lift_X_pow_eq_zero {N : ℕ} (h : D.X ^ N = 0) : (D.lift P hE).X ^ N = 0 := by
  rw [lift_X, liftEnd_pow, h]
  exact NatTrans.ext (funext fun M => P.hom_ext rfl)

end Lift

section Dual

variable [Preadditive C] {E F : C ⥤ C} [E.Additive] (D : NilHeckeData E) (adj : E ⊣ F)

theorem dual_X_pow_eq_zero {N : ℕ} (h : D.X ^ N = 0) : (D.dual adj).X ^ N = 0 := by
  rw [dual_X, neg_pow, ← mateEnd_pow, h, mateEnd_zero, mul_zero]

end Dual

theorem isNilpotent_app_of_pow_eq_zero [Preadditive C] {E : C ⥤ C} {a : End E} {N : ℕ}
    (h : a ^ N = 0) (M : C) : IsNilpotent (R := End (E.obj M)) (a.app M) := by
  refine ⟨N, ?_⟩
  have key : ∀ n, (show End (E.obj M) from a.app M) ^ n = (a ^ n).app M := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ, ih, pow_succ, End.mul_def, End.mul_def, NatTrans.comp_app]
  rw [key, h]
  rfl

end NilHeckeData

end Categorification.Sl2
