/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.AdjointPositive

/-!
# Powers of 2-morphisms in `Cat`

For a natural endomorphism `x` of a 1-morphism of `Cat`, the underlying transformation of the
power `powComp x m` is the `m`-th power of that of `x` in the endomorphism monoid
(`TwoRep.Cat.powComp_toNatTrans`). Hence the dotted counits `R x^m ε` and the dotted units
`η x^m R` of an adjunction in `Cat` (Brundan, arXiv:1501.00350v1, (1.8) and (1.9)) are the
corresponding whiskered powers of natural transformations (`TwoRep.Cat.dottedCap_toNatTrans`,
`TwoRep.Cat.dottedCup_toNatTrans`).
-/

namespace Categorification.TwoRep.Cat

open CategoryTheory CategoryTheory.Bicategory

universe v u

variable {C D : CategoryTheory.Cat.{v, u}}

/-- The transformation underlying `powComp x m` is the power `x^m`. -/
theorem powComp_toNatTrans {F : C ⟶ D} (x : F ⟶ F) (m : ℕ) :
    (powComp x m).toNatTrans = (show End F.toFunctor from x.toNatTrans) ^ m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [powComp_succ, CategoryTheory.Cat.Hom.toNatTrans_comp, ih, pow_succ']
    rfl

/-- The dotted counit `R x^m ε` in `Cat`. -/
theorem dottedCap_toNatTrans {R : D ⟶ C} {E : C ⟶ D} (x : E ⟶ E) (κ : R ≫ E ⟶ 𝟙 D) (m : ℕ) :
    (R ◁ powComp x m ≫ κ).toNatTrans =
      Functor.whiskerLeft R.toFunctor ((show End E.toFunctor from x.toNatTrans) ^ m) ≫
        κ.toNatTrans := by
  rw [CategoryTheory.Cat.Hom.toNatTrans_comp, ← powComp_toNatTrans]
  rfl

/-- The dotted unit `η x^m R` in `Cat`. -/
theorem dottedCup_toNatTrans {R : D ⟶ C} {E : C ⟶ D} (x : E ⟶ E) (η : 𝟙 C ⟶ E ≫ R) (m : ℕ) :
    (η ≫ powComp x m ▷ R).toNatTrans =
      η.toNatTrans ≫
        Functor.whiskerRight ((show End E.toFunctor from x.toNatTrans) ^ m) R.toFunctor := by
  rw [CategoryTheory.Cat.Hom.toNatTrans_comp, ← powComp_toNatTrans]
  rfl

end Categorification.TwoRep.Cat
