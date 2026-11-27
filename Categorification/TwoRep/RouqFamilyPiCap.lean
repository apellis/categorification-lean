/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqFamilyPi
import Categorification.TwoRep.RouqModel

/-!
# Leftward caps of a product of Rouquier families

In a product of Rouquier families (`RouqFamily.pi`) the leftward cap of Brundan,
arXiv:1501.00350v1, (1.15) and (1.17), is computed factor by factor (`piLoc_capL_app`). Hence
so is the counit of the left adjunction `F_i ⊣ E_i` built from the local Rouquier data
(`pi_adjL_counit_app`).
-/

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Bicategory

universe w v u u₀ u₁

variable {k : Type w} [CommRing k] {J : Type u₀}
  {I : Type*} {C : QuantumGroup.CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  {RD : QuantumGroup.UDot.WeightDatum C X Y}

namespace RouqFamily

variable (S : J → RouqFamily (B := LinearCat.{w, v, u} k) RD)

/-- **The leftward cap of a product** is the leftward cap of each factor. -/
theorem piLoc_capL_app (i : I) {a b c : X} (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX i = c)
    (M : LinearCat.pi fun j => (S j).obj b) (j : J) :
    (piLoc S i h₁ h₂).capL.hom.app M j = ((S j).loc i h₁ h₂).capL.hom.app (M j) := by
  unfold RouqLoc.capL RouqLoc.capN RouqLoc.sigL RouqLoc.capD
  split_ifs <;>
    simp only [LinearCat.pi_comp_app, LinearCat.pi_neg_app, LinearCat.powComp_piCell] <;> rfl

/-- **The counit of the left adjunction `F_i ⊣ E_i` of a product** is the counit of each
factor. -/
theorem pi_adjL_counit_app (i : I) {x y : X} (h : x + RD.iX i = y)
    (M : LinearCat.pi fun j => (S j).obj x) (j : J) :
    ((pi S).adjL i h).counit.hom.app M j = ((S j).adjL i h).counit.hom.app (M j) :=
  piLoc_capL_app S i (sub_add_cancel x (RD.iX i)) h M j

end RouqFamily

end Categorification.TwoRep
