/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoNativeTor
import Categorification.WeightedKLR.RedStrands.LabelTwoUnknotGrading

/-!
# The label-two middle Tor in characteristic two

In the middle-algebra calculation preceding Webster, arXiv:1309.3796v2,
§8.2, Proposition 8.4, the surviving differential is multiplication by
twice epsilon. In characteristic two the entire specialized complex has
zero differential.
-/

namespace Categorification.Webster.LabelTwo

open CategoryTheory

noncomputable section

universe u
variable {k : Type u} [Field k]

local notation "T" => postTensorComplex (k := k)

/-- Both kinds of specialized differential vanish in characteristic two. -/
theorem postTensorComplex_d_eq_zero_of_two_eq_zero (h2 : (2 : k) = 0) (i j : ℕ) :
    (T).d i j = 0 := by
  by_cases h : i = j + 1
  · subst i
    apply ModuleCat.hom_ext
    rw [postTensorComplex_d_succ, twiceEps_eq_zero_of_two_eq_zero h2, ite_self]
    rfl
  · apply (T).shape i j
    simpa only [ComplexShape.down_Rel, eq_comm] using h

/-- In characteristic two every native middle Tor is the dual-number module. -/
def middleTor_of_two_eq_zero (h2 : (2 : k) = 0) (n : ℕ) :
    middleTor (k := k) n ≅ ModuleCat.of k (DualNumber k) :=
  middleTorHomologyIso n ≪≫
    (ShortComplex.LeftHomologyData.ofZeros (S := (T).sc n)
      (postTensorComplex_d_eq_zero_of_two_eq_zero h2 _ _)
      (postTensorComplex_d_eq_zero_of_two_eq_zero h2 _ _)).homologyIso

end

end Categorification.Webster.LabelTwo
