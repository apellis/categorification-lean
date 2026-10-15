/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.KLR.CyclotomicMixedMate.Weight

/-!
# The accepted mixed coefficient equivalence

`coefficientEquiv` composes the lower comparison, `quotientTauEquiv`, and upper
comparison. Its signed formula and both outer coefficient actions are proved.
-/

noncomputable section
namespace Categorification.KLR.KLRAlgebra.AbsentColour.MixedComparison
open MulOpposite MixedTransport MixedMate
variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (a : I → Polynomial k)
  (γ : Multiset I) (i j : I)
local notation "A" => CycKLR k Q a ((Singleton.singleton j : Multiset I) + γ)
local notation "C" => CycKLR k Q a ((Singleton.singleton i : Multiset I) + γ)
variable (hij : i ≠ j) (hsym : KLRSymm Q)

/-- Accepted cyclotomic equivalence, in the two original weight conventions. -/
def coefficientEquiv : MixedModule.Lower Q γ i j a ≃ₗ[k] Corner Q a γ i j :=
  (lowerAcceptedSource Q a γ i j).trans
    ((MixedCyclotomic.quotientTauEquiv Q γ i j a hij hsym).trans
      (upperAcceptedCorner Q a γ i j))

theorem quotientTau_quotient_tmul (x : MixedCyclotomic.QuotientLeft Q γ j a)
    (y : MixedCyclotomic.QuotientRight Q γ i a) :
    (MixedCyclotomic.quotientTau Q γ i j a hij hsym (BalancedTensor.tmul x y)).1 =
      MixedCyclotomic.quotientInc Q a (γ + {j}) i x.1 *
        (-CycKLR.mk k Q a ((γ + {j}) + {i}) (ψ (Multiset.card γ))) *
          MixedCyclotomic.quotientBotLinear Q γ i j a y.1 := by
  obtain ⟨x, rfl⟩ := MixedCyclotomic.leftMk_surjective Q γ j a x
  obtain ⟨y, rfl⟩ := MixedCyclotomic.rightMk_surjective Q γ i a y
  rw [MixedCyclotomic.quotientTau_tmul]
  change _ = MixedCyclotomic.quotientInc Q a (γ + {j}) i (CycKLR.mk k Q a _ x.1) *
    (-CycKLR.mk k Q a _ (ψ (Multiset.card γ))) *
      MixedCyclotomic.quotientBotLinear Q γ i j a (CycKLR.mk k Q a _ y.1)
  rw [MixedCyclotomic.quotientInc_mk, MixedCyclotomic.quotientBotLinear_mk]
  simp only [map_neg, map_mul, mul_neg, neg_mul]
  rfl

theorem upperWeight_psi :
    upperWeight Q a γ i j (CycKLR.mk k Q a ((γ + {j}) + {i}) (ψ (Multiset.card γ))) =
      (κ Q a γ i j).symm (CycKLR.mk k Q a ({i} + ({j} + γ)) (ψ (Multiset.card γ))) := by
  change weightEquiv Q a _ _ = _
  rw [κ, weightEquiv_symm, weightEquiv_mk, weightEquiv_mk]
  congr 1
  rw [castKLR_ψ, castKLR_ψ]

/-- The accepted equivalence has the actual ordinary-mate coefficient, not an assumed one. -/
theorem coefficientEquiv_tmul (x : IndCorner Q j a γ)
    (y : MixedModule.Coefficient Q γ i a) :
    (coefficientEquiv Q a γ i j hij hsym (BalancedTensor.tmul x y)).1 =
      (op y.1 • factor Q a γ i j x).1 := by
  change upperWeight Q a γ i j
    (MixedCyclotomic.quotientTau Q γ i j a hij hsym
      (toAccepted Q a γ i j (BalancedTensor.tmul x y))).1 = _
  rw [toAccepted_tmul, quotientTau_quotient_tmul, map_mul, map_mul, map_neg,
    upperWeight_left, upperWeight_right, upperWeight_psi]
  change leftInc Q a γ i j (lowerWeight Q a γ j ((lowerWeight Q a γ j).symm x.1)) *
    (-(κ Q a γ i j).symm (CycKLR.mk k Q a _ (ψ (Multiset.card γ)))) *
      cyclotomicLast Q j a ({i} + γ) (lowerWeight Q a γ i ((lowerWeight Q a γ i).symm y.1)) = _
  rw [AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply, factor_right_signed]
  change (κ Q a γ i j).symm (cyclotomicLast Q i a ({j} + γ) x.1) * _ * _ = _
  rw [map_mul, map_mul, map_neg, AlgEquiv.symm_apply_apply]

/-- The weight-compared accepted equivalence respects the original left action. -/
theorem coefficientEquiv_left (b : A) (z : MixedModule.Lower Q γ i j a) :
    coefficientEquiv Q a γ i j hij hsym (b • z) =
      b • coefficientEquiv Q a γ i j hij hsym z := by
  induction z using BalancedTensor.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | add z t hz ht => simp only [smul_add, map_add, hz, ht]
  | tmul x y =>
    rw [BalancedTensor.smul_tmul']
    apply Subtype.ext
    rw [coefficientEquiv_tmul]
    change (op y.1 • factor Q a γ i j (b • x)).1 =
      leftInc Q a γ i j b * (coefficientEquiv Q a γ i j hij hsym
        (BalancedTensor.tmul x y)).1
    rw [coefficientEquiv_tmul]
    change (κ Q a γ i j).symm (cyclotomicLast Q i a ({j} + γ) (b * x.1) *
      coefficient Q a γ i j) * cyclotomicLast Q j a ({i} + γ) y.1 = _
    change (κ Q a γ i j).symm (cyclotomicLast Q i a ({j} + γ) (b * x.1) *
      coefficient Q a γ i j) * cyclotomicLast Q j a ({i} + γ) y.1 =
        (κ Q a γ i j).symm (cyclotomicLast Q i a ({j} + γ) b) *
          ((κ Q a γ i j).symm (cyclotomicLast Q i a ({j} + γ) x.1 *
            coefficient Q a γ i j) * cyclotomicLast Q j a ({i} + γ) y.1)
    simp only [map_mul, mul_assoc]

/-- The weight-compared accepted equivalence respects the original right action. -/
theorem coefficientEquiv_right (c : C) (z : MixedModule.Lower Q γ i j a) :
    coefficientEquiv Q a γ i j hij hsym (op c • z) =
      op c • coefficientEquiv Q a γ i j hij hsym z := by
  induction z using BalancedTensor.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | add z t hz ht => simp only [smul_add, map_add, hz, ht]
  | tmul x y =>
    change coefficientEquiv Q a γ i j hij hsym
      (BalancedTensor.tmul x (MixedModule.rightMul Q γ i a c y)) = _
    apply Subtype.ext
    rw [coefficientEquiv_tmul]
    change (factor Q a γ i j x).1 * cyclotomicLast Q j a ({i} + γ) (y.1 * c) =
      (coefficientEquiv Q a γ i j hij hsym (BalancedTensor.tmul x y)).1 *
        cyclotomicLast Q j a ({i} + γ) c
    rw [coefficientEquiv_tmul, map_mul]
    exact (mul_assoc _ _ _).symm

end Categorification.KLR.KLRAlgebra.AbsentColour.MixedComparison
