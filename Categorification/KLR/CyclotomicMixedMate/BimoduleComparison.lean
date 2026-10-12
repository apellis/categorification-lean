/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.KLR.CyclotomicMixedMate.NaturalInverse

/-!
# Both outer actions of the mixed comparisons

Each lower and upper accepted comparison preserves both original coefficient
actions under the actual weight equivalences. These are concrete bimodule identities.
-/

noncomputable section
namespace Categorification.KLR.KLRAlgebra.AbsentColour.MixedComparison
open MulOpposite
variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (a : I → Polynomial k)
  (γ : Multiset I) (i j : I)

/-- The lower weight comparison preserves the left action under the actual weight transport. -/
theorem lowerAcceptedSource_left (b : CycKLR k Q a ({j} + γ))
    (z : MixedModule.Lower Q γ i j a) :
    lowerAcceptedSource Q a γ i j (b • z) =
      (lowerWeight Q a γ j).symm b • lowerAcceptedSource Q a γ i j z := by
  induction z using BalancedTensor.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | add z t hz ht => simp only [smul_add, map_add, hz, ht]
  | tmul x y =>
    change toAccepted Q a γ i j (b • BalancedTensor.tmul x y) =
      (lowerWeight Q a γ j).symm b • toAccepted Q a γ i j (BalancedTensor.tmul x y)
    rw [BalancedTensor.smul_tmul', toAccepted_tmul, toAccepted_tmul,
      BalancedTensor.smul_tmul']
    congr 1
    apply Subtype.ext
    exact map_mul (lowerWeight Q a γ j).symm b x.1

/-- The lower weight comparison preserves right multiplication, with its required order. -/
theorem lowerAcceptedSource_right (c : CycKLR k Q a ({i} + γ))
    (z : MixedModule.Lower Q γ i j a) :
    lowerAcceptedSource Q a γ i j (op c • z) =
      MixedCyclotomic.quotientRightAct Q γ i j a ((lowerWeight Q a γ i).symm c)
        (lowerAcceptedSource Q a γ i j z) := by
  induction z using BalancedTensor.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | add z t hz ht => simp only [smul_add, map_add, hz, ht]
  | tmul x y =>
    change toAccepted Q a γ i j (op c • BalancedTensor.tmul x y) = _
    rw [MixedModule.lower_op_tmul, toAccepted_tmul]
    change BalancedTensor.tmul ((leftWeight Q a γ j).symm x)
      ((rightWeight Q a γ i).symm (MixedModule.rightMul Q γ i a c y)) =
        BalancedTensor.tmul ((leftWeight Q a γ j).symm x)
          (MixedCyclotomic.quotientRightMul Q γ i a ((lowerWeight Q a γ i).symm c)
            ((rightWeight Q a γ i).symm y))
    congr 1
    apply Subtype.ext
    exact map_mul (lowerWeight Q a γ i).symm y.1 c

/-- The actual upper corner comparison preserves the differently ordered left action. -/
theorem upperAcceptedCorner_left (b : CycKLR k Q a (γ + {j}))
    (z : MixedCyclotomic.QuotientCorner Q γ i j a) :
    upperAcceptedCorner Q a γ i j (MixedCyclotomic.quotientCornerLeft Q γ i j a b z) =
      lowerWeight Q a γ j b • upperAcceptedCorner Q a γ i j z := by
  apply Subtype.ext
  change upperWeight Q a γ i j (MixedCyclotomic.quotientInc Q a (γ + {j}) i b * z.1) =
    leftInc Q a γ i j (lowerWeight Q a γ j b) * upperWeight Q a γ i j z.1
  rw [map_mul, upperWeight_left]

/-- The actual upper corner comparison preserves right multiplication. -/
theorem upperAcceptedCorner_right (c : CycKLR k Q a (γ + {i}))
    (z : MixedCyclotomic.QuotientCorner Q γ i j a) :
    upperAcceptedCorner Q a γ i j (MixedCyclotomic.quotientCornerRight Q γ i j a c z) =
      op (lowerWeight Q a γ i c) • upperAcceptedCorner Q a γ i j z := by
  apply Subtype.ext
  change upperWeight Q a γ i j (z.1 * MixedCyclotomic.quotientBotLinear Q γ i j a c) =
    upperWeight Q a γ i j z.1 * cyclotomicLast Q j a ({i} + γ) (lowerWeight Q a γ i c)
  rw [map_mul, upperWeight_right]

end Categorification.KLR.KLRAlgebra.AbsentColour.MixedComparison
