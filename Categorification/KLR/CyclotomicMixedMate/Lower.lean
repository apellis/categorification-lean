/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.KLR.CyclotomicMixedMate.Upper

/-!
# The lower accepted crossing comparison

`lowerAcceptedSource` identifies the original lower tensor with the source of the
cyclotomic crossing equivalence, using the actual lower weight transports.
-/

noncomputable section
namespace Categorification.KLR.KLRAlgebra.AbsentColour.MixedComparison
open MulOpposite MixedTransport
variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (a : I → Polynomial k)
  (γ : Multiset I) (i j : I)

abbrev lowerWeight (c : I) := weightEquiv Q a (add_comm γ ({c} : Multiset I))

def leftWeight : MixedCyclotomic.QuotientLeft Q γ j a ≃ₗ[k] IndCorner Q j a γ where
  toFun x := ⟨lowerWeight Q a γ j x.1, by
    change lowerWeight Q a γ j x.1 * cyclotomicLast Q j a γ 1 = _
    rw [last_eq_weight_inc, ← map_mul]
    exact congrArg (lowerWeight Q a γ j) (CornerTensor.left_mem _ x)⟩
  invFun x := ⟨(lowerWeight Q a γ j).symm x.1, by
    change (lowerWeight Q a γ j).symm x.1 * MixedCyclotomic.quotientInc Q a γ j 1 = _
    apply (lowerWeight Q a γ j).injective
    rw [map_mul, AlgEquiv.apply_symm_apply, ← last_eq_weight_inc]
    exact x.2⟩
  left_inv x := Subtype.ext ((lowerWeight Q a γ j).symm_apply_apply x.1)
  right_inv x := Subtype.ext ((lowerWeight Q a γ j).apply_symm_apply x.1)
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' c x := Subtype.ext (map_smul _ _ _)

def rightWeight : MixedCyclotomic.QuotientRight Q γ i a ≃ₗ[k]
    MixedModule.Coefficient Q γ i a where
  toFun y := ⟨lowerWeight Q a γ i y.1, by
    change cyclotomicLast Q i a γ 1 * lowerWeight Q a γ i y.1 = _
    rw [last_eq_weight_inc, ← map_mul]
    exact congrArg (lowerWeight Q a γ i) (CornerTensor.right_mem _ _ y)⟩
  invFun y := ⟨(lowerWeight Q a γ i).symm y.1, by
    change MixedCyclotomic.quotientInc Q a γ i 1 * (lowerWeight Q a γ i).symm y.1 = _
    apply (lowerWeight Q a γ i).injective
    rw [map_mul, AlgEquiv.apply_symm_apply, ← last_eq_weight_inc]
    exact y.2⟩
  left_inv y := Subtype.ext ((lowerWeight Q a γ i).symm_apply_apply y.1)
  right_inv y := Subtype.ext ((lowerWeight Q a γ i).apply_symm_apply y.1)
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' c x := Subtype.ext (map_smul _ _ _)

theorem leftWeight_right (r : CycKLR k Q a γ) (x : MixedCyclotomic.QuotientLeft Q γ j a) :
    leftWeight Q a γ j (op r • x) = op r • leftWeight Q a γ j x := by
  apply Subtype.ext
  change lowerWeight Q a γ j (x.1 * MixedCyclotomic.quotientInc Q a γ j r) =
    lowerWeight Q a γ j x.1 * cyclotomicLast Q j a γ r
  rw [map_mul, last_eq_weight_inc]

theorem rightWeight_left (r : CycKLR k Q a γ)
    (y : MixedCyclotomic.QuotientRight Q γ i a) :
    rightWeight Q a γ i (r • y) = r • rightWeight Q a γ i y := by
  apply Subtype.ext
  change lowerWeight Q a γ i (MixedCyclotomic.quotientInc Q a γ i r * y.1) =
    cyclotomicLast Q i a γ r * lowerWeight Q a γ i y.1
  rw [map_mul, last_eq_weight_inc]

def fromAcceptedBil : MixedCyclotomic.QuotientLeft Q γ j a →ₗ[k]
    MixedCyclotomic.QuotientRight Q γ i a →ₗ[k] MixedModule.Lower Q γ i j a :=
  LinearMap.mk₂ k (fun x y => BalancedTensor.tmul (leftWeight Q a γ j x) (rightWeight Q a γ i y))
    (fun x z y => by rw [map_add, BalancedTensor.add_tmul])
    (fun c x y => by rw [map_smul, BalancedTensor.smul_tmul])
    (fun x y z => by rw [map_add, BalancedTensor.tmul_add])
    (fun c x y => by rw [map_smul, BalancedTensor.tmul_smul])

def fromAccepted : MixedCyclotomic.QuotientSource Q γ i j a →ₗ[k]
    MixedModule.Lower Q γ i j a :=
  BalancedTensor.lift (fromAcceptedBil Q a γ i j) (fun x r y => by
    change BalancedTensor.tmul (leftWeight Q a γ j (op r • x)) (rightWeight Q a γ i y) =
      BalancedTensor.tmul (leftWeight Q a γ j x) (rightWeight Q a γ i (r • y))
    rw [leftWeight_right, rightWeight_left, BalancedTensor.op_smul_tmul])

def toAcceptedBil : IndCorner Q j a γ →ₗ[k]
    MixedModule.Coefficient Q γ i a →ₗ[k] MixedCyclotomic.QuotientSource Q γ i j a :=
  LinearMap.mk₂ k (fun x y =>
    BalancedTensor.tmul ((leftWeight Q a γ j).symm x) ((rightWeight Q a γ i).symm y))
    (fun x z y => by rw [map_add, BalancedTensor.add_tmul])
    (fun c x y => by rw [map_smul, BalancedTensor.smul_tmul])
    (fun x y z => by rw [map_add, BalancedTensor.tmul_add])
    (fun c x y => by rw [map_smul, BalancedTensor.tmul_smul])

def toAccepted : MixedModule.Lower Q γ i j a →ₗ[k]
    MixedCyclotomic.QuotientSource Q γ i j a :=
  BalancedTensor.lift (toAcceptedBil Q a γ i j) (fun x r y => by
    change BalancedTensor.tmul ((leftWeight Q a γ j).symm (op r • x))
      ((rightWeight Q a γ i).symm y) =
        BalancedTensor.tmul ((leftWeight Q a γ j).symm x)
          ((rightWeight Q a γ i).symm (r • y))
    have hx : (leftWeight Q a γ j).symm (op r • x) =
        op r • (leftWeight Q a γ j).symm x := by
      apply (leftWeight Q a γ j).injective
      rw [LinearEquiv.apply_symm_apply, leftWeight_right, LinearEquiv.apply_symm_apply]
    have hy : (rightWeight Q a γ i).symm (r • y) =
        r • (rightWeight Q a γ i).symm y := by
      apply (rightWeight Q a γ i).injective
      rw [LinearEquiv.apply_symm_apply, rightWeight_left, LinearEquiv.apply_symm_apply]
    rw [hx, hy, BalancedTensor.op_smul_tmul])

@[simp] theorem fromAccepted_tmul (x : MixedCyclotomic.QuotientLeft Q γ j a)
    (y : MixedCyclotomic.QuotientRight Q γ i a) :
    fromAccepted Q a γ i j (BalancedTensor.tmul x y) =
      BalancedTensor.tmul (leftWeight Q a γ j x) (rightWeight Q a γ i y) := rfl

@[simp] theorem toAccepted_tmul (x : IndCorner Q j a γ) (y : MixedModule.Coefficient Q γ i a) :
    toAccepted Q a γ i j (BalancedTensor.tmul x y) =
      BalancedTensor.tmul ((leftWeight Q a γ j).symm x) ((rightWeight Q a γ i).symm y) := rfl

/-- Weight comparison with the accepted source, balanced over the actual lower quotient. -/
def lowerAcceptedSource : MixedModule.Lower Q γ i j a ≃ₗ[k]
    MixedCyclotomic.QuotientSource Q γ i j a :=
  LinearEquiv.ofLinearMap (toAccepted Q a γ i j) (fromAccepted Q a γ i j)
    (by
      apply BalancedTensor.ext
      intro x y
      simp only [LinearMap.coe_comp, Function.comp_apply, fromAccepted_tmul, toAccepted_tmul,
        LinearEquiv.symm_apply_apply, LinearMap.id_apply])
    (by
      apply BalancedTensor.ext
      intro x y
      simp only [LinearMap.coe_comp, Function.comp_apply, fromAccepted_tmul, toAccepted_tmul,
        LinearEquiv.apply_symm_apply, LinearMap.id_apply])

end Categorification.KLR.KLRAlgebra.AbsentColour.MixedComparison
