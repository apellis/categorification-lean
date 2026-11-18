/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicDottedTraceCoordinates
import Categorification.WeightedKLR.RedStrands.CyclotomicRedTracePolynomial

/-!
# Red projection of dotted cap coordinates

For the red crossing of Webster, arXiv:1309.3796v2, §4.5, Theorem 4.25,
taking the complementary polynomial coordinate on an affine representative
commutes with projection of its coefficients to the smaller cyclotomic algebra.
-/

noncomputable section
namespace Categorification.Stendhal
open KLR KLRAlgebra
variable {I k : Type*} [DecidableEq I] [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) {a b : I → Polynomial k}
  (hab : ∀ j, a j ∣ b j) (i : I) (γ : Multiset I) (hsym : KLRSymm Q)
local notation "β" => ((Singleton.singleton i : Multiset I) + γ)
local notation "B" => ((Singleton.singleton i : Multiset I) + β)
local notation "y" => (x (Q := Q) (ν := B) (Fin.mk (Multiset.card β) (lastPos_lt i β)))
local notation "e" => cL Q i β 1
local notation "π" => cyclotomicRedProjection Q hab β

private theorem dotPow_mk (a : I → Polynomial k) (n : ℕ) (r : KLRAlgebra k Q B) :
    (lastDot0 i β a ^ n) (Submodule.Quotient.mk r) = Submodule.Quotient.mk (r * y ^ n) := by
  induction n with
  | zero => rw [pow_zero, Module.End.one_apply, pow_zero, mul_one]
  | succ n ih => rw [pow_succ', Module.End.mul_apply, ih, lastDot0_mk, pow_succ, mul_assoc]

private theorem dottedCapPolynomial_mk (a : I → Polynomial k) (n : ℕ) (r : KLRAlgebra k Q B) :
    CornerTrace.dottedCapPolynomial Q i γ a hsym n (middleTensorLift Q i γ a (Submodule.Quotient.mk r)) =
      cPoly i β hsym a (e * (r * e) * y ^ n) := by
  change cMap i β hsym a (zero_lt_card_single_add i γ) ((lastDot0 i β a ^ n) (eiZeroCoordinates Q i γ a _)) = _
  rw [middleTensorLift_coordinates, act0_mk]
  change cMap i β hsym a (zero_lt_card_single_add i γ) ((lastDot0 i β a ^ n) (Submodule.Quotient.mk (e * (r * e)))) = _
  rw [dotPow_mk, cMap_mk]

/-- The physical last dot commutes with the cut idempotent, and each
coefficient of the KK polynomial coordinate projects along the red quotient. -/
theorem redProjection_dottedCapPolynomial (N d : ℕ) (r : KLRAlgebra k Q B) :
    (CornerTrace.dottedCapPolynomial Q i γ b hsym N
      (middleTensorLift Q i γ b (Submodule.Quotient.mk (r * y ^ d)))).map (π).toRingHom =
    CornerTrace.dottedCapPolynomial Q i γ a hsym (N+d)
      (middleTensorLift Q i γ a (Submodule.Quotient.mk r)) := by
  rw [dottedCapPolynomial_mk, dottedCapPolynomial_mk]
  have hc := ((commute_x_last_cL (Q := Q) i β 1).pow_left d).eq
  rw [mul_assoc r (y ^ d) e, hc, Nat.add_comm N d, pow_add]
  simp only [mul_assoc]
  let u := cCoord i β hsym (e * (r * (e * (y ^ d * y ^ N))))
  let v := theta Q i β (Algebra.TensorProduct.comm k _ _ u)
  change (v.map (CycKLR.mk k Q b β).toRingHom).map (π).toRingHom =
    v.map (CycKLR.mk k Q a β).toRingHom
  ext j
  simp only [Polynomial.coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    cyclotomicRedProjection_mk]

end Categorification.Stendhal
