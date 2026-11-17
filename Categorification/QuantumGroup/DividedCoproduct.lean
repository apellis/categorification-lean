/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.QuantumGroup.GabberKacBridge
import LieLean.Algebra.QuantumGroup.TensorModule

/-!
# The coproduct of divided lowering operators

Webster, arXiv:1309.3796v2, §4.7 and (5.10), with the symmetric
quantum factorial convention of Lusztig, §1.3. The coproduct has two
quantum-commuting summands, so division by the factorial leaves a
Laurent monomial in each coefficient.
-/

noncomputable section

namespace Categorification.QuantumGroup

open LieLean.QuantumGroup Finset

variable {k A : Type*} [Field k] [Ring A] [Algebra k A]

/-- The divided quantum binomial formula, in the normalization of
Lusztig, §1.3.5. -/
theorem qDivPow_add_of_qcomm (t : kˣ) (a b : A)
    (h : b * a = ((t ^ (2 : ℤ) : kˣ) : k) • (a * b)) (n : ℕ)
    (ht : qFactorial (t : k) n ≠ 0) :
    qDivPow (t : k) n (a + b) = ∑ p ∈ antidiagonal n,
      ((t ^ ((p.1 : ℤ) * p.2) : kˣ) : k) •
        (qDivPow (t : k) p.1 a * qDivPow (t : k) p.2 b) := by
  rw [qDivPow, qbinomial_theorem t h, Finset.smul_sum]
  apply sum_congr rfl
  rintro ⟨r, s⟩ hrs
  obtain rfl := mem_antidiagonal.mp hrs
  have hu : qfact t (r + s) ≠ 0 := by rwa [← PreF.qFactorial_eq_qfact]
  simp only [qDivPow, PreF.qFactorial_eq_qfact, qbinomCoef,
    qbinom_eq_div t hu, smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  field_simp

open LieLean
open scoped TensorProduct

variable {I Y : Type*} [DecidableEq I] [AddCommGroup Y] {D : LusztigCartanDatum I}
    (R : D.RootDatum Y)
local notation "𝕍" => (RatFunc.X : RatFunc ℚ)
local notation "𝕂" => RatFunc ℚ
local notation "𝕌" => LieLean.QuantumGroup R 𝕍
local instance : NeZero 𝕍 := ⟨RatFunc.X_ne_zero⟩

/-- The divided lowering coproduct, with the right-hand torus ordered to act
before the right-hand lowering operator (Webster, (5.10); Lusztig, §3.1). -/
theorem comul_dividedF (i : I) (n : ℕ) :
    comul R 𝕍 (qDivPow (𝕍 ^ D.d i) n (F R 𝕍 i)) =
      ∑ p ∈ antidiagonal n, ((𝕍 ^ D.d i) ^ (p.1 * p.2)) •
        (qDivPow (𝕍 ^ D.d i) p.2 (F R 𝕍 i) ⊗ₜ[𝕂]
          (qDivPow (𝕍 ^ D.d i) p.1 (F R 𝕍 i) * K R 𝕍 (-ktilde R i) ^ p.2)) := by
  let t : 𝕂ˣ := vQ ^ D.d i
  let x : 𝕌 ⊗[𝕂] 𝕌 := 1 ⊗ₜ[𝕂] F R 𝕍 i
  let y : 𝕌 ⊗[𝕂] 𝕌 := F R 𝕍 i ⊗ₜ[𝕂] K R 𝕍 (-ktilde R i)
  have ht : (t : 𝕂) = 𝕍 ^ D.d i := by simp [t]
  have hz (a : ℕ) (ha : 0 < a) : (𝕍 ^ D.d i) ^ a ≠ 1 := by
    rw [← pow_mul]
    change (vQ : 𝕂) ^ (D.d i * a) ≠ 1
    rw [← Units.val_pow_eq_pow_val, ne_eq, Units.val_eq_one]
    exact vQ_pow_ne_one (mul_pos (D.d_pos i) ha)
  have hf : qFactorial (t : 𝕂) n ≠ 0 := by
    rw [ht]
    exact qFactorial_ne_zero (pow_ne_zero _ RatFunc.X_ne_zero) (fun m hm _ => hz _ (by omega))
  have hcomm : y * x = ((t ^ (2 : ℤ) : 𝕂ˣ) : 𝕂) • (x * y) := by
    simp only [x, y, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, K_mul_F,
      map_neg, neg_neg, root_ktilde, D.cartanMatrix_self, TensorProduct.tmul_smul]
    congr 1
    rw [Units.val_zpow_eq_zpow_val, ht, ← zpow_natCast, ← zpow_mul]
  have he : comul R 𝕍 (qDivPow (𝕍 ^ D.d i) n (F R 𝕍 i)) = qDivPow (t : 𝕂) n (x + y) := by
    rw [ht, qDivPow, qDivPow, map_smul, map_pow, comul_F, add_comm]
  rw [he, qDivPow_add_of_qcomm t x y hcomm n hf]
  apply Finset.sum_congr rfl
  rintro ⟨r, s⟩ _
  rw [Units.val_zpow_eq_zpow_val, ht, ← Nat.cast_mul, zpow_natCast]
  congr 1
  simp only [qDivPow, x, y, Algebra.TensorProduct.tmul_pow, one_pow, smul_mul_assoc,
    mul_smul_comm, Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.tmul_smul,
    TensorProduct.smul_tmul', smul_smul]
  rw [mul_comm]

end Categorification.QuantumGroup
