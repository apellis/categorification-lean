/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.SingleBlackShapovalov
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.HighestWeightForm
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.HighestWeightIntegral
import LieLean.Algebra.QuantumGroup.Modified.TensorVermaQuasiR

/-!
# Pairing along a saturated simple-root string

Webster, arXiv:1309.3796v2, Proposition 7.2. The divided-power normalization
preserves the pairing between the two ends of an entire primitive string.
-/


open LieLean.QuantumGroup

noncomputable section
namespace Categorification.Stendhal

private theorem endpoint_of_string_recurrence {k : Type*} [Field k] (q : k) (hq : q ≠ 0)
    (hn : ∀ j : ℕ, 0 < j → qInt q j ≠ 0) (n : ℕ) (f : ℕ → k) (f0 : f 0 = 1)
    (step : ∀ j < n, f (j + 1) =
      f j * ((qInt q (j + 1))⁻¹ * q ^ (2 * (j : ℤ) + 1 - n) * qInt q (n - j))) :
    f n = 1 := by
  have fact (r : ℕ) : qFactorial q r ≠ 0 := by
    induction r with
    | zero => simp
    | succ r ih => exact mul_ne_zero (hn _ (Nat.succ_pos r)) ih
  have h (j : ℕ) (hj : j ≤ n) :
      f j * qFactorial q j * qFactorial q (n - j) =
        q ^ ((j : ℤ) * (j - (n : ℤ))) * qFactorial q n := by
    induction j with
    | zero => simp [f0]
    | succ j ih =>
      have hlt : j < n := hj
      have hsub : n - j = n - (j + 1) + 1 := by omega
      have hfac : qInt q (n - j) * qFactorial q (n - (j + 1)) = qFactorial q (n - j) := by
        conv_rhs => rw [hsub, qFactorial_succ]
        rw [← hsub]
      have hmul :=
        congrArg (fun a => q ^ (2 * (j : ℤ) + 1 - n) * a) (ih (Nat.le_of_lt hlt))
      rw [step j hlt, qFactorial_succ q j]
      calc
        _ = q ^ (2 * (j : ℤ) + 1 - n) *
            (f j * qFactorial q j * (qInt q (n - j) * qFactorial q (n - (j + 1)))) := by
          field_simp [hn (j+1) (Nat.succ_pos j)]
        _ = _ := by
          rw [hfac, hmul, ← mul_assoc, ← zpow_add₀ hq]
          congr 2
          push_cast
          ring
  have z := h n le_rfl
  exact (mul_right_cancel₀ (fact n) (show f n * qFactorial q n = 1 * qFactorial q n by simpa using z))

/-- The string-pairing scalar at the bottom of a complete string is one. -/
theorem polCoef_endpoint {k : Type*} [Field k] {q : k} (hq : q ≠ 0)
    (hpow : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) (n : ℕ) : IntegrableSl2.polCoef q n n = 1 := by
  apply endpoint_of_string_recurrence q hq (fun _ => qInt_ne_zero_of_pow_ne_one hq hpow) n
    (IntegrableSl2.polCoef q n) rfl
  intro j hj
  rw [IntegrableSl2.polCoef, ← qIntZ_natCast (sub_inv_ne_zero_of_pow_ne_one hq hpow) (n-j),
    Nat.cast_sub hj.le]

namespace SingleBlack
open LieLean LieLean.QuantumGroup.GrandLoop LusztigF
local notation "v" => (RatFunc.X : RatFunc ℚ)
local instance : NeZero v := ⟨RatFunc.X_ne_zero⟩

variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} (highest : Dom R) (hR : R.IsXRegular)

/-- Taking the saturated divided power on a bar-invariant primitive weight
vector preserves its normalized Shapovalov norm. -/
theorem websterForm_saturated_dividedPower (i : I) (n : ℕ) (μ : Y →+ ℤ)
    (x : IrreducibleModule R v highest.1) (hx : x ∈ weightSpace R v _ μ)
    (hμ : μ (R.coroot i) = (n : ℤ)) (hE : E R v i • x = 0) (hbar : hwBar hR highest x = x) :
    websterForm highest hR (qDivPow (v ^ D.d i) n (F R v i) • x)
      (qDivPow (v ^ D.d i) n (F R v i) • x) = websterForm highest hR x x := by
  let U := nodeSl2 R v (IrreducibleModule R v highest.1) hvn_ratFunc (isInt transcendental_ratFunc_X hR highest) i
  have hprim : x ∈ U.prim (n : ℤ) := ⟨hμ ▸ mem_nodeWt_of_mem hx, hE⟩
  have hB := IrreducibleModule.isContravariant_form (Λ := highest.1) hR hvn_ratFunc
  have h := IntegrableSl2.form_dF_dF (V := U) (pow_ne_zero _ RatFunc.X_ne_zero)
    (vd_pow_ne_one (D := D) hvn_ratFunc i) (IrreducibleModule.form_comm hR hvn_ratFunc)
    (IsContravariant.nodeSl2_F hvn_ratFunc (isInt transcendental_ratFunc_X hR highest) hB i)
    hprim hprim n n
  simp only [↓reduceIte] at h
  rw [polCoef_endpoint (pow_ne_zero _ RatFunc.X_ne_zero)
    (vd_pow_ne_one (D := D) hvn_ratFunc i), one_mul] at h
  dsimp only [U] at h
  rw [nodeSl2_dF_eq hR] at h
  rw [websterForm, websterForm, hwBar_smul_U, barHom_qDivPow, barHom_F, hbar, h]

end SingleBlack
end Categorification.Stendhal
