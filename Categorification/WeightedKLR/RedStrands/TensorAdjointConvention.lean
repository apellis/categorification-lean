/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.SingleBlackShapovalov
import LieLean.Algebra.QuantumGroup.Sl2.SimpleModule

/-!
# The coproduct and the adjoint in Webster's tensor form

Webster, arXiv:1309.3796v2, §4.7, proof of Proposition 4.33, p. 44.
With the coproduct in §1.2 and the antiautomorphism (3.24), the printed
identity `(τ ⊗ τ) barΔ(u) = Δ(τ(u))` fails for `u = F` in type A₁.
The matrix coefficient from `h ⊗ Fh` to `h ⊗ h` in the tensor square
of the two-dimensional representation detects the discrepancy.
-/

noncomputable section

namespace Categorification.Stendhal.TensorAdjointConvention

open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop TensorProduct
open scoped TensorProduct

local notation "𝕂" => RatFunc ℚ
local notation "q" => (RatFunc.X : 𝕂)
local notation "U" => Sl2 q
local notation "R" => sl2RootDatum
local notation "F₁" => F R q ()
local notation "E₁" => E R q ()
local notation "K₁" => K R q 1
local notation "τ" => fun (u : U) => barHom R (rho R q u)
local instance : NeZero q := ⟨RatFunc.X_ne_zero⟩

private def std : U →ₐ[𝕂] Module.End 𝕂 (Fin 2 → 𝕂) :=
  Sl2.simpleRep q 1 1 RatFunc.X_ne_zero (hvn_ratFunc 2 (by decide)) (by simp)

private def entry (j : Fin 2) : U →ₗ[𝕂] 𝕂 where
  toFun u := std u (Pi.single j 1) 0
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

private def matrixEntry : U ⊗[𝕂] U →ₗ[𝕂] 𝕂 :=
  (TensorProduct.lid 𝕂 𝕂).toLinearMap.comp (TensorProduct.map (entry 0) (entry 1))

private theorem entry_tmul (x y : U) :
    matrixEntry (x ⊗ₜ[𝕂] y) = std x (Pi.single 0 1) 0 * std y (Pi.single 1 1) 0 := rfl

private theorem tau_F : τ F₁ = q⁻¹ • (K₁ * E₁) := by
  change barHom R (rho R q F₁) = _
  rw [rho_F, rhoF, barHom_smul, map_mul, barHom_K, barHom_E]
  simp

private theorem highest_E : std E₁ (Pi.single 0 1) = 0 := by
  rw [std, Sl2.simpleRep_E_single]
  rfl

private theorem lowered_E : std E₁ (Pi.single 1 1) = Pi.single 0 1 := by
  rw [std, Sl2.simpleRep_E_single]
  simp [Sl2.eCoeff, qInt]

private theorem highest_K (m : ℤ) : std (K R q m) (Pi.single 0 1) = q ^ m • Pi.single 0 1 := by
  rw [std, Sl2.simpleRep_K_single]
  simp

/-- For `u=F`, the purported equality in the proof of Webster's Proposition
4.33 fails in `U_q(sl₂) ⊗ U_q(sl₂)`. Since `barΔ(F)=F ⊗ K + 1 ⊗ F`,
the left side below is precisely `(τ ⊗ τ)barΔ(F)`. -/
theorem tau_barComul_F_ne_comul_tau_F :
    τ F₁ ⊗ₜ[𝕂] τ K₁ + 1 ⊗ₜ[𝕂] τ F₁ ≠ comul R q (τ F₁) := by
  intro h
  have he := congrArg matrixEntry h
  rw [tau_F, map_smul, map_mul, comul_K, comul_E, mul_add,
    Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul] at he
  simp only [map_add, map_smul, entry_tmul, map_mul, Module.End.mul_apply, LinearMap.smul_apply,
    highest_E, lowered_E, highest_K, map_zero, Pi.zero_apply, Pi.smul_apply, smul_eq_mul,
    map_one, Module.End.one_apply, Kt, sl2RootDatum_ktilde, Pi.single_eq_same, one_mul, mul_one,
    zero_mul, zero_add, zpow_one] at he
  have hn := hvn_ratFunc 2 (by decide)
  apply hn
  field_simp [RatFunc.X_ne_zero] at he
  simp only [zero_mul, zero_add, pow_succ] at he
  exact mul_right_cancel₀ RatFunc.X_ne_zero (show q ^ 2 * q = 1 * q by simpa [pow_succ] using he.symm)

section ConjugateCoproduct

variable {I Y : Type*} [DecidableEq I] [AddCommGroup Y] {D : LusztigCartanDatum I}
    (rd : D.RootDatum Y) (i : I)

local notation "τᵣ" => fun u => barHom rd (rho rd q u)

/-- Componentwise application of (3.24) to the `Fᵢ` coproduct of §1.2
agrees with the *bar-conjugate* coproduct of `τ(Fᵢ)`.
This checks one possible change of convention without identifying the
resulting tensor form with the printed one. -/
theorem barComul_tau_F :
    barComul rd (τᵣ (F rd q i)) =
      τᵣ (F rd q i) ⊗ₜ[𝕂] τᵣ (K rd q (-ktilde rd i)) + 1 ⊗ₜ[𝕂] τᵣ (F rd q i) := by
  change barComul rd (barHom rd (rho rd q (F rd q i))) = _
  rw [barComul_apply, barHom_barHom, rho_F, rhoF, map_smul, map_mul, comul_K, comul_E, mul_add,
    Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
    Kt, K_neg_mul_K, mul_one, barTensor_smul, map_add, barTensor_tmul, barTensor_tmul]
  simp only [rho_F, rhoF, rho_K, barHom_smul, map_mul, barHom_K, barHom_E, map_one,
    neg_neg, smul_add, tmul_smul, ← smul_tmul']

/-- The corresponding generator identity for `Eᵢ`. -/
theorem barComul_tau_E :
    barComul rd (τᵣ (E rd q i)) =
      τᵣ (E rd q i) ⊗ₜ[𝕂] 1 + τᵣ (Kt rd q i) ⊗ₜ[𝕂] τᵣ (E rd q i) := by
  change barComul rd (barHom rd (rho rd q (E rd q i))) = _
  rw [barComul_apply, barHom_barHom, rho_E, rhoE, map_smul, map_mul, Kt, comul_K, comul_F,
    mul_add, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
    K_mul_K_neg, mul_one, barTensor_smul, map_add, barTensor_tmul, barTensor_tmul]
  simp only [rho_E, rhoE, Kt, rho_K, barHom_smul, map_mul, barHom_K, barHom_F, map_one,
    smul_add, tmul_smul, ← smul_tmul']

/-- The two choices of coproduct coincide on the toral generator. -/
theorem barComul_tau_K (μ : Y) :
    barComul rd (τᵣ (K rd q μ)) = τᵣ (K rd q μ) ⊗ₜ[𝕂] τᵣ (K rd q μ) := by
  simp [barComul_K]

end ConjugateCoproduct

end Categorification.Stendhal.TensorAdjointConvention
