/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TensorShapovalov
import Categorification.WeightedKLR.RedStrands.TensorAdjointConvention

/-!
# The adjoint tensor form

For the coproduct of Webster, arXiv:1309.3796v2, §1.2 and the adjoint (3.24),
the intertwiner in Proposition 4.33 acts on the second argument.
-/

noncomputable section

namespace Categorification.Stendhal.TensorPairing

open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop TensorProduct LusztigF
open scoped TensorProduct

local notation "𝕂" => RatFunc ℚ
local notation "q" => (RatFunc.X : 𝕂)
local instance : NeZero q := ⟨RatFunc.X_ne_zero⟩

variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} (hR : R.IsXRegular) (Λ₁ Λ₂ : Dom R)
local notation "V" => fun w : Dom R => IrreducibleModule R q (Subtype.val w)
local notation "T" => V Λ₁ ⊗[𝕂] V Λ₂
local notation "act" => TensorModule.act R q (V Λ₁) (V Λ₂)
local notation "act₂" => TensorModule.actPair R q (V Λ₁) (V Λ₂)
local notation "τ" => fun (u : QuantumGroup R q) => barHom R (rho R q u)

/-- The repair to the two-factor formula immediately before Proposition 4.33
in Webster, arXiv:1309.3796v2. -/
def correctedForm (x y : T) : 𝕂 := factorwise hR Λ₁ Λ₂ x (websterTheta hR Λ₁ Λ₂ y)

private theorem factor_add_left (x y z : T) :
    factorwise hR Λ₁ Λ₂ (x + y) z = factorwise hR Λ₁ Λ₂ x z + factorwise hR Λ₁ Λ₂ y z := by
  simp [factorwise]

private theorem factor_add_right (x y z : T) :
    factorwise hR Λ₁ Λ₂ x (y + z) = factorwise hR Λ₁ Λ₂ x y + factorwise hR Λ₁ Λ₂ x z := by
  simp [factorwise]

private theorem factor_tmul_adjoint (u v : QuantumGroup R q) (x y : T) :
    factorwise hR Λ₁ Λ₂ (act₂ (u ⊗ₜ[𝕂] v) x) y =
      factorwise hR Λ₁ Λ₂ x (act₂ ((τ u) ⊗ₜ[𝕂] (τ v)) y) := by
  induction x using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, factor_add_left, ha, hb]
  | tmul a b =>
    induction y using TensorProduct.inductionOn with
    | add c d hc hd => simp only [map_add, factor_add_right, hc, hd]
    | tmul c d => simp only [TensorModule.act_tmul, factorwise_tmul, SingleBlack.websterForm_adjoint]

private theorem factor_coproduct_adjoint (u : QuantumGroup R q) (x y : T) :
    factorwise hR Λ₁ Λ₂ (act u x) y = factorwise hR Λ₁ Λ₂ x (act₂ (barComul R (τ u)) y) := by
  induction u using QuantumGroup.induction_on generalizing x y with
  | E i =>
    rw [TensorModule.act, AlgHom.comp_apply, comul_E, TensorAdjointConvention.barComul_tau_E]
    simp only [map_add, LinearMap.add_apply, factor_add_left, factor_add_right, factor_tmul_adjoint,
      rho_one, map_one]
  | F i =>
    rw [TensorModule.act, AlgHom.comp_apply, comul_F, TensorAdjointConvention.barComul_tau_F]
    simp only [map_add, LinearMap.add_apply, factor_add_left, factor_add_right, factor_tmul_adjoint,
      rho_one, map_one]
  | K μ =>
    rw [TensorModule.act, AlgHom.comp_apply, comul_K, TensorAdjointConvention.barComul_tau_K,
      factor_tmul_adjoint]
  | algebraMap c =>
    dsimp only
    rw [AlgHom.commutes, rho_algebraMap, barHom_algebraMap, barComul_algebraMap, AlgHom.commutes,
      Module.algebraMap_end_apply, Module.algebraMap_end_apply]
    induction x using TensorProduct.inductionOn with
    | add a b ha hb => simp only [smul_add, factor_add_left, ha, hb]
    | tmul a b =>
      induction y using TensorProduct.inductionOn with
      | add d e hd he => simp only [smul_add, factor_add_right, hd, he]
      | tmul d e =>
        rw [smul_tmul', smul_tmul', factorwise_tmul, factorwise_tmul,
          SingleBlack.websterForm_smul_left, SingleBlack.websterForm_smul_right]
  | add v w hv hw =>
    simp only [map_add, LinearMap.add_apply, factor_add_left, factor_add_right, hv, hw]
  | mul v w hv hw =>
    simp only [rho_mul, map_mul, Module.End.mul_apply, hv, hw]

/-- Proposition 4.33(2) of Webster, arXiv:1309.3796v2, for the tensor form
with the quasi-R intertwiner in the second argument, using (3.24). -/
theorem correctedForm_adjoint (u : QuantumGroup R q) (x y : T) :
    correctedForm hR Λ₁ Λ₂ (act u x) y = correctedForm hR Λ₁ Λ₂ x (act (τ u) y) := by
  rw [correctedForm, correctedForm, websterTheta_act, factor_coproduct_adjoint]

/-- Appending the final highest vector preserves the form, as required in
Webster, arXiv:1309.3796v2, Proposition 4.33(3). -/
theorem correctedForm_append_highest (x y : V Λ₁) :
    let v := IrreducibleModule.hwv R q Λ₂.1
    correctedForm hR Λ₁ Λ₂ (x ⊗ₜ[𝕂] v) (y ⊗ₜ[𝕂] v) = SingleBlack.websterForm Λ₁ hR x y := by
  dsimp only
  rw [correctedForm, websterTheta_append_highest, factorwise_tmul, SingleBlack.websterForm_hwv,
    mul_one]

/-- Additivity in the first variable of the corrected tensor form. -/
theorem correctedForm_add_left (x y z : T) :
    correctedForm hR Λ₁ Λ₂ (x + y) z =
      correctedForm hR Λ₁ Λ₂ x z + correctedForm hR Λ₁ Λ₂ y z :=
  factor_add_left _ _ _ _ _ _

/-- Additivity in the second variable of the corrected tensor form. -/
theorem correctedForm_add_right (x y z : T) :
    correctedForm hR Λ₁ Λ₂ x (y + z) =
      correctedForm hR Λ₁ Λ₂ x y + correctedForm hR Λ₁ Λ₂ x z := by
  simp only [correctedForm, websterTheta, map_add, factor_add_right]

/-- The bar involution acts on scalars in the first argument. -/
theorem correctedForm_smul_left (c : 𝕂) (x y : T) :
    correctedForm hR Λ₁ Λ₂ (c • x) y = RatFunc.bar c * correctedForm hR Λ₁ Λ₂ x y := by
  simp [correctedForm, factorwise, smul_eq_mul]

/-- The corrected form is linear in its second argument. -/
theorem correctedForm_smul_right (c : 𝕂) (x y : T) :
    correctedForm hR Λ₁ Λ₂ x (c • y) = c * correctedForm hR Λ₁ Λ₂ x y := by
  have h := correctedForm_adjoint hR Λ₁ Λ₂ (algebraMap 𝕂 _ (RatFunc.bar c)) x y
  dsimp only at h
  rw [AlgHom.commutes, rho_algebraMap, barHom_algebraMap, RatFunc.bar_bar, AlgHom.commutes,
    Module.algebraMap_end_apply, Module.algebraMap_end_apply, correctedForm_smul_left,
    RatFunc.bar_bar] at h
  exact h.symm

end Categorification.Stendhal.TensorPairing
