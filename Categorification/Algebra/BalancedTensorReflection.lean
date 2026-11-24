/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.BalancedTensorSplit


/-!
# Reflection swaps balanced tensor factors

If a fixed algebra involution relates the left and right actions on two
modules, balanced tensor is compatible with exchanging the factors. This
exchanges the functorial maps in the two factors.
-/

noncomputable section

namespace Categorification.BalancedTensor

open MulOpposite

variable {k A M N : Type*} [CommRing k] [Ring A]
  [AddCommGroup M] [AddCommGroup N] [Module k M] [Module k N]
  [Module A M] [Module A N] [Module Aᵐᵒᵖ M] [Module Aᵐᵒᵖ N]
  [SMulCommClass k Aᵐᵒᵖ M] [SMulCommClass k Aᵐᵒᵖ N]

omit [SMulCommClass k Aᵐᵒᵖ M] [SMulCommClass k Aᵐᵒᵖ N] in
private theorem reflectionSwap_balanced (σ : A → A) (hσ : Function.Involutive σ)
    (hM : ∀ (a : A) (m : M), op a • m = σ a • m)
    (hN : ∀ (a : A) (n : N), op a • n = σ a • n) (m : M) (a : A) (n : N) :
    (tmul n (op a • m) : BalancedTensor k k A N M) =
      tmul (a • n) m := by
  rw [hM, ← op_smul_tmul, hN, hσ]

/-- Swapping the factors is balanced when both right module structures come
from the same involution on the scalar algebra. -/
def reflectionSwap (σ : A → A) (hσ : Function.Involutive σ)
    (hM : ∀ (a : A) (m : M), op a • m = σ a • m)
    (hN : ∀ (a : A) (n : N), op a • n = σ a • n) :
    BalancedTensor k k A M N ≃ₗ[k] BalancedTensor k k A N M := by
  let f : BalancedTensor k k A M N →ₗ[k] BalancedTensor k k A N M :=
    lift (mkBil k k A N M).flip (reflectionSwap_balanced (k := k) σ hσ hM hN)
  let g : BalancedTensor k k A N M →ₗ[k] BalancedTensor k k A M N :=
    lift (mkBil k k A M N).flip (reflectionSwap_balanced (k := k) σ hσ hN hM)
  exact LinearEquiv.ofLinearMap f g (BalancedTensor.ext fun _ _ => rfl)
    (BalancedTensor.ext fun _ _ => rfl)

/-- Reflection exchanges the two entries of a pure tensor. -/
theorem reflectionSwap_tmul (σ : A → A) (hσ : Function.Involutive σ)
    (hM : ∀ (a : A) (m : M), op a • m = σ a • m)
    (hN : ∀ (a : A) (n : N), op a • n = σ a • n) (m : M) (n : N) :
    reflectionSwap (k := k) σ hσ hM hN (tmul m n) = tmul n m := rfl

variable {N' : Type*} [AddCommGroup N'] [Module k N'] [Module A N'] [Module Aᵐᵒᵖ N']
    [SMulCommClass k Aᵐᵒᵖ N']
variable [Algebra k A] [IsScalarTower k A N] [IsScalarTower k A N']

/-- Reflection swaps the ordinary tensor map on a left module with the
coefficient map on its reflected right module. -/
theorem reflectionSwap_mapRight (σ : A → A) (hσ : Function.Involutive σ)
    (hM : ∀ (a : A) (m : M), op a • m = σ a • m)
    (hN : ∀ (a : A) (n : N), op a • n = σ a • n)
    (hN' : ∀ (a : A) (n : N'), op a • n = σ a • n)
    (f : N →ₗ[A] N') :
    (reflectionSwap σ hσ hM hN').toLinearMap.comp (mapRight f) =
      (mapLeftOp k M (f.restrictScalars k)
        (fun a n => by change f (op a • n) = op a • f n; rw [hN, hN', f.map_smul])).comp
        (reflectionSwap σ hσ hM hN).toLinearMap := by
  apply BalancedTensor.ext
  intro m n
  rfl

end Categorification.BalancedTensor
