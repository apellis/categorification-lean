/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.K0Free
import Categorification.KLR.KL2.Prop34KL2

/-!
# `K₀` of the KL II rings is free

For a symmetric Cartan datum and a field `k`, each `K₀(R(ν))` of the rings of
Khovanov–Lauda II is a free `ℤ[q, q⁻¹]`-module (the general graded Krull–Schmidt results of
`Categorification.Graded` applied to `R(ν)`). Consequently the base change
`K₀(R) → ℚ(v) ⊗_{ℤ[q, q⁻¹]} K₀(R)` is injective, discharging the torsion-freeness hypothesis of
the integral map `γ` (`KL2Gamma.gammaInt2`).
-/

namespace Categorification.KLR

open Graded QuantumGroup KLGamma

variable {I : Type*} [DecidableEq I] (k : Type*) [Field k] (C : CartanDatum I)

namespace KL2Gamma

omit [DecidableEq I] in
theorem klGradingDatum2_degX_pos : ∀ a, 0 < (klGradingDatum2 k C).degX a :=
  fun a => C.dot_self_pos a

/-- `K₀(R) = ⊕_ν K₀(R(ν))` is a free `ℤ[q, q⁻¹]`-module for the KL II rings over a field. -/
theorem K0R_free2 : Module.Free (LaurentPolynomial ℤ) (klGradingDatum2 k C).K0R :=
  (klGradingDatum2 k C).K0R_free (klQ2_eq_klP2 (o := KL1.stdOrient) KL2.stdOrient_spec)
    (fun a b hab => klP2_ne_zero a b hab) (klGradingDatum2_degX_pos k C)

attribute [local instance] qToVAlgebra in
/-- **`K₀(R) → ℚ(v) ⊗_{ℤ[q, q⁻¹]} K₀(R)` is injective** for the KL II rings over a field. -/
theorem toK0Q2_injective : Function.Injective (toK0Q2 k C) := by
  haveI := K0R_free2 k C
  exact Algebra.TensorProduct.includeRight_injective (A := RatFunc ℚ) qToV_injective

/-- The integral `γ : _𝒜 f → K₀(R)` for an arbitrary symmetric Cartan datum over a field,
under the quantum Gabber–Kac hypothesis only. -/
noncomputable def gammaInt2' (hGK : C.GabberKac vQ C.c) : C.Af →+* (klGradingDatum2 k C).K0R :=
  gammaInt2 k C hGK (toK0Q2_injective k C)

theorem gammaInt2'_injective (hGK : C.GabberKac vQ C.c) :
    Function.Injective (gammaInt2' k C hGK) :=
  gammaInt2_injective k C hGK (toK0Q2_injective k C)

end KL2Gamma

end Categorification.KLR
