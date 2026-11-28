/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendViolated

/-!
# `𝔉_i` of the model modulo violated diagrams

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, for a cap not at the right end (`j < ℓ`). The isomorphism
`𝔉_i(model_ν) ≅ e' · model_{{i} + ν}` (`CupCap.appendModelEquiv`) matches the bottom-violated
parts (`CupCap.mem_appendBotViolSub_iff`), so it descends to the quotients by them
(`CupCap.appendViolQuotEquiv`): `𝔉_i(model_ν) / 𝔉_i(model_ν) V_{λ⁺}` is isomorphic to
`e' · model_{{i} + ν}` modulo its violated part.

## Main definitions

* `CupCap.appendViolQuotEquiv`.

## Main results

* `CupCap.map_appendModelEquiv_appendBotViolSub`, `CupCap.appendViolQuotEquiv_mk`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} (ν : Multiset I) {ν₀ : Multiset I} (i : I)
  (L : Type*) [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] (h : j < ℓ)

local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "Tᵢ" => (StendhalAlgebra k Q (plusLabels Λ Λc j hj) (νᵢ + ν₀))ᵐᵒᵖ
local notation "Rg" => LinearMap.range (toAppendMid Q Λ Λc j hj ν ν₀ i L h)

/-- The violated part of `e' · model_{{i} + ν}`. -/
abbrev appendRangeViolSub : Submodule Tᵢ Rg :=
  (midBotViolSub Q Λ Λc j hj νᵢ ν₀ L).comap (Submodule.subtype Rg)

/-- The isomorphism `𝔉_i(model_ν) ≅ e' · model_{{i} + ν}` carries the bottom-violated part of
`𝔉_i(model_ν)` onto the violated part of `e' · model_{{i} + ν}`. -/
theorem map_appendModelEquiv_appendBotViolSub :
    (appendBotViolSub Q Λ Λc j hj ν ν₀ i L).map (appendModelEquiv ν i L h).toLinearMap =
      appendRangeViolSub ν i L h := by
  ext y
  rw [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap, mem_appendBotViolSub_iff ν i h,
    Submodule.mem_comap, Submodule.subtype_apply]
  change ((appendModelEquiv ν i L h ((appendModelEquiv ν i L h).symm y) : Rg) :
    MidModel j hj Q Λ Λc νᵢ ν₀ L) ∈ _ ↔ _
  rw [LinearEquiv.apply_symm_apply]

/-- **`𝔉_i` of the model modulo violated diagrams** (arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21), for `j < ℓ`: the quotient of `𝔉_i(model_ν)` by its bottom-violated part is
isomorphic to `e' · model_{{i} + ν}` modulo its violated part. -/
def appendViolQuotEquiv :
    (Ind (MidModel j hj Q Λ Λc ν ν₀ L) (appendBlackPlusOp Q Λ Λc j hj ν ν₀ i) ⧸
        appendBotViolSub Q Λ Λc j hj ν ν₀ i L) ≃ₗ[Tᵢ]
      Rg ⧸ appendRangeViolSub ν i L h :=
  Submodule.Quotient.equiv _ _ (appendModelEquiv ν i L h)
    (map_appendModelEquiv_appendBotViolSub ν i L h)

theorem appendViolQuotEquiv_mk
    (x : Ind (MidModel j hj Q Λ Λc ν ν₀ L) (appendBlackPlusOp Q Λ Λc j hj ν ν₀ i)) :
    appendViolQuotEquiv ν i L h (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (appendModelEquiv ν i L h x) := rfl

end Categorification.Stendhal.CupCap
