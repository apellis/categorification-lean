/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LastRedBlackInjective

/-!
# The isomorphism of Proposition 4.32

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §4.6,
Proposition 4.32: `IR^μ F_i I^μ ≅ F_i`. On bimodules, `F_i` on `T₀` is `T₀_{i+ν} ν_i(1)` and
`IR^μ F_i I^μ` is `e_ℓ T_{i+ν} ν_i(e_ℓ)`. The map `g ↦ appendRed(g) · (crossing)` restricts to a
`k`-linear isomorphism between them (`lastRedBlackEquiv`). It is a map of bimodules for
`T₀_{i+ν}` acting through `appendRed` on the left and `T₀_ν` acting through
`appendBlack ∘ appendRed` on the right (`lastRedBlackMap_mul_left`,
`lastRedBlackMap_mul_appendBlack`).

## Main results

* `blackInductionSubmodule`: `T₀_{i+ν} ν_i(1)`, the elements fixed by right multiplication by
  `ν_i(1)`.
* `lastRedCornerSubmodule`: `e_ℓ T_{i+ν} ν_i(e_ℓ)`.
* `lastRedBlackEquiv`: the isomorphism of Proposition 4.32.

## Hypotheses

The crossing polynomials are those of Webster's §2.2 (`IsRouquierQ`), as in
`lastRedBlackMap_eq_zero_iff`. The grading shift is not part of the statement.
-/

noncomputable section

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA Equiv

variable {I : Type} {ℓ : ℕ} [DecidableEq I] {k : Type*} [CommRing k]
  {C : QuantumGroup.CartanDatum I}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I) (ν : Multiset I)
  (hQ : IsRouquierQ C Q)

local notation "Λ₀" => (Λ ∘ Fin.castSucc)
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "T₀'" => TensorProductAlgebra k Q Λ₀ νᵢ
local notation "T'" => TensorProductAlgebra k Q Λ νᵢ
local notation "ab₀" => appendBlack Q Λ₀ i ν (1 : TensorProductAlgebra k Q Λ₀ ν)
local notation "E" => TensorProductAlgebra.lastRedIdem Q Λ νᵢ
local notation "E'" => appendBlack Q Λ i ν (TensorProductAlgebra.lastRedIdem Q Λ ν)

/-- `T₀_{i+ν} ν_i(1)`: the elements `g` with `g · ν_i(1) = g`. -/
def blackInductionSubmodule : Submodule k T₀' where
  carrier := {g | g * ab₀ = g}
  add_mem' {a b} ha hb := by
    change (a + b) * ab₀ = a + b
    rw [add_mul, ha, hb]
  zero_mem' := zero_mul _
  smul_mem' c g hg := by
    change (c • g) * ab₀ = c • g
    rw [smul_mul_assoc, hg]

/-- `e_ℓ T_{i+ν} ν_i(e_ℓ)`: the elements `y` with `e_ℓ y ν_i(e_ℓ) = y`. -/
def lastRedCornerSubmodule : Submodule k T' where
  carrier := {y | E * y * E' = y}
  add_mem' {a b} ha hb := by
    change E * (a + b) * E' = a + b
    rw [mul_add, add_mul, ha, hb]
  zero_mem' := by
    change E * 0 * E' = 0
    rw [mul_zero, zero_mul]
  smul_mem' c y hy := by
    change E * (c • y) * E' = c • y
    rw [mul_smul_comm, smul_mul_assoc, hy]

theorem mem_blackInductionSubmodule_iff (g : T₀') :
    g ∈ blackInductionSubmodule Q Λ i ν ↔ g * ab₀ = g := Iff.rfl

theorem mem_lastRedCornerSubmodule_iff (y : T') :
    y ∈ lastRedCornerSubmodule Q Λ i ν ↔ E * y * E' = y := Iff.rfl

theorem lastRedBlackMap_mul_appendBlack_one (g : T₀') :
    lastRedBlackMap Q Λ i ν (g * ab₀) = lastRedBlackMap Q Λ i ν g := by
  rw [lastRedBlackMap_mul_appendBlack, appendRed_one_val,
    lastRedBlackMap_mul_appendBlack_lastRedIdem]

theorem lastRedBlackMap_mem (g : T₀') :
    lastRedBlackMap Q Λ i ν g ∈ lastRedCornerSubmodule Q Λ i ν := by
  change E * _ * E' = _
  rw [lastRedIdem_mul_lastRedBlackMap, lastRedBlackMap_mul_appendBlack_lastRedIdem]

/-- The map of Proposition 4.32 restricted to `T₀_{i+ν} ν_i(1)`. -/
def lastRedBlackRestrict :
    blackInductionSubmodule Q Λ i ν →ₗ[k] lastRedCornerSubmodule Q Λ i ν :=
  ((lastRedBlackMap Q Λ i ν).comp (blackInductionSubmodule Q Λ i ν).subtype).codRestrict _
    fun g => lastRedBlackMap_mem Q Λ i ν g.1

include hQ in
theorem lastRedBlackRestrict_injective :
    Function.Injective (lastRedBlackRestrict Q Λ i ν) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro g hg
  have h0 : lastRedBlackMap Q Λ i ν g.1 = 0 := congrArg Subtype.val hg
  have h := (lastRedBlackMap_eq_zero_iff Q Λ i ν hQ g.1).1 h0
  rw [g.2] at h
  exact Subtype.ext h

theorem lastRedBlackRestrict_surjective :
    Function.Surjective (lastRedBlackRestrict Q Λ i ν) := by
  intro y
  obtain ⟨g, hg⟩ := exists_lastRedBlackMap_eq Q Λ i ν y.1 y.2
  have hmem : g * ab₀ ∈ blackInductionSubmodule Q Λ i ν := by
    change g * ab₀ * ab₀ = g * ab₀
    rw [mul_assoc, ← map_mul, one_mul]
  refine ⟨⟨g * ab₀, hmem⟩, Subtype.ext ?_⟩
  change lastRedBlackMap Q Λ i ν (g * ab₀) = y.1
  rw [lastRedBlackMap_mul_appendBlack_one, hg]

/-- **Webster, Proposition 4.32** (arXiv:1309.3796v3), without the grading shift:
`g ↦ appendRed(g) · (crossing)` is a `k`-linear isomorphism
`T₀_{i+ν} ν_i(1) ≅ e_ℓ T_{i+ν} ν_i(e_ℓ)`, compatible with the bimodule structures
(`lastRedBlackMap_mul_left`, `lastRedBlackMap_mul_appendBlack`). -/
def lastRedBlackEquiv :
    blackInductionSubmodule Q Λ i ν ≃ₗ[k] lastRedCornerSubmodule Q Λ i ν :=
  LinearEquiv.ofBijective (lastRedBlackRestrict Q Λ i ν)
    ⟨lastRedBlackRestrict_injective Q Λ i ν hQ, lastRedBlackRestrict_surjective Q Λ i ν⟩

theorem lastRedBlackEquiv_apply (g : blackInductionSubmodule Q Λ i ν) :
    (lastRedBlackEquiv Q Λ i ν hQ g).1 = lastRedBlackMap Q Λ i ν g.1 := rfl

end Categorification.Stendhal
