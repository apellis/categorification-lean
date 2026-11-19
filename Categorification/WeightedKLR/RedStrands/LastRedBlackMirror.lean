/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LastRedBlackEquiv
import Categorification.WeightedKLR.RedStrands.AppendStrandReflection

/-!
# The mirror isomorphism of Proposition 4.32

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §4.6,
Proposition 4.32: `IR^μ E_i I^μ ≅ E_i`. The paper proves the `F_i` part and states that the
`E_i` part follows by a similar argument. Here the `E_i` part is the horizontal mirror image of
the `F_i` part (`lastRedBlackEquiv`): the reflection `tensorFlip` commutes with adding the last
red strand and with adding a black strand on the right (`tensorFlip_appendRed`,
`tensorFlip_appendBlack`), so it carries `T₀_{i+ν} ν_i(1)` to `ν_i(1) T₀_{i+ν}` and
`e_ℓ T_{i+ν} ν_i(e_ℓ)` to `ν_i(e_ℓ) T_{i+ν} e_ℓ`.

## Main results

* `blackRestrictionSubmodule`: `ν_i(1) T₀_{i+ν}`.
* `lastRedCornerMirrorSubmodule`: `ν_i(e_ℓ) T_{i+ν} e_ℓ`.
* `lastRedBlackMirror`: `g ↦ (crossing)ᵗ · appendRed(g)`, the reflection of `lastRedBlackMap`.
* `lastRedBlackMirrorEquiv`: the isomorphism of the `E_i` part of Proposition 4.32.

## Hypotheses

The crossing polynomials are those of Webster's §2.2 (`IsRouquierQ`) and `k` is a field (the
reflection of `T^λ` is constructed over a field, as in the paper). The grading shift is not part
of the statement.
-/

noncomputable section

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

namespace Categorification.Stendhal

open KLR KLRAlgebra

variable {I : Type} {ℓ : ℕ} [DecidableEq I] {k : Type*} [Field k]
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

/-- A `k`-linear isomorphism between submodules exchanged by the reflection. -/
def tensorFlipSubmoduleEquiv {ℓ' : ℕ} {Λ' : Fin ℓ' → I →₀ ℕ} {β : Multiset I}
    (p q : Submodule k (TensorProductAlgebra k Q Λ' β))
    (hp : ∀ g ∈ p, tensorFlip g ∈ q) (hq : ∀ g ∈ q, tensorFlip g ∈ p) : p ≃ₗ[k] q where
  toFun g := ⟨tensorFlip g.1, hp g.1 g.2⟩
  invFun g := ⟨tensorFlip g.1, hq g.1 g.2⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)
  left_inv g := Subtype.ext (tensorFlip_tensorFlip g.1)
  right_inv g := Subtype.ext (tensorFlip_tensorFlip g.1)

theorem tensorFlip_ab₀ : tensorFlip ab₀ = ab₀ := by
  rw [tensorFlip_appendBlack, tensorFlip_one]

theorem tensorFlip_lastRedIdem_append : tensorFlip E' = E' := by
  rw [tensorFlip_appendBlack, tensorFlip_lastRedIdem]

/-- `ν_i(1) T₀_{i+ν}`: the elements `g` with `ν_i(1) · g = g`. -/
def blackRestrictionSubmodule : Submodule k T₀' where
  carrier := {g | ab₀ * g = g}
  add_mem' {a b} ha hb := by
    change ab₀ * (a + b) = a + b
    rw [mul_add, ha, hb]
  zero_mem' := mul_zero _
  smul_mem' c g hg := by
    change ab₀ * (c • g) = c • g
    rw [mul_smul_comm, hg]

/-- `ν_i(e_ℓ) T_{i+ν} e_ℓ`: the elements `y` with `ν_i(e_ℓ) y e_ℓ = y`. -/
def lastRedCornerMirrorSubmodule : Submodule k T' where
  carrier := {y | E' * y * E = y}
  add_mem' {a b} ha hb := by
    change E' * (a + b) * E = a + b
    rw [mul_add, add_mul, ha, hb]
  zero_mem' := by
    change E' * 0 * E = 0
    rw [mul_zero, zero_mul]
  smul_mem' c y hy := by
    change E' * (c • y) * E = c • y
    rw [mul_smul_comm, smul_mul_assoc, hy]

/-- The reflection exchanges `T₀_{i+ν} ν_i(1)` and `ν_i(1) T₀_{i+ν}`. -/
def blackInductionFlip :
    blackInductionSubmodule Q Λ i ν ≃ₗ[k] blackRestrictionSubmodule Q Λ i ν :=
  tensorFlipSubmoduleEquiv Q _ _
    (fun g (hg : g * ab₀ = g) => by
      change ab₀ * tensorFlip g = tensorFlip g
      rw [← tensorFlip_ab₀ Q Λ i ν, ← tensorFlip_mul, hg])
    (fun g (hg : ab₀ * g = g) => by
      change tensorFlip g * ab₀ = tensorFlip g
      rw [← tensorFlip_ab₀ Q Λ i ν, ← tensorFlip_mul, hg])

/-- The reflection exchanges `e_ℓ T_{i+ν} ν_i(e_ℓ)` and `ν_i(e_ℓ) T_{i+ν} e_ℓ`. -/
def lastRedCornerFlip :
    lastRedCornerSubmodule Q Λ i ν ≃ₗ[k] lastRedCornerMirrorSubmodule Q Λ i ν :=
  tensorFlipSubmoduleEquiv Q _ _
    (fun y (hy : E * y * E' = y) => by
      change E' * tensorFlip y * E = tensorFlip y
      rw [← tensorFlip_lastRedIdem_append Q Λ i ν, ← tensorFlip_lastRedIdem Q Λ νᵢ,
        ← tensorFlip_mul, ← tensorFlip_mul, ← mul_assoc, hy])
    (fun y (hy : E' * y * E = y) => by
      change E * tensorFlip y * E' = tensorFlip y
      rw [← tensorFlip_lastRedIdem_append Q Λ i ν, ← tensorFlip_lastRedIdem Q Λ νᵢ,
        ← tensorFlip_mul, ← tensorFlip_mul, ← mul_assoc, hy])

/-- The reflection of the map of Proposition 4.32: add the last red strand to a diagram and let
it cross the new black strand `i` at the top. -/
def lastRedBlackMirror : T₀' →ₗ[k] T' :=
  tensorFlip ∘ₗ lastRedBlackMap Q Λ i ν ∘ₗ tensorFlip

theorem lastRedBlackMirror_apply (g : T₀') :
    lastRedBlackMirror Q Λ i ν g =
      tensorFlip (lastRedBlackCrossing Q Λ i ν) * (appendRed Q Λ νᵢ g).val := by
  change tensorFlip (lastRedBlackMap Q Λ i ν (tensorFlip g)) = _
  rw [lastRedBlackMap_apply, tensorFlip_mul, tensorFlip_appendRed, tensorFlip_tensorFlip]

/-- The mirror map is right linear for `T₀_{i+ν}` acting through `appendRed`. -/
theorem lastRedBlackMirror_mul_right (g a : T₀') :
    lastRedBlackMirror Q Λ i ν (g * a) =
      lastRedBlackMirror Q Λ i ν g * (appendRed Q Λ νᵢ a).val := by
  rw [lastRedBlackMirror_apply, lastRedBlackMirror_apply, map_mul, KLR.Corner.val_mul,
    mul_assoc]

/-- The mirror map is left linear for `T₀_ν` acting on the source through `appendBlack` and on
the target through `appendBlack ∘ appendRed`. -/
theorem lastRedBlackMirror_appendBlack_mul (h : TensorProductAlgebra k Q Λ₀ ν) (g : T₀') :
    lastRedBlackMirror Q Λ i ν (appendBlack Q Λ₀ i ν h * g) =
      appendBlack Q Λ i ν (appendRed Q Λ ν h).val * lastRedBlackMirror Q Λ i ν g := by
  change tensorFlip (lastRedBlackMap Q Λ i ν (tensorFlip _)) =
    _ * tensorFlip (lastRedBlackMap Q Λ i ν (tensorFlip g))
  rw [tensorFlip_mul, tensorFlip_appendBlack, lastRedBlackMap_mul_appendBlack, tensorFlip_mul,
    tensorFlip_appendBlack, tensorFlip_appendRed, tensorFlip_tensorFlip]

include hQ in
/-- **Webster, Proposition 4.32, `E_i` part** (arXiv:1309.3796v3), without the grading shift:
`g ↦ (crossing)ᵗ · appendRed(g)` is a `k`-linear isomorphism
`ν_i(1) T₀_{i+ν} ≅ ν_i(e_ℓ) T_{i+ν} e_ℓ`, compatible with the bimodule structures
(`lastRedBlackMirror_mul_right`, `lastRedBlackMirror_appendBlack_mul`). -/
def lastRedBlackMirrorEquiv :
    blackRestrictionSubmodule Q Λ i ν ≃ₗ[k] lastRedCornerMirrorSubmodule Q Λ i ν :=
  (blackInductionFlip Q Λ i ν).symm.trans
    ((lastRedBlackEquiv Q Λ i ν hQ).trans (lastRedCornerFlip Q Λ i ν))

theorem lastRedBlackMirrorEquiv_apply (g : blackRestrictionSubmodule Q Λ i ν) :
    (lastRedBlackMirrorEquiv Q Λ i ν hQ g).1 = lastRedBlackMirror Q Λ i ν g.1 := rfl

end Categorification.Stendhal
