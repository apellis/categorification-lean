/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapLeftProjectiveGen

/-!
# The black block beside the window: the juxtaposition map

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, input (B3). Let `λ⁺` be `λ` followed by
the two red strands `(μ, μ*)` of a cap at the right end, with `ν` black strands for `λ` and `ν₀`
black strands at the maximum. Placing a diagram of `T̃^λ` on the first `m` strands
(`CupCap.prefixStendhal`) and a diagram of `T̃^{(μ,μ*)}(ν₀)` on the last `N` strands
(`CupCap.endStendhal`) is horizontal juxtaposition

  `ι : T̃^λ ⊗_k T̃^{(μ,μ*)}(ν₀) → T̃^{λ⁺}(ν + ν₀)`, `x ⊗ y ↦ x y`

(`CupCap.blockTensor`). The two placements commute, so `ι` is multiplicative; it is not unital:
`ι(1)` is the end idempotent `e_L` (`CupCap.blockTensor_one`).

For `ℓ = 0` the algebra `T̃^λ` has no red strands and is the KLR algebra `R(ν)` of the black block,
and `T̃^{λ⁺}(ν + ν₀)` is `T̃^{(μ,μ*)}(ν + ν₀)`: then `ι` is the map `R(b) ⊗ A′ → A` of (B3-L), with
`b = ν` and `A′ = T̃^{(μ,μ*)}(ν₀)`, the `b`-block on the left. The statements here hold for every
`ℓ`.

## Main definitions

* `CupCap.blockTensor`: the juxtaposition map `ι`, a non-unital algebra map.

## Main results

* `CupCap.blockTensor_tmul`, `CupCap.blockTensor_mul`, `CupCap.blockTensor_one`.
* `CupCap.endStendhal_one_mul_blockTensor`, `CupCap.blockTensor_mul_endStendhal_one`: `ι` lands
  in the corner `e_L T̃^{λ⁺} e_L`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MulOpposite
open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)
  (ν ν₀ : Multiset I)

local notation "T" => StendhalAlgebra k Q Λ ν
local notation "Tc" => StendhalAlgebra k Q Λc ν₀
local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc ℓ le_rfl) (ν + ν₀)

/-- The bilinear map `(x, y) ↦ x y` placing `x ∈ T̃^λ` on the first strands and
`y ∈ T̃^{(μ,μ*)}` on the last strands. -/
def blockBil : T →ₗ[k] Tc →ₗ[k] Tp :=
  LinearMap.mk₂ k (fun x y => prefixStendhal Q Λ Λc ν ν₀ x * endStendhal Q Λ Λc ν ν₀ y)
    (fun x x' y => by rw [map_add, add_mul])
    (fun c x y => by rw [map_smul, smul_mul_assoc])
    (fun x y y' => by rw [map_add, mul_add])
    (fun c x y => by rw [map_smul, mul_smul_comm])

/-- The juxtaposition `x ⊗ y ↦ x y` as a `k`-linear map `T̃^λ ⊗_k T̃^{(μ,μ*)} → T̃^{λ⁺}`. -/
def blockTensorLin : T ⊗[k] Tc →ₗ[k] Tp := TensorProduct.lift (blockBil Q Λ Λc ν ν₀)

variable {Q Λ Λc ν ν₀}

theorem blockTensorLin_tmul (x : T) (y : Tc) :
    blockTensorLin Q Λ Λc ν ν₀ (x ⊗ₜ y) =
      prefixStendhal Q Λ Λc ν ν₀ x * endStendhal Q Λ Λc ν ν₀ y := by
  rw [blockTensorLin, TensorProduct.lift.tmul]
  rfl

theorem blockTensorLin_mul (d d' : T ⊗[k] Tc) :
    blockTensorLin Q Λ Λc ν ν₀ (d * d') =
      blockTensorLin Q Λ Λc ν ν₀ d * blockTensorLin Q Λ Λc ν ν₀ d' := by
  induction d using TensorProduct.inductionOn with
  | add a b ha hb => rw [add_mul, map_add, ha, hb, map_add, add_mul]
  | tmul x y =>
    induction d' using TensorProduct.inductionOn with
    | add a b ha hb => rw [mul_add, map_add, ha, hb, map_add, mul_add]
    | tmul x' y' =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, blockTensorLin_tmul, blockTensorLin_tmul,
        blockTensorLin_tmul, map_mul, map_mul, mul_assoc, mul_assoc,
        ← mul_assoc _ _ (endStendhal _ _ _ _ _ y'),
        (commute_prefixStendhal_endStendhal Q Λ Λc x' y).eq, mul_assoc]

variable (Q Λ Λc ν ν₀) in
/-- **The juxtaposition map** `ι : T̃^λ ⊗_k T̃^{(μ,μ*)}(ν₀) → T̃^{λ⁺}(ν + ν₀)`, `x ⊗ y ↦ x y`
(arXiv:1309.3796v3, proof of Lemma 7.19, (B3); for `ℓ = 0` the map `R(b) ⊗ A′ → A` with the
black block on the left). -/
def blockTensor : T ⊗[k] Tc →ₙₐ[k] Tp where
  toFun := blockTensorLin Q Λ Λc ν ν₀
  map_smul' c d := map_smul _ c d
  map_zero' := map_zero _
  map_add' := map_add _
  map_mul' := blockTensorLin_mul

theorem blockTensor_apply (d : T ⊗[k] Tc) :
    blockTensor Q Λ Λc ν ν₀ d = blockTensorLin Q Λ Λc ν ν₀ d := rfl

theorem blockTensor_tmul (x : T) (y : Tc) :
    blockTensor Q Λ Λc ν ν₀ (x ⊗ₜ y) =
      prefixStendhal Q Λ Λc ν ν₀ x * endStendhal Q Λ Λc ν ν₀ y :=
  blockTensorLin_tmul x y

theorem blockTensor_mul (d d' : T ⊗[k] Tc) :
    blockTensor Q Λ Λc ν ν₀ (d * d') =
      blockTensor Q Λ Λc ν ν₀ d * blockTensor Q Λ Λc ν ν₀ d' :=
  map_mul _ d d'

/-- `ι(1)` is the end idempotent `e_L`. -/
theorem blockTensor_one :
    blockTensor Q Λ Λc ν ν₀ 1 = endStendhal Q Λ Λc ν ν₀ 1 := by
  rw [Algebra.TensorProduct.one_def, blockTensor_tmul, prefixStendhal_one_mul_endUnit]

/-- The image of `ι` is fixed by `e_L` on the left. -/
theorem endStendhal_one_mul_blockTensor (d : T ⊗[k] Tc) :
    endStendhal Q Λ Λc ν ν₀ 1 * blockTensor Q Λ Λc ν ν₀ d = blockTensor Q Λ Λc ν ν₀ d := by
  rw [← blockTensor_one, ← blockTensor_mul, one_mul]

/-- The image of `ι` is fixed by `e_L` on the right. -/
theorem blockTensor_mul_endStendhal_one (d : T ⊗[k] Tc) :
    blockTensor Q Λ Λc ν ν₀ d * endStendhal Q Λ Λc ν ν₀ 1 = blockTensor Q Λ Λc ν ν₀ d := by
  rw [← blockTensor_one, ← blockTensor_mul, mul_one]

end Categorification.Stendhal.CupCap
