/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FrontWindowDescent

/-!
# The black block at the right end: the juxtaposition map

Webster, arXiv:1309.3796v3, proof of Lemma 7.19, input (B3) with the black block at the right
end. Let `λ⁺` be the two red strands `(μ, μ*)` followed by `λ`, with `ν₀` black strands at the
maximum and `ν` black strands for `λ`. Placing a diagram of `T̃^{(μ,μ*)}(ν₀)` on the first `N`
strands (`CupCap.frontStendhal`) and a diagram of `T̃^λ` on the last `m` strands
(`CupCap.suffixStendhal`) is horizontal juxtaposition

  `ι : T̃^{(μ,μ*)}(ν₀) ⊗_k T̃^λ → T̃^{λ⁺}(ν + ν₀)`, `y ⊗ x ↦ y x`

(`CupCap.blockTensorR`). The two placements commute, so `ι` is multiplicative; it is not unital:
`ι(1)` is the front idempotent `e_R` (`CupCap.blockTensorR_one`).

For `ℓ = 0` the algebra `T̃^λ` has no red strands and is the KLR algebra `R(ν)` of the black block,
and `T̃^{λ⁺}(ν + ν₀)` is `T̃^{(μ,μ*)}(ν + ν₀)`: then `ι` is the map `A′ ⊗ R(b) → A` of (B3-R), with
`b = ν` and `A′ = T̃^{(μ,μ*)}(ν₀)`, the `b`-block on the right. The statements here hold for every
`ℓ`.

## Main definitions

* `CupCap.blockTensorR`: the juxtaposition map `ι`, a non-unital algebra map.

## Main results

* `CupCap.blockTensorR_tmul`, `CupCap.blockTensorR_mul`, `CupCap.blockTensorR_one`.
* `CupCap.frontStendhal_one_mul_blockTensorR`, `CupCap.blockTensorR_mul_frontStendhal_one`: `ι`
  lands in the corner `e_R T̃^{λ⁺} e_R`.
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
local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc 0 (Nat.zero_le ℓ)) (ν + ν₀)

/-- The bilinear map `(y, x) ↦ y x` placing `y ∈ T̃^{(μ,μ*)}` on the first strands and
`x ∈ T̃^λ` on the last strands. -/
def blockBilR : Tc →ₗ[k] T →ₗ[k] Tp :=
  LinearMap.mk₂ k (fun y x => frontStendhal Q Λ Λc ν ν₀ y * suffixStendhal Q Λ Λc ν ν₀ x)
    (fun y y' x => by rw [map_add, add_mul])
    (fun c y x => by rw [map_smul, smul_mul_assoc])
    (fun y x x' => by rw [map_add, mul_add])
    (fun c y x => by rw [map_smul, mul_smul_comm])

/-- The juxtaposition `y ⊗ x ↦ y x` as a `k`-linear map `T̃^{(μ,μ*)} ⊗_k T̃^λ → T̃^{λ⁺}`. -/
def blockTensorRLin : Tc ⊗[k] T →ₗ[k] Tp := TensorProduct.lift (blockBilR Q Λ Λc ν ν₀)

variable {Q Λ Λc ν ν₀}

theorem blockTensorRLin_tmul (y : Tc) (x : T) :
    blockTensorRLin Q Λ Λc ν ν₀ (y ⊗ₜ x) =
      frontStendhal Q Λ Λc ν ν₀ y * suffixStendhal Q Λ Λc ν ν₀ x := by
  rw [blockTensorRLin, TensorProduct.lift.tmul]
  rfl

theorem blockTensorRLin_mul (d d' : Tc ⊗[k] T) :
    blockTensorRLin Q Λ Λc ν ν₀ (d * d') =
      blockTensorRLin Q Λ Λc ν ν₀ d * blockTensorRLin Q Λ Λc ν ν₀ d' := by
  induction d using TensorProduct.inductionOn with
  | add a b ha hb => rw [add_mul, map_add, ha, hb, map_add, add_mul]
  | tmul y x =>
    induction d' using TensorProduct.inductionOn with
    | add a b ha hb => rw [mul_add, map_add, ha, hb, map_add, mul_add]
    | tmul y' x' =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, blockTensorRLin_tmul, blockTensorRLin_tmul,
        blockTensorRLin_tmul, map_mul, map_mul, mul_assoc, mul_assoc,
        ← mul_assoc _ _ (suffixStendhal _ _ _ _ _ x'),
        ← (commute_suffixStendhal_frontStendhal Q Λ Λc x y').eq, mul_assoc]

variable (Q Λ Λc ν ν₀) in
/-- **The juxtaposition map** `ι : T̃^{(μ,μ*)}(ν₀) ⊗_k T̃^λ → T̃^{λ⁺}(ν + ν₀)`, `y ⊗ x ↦ y x`
(arXiv:1309.3796v3, proof of Lemma 7.19, (B3); for `ℓ = 0` the map `A′ ⊗ R(b) → A` with the
black block on the right). -/
def blockTensorR : Tc ⊗[k] T →ₙₐ[k] Tp where
  toFun := blockTensorRLin Q Λ Λc ν ν₀
  map_smul' c d := map_smul _ c d
  map_zero' := map_zero _
  map_add' := map_add _
  map_mul' := blockTensorRLin_mul

theorem blockTensorR_apply (d : Tc ⊗[k] T) :
    blockTensorR Q Λ Λc ν ν₀ d = blockTensorRLin Q Λ Λc ν ν₀ d := rfl

theorem blockTensorR_tmul (y : Tc) (x : T) :
    blockTensorR Q Λ Λc ν ν₀ (y ⊗ₜ x) =
      frontStendhal Q Λ Λc ν ν₀ y * suffixStendhal Q Λ Λc ν ν₀ x :=
  blockTensorRLin_tmul y x

theorem blockTensorR_mul (d d' : Tc ⊗[k] T) :
    blockTensorR Q Λ Λc ν ν₀ (d * d') =
      blockTensorR Q Λ Λc ν ν₀ d * blockTensorR Q Λ Λc ν ν₀ d' :=
  map_mul _ d d'

/-- `ι(1)` is the front idempotent `e_R`. -/
theorem blockTensorR_one :
    blockTensorR Q Λ Λc ν ν₀ 1 = frontStendhal Q Λ Λc ν ν₀ 1 := by
  rw [Algebra.TensorProduct.one_def, blockTensorR_tmul,
    ← (commute_suffixStendhal_frontStendhal Q Λ Λc 1 1).eq, suffixStendhal_one_mul_frontUnit]

/-- The image of `ι` is fixed by `e_R` on the left. -/
theorem frontStendhal_one_mul_blockTensorR (d : Tc ⊗[k] T) :
    frontStendhal Q Λ Λc ν ν₀ 1 * blockTensorR Q Λ Λc ν ν₀ d = blockTensorR Q Λ Λc ν ν₀ d := by
  rw [← blockTensorR_one, ← blockTensorR_mul, one_mul]

/-- The image of `ι` is fixed by `e_R` on the right. -/
theorem blockTensorR_mul_frontStendhal_one (d : Tc ⊗[k] T) :
    blockTensorR Q Λ Λc ν ν₀ d * frontStendhal Q Λ Λc ν ν₀ 1 = blockTensorR Q Λ Λc ν ν₀ d := by
  rw [← blockTensorR_one, ← blockTensorR_mul, mul_one]

end Categorification.Stendhal.CupCap
