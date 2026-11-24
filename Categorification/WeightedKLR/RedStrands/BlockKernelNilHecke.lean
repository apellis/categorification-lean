/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockKernelTensor

/-!
# NilHecke splitting of a higher loading kernel

An equal-label adjacent crossing and its first dot restrict to the actual
higher kernel. The dot contracts the square-zero crossing and splits the
kernel into two copies of its crossing image.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR KLRAlgebra

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} {k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ} {ν : Multiset I}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
  (t : Seq (stendhalWeight ℓ ν)) (a b : Fin ℓ)

local notation "μ" => stendhalWeight ℓ ν
local notation "N" => Multiset.card μ
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ
local notation "V" => ViolQuotient k Q Λ ν
local notation "F" => AlgHom.comp (violMk k Q Λ ν) (ofKLR k Q Λ ν)
local notation "p" => F (e t)
local notation "ord" => isIdempotentElem_violMk_redProj k Q Λ ν (redWord t)
local notation "E" => violMk k Q Λ ν (redProj k Q Λ ν (redWord t))
local notation "T" => IsIdempotentElem.Corner ord
local notation "K" => blockLoadingKernel Q Λ t a b

private theorem blockKernel_left_supported (z : K) : p * z.1.1.1 = z.1.1.1 :=
  congrArg (fun w : T => w.1) z.1.2

private theorem blockKernel_leftMul_rep (c : V) (hc : p * c = c * p) (z : K) :
    (blockLoadingRep Q Λ t (c * z.1.1.1)).1.1 = c * z.1.1.1 := by
  rw [blockLoadingRep_val]
  change p * (c * z.1.1.1) * E = c * z.1.1.1
  rw [← mul_assoc, hc, mul_assoc c, blockKernel_left_supported Q Λ t a b,
    mul_assoc, CornerEndomorphism.corner_mul_right ord z.1.1]

private def blockKernel_leftMulValue (c : V) (hc : p * c = c * p) (z : K) : K :=
  ⟨blockLoadingRep Q Λ t (c * z.1.1.1), by
    let J := blockUpperIdeal k Q Λ ν a b (adjacentBlockRoot a b t) (redWord t)
    change (blockLoadingRep Q Λ t (c * z.1.1.1)).1.1 ∈ J
    rw [blockKernel_leftMul_rep Q Λ t a b c hc]
    exact TwoSidedIdeal.mul_mem_left J _ _ z.2⟩

private theorem blockKernel_value_injective : Function.Injective (fun z : K => z.1.1.1) :=
  fun _ _ h => Subtype.ext (Subtype.ext (Subtype.ext h))

private def blockKernel_leftMul (c : V) (hc : p * c = c * p) : K →ₗ[Tᵐᵒᵖ] K where
  toFun := blockKernel_leftMulValue Q Λ t a b c hc
  map_add' x y := by
    apply blockKernel_value_injective Q Λ t a b
    change (blockLoadingRep Q Λ t (c * (x + y).1.1.1)).1.1 =
      (blockLoadingRep Q Λ t (c * x.1.1.1)).1.1 + (blockLoadingRep Q Λ t (c * y.1.1.1)).1.1
    simp only [blockKernel_leftMul_rep Q Λ t a b c hc]
    exact mul_add c _ _
  map_smul' r z := by
    apply blockKernel_value_injective Q Λ t a b
    change (blockLoadingRep Q Λ t (c * (r • z).1.1.1)).1.1 =
      (blockLoadingRep Q Λ t (c * z.1.1.1)).1.1 * r.unop.1
    simp only [blockKernel_leftMul_rep Q Λ t a b c hc]
    exact (mul_assoc c _ _).symm

private theorem blockKernel_leftMul_val (c : V) (hc : p * c = c * p) (z : K) :
    (blockKernel_leftMul Q Λ t a b c hc z).1.1.1 = c * z.1.1.1 :=
  blockKernel_leftMul_rep Q Λ t a b c hc z

section EqualAdjacent

variable (j : ℕ) (hj : j + 1 < (stendhalWeight ℓ ν).card)

set_option quotPrecheck false in
local notation "i₀" => (⟨j, by omega⟩ : Fin N)
set_option quotPrecheck false in
local notation "i₁" => (⟨j + 1, hj⟩ : Fin N)
local notation "D" => F (ψ j : R)
local notation "X₀" => F (x i₀ : R)
local notation "X₁" => F (x i₁ : R)

variable (same : t.lbl ⟨j, by omega⟩ = t.lbl ⟨j + 1, hj⟩)

/-- Multiplication by the equal-label crossing restricts to the actual higher kernel. -/
def blockLoadingKernel_nilHeckeCrossing : K →ₗ[Tᵐᵒᵖ] K :=
  blockKernel_leftMul Q Λ t a b D (by
    rw [← map_mul F, ← map_mul F, e_mul_ψ, sadj_smul_eq_self hj same])

theorem blockLoadingKernel_nilHeckeCrossing_val (z : K) :
    (blockLoadingKernel_nilHeckeCrossing Q Λ t a b j hj same z).1.1.1 = D * z.1.1.1 :=
  blockKernel_leftMul_val Q Λ t a b D _ z

private def blockLoadingKernel_nilHeckeDot : K →ₗ[Tᵐᵒᵖ] K :=
  blockKernel_leftMul Q Λ t a b X₀ (by rw [← map_mul F, ← map_mul F, x_mul_e])

local notation "δ" => blockLoadingKernel_nilHeckeCrossing Q Λ t a b j hj same
local notation "u" => blockLoadingKernel_nilHeckeDot Q Λ t a b j hj

private theorem blockKernel_nilHecke_sq (z : K) : δ (δ z) = 0 := by
  apply blockKernel_value_injective Q Λ t a b
  simp only [blockLoadingKernel_nilHeckeCrossing_val]
  change D * (D * z.1.1.1) = (0 : V)
  have h : (ψ j * ψ j * e t : R) = 0 := by rw [ψ_sq j hj, ite_eq_left same]
  have mapped := congrArg F h
  simp only [map_mul F, map_zero] at mapped
  rw [← mul_assoc, ← blockKernel_left_supported Q Λ t a b z, ← mul_assoc, mapped, zero_mul]

private theorem blockKernel_nilHecke_contract (z : K) (hz : δ z = 0) : δ (u z) = z := by
  apply blockKernel_value_injective Q Λ t a b
  simp only [blockLoadingKernel_nilHeckeCrossing_val, blockLoadingKernel_nilHeckeDot, blockKernel_leftMul_val]
  have crosses : (ψ j * x i₀ * e t - x i₁ * ψ j * e t : R) = e t := by
    rw [← sub_mul, dot_cross_right j hj, ite_eq_left same]
  have mapped := congrArg (fun c => F c * z.1.1.1) crosses
  have z0 : D * z.1.1.1 = 0 := by
    rw [← blockLoadingKernel_nilHeckeCrossing_val Q Λ t a b j hj same z]
    exact congrArg (fun w : K => w.1.1.1) hz
  simpa only [map_mul F, map_sub, sub_mul, mul_assoc, blockKernel_left_supported Q Λ t a b z,
    z0, mul_zero, sub_zero] using mapped

private def nilHeckeRangeProd {S M : Type*} [Ring S] [AddCommGroup M] [Module S M]
    (d dot : M →ₗ[S] M) (sq : ∀ x, d (d x) = 0)
    (contract : ∀ x, d x = 0 → d (dot x) = x) :
    M ≃ₗ[S] LinearMap.range d × LinearMap.range d where
  toFun x := (⟨x - dot (d x), dot (x - dot (d x)), contract _ (by
    rw [map_sub, contract (d x) (sq x), sub_self])⟩, ⟨d x, x, rfl⟩)
  invFun w := w.1.1 + dot w.2.1
  left_inv x := sub_add_cancel _ _
  right_inv w := by
    have h₁ : d w.1.1 = 0 := by
      obtain ⟨x, hx⟩ := w.1.2
      rw [← hx, sq x]
    have h₂ : d w.2.1 = 0 := by
      obtain ⟨x, hx⟩ := w.2.2
      rw [← hx, sq x]
    have hd : d (w.1.1 + dot w.2.1) = w.2.1 := by
      rw [map_add, h₁, contract _ h₂, zero_add]
    apply Prod.ext
    · apply Subtype.ext
      change w.1.1 + dot w.2.1 - dot (d (w.1.1 + dot w.2.1)) = w.1.1
      rw [hd, add_sub_cancel_right]
    · exact Subtype.ext hd
  map_add' x y := by
    apply Prod.ext
    · apply Subtype.ext
      change x + y - dot (d (x + y)) = (x - dot (d x)) + (y - dot (d y))
      rw [map_add, map_add]
      abel
    · exact Subtype.ext (map_add d x y)
  map_smul' r x := by
    apply Prod.ext
    · apply Subtype.ext
      change r • x - dot (d (r • x)) = r • (x - dot (d x))
      rw [map_smul, map_smul, smul_sub]
    · exact Subtype.ext (map_smul d r x)

/-- On the actual higher kernel, the equal-label crossing is exact. -/
theorem blockLoadingKernel_nilHecke_range_eq_ker :
    LinearMap.range (δ : K →ₗ[Tᵐᵒᵖ] K) = LinearMap.ker δ := by
  apply le_antisymm
  · rintro z ⟨x, rfl⟩
    exact LinearMap.mem_ker.mpr (blockKernel_nilHecke_sq Q Λ t a b j hj same x)
  · intro z hz
    exact ⟨u z, blockKernel_nilHecke_contract Q Λ t a b j hj same z (LinearMap.mem_ker.mp hz)⟩

/-- The loading kernel is two copies of the image of its equal-label crossing. -/
def blockLoadingKernel_equiv_nilHeckeRangeProd :
    K ≃ₗ[Tᵐᵒᵖ] LinearMap.range (δ : K →ₗ[Tᵐᵒᵖ] K) × LinearMap.range (δ : K →ₗ[Tᵐᵒᵖ] K) :=
  nilHeckeRangeProd δ u (blockKernel_nilHecke_sq Q Λ t a b j hj same)
    (blockKernel_nilHecke_contract Q Λ t a b j hj same)

end EqualAdjacent
end Categorification.Stendhal.BraidedStendhalAlgebra
