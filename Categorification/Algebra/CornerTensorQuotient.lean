/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.CornerTensor

/-!
# Corner tensor products along a quotient map

Let `f : A → B` be a surjective homomorphism of `k`-algebras and `e₂, e₁, e₀ ∈ A` idempotents.
The corner tensor products over `A` and over `B` are related by the map `x ⊗ y ↦ f x ⊗ f y`,
which is compatible with multiplication. If multiplication over `A` is injective, then so is
multiplication over `B` provided every element `e₂ z e₀` with `f z = 0` is a sum of products
`e₂ j e₁ x e₀` and `e₂ x e₁ j e₀` with `f j = 0`.

This is the form in which Lemma 6.5 of Webster (arXiv:1309.3796v2) passes from the bimodules
`B̃_w` to their quotients `B_w` by violated diagrams.

## Main results

* `CornerTensor.map` : the map `x ⊗ y ↦ f x ⊗ f y` (`map_tmul`), surjective for surjective `f`.
* `CornerTensor.mult_map` : compatibility with multiplication.
* `CornerTensor.mult_injective_of_ker` : injectivity of multiplication passes to `B`.
* `CornerTensor.mult_surjective_of_surjective` : so does surjectivity onto the corner.
-/

namespace Categorification

open scoped TensorProduct

noncomputable section

namespace CornerTensor

variable {k : Type*} [CommRing k] {A B : Type*} [Ring A] [Algebra k A] [Ring B] [Algebra k B]
  (f : A →ₐ[k] B) {e₂ e₁ e₀ : A}

/-- The map `x ⊗ y ↦ f x ⊗ f y` of corner tensor products. -/
def map : CornerTensor k A e₂ e₁ e₀ →ₗ[k] CornerTensor k B (f e₂) (f e₁) (f e₀) :=
  (rel k A e₂ e₁ e₀).liftQ
    ((mkQ k B (f e₂) (f e₁) (f e₀)).comp (TensorProduct.map f.toLinearMap f.toLinearMap)) <| by
    rw [rel, Submodule.span_le]
    rintro t (⟨x, y, rfl⟩ | ⟨x, c, y, rfl⟩) <;>
      simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, LinearMap.comp_apply,
        TensorProduct.map_tmul, AlgHom.toLinearMap_apply, map_mul, sub_eq_zero]
    · exact tmul_corner (f x) (f y)
    · exact tmul_balance (f x) (f c) (f y)

theorem map_tmul (x y : A) :
    map f (tmul x y : CornerTensor k A e₂ e₁ e₀) = tmul (f x) (f y) := by
  simp [map, tmul, tmulₗ, mkQ]

theorem map_surjective (hf : Function.Surjective f) :
    Function.Surjective (map f : CornerTensor k A e₂ e₁ e₀ →ₗ[k] _) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← span_tmul, Submodule.span_le]
  rintro _ ⟨a, b, rfl⟩
  obtain ⟨x, rfl⟩ := hf a
  obtain ⟨y, rfl⟩ := hf b
  exact ⟨tmul x y, map_tmul f x y⟩

variable (h₂ : IsIdempotentElem e₂) (h₁ : IsIdempotentElem e₁) (h₀ : IsIdempotentElem e₀)

theorem mult_map (t : CornerTensor k A e₂ e₁ e₀) :
    mult (h₂.map f) (h₁.map f) (h₀.map f) (map f t) = f (mult h₂ h₁ h₀ t) := by
  induction t using induction_on with
  | tmul x y => simp [map_tmul, mult_tmul]
  | add s t hs ht => rw [map_add, map_add, hs, ht, map_add, map_add]

theorem mult_corner (t : CornerTensor k A e₂ e₁ e₀) :
    e₂ * mult h₂ h₁ h₀ t * e₀ = mult h₂ h₁ h₀ t := by
  induction t using induction_on with
  | tmul x y =>
    rw [mult_tmul]
    simp only [← mul_assoc, h₂.eq]
    rw [mul_assoc _ e₀ e₀, h₀.eq]
  | add s t hs ht => rw [map_add, mul_add, add_mul, hs, ht]

/-- **Injectivity along a quotient.** If multiplication over `A` is injective, `f` is surjective,
and every `e₂ z e₀` with `f z = 0` is a sum of products `e₂ j e₁ x e₀` and `e₂ x e₁ j e₀` with
`f j = 0`, then multiplication over `B` is injective. -/
theorem mult_injective_of_ker (hf : Function.Surjective f)
    (hinj : Function.Injective (mult h₂ h₁ h₀ : CornerTensor k A e₂ e₁ e₀ →ₗ[k] A))
    (hS : ∀ z, f z = 0 → e₂ * z * e₀ ∈ Submodule.span k
      {y | ∃ j x, f j = 0 ∧ (y = e₂ * j * e₁ * x * e₀ ∨ y = e₂ * x * e₁ * j * e₀)}) :
    Function.Injective (mult (h₂.map f) (h₁.map f) (h₀.map f) :
      CornerTensor k B (f e₂) (f e₁) (f e₀) →ₗ[k] B) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  obtain ⟨t, rfl⟩ := map_surjective f hf s
  rw [mult_map f h₂ h₁ h₀] at hs
  have hle : Submodule.span k
      {y | ∃ j x, f j = 0 ∧ (y = e₂ * j * e₁ * x * e₀ ∨ y = e₂ * x * e₁ * j * e₀)} ≤
      (LinearMap.ker (map f : CornerTensor k A e₂ e₁ e₀ →ₗ[k] _)).map (mult h₂ h₁ h₀) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, x, hj, rfl | rfl⟩
    · exact ⟨tmul j x, by simp [map_tmul, hj], mult_tmul h₂ h₁ h₀ j x⟩
    · exact ⟨tmul x j, by simp [map_tmul, hj], mult_tmul h₂ h₁ h₀ x j⟩
  have hmem := hle (hS _ hs)
  rw [mult_corner h₂ h₁ h₀] at hmem
  obtain ⟨t', ht', he⟩ := hmem
  rw [← hinj he]
  exact ht'

/-- **Surjectivity along a quotient.** If every corner element of `A` is a product, so is every
corner element of `B`. -/
theorem mult_surjective_of_surjective (hf : Function.Surjective f)
    (hsurj : ∀ y, ∃ t, mult h₂ h₁ h₀ (t : CornerTensor k A e₂ e₁ e₀) = e₂ * y * e₀) (y : B) :
    ∃ t, mult (h₂.map f) (h₁.map f) (h₀.map f)
      (t : CornerTensor k B (f e₂) (f e₁) (f e₀)) = f e₂ * y * f e₀ := by
  obtain ⟨x, rfl⟩ := hf y
  obtain ⟨t, ht⟩ := hsurj x
  exact ⟨map f t, by rw [mult_map f h₂ h₁ h₀, ht, map_mul, map_mul]⟩

end CornerTensor

end

end Categorification
