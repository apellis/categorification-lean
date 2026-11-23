/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Tensor products of corners over a corner algebra

Let `A` be a `k`-algebra and `e₂, e₁, e₀ ∈ A` idempotents. The corner `e₂ A e₁` is a right
module and `e₁ A e₀` a left module over the corner algebra `e₁ A e₁`. This file builds their
balanced tensor product directly as a quotient of `A ⊗[k] A`:

`CornerTensor k A e₂ e₁ e₀ = (A ⊗[k] A) ⧸ ⟨x ⊗ y - e₂xe₁ ⊗ e₁ye₀, x(e₁ce₁) ⊗ y - x ⊗ (e₁ce₁)y⟩`.

The first family of relations identifies `A ⊗[k] A` with `e₂Ae₁ ⊗[k] e₁Ae₀` modulo the
second, and the second is the balancing over `e₁Ae₁`. This is the form in which the tensor
products of bimodules `B_w` of Webster (arXiv:1309.3796v2, §6, Lemma 6.5) are compared with
corners of the braided algebra.

## Main definitions and results

* `CornerTensor.tmul x y` : the class of `x ⊗ y`, `k`-bilinear (`tmulₗ`).
* `CornerTensor.tmul_corner` : `tmul x y = tmul (e₂xe₁) (e₁ye₀)`.
* `CornerTensor.tmul_balance` : `tmul (x(e₁ce₁)) y = tmul x ((e₁ce₁)y)`.
* `CornerTensor.span_tmul` : the classes `tmul x y` span.
* `CornerTensor.mult` : multiplication `tmul x y ↦ e₂xe₁ye₀` (`mult_tmul`).
-/

namespace Categorification

open scoped TensorProduct

noncomputable section

variable (k : Type*) [CommRing k] (A : Type*) [Ring A] [Algebra k A] (e₂ e₁ e₀ : A)

namespace CornerTensor

/-- The defining relations of the corner tensor product. -/
def relSet : Set (A ⊗[k] A) :=
  {t | ∃ x y : A, t = x ⊗ₜ[k] y - (e₂ * x * e₁) ⊗ₜ[k] (e₁ * y * e₀)} ∪
    {t | ∃ x c y : A, t = (x * (e₁ * c * e₁)) ⊗ₜ[k] y - x ⊗ₜ[k] ((e₁ * c * e₁) * y)}

/-- The submodule spanned by the defining relations. -/
def rel : Submodule k (A ⊗[k] A) := Submodule.span k (relSet k A e₂ e₁ e₀)

end CornerTensor

/-- The tensor product `e₂Ae₁ ⊗_{e₁Ae₁} e₁Ae₀`, as a quotient of `A ⊗[k] A`. -/
abbrev CornerTensor : Type _ := A ⊗[k] A ⧸ CornerTensor.rel k A e₂ e₁ e₀

namespace CornerTensor

/-- The quotient map. -/
def mkQ : A ⊗[k] A →ₗ[k] CornerTensor k A e₂ e₁ e₀ := (rel k A e₂ e₁ e₀).mkQ

/-- The bilinear map `x, y ↦ x ⊗ y`. -/
def tmulₗ : A →ₗ[k] A →ₗ[k] CornerTensor k A e₂ e₁ e₀ :=
  (TensorProduct.mk k A A).compr₂ (mkQ k A e₂ e₁ e₀)

variable {k A e₂ e₁ e₀}

/-- The class of `x ⊗ y`. -/
def tmul (x y : A) : CornerTensor k A e₂ e₁ e₀ := tmulₗ k A e₂ e₁ e₀ x y

theorem tmul_def (x y : A) :
    (tmul x y : CornerTensor k A e₂ e₁ e₀) = mkQ k A e₂ e₁ e₀ (x ⊗ₜ[k] y) := rfl

theorem tmul_add_left (x x' y : A) :
    (tmul (x + x') y : CornerTensor k A e₂ e₁ e₀) = tmul x y + tmul x' y := by
  simp [tmul]

theorem tmul_add_right (x y y' : A) :
    (tmul x (y + y') : CornerTensor k A e₂ e₁ e₀) = tmul x y + tmul x y' := by
  simp [tmul]

theorem tmul_sub_left (x x' y : A) :
    (tmul (x - x') y : CornerTensor k A e₂ e₁ e₀) = tmul x y - tmul x' y := by
  simp [tmul]

theorem tmul_sub_right (x y y' : A) :
    (tmul x (y - y') : CornerTensor k A e₂ e₁ e₀) = tmul x y - tmul x y' := by
  simp [tmul]

theorem tmul_smul_left (r : k) (x y : A) :
    (tmul (r • x) y : CornerTensor k A e₂ e₁ e₀) = r • tmul x y := by
  simp [tmul]

theorem tmul_smul_right (r : k) (x y : A) :
    (tmul x (r • y) : CornerTensor k A e₂ e₁ e₀) = r • tmul x y := by
  simp [tmul]

@[simp] theorem tmul_zero_left (y : A) : (tmul 0 y : CornerTensor k A e₂ e₁ e₀) = 0 := by
  simp [tmul]

@[simp] theorem tmul_zero_right (x : A) : (tmul x 0 : CornerTensor k A e₂ e₁ e₀) = 0 := by
  simp [tmul]

theorem tmul_sum_left {ι : Type*} (s : Finset ι) (f : ι → A) (y : A) :
    (tmul (∑ i ∈ s, f i) y : CornerTensor k A e₂ e₁ e₀) = ∑ i ∈ s, tmul (f i) y := by
  simp [tmul]

theorem tmul_sum_right {ι : Type*} (s : Finset ι) (x : A) (f : ι → A) :
    (tmul x (∑ i ∈ s, f i) : CornerTensor k A e₂ e₁ e₀) = ∑ i ∈ s, tmul x (f i) := by
  simp [tmul]

/-- A tensor only depends on the corner parts of its factors. -/
theorem tmul_corner (x y : A) :
    (tmul x y : CornerTensor k A e₂ e₁ e₀) = tmul (e₂ * x * e₁) (e₁ * y * e₀) := by
  rw [tmul_def, tmul_def, ← sub_eq_zero, ← map_sub, mkQ, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  exact Submodule.subset_span (Or.inl ⟨x, y, rfl⟩)

/-- The balancing over the corner algebra `e₁Ae₁`. -/
theorem tmul_balance (x c y : A) :
    (tmul (x * (e₁ * c * e₁)) y : CornerTensor k A e₂ e₁ e₀) = tmul x ((e₁ * c * e₁) * y) := by
  rw [tmul_def, tmul_def, ← sub_eq_zero, ← map_sub, mkQ, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  exact Submodule.subset_span (Or.inr ⟨x, c, y, rfl⟩)

/-- Balancing for an element of the corner algebra given with its corner property. -/
theorem tmul_balance_of {c : A} (hc : e₁ * c * e₁ = c) (x y : A) :
    (tmul (x * c) y : CornerTensor k A e₂ e₁ e₀) = tmul x (c * y) := by
  have h := tmul_balance (k := k) (A := A) (e₂ := e₂) (e₁ := e₁) (e₀ := e₀) x c y
  rwa [hc] at h

theorem mkQ_surjective : Function.Surjective (mkQ k A e₂ e₁ e₀) :=
  Submodule.mkQ_surjective _

/-- The classes `tmul x y` span the corner tensor product. -/
theorem span_tmul :
    Submodule.span k {t : CornerTensor k A e₂ e₁ e₀ | ∃ x y, t = tmul x y} = ⊤ := by
  rw [eq_top_iff]
  rintro t -
  obtain ⟨t, rfl⟩ := mkQ_surjective t
  induction t using TensorProduct.inductionOn with
  | tmul x y => exact Submodule.subset_span ⟨x, y, rfl⟩
  | add s t hs ht => rw [map_add]; exact add_mem hs ht

/-- Induction principle: a property closed under addition and holding on all `tmul x y` holds
everywhere. -/
theorem induction_on {P : CornerTensor k A e₂ e₁ e₀ → Prop} (t : CornerTensor k A e₂ e₁ e₀)
    (tmul : ∀ x y, P (tmul x y)) (add : ∀ s t, P s → P t → P (s + t)) : P t := by
  obtain ⟨t, rfl⟩ := mkQ_surjective t
  induction t using TensorProduct.inductionOn with
  | tmul x y => exact tmul x y
  | add s t hs ht => rw [map_add]; exact add _ _ hs ht

theorem ext {M : Type*} [AddCommGroup M] [Module k M]
    {f g : CornerTensor k A e₂ e₁ e₀ →ₗ[k] M} (h : ∀ x y, f (tmul x y) = g (tmul x y)) :
    f = g := by
  refine LinearMap.ext fun t => ?_
  induction t using induction_on with
  | tmul x y => exact h x y
  | add s t hs ht => rw [map_add, map_add, hs, ht]

section Mult

/-- The bilinear map `x, y ↦ e₂ x e₁ y e₀`. -/
def multₗ (e₂ e₁ e₀ : A) : A →ₗ[k] A →ₗ[k] A :=
  LinearMap.mk₂ k (fun x y => e₂ * x * e₁ * y * e₀)
    (fun x x' y => by noncomm_ring) (fun r x y => by simp)
    (fun x y y' => by noncomm_ring) (fun r x y => by simp)

variable (h₂ : IsIdempotentElem e₂) (h₁ : IsIdempotentElem e₁) (h₀ : IsIdempotentElem e₀)
include h₂ h₁ h₀

/-- Multiplication `x ⊗ y ↦ e₂ x e₁ y e₀`. -/
def mult : CornerTensor k A e₂ e₁ e₀ →ₗ[k] A :=
  (rel k A e₂ e₁ e₀).liftQ (TensorProduct.lift (multₗ e₂ e₁ e₀)) <| by
    rw [rel, Submodule.span_le]
    rintro t (⟨x, y, rfl⟩ | ⟨x, c, y, rfl⟩) <;>
      simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, TensorProduct.lift.tmul, multₗ,
        LinearMap.mk₂_apply, sub_eq_zero]
    · have r : ∀ a : A, a * e₁ * e₁ = a * e₁ := fun a => by rw [mul_assoc, h₁.eq]
      have r0 : ∀ a : A, a * e₀ * e₀ = a * e₀ := fun a => by rw [mul_assoc, h₀.eq]
      simp only [← mul_assoc, h₂.eq, r, r0]
    · have r : ∀ a : A, a * e₁ * e₁ = a * e₁ := fun a => by rw [mul_assoc, h₁.eq]
      simp only [← mul_assoc, r]

theorem mult_tmul (x y : A) :
    mult h₂ h₁ h₀ (tmul x y : CornerTensor k A e₂ e₁ e₀) = e₂ * x * e₁ * y * e₀ := by
  simp [mult, tmul, tmulₗ, mkQ, multₗ]

end Mult

end CornerTensor

end

end Categorification
