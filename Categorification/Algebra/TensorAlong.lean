/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Tensor products of corners along a homomorphism

Let `φ : C → A` be a (not necessarily unital) homomorphism of `k`-algebras, `e₂ ∈ A` and
`e₁, e₀ ∈ C` idempotents. Through `φ`, the corner `e₂ A φ(e₁)` is a right module over the corner
algebra `e₁ C e₁`, and `e₁ C e₀` is a left module over it. This file builds their balanced tensor
product as a quotient of `A ⊗[k] C`:

`TensorAlong k A C φ e₂ e₁ e₀ = (A ⊗[k] C) ⧸ ⟨x ⊗ y - e₂xφ(e₁) ⊗ e₁ye₀,
  xφ(e₁ce₁) ⊗ y - x ⊗ (e₁ce₁)y⟩`,

with multiplication `x ⊗ y ↦ e₂ x φ(e₁ y e₀)`. It generalizes `CornerTensor`, which is the case
`C = A`, `φ = id`. This is the form in which Webster (arXiv:1309.3796v2, Proposition 6.7)
compares the tensor product of the bimodule of the functor `E_i` with the bimodules `B_w`: the
homomorphism `φ` adds a black strand at the right.

## Main results

* `TensorAlong.tmul_corner`, `TensorAlong.tmul_balance` : the defining relations.
* `TensorAlong.mult` : multiplication `x ⊗ y ↦ e₂xφ(e₁ye₀)` (`mult_tmul`).
* `TensorAlong.mult_injective_of_basis`, `TensorAlong.mult_surjective_of_basis` : if
  `e₂ A φ(e₁)` is generated as a right module by a family `g` such that the products
  `g_c φ(y_c)` with `y_c ∈ e₁ C e₀` are independent and fill `e₂ A φ(e₀)`, multiplication is a
  bijection onto `e₂ A φ(e₀)`.
* `TensorAlong.map` : the map along quotients `x ⊗ y ↦ π x ⊗ π₀ y`, with
  `TensorAlong.mult_injective_of_ker` and `TensorAlong.mult_surjective_of_surjective`.
-/

namespace Categorification

open scoped TensorProduct

noncomputable section

variable (k : Type*) [CommRing k] (A C : Type*) [Ring A] [Algebra k A] [Ring C] [Algebra k C]
  (φ : C →ₙₐ[k] A) (e₂ : A) (e₁ e₀ : C)

namespace TensorAlong

/-- The defining relations of the tensor product along `φ`. -/
def relSet : Set (A ⊗[k] C) :=
  {t | ∃ (x : A) (y : C), t = x ⊗ₜ[k] y - (e₂ * x * φ e₁) ⊗ₜ[k] (e₁ * y * e₀)} ∪
    {t | ∃ (x : A) (c y : C), t = (x * φ (e₁ * c * e₁)) ⊗ₜ[k] y - x ⊗ₜ[k] ((e₁ * c * e₁) * y)}

/-- The submodule spanned by the defining relations. -/
def rel : Submodule k (A ⊗[k] C) := Submodule.span k (relSet k A C φ e₂ e₁ e₀)

end TensorAlong

/-- The tensor product `e₂Aφ(e₁) ⊗_{e₁Ce₁} e₁Ce₀`, as a quotient of `A ⊗[k] C`. -/
abbrev TensorAlong : Type _ := A ⊗[k] C ⧸ TensorAlong.rel k A C φ e₂ e₁ e₀

namespace TensorAlong

/-- The quotient map. -/
def mkQ : A ⊗[k] C →ₗ[k] TensorAlong k A C φ e₂ e₁ e₀ := (rel k A C φ e₂ e₁ e₀).mkQ

/-- The bilinear map `x, y ↦ x ⊗ y`. -/
def tmulₗ : A →ₗ[k] C →ₗ[k] TensorAlong k A C φ e₂ e₁ e₀ :=
  (TensorProduct.mk k A C).compr₂ (mkQ k A C φ e₂ e₁ e₀)

variable {k A C φ e₂ e₁ e₀}

/-- The class of `x ⊗ y`. -/
def tmul (x : A) (y : C) : TensorAlong k A C φ e₂ e₁ e₀ := tmulₗ k A C φ e₂ e₁ e₀ x y

theorem tmul_def (x : A) (y : C) :
    (tmul x y : TensorAlong k A C φ e₂ e₁ e₀) = mkQ k A C φ e₂ e₁ e₀ (x ⊗ₜ[k] y) := rfl

@[simp] theorem tmul_zero_left (y : C) : (tmul 0 y : TensorAlong k A C φ e₂ e₁ e₀) = 0 := by
  simp [tmul]

@[simp] theorem tmul_zero_right (x : A) : (tmul x 0 : TensorAlong k A C φ e₂ e₁ e₀) = 0 := by
  simp [tmul]

theorem tmul_add_right (x : A) (y y' : C) :
    (tmul x (y + y') : TensorAlong k A C φ e₂ e₁ e₀) = tmul x y + tmul x y' := by
  simp [tmul]

theorem tmul_sum_left {ι : Type*} (s : Finset ι) (f : ι → A) (y : C) :
    (tmul (∑ i ∈ s, f i) y : TensorAlong k A C φ e₂ e₁ e₀) = ∑ i ∈ s, tmul (f i) y := by
  simp [tmul]

theorem tmul_sum_right {ι : Type*} (s : Finset ι) (x : A) (f : ι → C) :
    (tmul x (∑ i ∈ s, f i) : TensorAlong k A C φ e₂ e₁ e₀) = ∑ i ∈ s, tmul x (f i) := by
  simp [tmul]

theorem tmul_smul_right (r : k) (x : A) (y : C) :
    (tmul x (r • y) : TensorAlong k A C φ e₂ e₁ e₀) = r • tmul x y := by
  simp [tmul]

/-- A tensor only depends on the corner parts of its factors. -/
theorem tmul_corner (x : A) (y : C) :
    (tmul x y : TensorAlong k A C φ e₂ e₁ e₀) = tmul (e₂ * x * φ e₁) (e₁ * y * e₀) := by
  rw [tmul_def, tmul_def, ← sub_eq_zero, ← map_sub, mkQ, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  exact Submodule.subset_span (Or.inl ⟨x, y, rfl⟩)

/-- The balancing over the corner algebra `e₁Ce₁`. -/
theorem tmul_balance (x : A) (c y : C) :
    (tmul (x * φ (e₁ * c * e₁)) y : TensorAlong k A C φ e₂ e₁ e₀) =
      tmul x ((e₁ * c * e₁) * y) := by
  rw [tmul_def, tmul_def, ← sub_eq_zero, ← map_sub, mkQ, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  exact Submodule.subset_span (Or.inr ⟨x, c, y, rfl⟩)

theorem mkQ_surjective : Function.Surjective (mkQ k A C φ e₂ e₁ e₀) :=
  Submodule.mkQ_surjective _

/-- Induction principle: a property closed under addition and holding on all `tmul x y` holds
everywhere. -/
theorem induction_on {P : TensorAlong k A C φ e₂ e₁ e₀ → Prop} (t : TensorAlong k A C φ e₂ e₁ e₀)
    (tmul : ∀ x y, P (tmul x y)) (add : ∀ s t, P s → P t → P (s + t)) : P t := by
  obtain ⟨t, rfl⟩ := mkQ_surjective t
  induction t using TensorProduct.inductionOn with
  | tmul x y => exact tmul x y
  | add s t hs ht => rw [map_add]; exact add _ _ hs ht

/-- The classes `tmul x y` span the tensor product. -/
theorem span_tmul :
    Submodule.span k {t : TensorAlong k A C φ e₂ e₁ e₀ | ∃ x y, t = tmul x y} = ⊤ := by
  rw [eq_top_iff]
  rintro t -
  induction t using induction_on with
  | tmul x y => exact Submodule.subset_span ⟨x, y, rfl⟩
  | add s t hs ht => exact add_mem hs ht

section Mult

/-- The bilinear map `x, y ↦ e₂ x φ(e₁ y e₀)`. -/
def multₗ (φ : C →ₙₐ[k] A) (e₂ : A) (e₁ e₀ : C) : A →ₗ[k] C →ₗ[k] A :=
  LinearMap.mk₂ k (fun x y => e₂ * x * φ (e₁ * y * e₀))
    (fun x x' y => by noncomm_ring) (fun r x y => by simp)
    (fun x y y' => by simp [mul_add, add_mul]) (fun r x y => by simp)

private theorem mul_map_mul_map (a : A) (b c : C) : a * φ b * φ c = a * φ (b * c) := by
  rw [mul_assoc, ← map_mul]

private theorem mul_idem {R : Type*} [Semigroup R] {e : R} (h : IsIdempotentElem e) (a : R) :
    a * e * e = a * e := by rw [mul_assoc, h.eq]

variable (h₂ : IsIdempotentElem e₂) (h₁ : IsIdempotentElem e₁) (h₀ : IsIdempotentElem e₀)
include h₂ h₁ h₀

/-- Multiplication `x ⊗ y ↦ e₂ x φ(e₁ y e₀)`. -/
def mult : TensorAlong k A C φ e₂ e₁ e₀ →ₗ[k] A :=
  (rel k A C φ e₂ e₁ e₀).liftQ (TensorProduct.lift (multₗ φ e₂ e₁ e₀)) <| by
    rw [rel, Submodule.span_le]
    rintro t (⟨x, y, rfl⟩ | ⟨x, c, y, rfl⟩) <;>
      simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, TensorProduct.lift.tmul, multₗ,
        LinearMap.mk₂_apply, sub_eq_zero]
    · have r1 : ∀ a : C, a * e₁ * e₁ = a * e₁ := fun a => by rw [mul_assoc, h₁.eq]
      have r0 : ∀ a : C, a * e₀ * e₀ = a * e₀ := fun a => by rw [mul_assoc, h₀.eq]
      have hφ : ∀ (a : A) (b c : C), a * φ b * φ c = a * φ (b * c) := fun a b c => by
        rw [mul_assoc, ← map_mul]
      simp only [← mul_assoc, hφ, h₂.eq, h₁.eq, r0]
    · have r1 : ∀ a : C, a * e₁ * e₁ = a * e₁ := fun a => by rw [mul_assoc, h₁.eq]
      have hφ : ∀ (a : A) (b c : C), a * φ b * φ c = a * φ (b * c) := fun a b c => by
        rw [mul_assoc, ← map_mul]
      simp only [← mul_assoc, hφ, h₁.eq, r1]

theorem mult_tmul (x : A) (y : C) :
    mult h₂ h₁ h₀ (tmul x y : TensorAlong k A C φ e₂ e₁ e₀) = e₂ * x * φ (e₁ * y * e₀) := by
  simp [mult, tmul, tmulₗ, mkQ, multₗ]

theorem mult_corner (t : TensorAlong k A C φ e₂ e₁ e₀) :
    e₂ * mult h₂ h₁ h₀ t * φ e₀ = mult h₂ h₁ h₀ t := by
  induction t using induction_on with
  | tmul x y =>
    rw [mult_tmul]
    simp only [← mul_assoc, mul_map_mul_map, h₂.eq, mul_idem h₀]
  | add s t hs ht => rw [map_add, mul_add, add_mul, hs, ht]

omit h₂ h₁ h₀ in
/-- Every tensor is a sum of tensors `g_c ⊗ y_c`, when `e₂Aφ(e₁)` is generated by `g` as a
right `e₁Ce₁`-module. -/
theorem exists_eq_sum_of_span {ι : Type*} (g : ι → A)
    (hspan : ∀ x : A, ∃ t : ι →₀ C, e₂ * x * φ e₁ = t.sum fun c y => g c * φ (e₁ * y * e₁))
    (t : TensorAlong k A C φ e₂ e₁ e₀) :
    ∃ Y : ι →₀ C, t = Y.sum fun c y => tmul (g c) y := by
  classical
  induction t using induction_on with
  | tmul x y =>
    obtain ⟨s, hs⟩ := hspan x
    refine ⟨s.mapRange (fun c => e₁ * c * e₁ * (e₁ * y * e₀)) (by simp), ?_⟩
    rw [tmul_corner, hs, Finsupp.sum, Finsupp.sum_mapRange_index (by simp), Finsupp.sum,
      tmul_sum_left]
    exact Finset.sum_congr rfl fun c _ => tmul_balance _ _ _
  | add s t hs ht =>
    obtain ⟨Y, rfl⟩ := hs
    obtain ⟨Y', rfl⟩ := ht
    refine ⟨Y + Y', ?_⟩
    rw [Finsupp.sum_add_index' (by simp) fun c y y' => tmul_add_right _ _ _]

/-- **Injectivity of multiplication for a basis.** If `e₂ A φ(e₁)` is generated by `g` as a
right `e₁Ce₁`-module, each `g_c` lies in that corner, and the products `g_c φ(y_c)` with
`y_c ∈ e₁ C e₀` are independent, multiplication is injective. -/
theorem mult_injective_of_basis {ι : Type*} (g : ι → A) (hg : ∀ c, e₂ * g c * φ e₁ = g c)
    (hspan : ∀ x : A, ∃ t : ι →₀ C, e₂ * x * φ e₁ = t.sum fun c y => g c * φ (e₁ * y * e₁))
    (hindep : ∀ Y : ι →₀ C, (Y.sum fun c y => g c * φ (e₁ * y * e₀)) = 0 →
      ∀ c, e₁ * Y c * e₀ = 0) :
    Function.Injective (mult h₂ h₁ h₀ : TensorAlong k A C φ e₂ e₁ e₀ →ₗ[k] A) := by
  rw [injective_iff_map_eq_zero]
  intro t ht
  obtain ⟨Y, rfl⟩ := exists_eq_sum_of_span g hspan t
  have hm : ∀ c y, mult h₂ h₁ h₀ (tmul (g c) y : TensorAlong k A C φ e₂ e₁ e₀) =
      g c * φ (e₁ * y * e₀) := fun c y => by
    have hg2 : e₂ * g c = g c := by
      calc e₂ * g c = e₂ * (e₂ * g c * φ e₁) := by rw [hg]
        _ = g c := by rw [← mul_assoc, ← mul_assoc, h₂.eq, hg]
    rw [mult_tmul]
    conv_lhs => rw [← hg c]
    simp only [← mul_assoc, mul_map_mul_map, h₁.eq, hg2]
  rw [Finsupp.sum, map_sum] at ht
  simp only [hm] at ht
  have h0 := hindep Y ht
  rw [Finsupp.sum]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [tmul_corner, h0 c, hg, tmul_zero_right]

/-- **Surjectivity of multiplication for a generating family.** -/
theorem mult_surjective_of_basis {ι : Type*} (g : ι → A) (hg : ∀ c, e₂ * g c * φ e₁ = g c)
    (hsurj : ∀ z : A, ∃ Y : ι →₀ C, e₂ * z * φ e₀ = Y.sum fun c y => g c * φ (e₁ * y * e₀))
    (z : A) : ∃ t, mult h₂ h₁ h₀ (t : TensorAlong k A C φ e₂ e₁ e₀) = e₂ * z * φ e₀ := by
  obtain ⟨Y, hY⟩ := hsurj z
  refine ⟨Y.sum fun c y => tmul (g c) y, ?_⟩
  rw [hY, Finsupp.sum, map_sum, Finsupp.sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hg2 : e₂ * g c = g c := by
    calc e₂ * g c = e₂ * (e₂ * g c * φ e₁) := by rw [hg]
      _ = g c := by rw [← mul_assoc, ← mul_assoc, h₂.eq, hg]
  rw [mult_tmul]
  conv_lhs => rw [← hg c]
  simp only [← mul_assoc, mul_map_mul_map, h₁.eq, hg2]

end Mult

section Map

variable {A' C' : Type*} [Ring A'] [Algebra k A'] [Ring C'] [Algebra k C']
  {φ' : C' →ₙₐ[k] A'} (π : A →ₐ[k] A') (π₀ : C →ₐ[k] C')
  (hπ : ∀ c, π (φ c) = φ' (π₀ c))
include hπ

/-- The map `x ⊗ y ↦ π x ⊗ π₀ y` along homomorphisms compatible with `φ` and `φ'`. -/
def map : TensorAlong k A C φ e₂ e₁ e₀ →ₗ[k] TensorAlong k A' C' φ' (π e₂) (π₀ e₁) (π₀ e₀) :=
  (rel k A C φ e₂ e₁ e₀).liftQ
    ((mkQ k A' C' φ' (π e₂) (π₀ e₁) (π₀ e₀)).comp
      (TensorProduct.map π.toLinearMap π₀.toLinearMap)) <| by
    rw [rel, Submodule.span_le]
    rintro t (⟨x, y, rfl⟩ | ⟨x, c, y, rfl⟩) <;>
      simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, LinearMap.comp_apply,
        TensorProduct.map_tmul, AlgHom.toLinearMap_apply, map_mul, sub_eq_zero, hπ]
    · exact tmul_corner (k := k) (φ := φ') (π x) (π₀ y)
    · simpa only [map_mul, tmul_def] using
        tmul_balance (k := k) (φ := φ') (e₂ := π e₂) (e₁ := π₀ e₁) (e₀ := π₀ e₀)
          (π x) (π₀ c) (π₀ y)

theorem map_tmul (x : A) (y : C) :
    map π π₀ hπ (tmul x y : TensorAlong k A C φ e₂ e₁ e₀) = tmul (π x) (π₀ y) := by
  simp [map, tmul, tmulₗ, mkQ]

theorem map_surjective (hA : Function.Surjective π) (hC : Function.Surjective π₀) :
    Function.Surjective (map π π₀ hπ : TensorAlong k A C φ e₂ e₁ e₀ →ₗ[k] _) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← span_tmul, Submodule.span_le]
  rintro _ ⟨a, b, rfl⟩
  obtain ⟨x, rfl⟩ := hA a
  obtain ⟨y, rfl⟩ := hC b
  exact ⟨tmul x y, map_tmul π π₀ hπ x y⟩

variable (h₂ : IsIdempotentElem e₂) (h₁ : IsIdempotentElem e₁) (h₀ : IsIdempotentElem e₀)

theorem mult_map (t : TensorAlong k A C φ e₂ e₁ e₀) :
    mult (h₂.map π) (h₁.map π₀) (h₀.map π₀) (map π π₀ hπ t) = π (mult h₂ h₁ h₀ t) := by
  induction t using induction_on with
  | tmul x y => simp [map_tmul, mult_tmul, hπ]
  | add s t hs ht => rw [map_add, map_add, hs, ht, map_add, map_add]

/-- **Injectivity along quotients.** If multiplication over `A, C` is injective, `π` and `π₀`
are surjective, and every `e₂ z φ(e₀)` with `π z = 0` is a sum of products `e₂xφ(e₁ye₀)` with
`π x = 0` or `π₀ y = 0`, then multiplication over `A', C'` is injective. -/
theorem mult_injective_of_ker (hA : Function.Surjective π) (hC : Function.Surjective π₀)
    (hinj : Function.Injective (mult h₂ h₁ h₀ : TensorAlong k A C φ e₂ e₁ e₀ →ₗ[k] A))
    (hS : ∀ z, π z = 0 → e₂ * z * φ e₀ ∈ Submodule.span k
      {w | ∃ x y, (π x = 0 ∨ π₀ y = 0) ∧ w = e₂ * x * φ (e₁ * y * e₀)}) :
    Function.Injective (mult (h₂.map π) (h₁.map π₀) (h₀.map π₀) :
      TensorAlong k A' C' φ' (π e₂) (π₀ e₁) (π₀ e₀) →ₗ[k] A') := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  obtain ⟨t, rfl⟩ := map_surjective π π₀ hπ hA hC s
  rw [mult_map π π₀ hπ h₂ h₁ h₀] at hs
  have hle : Submodule.span k
      {w | ∃ x y, (π x = 0 ∨ π₀ y = 0) ∧ w = e₂ * x * φ (e₁ * y * e₀)} ≤
      (LinearMap.ker (map π π₀ hπ : TensorAlong k A C φ e₂ e₁ e₀ →ₗ[k] _)).map
        (mult h₂ h₁ h₀) := by
    rw [Submodule.span_le]
    rintro _ ⟨x, y, hxy, rfl⟩
    refine ⟨tmul x y, ?_, mult_tmul h₂ h₁ h₀ x y⟩
    rcases hxy with h | h <;> simp [map_tmul, h]
  have hmem := hle (hS _ hs)
  rw [mult_corner h₂ h₁ h₀] at hmem
  obtain ⟨t', ht', he⟩ := hmem
  rw [← hinj he]
  exact ht'

/-- **Surjectivity along quotients.** -/
theorem mult_surjective_of_surjective (hA : Function.Surjective π)
    (hsurj : ∀ z, ∃ t, mult h₂ h₁ h₀ (t : TensorAlong k A C φ e₂ e₁ e₀) = e₂ * z * φ e₀)
    (z : A') : ∃ t, mult (h₂.map π) (h₁.map π₀) (h₀.map π₀)
      (t : TensorAlong k A' C' φ' (π e₂) (π₀ e₁) (π₀ e₀)) = π e₂ * z * φ' (π₀ e₀) := by
  obtain ⟨x, rfl⟩ := hA z
  obtain ⟨t, ht⟩ := hsurj x
  exact ⟨map π π₀ hπ t, by rw [mult_map π π₀ hπ h₂ h₁ h₀, ht, ← hπ]; simp⟩

end Map

end TensorAlong

end

end Categorification
