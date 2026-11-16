/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.GalleryBasis.Twisted

/-!
# Supports of twisted operators

Bookkeeping for the Mackey filtration of B. Webster, *Weighted Khovanov–Lauda–Rouquier
algebras*, arXiv:1209.2463v4, §2.4 (proof of Theorem 2.19; the filtration is that of
Khovanov–Lauda, arXiv:0803.4121v2, Proposition 2.18).

An operator `Op` on the polynomial ring is *supported* in a set `S` of relabellings if, after
multiplication by a non-zero-divisor, it is a combination `f ↦ ∑ₓ a x · x(f)` with `a x = 0`
for `x ∉ S`. The relabellings occurring do not depend on the chosen denominator
(`IsSupported.coeff_eq_zero`). Supports add under sums and multiply under composition; the
Mackey filtration is the filtration by the supports of the operators of its elements in the
polynomial representation.

## Main definitions

* `IsSupported Op S`: `Op` is twisted with a non-zero-divisor denominator and coefficients
  vanishing off `S`.

## Main results

* `IsSupported.comp`: `Op₂ ∘ Op₁` is supported in `S₂ * S₁`.
* `IsSupported.coeff_eq_zero`: for every twisted presentation with a non-zero-divisor
  denominator, the coefficients vanish off the support.
-/

namespace Categorification.WeightedKLR

open MvPolynomial Pointwise

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ν : I →₀ ℕ}

attribute [local instance] ColPerm.fintype

/-- `Op` is supported in `S`: `M * Op f = ∑ₓ a x * x(f)` with `M` a non-zero-divisor and
`a x = 0` for `x ∉ S`. -/
def IsSupported (Op : PolyRing ν k →ₗ[k] PolyRing ν k) (S : Set (ColPerm ν)) : Prop :=
  ∃ (M : PolyRing ν k) (a : ColPerm ν → PolyRing ν k), IsRegular M ∧ IsTwisted Op M a ∧
    ∀ x, a x ≠ 0 → x ∈ S

namespace IsSupported

variable {Op Op₁ Op₂ : PolyRing ν k →ₗ[k] PolyRing ν k} {S S₁ S₂ : Set (ColPerm ν)}

omit [DecidableEq I] in
theorem mono (h : IsSupported Op S₁) (hS : S₁ ⊆ S₂) : IsSupported Op S₂ := by
  obtain ⟨M, a, hM, hT, ha⟩ := h
  exact ⟨M, a, hM, hT, fun x hx => hS (ha x hx)⟩

theorem id : IsSupported (LinearMap.id : PolyRing ν k →ₗ[k] PolyRing ν k) {1} :=
  ⟨1, _, isRegular_one, IsTwisted.id, fun x hx => by
    by_contra h
    exact hx (by simp only [Set.mem_singleton_iff] at h; simp [h])⟩

omit [DecidableEq I] in
theorem zero (S : Set (ColPerm ν)) : IsSupported (0 : PolyRing ν k →ₗ[k] PolyRing ν k) S :=
  ⟨1, 0, isRegular_one, fun f => by simp, fun x hx => absurd rfl hx⟩

omit [DecidableEq I] in
theorem add (h₁ : IsSupported Op₁ S₁) (h₂ : IsSupported Op₂ S₂) :
    IsSupported (Op₁ + Op₂) (S₁ ∪ S₂) := by
  obtain ⟨M₁, a₁, hM₁, hT₁, ha₁⟩ := h₁
  obtain ⟨M₂, a₂, hM₂, hT₂, ha₂⟩ := h₂
  refine ⟨M₁ * M₂, fun x => M₂ * a₁ x + M₁ * a₂ x, hM₁.mul hM₂, fun f => ?_, fun x hx => ?_⟩
  · have e₁ := hT₁ f
    have e₂ := hT₂ f
    simp only [LinearMap.add_apply, add_mul, Finset.sum_add_distrib, mul_assoc,
      ← Finset.mul_sum, ← e₁, ← e₂]
    ring
  · by_contra hS
    have h1 : a₁ x = 0 := by by_contra h; exact hS (Or.inl (ha₁ x h))
    have h2 : a₂ x = 0 := by by_contra h; exact hS (Or.inr (ha₂ x h))
    exact hx (by simp only [h1, h2, mul_zero, add_zero])

omit [DecidableEq I] in
theorem smul (h : IsSupported Op S) (c : k) : IsSupported (c • Op) S := by
  obtain ⟨M, a, hM, hT, ha⟩ := h
  refine ⟨M, fun x => c • a x, hM, fun f => ?_, fun x hx => ha x fun h0 => hx (by
    simp only [h0, smul_zero])⟩
  rw [LinearMap.smul_apply, mul_smul_comm, hT f, Finset.smul_sum]
  simp only [smul_mul_assoc]

omit [DecidableEq I] in
theorem sum {ι : Type*} (s : Finset ι) {Op : ι → PolyRing ν k →ₗ[k] PolyRing ν k}
    (h : ∀ i ∈ s, IsSupported (Op i) S) : IsSupported (∑ i ∈ s, Op i) S := by
  classical
  induction s using Finset.induction_on with
  | empty => exact zero S
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    have := (h i (Finset.mem_insert_self i s)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
    rwa [Set.union_self] at this

omit [DecidableEq I] in
theorem mulLeft (h : IsSupported Op S) (c : PolyRing ν k) :
    IsSupported (LinearMap.mulLeft k c ∘ₗ Op) S := by
  obtain ⟨M, a, hM, hT, ha⟩ := h
  exact ⟨M, _, hM, hT.mulLeft c, fun x hx => ha x fun h0 => hx (by simp only [h0, mul_zero])⟩

omit [DecidableEq I] in
theorem rename (h : IsSupported Op S) (g : ColPerm ν) :
    IsSupported ((MvPolynomial.rename ⇑g.1).toLinearMap ∘ₗ Op) (g • S) := by
  obtain ⟨M, a, hM, hT, ha⟩ := h
  refine ⟨_, _, isRegular_rename_colPerm hM g, hT.rename g, fun y hy => ?_⟩
  have : a (g⁻¹ * y) ≠ 0 := fun h0 => hy (by simp only [h0, map_zero])
  exact ⟨g⁻¹ * y, ha _ this, by simp⟩

omit [DecidableEq I] in
/-- Composing with an operator `T` with `c * T u = α * u + β * s(u)`, `c` a non-zero-divisor. -/
theorem step (h : IsSupported Op S) (s : ColPerm ν) {c α β : PolyRing ν k} (hc : IsRegular c)
    {T : PolyRing ν k →ₗ[k] PolyRing ν k}
    (hT : ∀ u, c * T u = α * u + β * MvPolynomial.rename ⇑s.1 u) :
    IsSupported (T ∘ₗ Op) (S ∪ s • S) := by
  obtain ⟨M, a, hM, hTw, ha⟩ := h
  refine ⟨_, _, (hc.mul hM).mul (isRegular_rename_colPerm hM s), hTw.step s hT,
    fun y hy => ?_⟩
  by_cases hay : a y = 0
  · have : a (s⁻¹ * y) ≠ 0 := fun h0 => hy (by simp only [hay, h0, map_zero, mul_zero,
      add_zero])
    exact Or.inr ⟨s⁻¹ * y, ha _ this, by simp⟩
  · exact Or.inl (ha y hay)

/-- **Composition.** If `Op₁` is supported in `S₁` and `Op₂` in `S₂`, then `Op₂ ∘ Op₁` is
supported in `S₂ * S₁`. -/
theorem comp (h₂ : IsSupported Op₂ S₂) (h₁ : IsSupported Op₁ S₁) :
    IsSupported (Op₂ ∘ₗ Op₁) (S₂ * S₁) := by
  classical
  obtain ⟨M₁, a₁, hM₁, hT₁, ha₁⟩ := h₁
  obtain ⟨M₂, a₂, hM₂, hT₂, ha₂⟩ := h₂
  set P : PolyRing ν k := ∏ y' : ColPerm ν, MvPolynomial.rename ⇑y'.1 M₁ with hP
  set N : ColPerm ν → PolyRing ν k := fun y =>
    ∏ y' ∈ Finset.univ.erase y, MvPolynomial.rename ⇑(y' : ColPerm ν).1 M₁
  have hN : ∀ y, N y * MvPolynomial.rename ⇑y.1 M₁ = P :=
    fun y => Finset.prod_erase_mul _ _ (Finset.mem_univ y)
  refine ⟨P * M₂,
    fun z => ∑ y, a₂ y * N y * MvPolynomial.rename ⇑y.1 (a₁ (y⁻¹ * z)),
    (hP ▸ IsRegular.prod fun y _ => isRegular_rename_colPerm hM₁ y).mul hM₂, fun f => ?_,
    fun z hz => ?_⟩
  · have key : ∀ y : ColPerm ν, P *
        MvPolynomial.rename ⇑y.1 (Op₁ f) =
        N y * ∑ z, MvPolynomial.rename ⇑y.1 (a₁ (y⁻¹ * z)) * MvPolynomial.rename ⇑z.1 f := by
      intro y
      rw [← hN y, mul_assoc, ← map_mul, hT₁ f, map_sum]
      congr 1
      refine Fintype.sum_equiv (Equiv.mulLeft y) _ _ fun x => ?_
      simp only [Equiv.coe_mulLeft, inv_mul_cancel_left, map_mul, rename_colPerm_mul]
    calc P * M₂ * (Op₂ ∘ₗ Op₁) f
        = ∑ y, a₂ y * (P *
            MvPolynomial.rename ⇑y.1 (Op₁ f)) := by
          rw [mul_assoc, LinearMap.comp_apply, hT₂ (Op₁ f), Finset.mul_sum]
          exact Finset.sum_congr rfl fun y _ => by ring
      _ = ∑ z, (∑ y, a₂ y * N y * MvPolynomial.rename ⇑y.1 (a₁ (y⁻¹ * z))) *
            MvPolynomial.rename ⇑z.1 f := by
          simp only [key, Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => by ring
  · by_contra hS
    refine hz (Finset.sum_eq_zero fun y _ => ?_)
    by_cases h2 : a₂ y = 0
    · rw [h2, zero_mul, zero_mul]
    · have h1 : a₁ (y⁻¹ * z) = 0 := by
        by_contra h1
        exact hS ⟨y, ha₂ y h2, y⁻¹ * z, ha₁ _ h1, by simp⟩
      rw [h1, map_zero, mul_zero]

/-- The relabellings occurring in a twisted presentation of a supported operator lie in the
support, whatever the non-zero-divisor denominator. -/
theorem coeff_eq_zero (h : IsSupported Op S) {M' : PolyRing ν k} {a' : ColPerm ν → PolyRing ν k}
    (hT' : IsTwisted Op M' a') {x : ColPerm ν} (hx : x ∉ S) : a' x = 0 := by
  obtain ⟨M, a, hM, hT, ha⟩ := h
  have key := eq_zero_of_forall_sum_mul_rename (a := fun y => M * a' y - M' * a y) fun f => by
    simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, ← hT f, ← hT' f]
    ring
  have hax : a x = 0 := by
    by_contra h0
    exact hx (ha x h0)
  have := congrFun key x
  simp only [hax, mul_zero, sub_zero, Pi.zero_apply] at this
  exact hM.left.mul_left_eq_zero_iff.1 this

end IsSupported

end Categorification.WeightedKLR
