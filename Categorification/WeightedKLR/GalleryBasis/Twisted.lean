/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.GalleryRep

/-!
# Twisted operators on the polynomial ring

Linear-independence half of B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*,
arXiv:1209.2463v4, Theorem 2.8: the leading-term argument in the polynomial representation.

The operators of galleries in the polynomial representation become, after multiplication by a
non-zero-divisor `M`, combinations `f ↦ ∑ₓ a x · x(f)` of the relabellings `x` of the strands,
with polynomial coefficients. Such an operator is *twisted* (`IsTwisted`). This file proves that
twisted operators are stable under the operators of steps, and the two facts behind the
leading-term argument:

* relabellings are linearly independent over the polynomial ring (Dedekind's lemma,
  `eq_zero_of_forall_sum_mul_rename`);
* a family of twisted operators with triangular leading coefficients is linearly independent
  over the polynomial ring (`eq_zero_of_forall_sum_twisted_eq_zero`).

## Main definitions

* `ColPerm.fintype`: the finite type structure of the colour-preserving permutations.
* `IsTwisted Op M a`: `M * Op f = ∑ₓ a x * x(f)` for all `f`.
-/

namespace Categorification.WeightedKLR

open MvPolynomial Equiv

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ν : I →₀ ℕ}

/-- The colour-preserving permutations of the strands form a finite type. -/
@[instance_reducible] noncomputable def ColPerm.fintype : Fintype (ColPerm ν) := Fintype.ofFinite _

attribute [local instance] ColPerm.fintype

omit [DecidableEq I] in
theorem rename_colPerm_mul (g h : ColPerm ν) (f : PolyRing ν k) :
    rename ⇑(g * h).1 f = rename ⇑g.1 (rename ⇑h.1 f) := by
  rw [rename_rename]
  rfl

omit [DecidableEq I] in
theorem rename_colPerm_one (f : PolyRing ν k) : rename ⇑(1 : ColPerm ν).1 f = f :=
  rename_id_apply f

omit [DecidableEq I] in
theorem rename_colPerm_injective (g : ColPerm ν) :
    Function.Injective (rename (R := k) ⇑g.1) :=
  rename_injective _ g.1.injective

omit [DecidableEq I] in
/-- Relabelling the variables preserves non-zero-divisors. -/
theorem IsRegular.rename_colPerm {a : PolyRing ν k} (ha : IsRegular a) (g : ColPerm ν) :
    IsRegular (rename ⇑g.1 a) := by
  suffices IsLeftRegular (rename ⇑g.1 a) from ⟨this, this.right_of_commute <| Commute.all _⟩
  intro p q (hpq : rename ⇑g.1 a * p = rename ⇑g.1 a * q)
  have hinv : ∀ u : PolyRing ν k, rename ⇑g.1 (rename ⇑g⁻¹.1 u) = u := fun u => by
    rw [← rename_colPerm_mul, mul_inv_cancel, rename_colPerm_one]
  have h : rename ⇑g.1 (a * rename ⇑g⁻¹.1 p) = rename ⇑g.1 (a * rename ⇑g⁻¹.1 q) := by
    rw [map_mul, map_mul, hinv, hinv, hpq]
  have h' := ha.left (rename_colPerm_injective g h)
  rw [← hinv p, ← hinv q, h']

/-- `Op` is twisted with denominator `M` and coefficients `a`: `M * Op f = ∑ₓ a x * x(f)`. -/
def IsTwisted (Op : PolyRing ν k →ₗ[k] PolyRing ν k) (M : PolyRing ν k)
    (a : ColPerm ν → PolyRing ν k) : Prop :=
  ∀ f, M * Op f = ∑ x, a x * rename ⇑x.1 f

namespace IsTwisted

variable {Op : PolyRing ν k →ₗ[k] PolyRing ν k} {M : PolyRing ν k} {a : ColPerm ν → PolyRing ν k}

theorem id : IsTwisted (LinearMap.id : PolyRing ν k →ₗ[k] PolyRing ν k) 1
    (fun x => if x = 1 then 1 else 0) := by
  intro f
  simp only [LinearMap.id_apply, one_mul, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, rename_colPerm_one]

omit [DecidableEq I] in
/-- Composing with a multiplication operator. -/
theorem mulLeft (h : IsTwisted Op M a) (c : PolyRing ν k) :
    IsTwisted (LinearMap.mulLeft k c ∘ₗ Op) M (fun x => c * a x) := by
  intro f
  rw [LinearMap.comp_apply, LinearMap.mulLeft_apply, mul_left_comm, h f, Finset.mul_sum]
  simp only [mul_assoc]

omit [DecidableEq I] in
/-- Composing with a relabelling. -/
theorem rename (h : IsTwisted Op M a) (g : ColPerm ν) :
    IsTwisted ((MvPolynomial.rename ⇑g.1).toLinearMap ∘ₗ Op) (MvPolynomial.rename ⇑g.1 M)
      (fun y => MvPolynomial.rename ⇑g.1 (a (g⁻¹ * y))) := by
  intro f
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, ← map_mul, h f, map_sum]
  symm
  rw [← Equiv.sum_comp (Equiv.mulLeft g)]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Equiv.coe_mulLeft, inv_mul_cancel_left, map_mul, rename_colPerm_mul]

omit [DecidableEq I] in
/-- Composing with an operator `T` with `c * T u = α * u + β * s(u)`. -/
theorem step (h : IsTwisted Op M a) (s : ColPerm ν) {c α β : PolyRing ν k}
    {T : PolyRing ν k →ₗ[k] PolyRing ν k}
    (hT : ∀ u, c * T u = α * u + β * MvPolynomial.rename ⇑s.1 u) :
    IsTwisted (T ∘ₗ Op) (c * M * MvPolynomial.rename ⇑s.1 M)
      (fun y => α * MvPolynomial.rename ⇑s.1 M * a y +
        β * M * MvPolynomial.rename ⇑s.1 (a (s⁻¹ * y))) := by
  intro f
  have h1 : ∑ y, a y * MvPolynomial.rename ⇑y.1 f = M * Op f := (h f).symm
  have h2 : ∑ y, MvPolynomial.rename ⇑s.1 (a (s⁻¹ * y)) * MvPolynomial.rename ⇑y.1 f =
      MvPolynomial.rename ⇑s.1 M * MvPolynomial.rename ⇑s.1 (Op f) := by
    rw [← map_mul, h f, map_sum, ← Equiv.sum_comp (Equiv.mulLeft s)]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Equiv.coe_mulLeft, inv_mul_cancel_left, map_mul, rename_colPerm_mul]
  simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  rw [h1, h2, LinearMap.comp_apply]
  linear_combination (M * MvPolynomial.rename ⇑s.1 M) * hT (Op f)

end IsTwisted

/-- **Dedekind's lemma** for relabellings: if `∑ₓ a x * x(f) = 0` for every polynomial `f`, then
all the coefficients `a x` vanish. -/
theorem eq_zero_of_forall_sum_mul_rename {a : ColPerm ν → PolyRing ν k}
    (h : ∀ f, ∑ x, a x * rename ⇑x.1 f = 0) : a = 0 := by
  classical
  suffices H : ∀ S : Finset (ColPerm ν), ∀ a : ColPerm ν → PolyRing ν k, (∀ x ∉ S, a x = 0) →
      (∀ f, ∑ x, a x * rename ⇑x.1 f = 0) → a = 0 from
    H Finset.univ a (fun x hx => absurd (Finset.mem_univ x) hx) h
  intro S
  induction S using Finset.induction_on with
  | empty => exact fun a ha _ => funext fun x => ha x (Finset.notMem_empty x)
  | insert x₀ S hx₀ ih =>
    intro a ha h
    have hS : ∀ y ∈ S, a y = 0 := by
      intro y hy
      have hne : y ≠ x₀ := fun e => hx₀ (e ▸ hy)
      obtain ⟨t, ht⟩ : ∃ t, y.1 t ≠ x₀.1 t := by
        by_contra hc
        push Not at hc
        exact hne (Subtype.ext (Equiv.ext hc))
      have hb := ih (fun x => a x * (X (x.1 t) - X (x₀.1 t))) (fun x hx => ?_) (fun f => ?_)
      · have := congrFun hb y
        simpa only [Pi.zero_apply, (isRegular_X_sub_X (k := k) ht).right.mul_right_eq_zero_iff]
          using this
      · by_cases e : x = x₀
        · simp only [e, sub_self, mul_zero]
        · rw [ha x (by simp [e, hx]), zero_mul]
      · have h1 := h (X t * f)
        have h2 := h f
        have e : ∑ x, a x * (X (x.1 t) - X (x₀.1 t)) * rename ⇑x.1 f =
            ∑ x, a x * rename ⇑x.1 (X t * f) - X (x₀.1 t) * ∑ x, a x * rename ⇑x.1 f := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [map_mul, rename_X]
          ring
        rw [e, h1, h2, mul_zero, sub_zero]
    have h0 := h 1
    simp only [map_one, mul_one] at h0
    rw [Finset.sum_eq_single x₀ (fun y _ hy => by
      by_cases hyS : y ∈ S
      · exact hS y hyS
      · exact ha y (by simp [hy, hyS])) (fun hx => absurd (Finset.mem_univ x₀) hx)] at h0
    funext x
    by_cases e : x = x₀
    · rw [e]; exact h0
    · by_cases hxS : x ∈ S
      · exact hS x hxS
      · exact ha x (by simp [e, hxS])

/-- **Triangularity.** Let `Y g` be twisted operators with denominators `M g` and coefficients
`a g`, such that the coefficient `a g g` is a non-zero-divisor and `a g x ≠ 0` for `x ≠ g` only
if `Λ x < Λ g`. If `∑_g Y g (F g * f) = 0` for every polynomial `f`, then `F = 0`. -/
theorem eq_zero_of_forall_sum_twisted_eq_zero {Y : ColPerm ν → PolyRing ν k →ₗ[k] PolyRing ν k}
    {M : ColPerm ν → PolyRing ν k} {a : ColPerm ν → ColPerm ν → PolyRing ν k}
    (Λ : ColPerm ν → ℕ) (hM : ∀ g, IsRegular (M g)) (hY : ∀ g, IsTwisted (Y g) (M g) (a g))
    (ha : ∀ g, IsRegular (a g g)) (hlt : ∀ g x, a g x ≠ 0 → x ≠ g → Λ x < Λ g)
    {F : ColPerm ν → PolyRing ν k} (hF : ∀ f, ∑ g, Y g (F g * f) = 0) : F = 0 := by
  classical
  by_contra hne
  set S := Finset.univ.filter fun g => F g ≠ 0
  have hSne : S.Nonempty := by
    by_contra hc
    refine hne (funext fun g => ?_)
    by_contra hg
    exact hc ⟨g, Finset.mem_filter.2 ⟨Finset.mem_univ _, hg⟩⟩
  obtain ⟨g₀, hg₀, hmax⟩ := S.exists_max_image Λ hSne
  set N : ColPerm ν → PolyRing ν k := fun g => ∏ h ∈ Finset.univ.erase g, M h
  have hN : ∀ g, IsRegular (N g) := fun g => IsRegular.prod fun h _ => hM h
  have key : ∀ f, ∑ x, (∑ g, N g * a g x * rename ⇑x.1 (F g)) * rename ⇑x.1 f = 0 := by
    intro f
    have := congrArg ((∏ h, M h) * ·) (hF f)
    simp only [mul_zero, Finset.mul_sum] at this
    rw [← this]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ g), mul_assoc, hY g, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_mul]
    ring
  have hcoef := congrFun (eq_zero_of_forall_sum_mul_rename key) g₀
  simp only [Pi.zero_apply] at hcoef
  rw [Finset.sum_eq_single g₀ (fun g _ hg => ?_) (fun hx => absurd (Finset.mem_univ g₀) hx)]
    at hcoef
  · have hF₀ : rename ⇑g₀.1 (F g₀) = 0 :=
      ((hN g₀).mul (ha g₀)).left.mul_left_eq_zero_iff.1 hcoef
    rw [← map_zero (rename (R := k) ⇑g₀.1)] at hF₀
    exact (Finset.mem_filter.1 hg₀).2 (rename_colPerm_injective g₀ hF₀)
  · by_cases hFg : F g = 0
    · rw [hFg, map_zero, mul_zero]
    · have hle := hmax g (by simp [S, hFg])
      have hag : a g g₀ = 0 := by
        by_contra hag
        exact absurd (hlt g g₀ hag (Ne.symm hg)) (not_lt.2 hle)
      rw [hag, mul_zero, zero_mul]

end Categorification.WeightedKLR
