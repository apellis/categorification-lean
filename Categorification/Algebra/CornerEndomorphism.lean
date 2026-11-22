/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Idempotents
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.Opposite
import Mathlib.LinearAlgebra.Span.Defs

set_option backward.isDefEq.respectTransparency false

/-!
# An algebra as the endomorphism algebra of right ideals of a corner

Let `A` be a ring with an idempotent `e` and corner ring `B = e A e`. The right ideal `A e` is a
right `B`-module, and `A` acts on it by left multiplication. Suppose that

* `A` acts faithfully on `A e`, and every `B`-linear endomorphism of `A e` is left
  multiplication by an element of `A` (the double centralizer property);
* there is a complete family of orthogonal idempotents `e_s` and elements `θ_s ∈ e_s A e`,
  `θ̇_s ∈ e A e_s` such that `e_s A e = θ_s B` and left multiplication by `θ̇_s` is injective on
  `e_s A`.

Then `A ≅ End_B(⊕_s y_s B)` with `y_s = θ̇_s θ_s ∈ B`. This is the algebraic part of
B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
Proposition 5.30; the hypotheses are verified there for the tensor product algebra `T^λ`.

## Main results

* `CornerEndomorphism.rightIdeal`: the right ideal `A e`, a right `B`-module.
* `CornerEndomorphism.ringEquiv`: `A ≃+* End_B(⊕_s y_s B)`.
-/

namespace Categorification.CornerEndomorphism

open MulOpposite

variable {A : Type*} [Ring A] {e : A}

/-- The right ideal `A e = {x | x e = x}` of an idempotent. -/
def rightIdeal (e : A) : AddSubgroup A where
  carrier := {x | x * e = x}
  add_mem' {x y} hx hy := by simp only [Set.mem_ofPred_eq] at *; rw [add_mul, hx, hy]
  zero_mem' := zero_mul e
  neg_mem' {x} hx := by simp only [Set.mem_ofPred_eq] at *; rw [neg_mul, hx]

theorem mem_rightIdeal {x : A} : x ∈ rightIdeal e ↔ x * e = x := Iff.rfl

theorem corner_mul_right (he : IsIdempotentElem e) (b : he.Corner) : b.1 * e = b.1 :=
  ((Subsemigroup.mem_corner_iff he).1 b.2).2

theorem corner_mul_left (he : IsIdempotentElem e) (b : he.Corner) : e * b.1 = b.1 :=
  ((Subsemigroup.mem_corner_iff he).1 b.2).1

/-- The right action of the corner `B = e A e` on `A e`. -/
instance instModule (he : IsIdempotentElem e) : Module he.Cornerᵐᵒᵖ (rightIdeal e) where
  smul b x := ⟨x.1 * b.unop.1, by
    rw [mem_rightIdeal, mul_assoc, corner_mul_right he]⟩
  one_smul x := Subtype.ext x.2
  mul_smul b c x := Subtype.ext (show x.1 * (c.unop.1 * b.unop.1) = x.1 * c.unop.1 * b.unop.1
    from (mul_assoc _ _ _).symm)
  smul_zero b := Subtype.ext (zero_mul _)
  smul_add b x y := Subtype.ext (add_mul _ _ _)
  add_smul b c x := Subtype.ext (mul_add _ _ _)
  zero_smul x := Subtype.ext (mul_zero _)

theorem coe_smul (he : IsIdempotentElem e) (b : he.Cornerᵐᵒᵖ) (x : rightIdeal e) :
    ((b • x : rightIdeal e) : A) = x.1 * b.unop.1 := rfl

/-- Left multiplication by elements of `A` on `A e`, as a ring homomorphism into the
`B`-linear endomorphisms. -/
def leftMul (he : IsIdempotentElem e) : A →+* Module.End he.Cornerᵐᵒᵖ (rightIdeal e) where
  toFun a :=
    { toFun x := ⟨a * x.1, by rw [mem_rightIdeal, mul_assoc, x.2]⟩
      map_add' x y := Subtype.ext (mul_add _ _ _)
      map_smul' b x := Subtype.ext (mul_assoc _ _ _).symm }
  map_one' := LinearMap.ext fun x => Subtype.ext (one_mul _)
  map_mul' a b := LinearMap.ext fun x => Subtype.ext (mul_assoc _ _ _)
  map_zero' := LinearMap.ext fun x => Subtype.ext (zero_mul _)
  map_add' a b := LinearMap.ext fun x => Subtype.ext (add_mul _ _ _)

theorem coe_leftMul_apply (he : IsIdempotentElem e) (a : A) (x : rightIdeal e) :
    ((leftMul he a x : rightIdeal e) : A) = a * x.1 := rfl

/-- If `A` acts faithfully on `A e` and every `B`-linear endomorphism of `A e` is left
multiplication (the double centralizer property), then `A ≅ End_B(A e)`. -/
theorem leftMul_bijective (he : IsIdempotentElem e)
    (hfaith : ∀ z : A, (∀ c, c * e = c → z * c = 0) → z = 0)
    (hcor : ∀ f : A →+ A, (∀ x, f x = f (x * e)) → (∀ x, x * e = x → f x * e = f x) →
      (∀ b x, x * e = x → f (x * (e * b * e)) = f x * (e * b * e)) →
      ∃ a, ∀ x, x * e = x → f x = a * x) :
    Function.Bijective (leftMul he) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun a ha => hfaith a fun c hc => ?_, fun g => ?_⟩
  · simpa [coe_leftMul_apply] using congrArg Subtype.val (LinearMap.congr_fun ha ⟨c, hc⟩)
  · let p : A →+ rightIdeal e :=
      { toFun x := ⟨x * e, by rw [mem_rightIdeal, mul_assoc, he.eq]⟩
        map_zero' := Subtype.ext (zero_mul _)
        map_add' x y := Subtype.ext (add_mul _ _ _) }
    let f : A →+ A := (AddSubgroup.subtype _).comp (g.toAddMonoidHom.comp p)
    have hp : ∀ x (hx : x * e = x), p x = ⟨x, hx⟩ := fun x hx => Subtype.ext hx
    obtain ⟨a, ha⟩ := hcor f (fun x => by
        show (g (p x)).1 = (g (p (x * e))).1
        rw [hp (x * e) (by rw [mul_assoc, he.eq])]; rfl)
      (fun x _ => (g (p x)).2) (fun b x hx => by
        show (g (p _)).1 = (g (p x)).1 * _
        have hb : (e * b * e) * e = e * b * e := by rw [mul_assoc, he.eq]
        have : p (x * (e * b * e)) =
            (op (α := he.Corner) ⟨e * b * e, b, rfl⟩) • p x := by
          apply Subtype.ext
          rw [coe_smul]
          show x * (e * b * e) * e = x * e * (e * b * e)
          rw [hx, mul_assoc, hb]
        rw [this, map_smul, coe_smul]
        rfl)
    refine ⟨a, LinearMap.ext fun x => Subtype.ext ?_⟩
    rw [coe_leftMul_apply, ← ha x.1 x.2]
    show (g (p x.1)).1 = (g x).1
    rw [hp x.1 x.2]

section Shuffle

variable (he : IsIdempotentElem e) {σ : Type*} [Fintype σ] {es : σ → A}
  (hes : CompleteOrthogonalIdempotents es) (θ θd : σ → A)
  (hθr : ∀ s, θ s * e = θ s) (hθdl : ∀ s, e * θd s = θd s)
  (hθl : ∀ s, es s * θ s = θ s)

omit [Fintype σ] in
include he hθdl in
theorem mem_corner_mul (s : σ) (x : A) (hx : x * e = x) :
    θd s * es s * x ∈ Subsemigroup.corner e := by
  rw [Subsemigroup.mem_corner_iff he]
  exact ⟨by rw [← mul_assoc, ← mul_assoc, hθdl], by rw [mul_assoc, hx]⟩

/-- The element `y_s = θ̇_s θ_s` of the corner. -/
def yElem (s : σ) : he.Corner :=
  ⟨θd s * θ s, (Subsemigroup.mem_corner_iff he).2
    ⟨by rw [← mul_assoc, hθdl], by rw [mul_assoc, hθr]⟩⟩

/-- The right `B`-module `⊕_s y_s B`. -/
abbrev Target : Type _ :=
  Π s : σ, ↥(Submodule.span he.Cornerᵐᵒᵖ {yElem he θ θd hθr hθdl s})

include hes in
/-- `x ↦ (θ̇_s e_s x)_s`, as a `B`-linear map `A e → ⊕_s y_s B`, given that
`e_s A e = θ_s B`. -/
def toTarget (hfac : ∀ s x, es s * x = x → x * e = x → ∃ y, x = θ s * (e * y * e)) :
    rightIdeal e →ₗ[he.Cornerᵐᵒᵖ] Target he θ θd hθr hθdl where
  toFun x s := ⟨⟨θd s * es s * x.1, mem_corner_mul he θd hθdl s x.1 x.2⟩, by
    obtain ⟨y, hy⟩ := hfac s (es s * x.1) (by rw [← mul_assoc, (hes.idem s).eq])
      (by rw [mul_assoc, x.2])
    refine Submodule.mem_span_singleton.2 ⟨op ⟨e * y * e, y, rfl⟩, Subtype.ext ?_⟩
    show θd s * θ s * (e * y * e) = θd s * es s * x.1
    rw [mul_assoc (θd s) (es s), hy, mul_assoc]⟩
  map_add' x y := funext fun s => Subtype.ext (Subtype.ext (mul_add _ _ _))
  map_smul' b x := funext fun s => Subtype.ext (Subtype.ext (mul_assoc _ _ _).symm)

include hes in
theorem coe_toTarget_apply (hfac : ∀ s x, es s * x = x → x * e = x → ∃ y, x = θ s * (e * y * e))
    (x : rightIdeal e) (s : σ) :
    (toTarget he hes θ θd hθr hθdl hfac x s).1.1 = θd s * es s * x.1 := rfl

include hes hθl in
theorem toTarget_bijective
    (hfac : ∀ s x, es s * x = x → x * e = x → ∃ y, x = θ s * (e * y * e))
    (hinj : ∀ s x, es s * x = x → θd s * x = 0 → x = 0) :
    Function.Bijective (toTarget he hes θ θd hθr hθdl hfac) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => Subtype.ext ?_, fun m => ?_⟩
  · have h0 : ∀ s, es s * x.1 = 0 := fun s => hinj s _
      (by rw [← mul_assoc, (hes.idem s).eq])
      (by
        have := congrArg (fun m => (m s).1.1) hx
        simp only [coe_toTarget_apply, mul_assoc] at this
        exact this)
    show x.1 = 0
    rw [← one_mul x.1, ← hes.complete, Finset.sum_mul]
    exact Finset.sum_eq_zero fun s _ => h0 s
  · choose b hb using fun s => Submodule.mem_span_singleton.1 (m s).2
    have hmem : (∑ r, θ r * (b r).unop.1) * e = ∑ r, θ r * (b r).unop.1 := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun r _ => by rw [mul_assoc, corner_mul_right he]
    refine ⟨⟨_, hmem⟩, funext fun s => Subtype.ext (Subtype.ext ?_)⟩
    rw [coe_toTarget_apply]
    have hsum : es s * ∑ r, θ r * (b r).unop.1 = θ s * (b s).unop.1 := by
      rw [Finset.mul_sum, Finset.sum_eq_single s]
      · rw [← mul_assoc, hθl]
      · intro r _ hr
        rw [← mul_assoc, ← hθl r, ← mul_assoc, hes.ortho (Ne.symm hr), zero_mul, zero_mul]
      · intro h; exact absurd (Finset.mem_univ s) h
    show θd s * es s * ∑ r, θ r * (b r).unop.1 = _
    rw [mul_assoc, hsum, ← hb s, ← mul_assoc]
    rfl

include hes hθl in
/-- **Abstract form of Webster, arXiv:1309.3796v2, Proposition 5.30**: under the double
centralizer property for `A e` and the factorizations `e_s A e = θ_s B` with `θ̇_s` injective on
`e_s A`, `A` is the algebra of `B`-linear endomorphisms of `⊕_s y_s B`, `y_s = θ̇_s θ_s`. -/
noncomputable def ringEquiv
    (hfac : ∀ s x, es s * x = x → x * e = x → ∃ y, x = θ s * (e * y * e))
    (hinj : ∀ s x, es s * x = x → θd s * x = 0 → x = 0)
    (hfaith : ∀ z : A, (∀ c, c * e = c → z * c = 0) → z = 0)
    (hcor : ∀ f : A →+ A, (∀ x, f x = f (x * e)) → (∀ x, x * e = x → f x * e = f x) →
      (∀ b x, x * e = x → f (x * (e * b * e)) = f x * (e * b * e)) →
      ∃ a, ∀ x, x * e = x → f x = a * x) :
    A ≃+* Module.End he.Cornerᵐᵒᵖ (Target he θ θd hθr hθdl) :=
  (RingEquiv.ofBijective (leftMul he) (leftMul_bijective he hfaith hcor)).trans
    (LinearEquiv.conjRingEquiv
      (LinearEquiv.ofBijective _ (toTarget_bijective he hes θ θd hθr hθdl hθl hfac hinj)))

include hes hθl in
theorem ringEquiv_apply
    (hfac : ∀ s x, es s * x = x → x * e = x → ∃ y, x = θ s * (e * y * e))
    (hinj : ∀ s x, es s * x = x → θd s * x = 0 → x = 0)
    (hfaith : ∀ z : A, (∀ c, c * e = c → z * c = 0) → z = 0)
    (hcor : ∀ f : A →+ A, (∀ x, f x = f (x * e)) → (∀ x, x * e = x → f x * e = f x) →
      (∀ b x, x * e = x → f (x * (e * b * e)) = f x * (e * b * e)) →
      ∃ a, ∀ x, x * e = x → f x = a * x)
    (a : A) (x : rightIdeal e) :
    ringEquiv he hes θ θd hθr hθdl hθl hfac hinj hfaith hcor a
        (toTarget he hes θ θd hθr hθdl hfac x) =
      toTarget he hes θ θd hθr hθdl hfac (leftMul he a x) := by
  simp [ringEquiv]

end Shuffle

end Categorification.CornerEndomorphism
