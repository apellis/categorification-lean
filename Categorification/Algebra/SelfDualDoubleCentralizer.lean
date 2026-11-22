/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.SelfDualInjective

set_option backward.isDefEq.respectTransparency false

/-!
# Double centralizers of self-dual projectives

Background for B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v2, Corollary 5.29: the double centralizer property of the self-dual projective
`P⁰ = T^λ e⁰`. Webster deduces it from V. Mazorchuk, C. Stroppel, *Projective-injective modules,
Serre functors and symmetric algebras*, J. Reine Angew. Math. 616 (2008), Corollary 2.6. Here we
prove the module-theoretic step that does not depend on the stratification.

Let `A` be a finite-dimensional `k`-algebra, `e ∈ A` idempotent and `τ : A → k` a functional
pairing `e A` and `A e` perfectly (as in `Module.Baer.lIdeal_of_pairing`). Suppose the left
module `A` has a copresentation `0 → A → (A e)ⁿ → C` whose cokernel `C` has no nonzero submodule
killed by `e`: concretely, elements `c₁, …, cₙ ∈ A e` such that `z ↦ (z cⱼ)ⱼ` is injective, and
such that `y ∈ (A e)ⁿ` lies in the image of `A` as soon as `e A y` does. Then every `eAe`-linear
endomorphism of `e A` is right multiplication by an element of `A`
(`exists_eq_mul_right_of_copresentation`), and, given an anti-involution fixing `e`, every
`eAe`-linear endomorphism of `A e` is left multiplication by an element of `A`
(`exists_eq_mul_left_of_copresentation`).

The proof: for `g : e A → e A`, the functional `a ↦ τ(g(a) cⱼ)` on `e A` is `τ(· yⱼ)` for some
`yⱼ ∈ A e`. Then `x yⱼ = g(x) cⱼ` for `x ∈ e A`, so `e a y = (g(e a) cⱼ)ⱼ` lies in the image of
`A`, hence `y = (t cⱼ)ⱼ` for some `t`, and `g(x) = x t` by injectivity.
-/

noncomputable section

namespace Categorification

open _root_.Module

variable {k A : Type*} [Field k] [Ring A] [Algebra k A] {τ : A →ₗ[k] k} {e : A}

/-- Every functional on `e A` is `τ(· b)` for some `b ∈ A e`. -/
theorem exists_rightCorner_rep [FiniteDimensional k A]
    (hnd : ∀ a, e * a = a → a ≠ 0 → ∃ b, b * e = b ∧ τ (a * b) ≠ 0)
    (hdim : finrank k (leftCorner (k := k) e) = finrank k (rightCorner (k := k) e))
    (l : leftCorner (k := k) e →ₗ[k] k) :
    ∃ b, b * e = b ∧ ∀ a (ha : e * a = a), τ (a * b) = l ⟨a, ha⟩ := by
  obtain ⟨⟨b, hb⟩, hrep⟩ := (bijective_cornerPairing_dual hnd hdim).2 l
  refine ⟨b, hb, fun a ha => ?_⟩
  have := LinearMap.congr_fun hrep ⟨a, ha⟩
  rw [cornerPairing_dual_apply] at this
  exact this

/-- An element of `A e` pairing to zero with `e A` is zero. -/
theorem eq_zero_of_rightCorner_pairing [FiniteDimensional k A]
    (hnd : ∀ a, e * a = a → a ≠ 0 → ∃ b, b * e = b ∧ τ (a * b) ≠ 0)
    (hdim : finrank k (leftCorner (k := k) e) = finrank k (rightCorner (k := k) e))
    {c : A} (hc : c * e = c) (h : ∀ a, e * a = a → τ (a * c) = 0) : c = 0 := by
  have hbij := bijective_cornerPairing_dual hnd hdim
  have : ((cornerPairing τ e).dualMap ∘ₗ (evalEquiv k (rightCorner (k := k) e)).toLinearMap)
      ⟨c, hc⟩ = 0 := by
    ext a; exact h a.1 a.2
  exact congrArg Subtype.val (hbij.1 (this.trans (map_zero _).symm))

/-- `A` has a copresentation `0 → A → (A e)ⁿ → C` whose cokernel `C` has no nonzero submodule
killed by `e`. Concretely: elements `c₁, …, cₙ ∈ A e` such that `z ↦ (z cⱼ)ⱼ` is injective, and
such that `y ∈ (A e)ⁿ` lies in the image `{(t cⱼ)ⱼ}` of `A` whenever `e a y` does for every
`a ∈ A`. (For `A e` injective this says that `A` has dominant dimension at least two with
respect to `A e`.) -/
def HasCornerCopresentation (e : A) : Prop :=
  ∃ (n : ℕ) (c : Fin n → A), (∀ j, c j * e = c j) ∧ (∀ z, (∀ j, z * c j = 0) → z = 0) ∧
    ∀ y : Fin n → A, (∀ j, y j * e = y j) →
      (∀ a, ∃ t, ∀ j, e * a * y j = t * c j) → ∃ t, ∀ j, y j = t * c j

/-- **Double centralizer, right-module form.** Under a copresentation of `A` by copies of `A e`
whose cokernel has no nonzero submodule killed by `e`, every `eAe`-linear endomorphism `g` of
`e A` is right multiplication by an element of `A`. -/
theorem exists_eq_mul_right_of_copresentation [FiniteDimensional k A]
    (hnd : ∀ a, e * a = a → a ≠ 0 → ∃ b, b * e = b ∧ τ (a * b) ≠ 0)
    (hdim : finrank k (leftCorner (k := k) e) = finrank k (rightCorner (k := k) e))
    (he : e * e = e) {n : ℕ} (c : Fin n → A) (hc : ∀ j, c j * e = c j)
    (hinj : ∀ z, (∀ j, z * c j = 0) → z = 0)
    (hcok : ∀ y : Fin n → A, (∀ j, y j * e = y j) →
      (∀ a, ∃ t, ∀ j, e * a * y j = t * c j) → ∃ t, ∀ j, y j = t * c j)
    (g : A →ₗ[k] A) (hge : ∀ x, e * x = x → e * g x = g x)
    (hgb : ∀ b x, e * x = x → g (e * b * e * x) = e * b * e * g x) :
    ∃ t, ∀ x, e * x = x → g x = x * t := by
  have hrep : ∀ j, ∃ y, y * e = y ∧ ∀ a (ha : e * a = a),
      τ (a * y) = (τ ∘ₗ LinearMap.mulRight k (c j) ∘ₗ g ∘ₗ (leftCorner (k := k) e).subtype)
        ⟨a, ha⟩ :=
    fun j => exists_rightCorner_rep hnd hdim _
  choose y hy hyrep using hrep
  have hxy : ∀ j x, e * x = x → x * y j = g x * c j := by
    intro j x hx
    rw [← sub_eq_zero]
    refine eq_zero_of_rightCorner_pairing hnd hdim
      (by rw [sub_mul, mul_assoc, hy, mul_assoc, hc]) fun a ha => ?_
    have hax : e * (a * x) = a * x := by rw [← mul_assoc, ha]
    have hg : g (a * x) = a * g x := by
      have := hgb a x hx
      rw [ha, mul_assoc, hx] at this
      rwa [mul_assoc, hge x hx] at this
    have h1 := hyrep j (a * x) hax
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
      LinearMap.mulRight_apply] at h1
    rw [mul_sub, map_sub, ← mul_assoc, h1, hg, mul_assoc, sub_self]
  obtain ⟨t, ht⟩ := hcok y hy fun a =>
    ⟨g (e * a), fun j => by rw [← hxy j (e * a) (by rw [← mul_assoc, he])]⟩
  refine ⟨t, fun x hx => ?_⟩
  rw [← sub_eq_zero]
  refine hinj _ fun j => ?_
  rw [sub_mul, mul_assoc, ← ht j, ← hxy j x hx, sub_self]

/-- **Double centralizer, left-module form.** Under the hypotheses of
`exists_eq_mul_right_of_copresentation` and an anti-involution `σ` fixing `e`, every
`eAe`-linear endomorphism `f` of `A e` is left multiplication by an element of `A`. -/
theorem exists_eq_mul_left_of_copresentation [FiniteDimensional k A]
    (hnd : ∀ a, e * a = a → a ≠ 0 → ∃ b, b * e = b ∧ τ (a * b) ≠ 0)
    (hdim : finrank k (leftCorner (k := k) e) = finrank k (rightCorner (k := k) e))
    (he : e * e = e) {n : ℕ} (c : Fin n → A) (hc : ∀ j, c j * e = c j)
    (hinj : ∀ z, (∀ j, z * c j = 0) → z = 0)
    (hcok : ∀ y : Fin n → A, (∀ j, y j * e = y j) →
      (∀ a, ∃ t, ∀ j, e * a * y j = t * c j) → ∃ t, ∀ j, y j = t * c j)
    (σ : A ≃ₗ[k] A) (hmul : ∀ x y, σ (x * y) = σ y * σ x) (hinv : ∀ x, σ (σ x) = x)
    (hσe : σ e = e) (f : A →ₗ[k] A) (hfe : ∀ x, x * e = x → f x * e = f x)
    (hfb : ∀ b x, x * e = x → f (x * (e * b * e)) = f x * (e * b * e)) :
    ∃ a, ∀ x, x * e = x → f x = a * x := by
  have hσl : ∀ x, x * e = x → e * σ x = σ x := fun x hx => by
    rw [← hσe, ← hmul, hx]
  have hσr : ∀ x, e * x = x → σ x * e = σ x := fun x hx => by
    rw [← hσe, ← hmul, hx]
  let g : A →ₗ[k] A := σ.toLinearMap ∘ₗ f ∘ₗ σ.toLinearMap
  have hg : ∀ x, g x = σ (f (σ x)) := fun _ => rfl
  obtain ⟨t, ht⟩ := exists_eq_mul_right_of_copresentation hnd hdim he c hc hinj hcok g
    (fun x hx => by rw [hg, hσl _ (hfe _ (hσr x hx))])
    (fun b x hx => by
      have h1 : σ (e * b * e * x) = σ x * (e * σ b * e) := by
        rw [hmul, hmul, hmul, hσe]; simp only [mul_assoc]
      have h2 : σ (e * σ b * e) = e * b * e := by
        rw [hmul, hmul, hσe, hinv, mul_assoc]
      rw [hg, hg, h1, hfb _ _ (hσr x hx), hmul, h2])
  refine ⟨σ t, fun x hx => ?_⟩
  have := ht (σ x) (hσl x hx)
  rw [hg, hinv] at this
  rw [← hinv (f x), this, hmul, hinv]

/-- **Double centralizer of a self-dual corner** (left-module form, packaged): under
`HasCornerCopresentation e` and an anti-involution fixing `e`, every `eAe`-linear endomorphism of
`A e` is left multiplication by an element of `A`. -/
theorem exists_eq_mul_left_of_hasCornerCopresentation [FiniteDimensional k A]
    (hnd : ∀ a, e * a = a → a ≠ 0 → ∃ b, b * e = b ∧ τ (a * b) ≠ 0)
    (hdim : finrank k (leftCorner (k := k) e) = finrank k (rightCorner (k := k) e))
    (he : e * e = e) (hK : HasCornerCopresentation e)
    (σ : A ≃ₗ[k] A) (hmul : ∀ x y, σ (x * y) = σ y * σ x) (hinv : ∀ x, σ (σ x) = x)
    (hσe : σ e = e) (f : A →ₗ[k] A) (hfe : ∀ x, x * e = x → f x * e = f x)
    (hfb : ∀ b x, x * e = x → f (x * (e * b * e)) = f x * (e * b * e)) :
    ∃ a, ∀ x, x * e = x → f x = a * x := by
  obtain ⟨n, c, hc, hinj, hcok⟩ := hK
  exact exists_eq_mul_left_of_copresentation hnd hdim he c hc hinj hcok σ hmul hinv hσe f hfe hfb

end Categorification
