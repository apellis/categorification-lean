/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.SelfDualDoubleCentralizer
import Mathlib.RingTheory.Idempotents

set_option backward.isDefEq.respectTransparency false

/-!
# Criteria for a corner copresentation

Background for B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v3, Corollary 5.32 (v2: Corollary 5.29): the dominant dimension of `T^λ` with
respect to the self-dual projective `P⁰ = T^λ e⁰` is at least two, which is the hypothesis
`HasCornerCopresentation e⁰` of the double centralizer theorem
(`exists_eq_mul_left_of_hasCornerCopresentation`). Here we reduce that hypothesis to one
condition per element of a family of maps between projectives.

For `c ∈ A`, the quotient `A / A c` of the left regular module has *no nonzero submodule killed
by `e`* when `w ∈ A c` follows from `e a w ∈ A c` for every `a` (`IsCornerFaithfulQuot e c`).

* `isCornerFaithfulQuot_of_isExactMulRight`: if `A / A c` embeds into a free module, i.e.
  `A → A → Aⁿ`, `z ↦ z c`, `w ↦ (w gⱼ)ⱼ` is exact (`IsExactMulRight c g`), and `A` acts
  faithfully on the left of `e A`, then `A / A c` has no nonzero submodule killed by `e`.
* `exists_isExactMulRight_of_isCornerFaithfulQuot`: conversely, if `A` is finite-dimensional and
  `τ` pairs `e A` and `A e` perfectly, `A / A c` with no nonzero submodule killed by `e` embeds
  into a sum of copies of `A e` (the dual of `e A`).
* `isCornerFaithfulQuot_mul`: the condition is preserved by composition with an injective map
  `A f → A e'` between projectives.
* `hasCornerCopresentation_of_family`: given complete orthogonal idempotents `pᵢ` and elements
  `cᵢ ∈ pᵢ A e` with `x ↦ x cᵢ` injective on `A pᵢ` and every `A / A cᵢ` without nonzero
  submodules killed by `e`, `A` has a corner copresentation.
-/

noncomputable section

namespace Categorification

open _root_.Module

section Ring

variable {A : Type*} [Ring A]

/-- The sequence `A → A → Aⁿ`, `z ↦ z c`, `w ↦ (w gⱼ)ⱼ`, of left `A`-modules is exact:
`c gⱼ = 0`, and `w gⱼ = 0` for every `j` forces `w ∈ A c`. -/
def IsExactMulRight {n : ℕ} (c : A) (g : Fin n → A) : Prop :=
  (∀ j, c * g j = 0) ∧ ∀ w : A, (∀ j, w * g j = 0) → ∃ z, w = z * c

/-- The quotient `A / A c` of the left regular module has no nonzero submodule killed by `e`:
`e a w ∈ A c` for every `a` forces `w ∈ A c`. -/
def IsCornerFaithfulQuot (e c : A) : Prop :=
  ∀ w : A, (∀ a, ∃ z, e * a * w = z * c) → ∃ z, w = z * c

/-- A quotient embedding into a free module has no nonzero submodule killed by `e`, when `A`
acts faithfully on `e A` from the right. -/
theorem isCornerFaithfulQuot_of_isExactMulRight {e c : A} {n : ℕ} {g : Fin n → A}
    (hfaith : ∀ y : A, (∀ a, e * a * y = 0) → y = 0) (h : IsExactMulRight c g) :
    IsCornerFaithfulQuot e c := fun w hw =>
  h.2 w fun j => hfaith _ fun a => by
    obtain ⟨z, hz⟩ := hw a
    rw [← mul_assoc, hz, mul_assoc, h.1 j, mul_zero]

/-- `A / A f` for an idempotent `f` has no nonzero submodule killed by `e`, when `A` acts
faithfully on `e A`: it is `A (1 - f)`. -/
theorem isCornerFaithfulQuot_idem {e f : A} (hf : IsIdempotentElem f)
    (hfaith : ∀ y : A, (∀ a, e * a * y = 0) → y = 0) : IsCornerFaithfulQuot e f := by
  refine fun w hw => ⟨w, ?_⟩
  have h : w * (1 - f) = 0 := hfaith _ fun a => by
    obtain ⟨z, hz⟩ := hw a
    rw [← mul_assoc, hz, mul_assoc, mul_sub, mul_one, hf.eq, sub_self, mul_zero]
  rw [mul_sub, mul_one, sub_eq_zero] at h
  exact h

/-- **Composition.** If `A / A c'` and `A / A c` have no nonzero submodules killed by `e`, where
`c' ∈ f A` and `c ∈ A f` and `x ↦ x c'` is injective on `A f`, then neither has `A / A (c c')`. -/
theorem isCornerFaithfulQuot_mul {e f c c' : A} (hf : IsIdempotentElem f) (hc : c * f = c)
    (hc' : f * c' = c') (hinj : ∀ x, x * f = x → x * c' = 0 → x = 0)
    (h : IsCornerFaithfulQuot e c) (h' : IsCornerFaithfulQuot e c') :
    IsCornerFaithfulQuot e (c * c') := by
  intro w hw
  obtain ⟨w₁, hw₁⟩ := h' w fun a => by
    obtain ⟨z, hz⟩ := hw a
    exact ⟨z * c, by rw [hz, mul_assoc]⟩
  have hw₂ : w = w₁ * f * c' := by rw [mul_assoc, hc', hw₁]
  obtain ⟨z, hz⟩ := h (w₁ * f) fun a => by
    obtain ⟨z, hz⟩ := hw a
    refine ⟨z, ?_⟩
    rw [← sub_eq_zero]
    refine hinj _ (by simp only [sub_mul, mul_assoc, hf.eq, hc]) ?_
    rw [sub_mul, sub_eq_zero]
    calc e * a * (w₁ * f) * c' = e * a * w := by rw [hw₂]; simp only [mul_assoc]
      _ = z * c * c' := by rw [hz, mul_assoc]
  exact ⟨z, by rw [hw₂, hz, mul_assoc]⟩

/-- **Assembly.** Let `p` be complete orthogonal idempotents and `cᵢ ∈ pᵢ A e` such that
`x ↦ x cᵢ` is injective on `A pᵢ` and `A / A cᵢ` has no nonzero submodule killed by `e`. Then
`A` has a corner copresentation with respect to `e`. -/
theorem hasCornerCopresentation_of_family {e : A} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ι → A} (hp : CompleteOrthogonalIdempotents p) (c : ι → A) (hpc : ∀ i, p i * c i = c i)
    (hce : ∀ i, c i * e = c i) (hinj : ∀ i x, x * p i = x → x * c i = 0 → x = 0)
    (hquot : ∀ i, IsCornerFaithfulQuot e (c i)) : HasCornerCopresentation e := by
  let σ := Fintype.equivFin ι
  have hpc' : ∀ i j, p i * c j = if i = j then c j else 0 := by
    intro i j
    split_ifs with h
    · subst h; exact hpc i
    · rw [← hpc j, ← mul_assoc, hp.ortho h, zero_mul]
  refine ⟨Fintype.card ι, fun j => c (σ.symm j), fun j => hce _, fun z hz => ?_,
    fun y _ hy => ?_⟩
  · rw [← mul_one z, ← hp.complete, Finset.mul_sum]
    refine Finset.sum_eq_zero fun i _ => hinj i _ (by rw [mul_assoc, (hp.idem i).eq]) ?_
    rw [mul_assoc, hpc i]
    simpa using hz (σ i)
  · have hj : ∀ j, ∃ t, y j = t * c (σ.symm j) := fun j =>
      hquot _ (y j) fun a => by
        obtain ⟨t, ht⟩ := hy a
        exact ⟨t, ht j⟩
    choose t ht using hj
    refine ⟨∑ i, t (σ i) * p i, fun j => ?_⟩
    rw [Finset.sum_mul, Finset.sum_eq_single (σ.symm j), mul_assoc, hpc, Equiv.apply_symm_apply,
      ← ht j]
    · intro i _ hi
      rw [mul_assoc, hpc' i]
      simp [hi]
    · intro h; exact absurd (Finset.mem_univ _) h

end Ring

section Field

variable {k A : Type*} [Field k] [Ring A] [Algebra k A] {τ : A →ₗ[k] k} {e : A}

/-- **Embedding into copies of `A e`.** If `A` is finite-dimensional, `τ` pairs `e A` and `A e`
perfectly and `A / A c` has no nonzero submodule killed by `e`, then `A / A c` embeds into a
sum of copies of `A e`: there are `gⱼ ∈ A e` with `A → A → Aⁿ` exact. -/
theorem exists_isExactMulRight_of_isCornerFaithfulQuot [FiniteDimensional k A]
    (hnd : ∀ a, e * a = a → a ≠ 0 → ∃ b, b * e = b ∧ τ (a * b) ≠ 0)
    (hdim : finrank k (leftCorner (k := k) e) = finrank k (rightCorner (k := k) e))
    (he : e * e = e) {c : A} (h : IsCornerFaithfulQuot e c) :
    ∃ (n : ℕ) (g : Fin n → A), (∀ j, g j * e = g j) ∧ IsExactMulRight c g := by
  let W : Submodule k A := LinearMap.range (LinearMap.mulRight k c)
  let D := W.dualAnnihilator
  have : Module.Free k D := Module.Free.of_divisionRing k D
  let b := Module.finBasis k D
  have hrep : ∀ j, ∃ g, g * e = g ∧ ∀ a (ha : e * a = a),
      τ (a * g) = ((b j : Dual k A) ∘ₗ (leftCorner (k := k) e).subtype) ⟨a, ha⟩ :=
    fun j => exists_rightCorner_rep hnd hdim _
  choose g hg hgrep using hrep
  have hW : ∀ a, a * c ∈ W := fun a => ⟨a, rfl⟩
  refine ⟨_, g, hg, fun j => ?_, fun w hw => h w fun a => ?_⟩
  · refine eq_zero_of_rightCorner_pairing hnd hdim (by rw [mul_assoc, hg]) fun a ha => ?_
    rw [← mul_assoc, hgrep j (a * c) (by rw [← mul_assoc, ha])]
    exact (Submodule.mem_dualAnnihilator _).1 (b j).2 _ (hW a)
  · have hx : e * (e * a * w) = e * a * w := by rw [← mul_assoc, ← mul_assoc, he]
    have hmem : e * a * w ∈ W := by
      rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
      intro φ hφ
      have hL : (Module.Dual.eval k A (e * a * w)).comp D.subtype = 0 :=
        b.ext fun j => by
          change (b j : Dual k A) (e * a * w) = 0
          have := hgrep j (e * a * w) hx
          simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at this
          rw [← this, mul_assoc, hw j, mul_zero, map_zero]
      exact LinearMap.congr_fun hL ⟨φ, hφ⟩
    obtain ⟨z, hz⟩ := hmem
    exact ⟨z, hz.symm⟩

end Field

end Categorification
