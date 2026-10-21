/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Grading

/-!
# Transfer of degrees along algebra maps out of `R(ν)`

The grading of the KLR algebra `R(ν)` is defined by a coaction
(`Categorification.KLR.GradingDatum.grade`), so it is not formal that an algebra map out of
`R(ν)` which preserves the degrees of the generators preserves the degree of every homogeneous
element. This file proves it.

## Main results

* `grade_transfer`: an algebra map out of `R(ν)` which sends `e_i`, `x_a e_i`, `ψ_j e_i` into
  the corresponding degrees of a family `ℬ` of submodules closed under products sends every
  homogeneous element of degree `d` into `ℬ d`.
-/

noncomputable section

namespace Categorification.KLR

open KLRAlgebra

variable {I' : Type*} [DecidableEq I'] {k' : Type*} [CommRing k']
  {Q : I' → I' → MvPolynomial (Fin 2) k'} {ν : Multiset I'} (G : KLR.GradingDatum Q)
  {B : Type*} [Ring B] [Algebra k' B] (ℬ : ℤ → Submodule k' B)

/-- **Transfer of degrees.** Let `φ : R(ν) → B` be an algebra map and `ℬ` a family of
submodules of `B` with `1 ∈ ℬ 0` and `ℬ d ℬ d' ⊆ ℬ (d + d')`. If `φ` sends `e_i`, `x_a e_i` and
`ψ_j e_i` into `ℬ` of their degrees, then it sends every element of degree `d` into `ℬ d`. -/
theorem grade_transfer (hB1 : (1 : B) ∈ ℬ 0)
    (hBmul : ∀ {d d' : ℤ} {y z : B}, y ∈ ℬ d → z ∈ ℬ d' → y * z ∈ ℬ (d + d'))
    (φ : KLRAlgebra k' Q ν →ₐ[k'] B) (he : ∀ i, φ (e i) ∈ ℬ 0)
    (hx : ∀ a i, φ (x a * e i) ∈ ℬ (G.degX (i.lbl a)))
    (hψ : ∀ j i, φ (ψ j * e i) ∈ ℬ (G.dψ j i)) {d : ℤ} {r : KLRAlgebra k' Q ν}
    (hr : r ∈ G.grade ν d) : φ r ∈ ℬ d := by
  classical
  let T : Set (KLRAlgebra k' Q ν) := {b | ∀ d', φ (GradedRing.proj (G.grade ν) d' b) ∈ ℬ d'}
  have hT0 : (0 : KLRAlgebra k' Q ν) ∈ T := fun d' => by
    rw [map_zero, map_zero]; exact zero_mem _
  have hTadd : ∀ b c, b ∈ T → c ∈ T → b + c ∈ T := fun b c hb hc d' => by
    rw [map_add, map_add]; exact add_mem (hb d') (hc d')
  have hT1 : (1 : KLRAlgebra k' Q ν) ∈ T := by
    intro d'
    rw [GradedRing.proj_apply]
    by_cases hd : d' = 0
    · subst hd
      rw [DirectSum.decompose_of_mem_same _ (SetLike.one_mem_graded _), map_one]
      exact hB1
    · rw [DirectSum.decompose_of_mem_ne _ (SetLike.one_mem_graded _) (Ne.symm hd), map_zero]
      exact zero_mem _
  have hThom : ∀ (h : KLRAlgebra k' Q ν) (d₀ : ℤ), h ∈ G.grade ν d₀ → φ h ∈ ℬ d₀ →
      ∀ b ∈ T, h * b ∈ T := by
    intro h d₀ hh hφ b hb d'
    have key := DirectSum.coe_decompose_mul_add_of_left_mem (G.grade ν) (b := b)
      (j := d' - d₀) hh
    rw [add_sub_cancel] at key
    rw [GradedRing.proj_apply, key, map_mul]
    have h2 := hBmul hφ (hb (d' - d₀))
    rwa [GradedRing.proj_apply, add_sub_cancel] at h2
  let M : Set (KLRAlgebra k' Q ν) := {a | ∀ b ∈ T, a * b ∈ T}
  have hM0 : (0 : KLRAlgebra k' Q ν) ∈ M := fun b _ => by rw [zero_mul]; exact hT0
  have hMadd : ∀ a a', a ∈ M → a' ∈ M → a + a' ∈ M := fun a a' ha ha' b hb => by
    rw [add_mul]; exact hTadd _ _ (ha b hb) (ha' b hb)
  have hMmul : ∀ a a', a ∈ M → a' ∈ M → a * a' ∈ M := fun a a' ha ha' b hb => by
    rw [mul_assoc]; exact ha _ (ha' b hb)
  have hMsum : ∀ (f : Seq ν → KLRAlgebra k' Q ν), (∀ i, f i ∈ M) → ∑ i, f i ∈ M :=
    fun f hf => Finset.sum_induction f (· ∈ M) hMadd hM0 fun i _ => hf i
  have hMalg : ∀ c : k', algebraMap k' (KLRAlgebra k' Q ν) c ∈ M := fun c =>
    hThom _ 0 (SetLike.algebraMap_mem_graded _ c) (by
      rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one]; exact Submodule.smul_mem _ c hB1)
  have hall : ∀ u, KLRAlgebra.mk k' Q ν u ∈ M := by
    intro u
    induction u using FreeAlgebra.induction with
    | grade0 c => rw [AlgHom.commutes]; exact hMalg c
    | grade1 g =>
      cases g with
      | idem i => exact hThom _ 0 (G.e_mem_grade i) (he i)
      | dot a =>
        change x a ∈ M
        rw [← mul_one (x a), ← sum_e, Finset.mul_sum]
        exact hMsum _ fun i => hThom _ _ (G.x_mul_e_mem_grade a i) (hx a i)
      | cross j =>
        change ψ j ∈ M
        rw [← mul_one (ψ j), ← sum_e, Finset.mul_sum]
        exact hMsum _ fun i => hThom _ _ (G.ψ_mul_e_mem_grade' j i) (hψ j i)
    | mul u v hu hv => rw [map_mul]; exact hMmul _ _ hu hv
    | add u v hu hv => rw [map_add]; exact hMadd _ _ hu hv
  have hrT : r ∈ T := by
    obtain ⟨u, hu⟩ := mk_surjective (k := k') (Q := Q) (ν := ν) r
    have := hall u 1 hT1
    rwa [mul_one, hu] at this
  have := hrT d
  rwa [GradedRing.proj_apply, DirectSum.decompose_of_mem_same _ hr] at this


end Categorification.KLR
