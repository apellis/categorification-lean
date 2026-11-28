/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.BalancedTensor

/-!
# Induced modules recognized by a generator decomposition

Let `P` be a `(B, D)`-bimodule generated as a right `D`-module by a finite family `g_u`, `X` a left
`D`-module and `μ : P ⊗_D X → M` a `k`-linear map. If every element of `M` is uniquely a sum
`Σ_u μ(g_u ⊗ x_u)`, then `μ` is bijective (`bijective_of_rightGenerators`). Uniqueness on the
target makes the family `g_u` free in effect, so no freeness of `P` is assumed.

This is the counting argument by which a layer of a filtered module is recognized as an induced
module `P ⊗_D X`, with `X` the part of the layer on one idempotent: B. Webster, *Knot invariants
and higher representation theory*, arXiv:1309.3796v3, proof of Lemma 7.19 (the layers of the
filtration of a partial standardization by the head strands that enter the window).
-/

open MulOpposite

namespace Categorification.BalancedTensor

variable {k : Type*} [CommRing k] {B D : Type*} [Ring B] [Algebra k B] [Ring D]
  {P : Type*} [AddCommGroup P] [Module k P] [Module B P] [IsScalarTower k B P] [Module Dᵐᵒᵖ P]
  {X : Type*} [AddCommGroup X] [Module k X] [Module D X]
  {M : Type*} [AddCommGroup M] [Module k M]
  {ι : Type*} [Fintype ι]

theorem finset_sum_tmul {κ : Type*} (s : Finset κ) (p : κ → P) (y : X) :
    (tmul (∑ u ∈ s, p u) y : BalancedTensor k B D P X) = ∑ u ∈ s, tmul (p u) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_tmul, ih]

/-- If the upper factor is generated as a right module by a finite family, every tensor is a sum
with one lower coefficient per generator. -/
theorem exists_sum_tmul_of_rightGenerators (g : ι → P)
    (hg : ∀ p : P, ∃ d : ι → D, p = ∑ u, op (d u) • g u) (z : BalancedTensor k B D P X) :
    ∃ x : ι → X, z = ∑ u, tmul (g u) (x u) := by
  induction z using BalancedTensor.induction_on with
  | zero => exact ⟨fun _ => 0, by simp⟩
  | tmul p y =>
    obtain ⟨d, rfl⟩ := hg p
    exact ⟨fun u => d u • y, by simp only [finset_sum_tmul, op_smul_tmul]⟩
  | add z z' hz hz' =>
    obtain ⟨x, hx⟩ := hz
    obtain ⟨x', hx'⟩ := hz'
    exact ⟨fun u => x u + x' u, by simp only [hx, hx', tmul_add, Finset.sum_add_distrib]⟩

/-- **Recognizing an induced module**: if `P` is generated as a right `D`-module by `g_u` and
every element of `M` is uniquely `Σ_u μ(g_u ⊗ x_u)`, then `μ : P ⊗_D X → M` is bijective. -/
theorem bijective_of_rightGenerators (g : ι → P)
    (hg : ∀ p : P, ∃ d : ι → D, p = ∑ u, op (d u) • g u)
    (μ : BalancedTensor k B D P X →ₗ[k] M)
    (hsurj : ∀ m : M, ∃ x : ι → X, m = ∑ u, μ (tmul (g u) (x u)))
    (hinj : ∀ x : ι → X, ∑ u, μ (tmul (g u) (x u)) = 0 → ∀ u, x u = 0) :
    Function.Bijective μ := by
  refine ⟨(injective_iff_map_eq_zero μ).2 fun z hz => ?_, fun m => ?_⟩
  · obtain ⟨x, rfl⟩ := exists_sum_tmul_of_rightGenerators g hg z
    rw [map_sum] at hz
    have h0 := hinj x hz
    simp only [h0, tmul_zero, Finset.sum_const_zero]
  · obtain ⟨x, rfl⟩ := hsurj m
    exact ⟨∑ u, tmul (g u) (x u), by rw [map_sum]⟩

end Categorification.BalancedTensor
