/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Lifting finite right-factor relations across idempotent ideals

Generation at the idempotent generators suffices for lifting a finite relation
with its exact projected coefficients through the ideal they generate.
-/
open scoped BigOperators

namespace Categorification

/-- A finite family of right factors generating the columns at the idempotent
generators of a two-sided ideal generates every column of the ideal with
coefficients in the ideal. -/
theorem exists_idempotentSpan_exit_coefficients
    {A ι : Type*} [Ring A] [Fintype ι]
    (S : Set A) (s : A) (leg : ι → A) (idem : ∀ v ∈ S, v*v=v)
    (generate : ∀ v ∈ S, ∀ z, ∃ c : ι → A, v*z*s=∑ i, c i*leg i)
    {y : A} (hy : y ∈ TwoSidedIdeal.span S) :
    ∃ c : ι → A, (∀ i, c i ∈ TwoSidedIdeal.span S) ∧ y*s=∑ i, c i*leg i := by
  let J := TwoSidedIdeal.span S
  suffices H : ∀ z, ∃ c : ι → A, (∀ i, c i ∈ J) ∧ y*z*s=∑ i, c i*leg i by
    simpa only [mul_one] using H 1
  induction hy using TwoSidedIdeal.span_induction with
  | mem v hv =>
    intro z
    obtain ⟨c, hc⟩ := generate v hv z
    refine ⟨fun i => v*c i, fun _ => J.mul_mem_right _ _ (TwoSidedIdeal.subset_span hv), ?_⟩
    rw [← show v*(v*z*s)=v*z*s by rw [← mul_assoc v (v*z), ← mul_assoc v v, idem _ hv],
      hc, Finset.mul_sum]
    simp only [mul_assoc]
  | zero => intro z; exact ⟨fun _ => 0,fun _ => J.zero_mem,by simp⟩
  | add x y _ _ hx hy =>
    intro z
    obtain ⟨c,hc,hec⟩ := hx z
    obtain ⟨d,hd,hed⟩ := hy z
    refine ⟨fun i => c i+d i, fun i => J.add_mem (hc i) (hd i), ?_⟩
    simp only [add_mul,hec,hed,Finset.sum_add_distrib]
  | neg x _ hx =>
    intro z
    obtain ⟨c,hc,he⟩ := hx z
    refine ⟨fun i => -c i, fun i => J.neg_mem (hc i), ?_⟩
    simp only [neg_mul,he,Finset.sum_neg_distrib]
  | left_absorb r x _ hx =>
    intro z
    obtain ⟨c,hc,he⟩ := hx z
    refine ⟨fun i => r*c i,fun i => J.mul_mem_left _ _ (hc i),?_⟩
    rw [mul_assoc r x, mul_assoc r (x*z), he, Finset.mul_sum]
    simp only [mul_assoc]
  | right_absorb r x _ hx =>
    intro z
    simpa only [mul_assoc] using hx (r*z)

/-- A relation after quotienting by a span of idempotents lifts with exact
coefficient projections if the exit family generates the idempotent columns. -/
theorem exists_exitRelation_lift_of_idempotentSpan
    {A B ι : Type*} [Ring A] [Ring B] [Fintype ι]
    (π : A →+* B) (surj : Function.Surjective π)
    (S : Set A) (kernel : TwoSidedIdeal.ker π = TwoSidedIdeal.span S)
    (s : A) (leg : ι → A) (idem : ∀ v ∈ S, v*v=v)
    (generate : ∀ v ∈ S, ∀ z, ∃ c : ι → A, v*z*s=∑ i, c i*leg i)
    (right : ∀ i, leg i*s=leg i)
    (x : ι → B) (hx : ∑ i, x i*π (leg i)=0) :
    ∃ c : ι → A, (∀ i, π (c i)=x i) ∧ ∑ i, c i*leg i=0 := by
  classical
  choose a ha using fun i => surj (x i)
  let z := ∑ i, a i*leg i
  have hz : z ∈ TwoSidedIdeal.ker π := by
    rw [TwoSidedIdeal.mem_ker]
    simpa only [z,map_sum,map_mul,ha] using hx
  have hzCut : z*s=z := by
    simp only [z,Finset.sum_mul,mul_assoc,right]
  obtain ⟨b,hb,he⟩ := exists_idempotentSpan_exit_coefficients S s leg idem generate (kernel ▸ hz)
  have hb0 i : π (b i)=0 := by
    have hi : b i ∈ TwoSidedIdeal.ker π := kernel.symm ▸ hb i
    rwa [TwoSidedIdeal.mem_ker] at hi
  refine ⟨fun i => a i-b i, fun i => by rw [map_sub,ha,hb0,sub_zero], ?_⟩
  simp only [sub_mul, Finset.sum_sub_distrib]
  rw [← he,hzCut,sub_self]

end Categorification
