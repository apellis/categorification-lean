/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.OrthogonalIdempotentRangeSum

/-!
# Summed equivalences of orthogonal idempotent images intertwine actions blockwise

Used for Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, trace half, step L5 (the
`W`-linearity of (T)).

Let `P i`, `P' i` be finite families of orthogonal idempotents and `T i : P i M ≃ P' i M'`.
Endomorphisms `A` of `M` and `A'` of `M'` are intertwined by the summed equivalence
`orthRangeSumEquiv` as soon as they are intertwined blockwise:
`T i' (P i' (A (P i x))) = P' i' (A' (T i (P i x)))` for all `i, i'`
(`orthSumMap_intertwine`, `orthRangeSumEquiv_intertwine`).

## Main results

* `Categorification.orthSumMap_intertwine`, `Categorification.orthRangeSumEquiv_intertwine`.
-/

namespace Categorification

open LinearMap

variable {R M M' : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M'] {ι : Type*} [DecidableEq ι] {s : Finset ι}

/-- **Blockwise intertwining gives intertwining** of `orthSumMap`, on the range of `∑ P i`,
for `A'` preserving the range of `∑ P' i`. -/
theorem orthSumMap_intertwine {P : ι → M →ₗ[R] M} {P' : ι → M' →ₗ[R] M'}
    (hP : OrthIdem s P) (hP' : OrthIdem s P') (T : ∀ i, range (P i) ≃ₗ[R] range (P' i))
    (A : M →ₗ[R] M) (A' : M' →ₗ[R] M')
    (hpair : ∀ i ∈ s, ∀ i' ∈ s, ∀ x,
      (T i' ⟨P i' (A (P i x)), mem_range_self _ _⟩ : M') =
        P' i' (A' (T i ⟨P i x, mem_range_self _ _⟩)))
    (hA' : ∀ y ∈ range (∑ i ∈ s, P' i), A' y ∈ range (∑ i ∈ s, P' i))
    {x : M} (hx : x ∈ range (∑ i ∈ s, P i)) :
    orthSumMap s P P' T (A x) = A' (orthSumMap s P P' T x) := by
  have hxs : x = ∑ i ∈ s, P i x := by
    have h := hP.sum_apply_of_mem_range_sum hx
    rw [LinearMap.sum_apply] at h
    exact h.symm
  let τ : ι → M →ₗ[R] M' := fun i' =>
    (range (P' i')).subtype ∘ₗ (T i').toLinearMap ∘ₗ (P i').rangeRestrict
  have hτ : ∀ i' y, τ i' y = (T i' ⟨P i' y, mem_range_self _ _⟩ : M') := fun _ _ => rfl
  have h1 : ∀ i' ∈ s, (T i' ⟨P i' (A x), mem_range_self _ _⟩ : M') =
      P' i' (A' (orthSumMap s P P' T x)) := by
    intro i' hi'
    have e1 : τ i' (A x) = ∑ i ∈ s, τ i' (A (P i x)) := by
      conv_lhs => rw [hxs]
      rw [map_sum, map_sum]
    rw [← hτ, e1, Finset.sum_congr rfl fun i hi => (hτ i' _).trans (hpair i hi i' hi' x),
      orthSumMap_apply, map_sum, map_sum]
  rw [orthSumMap_apply, Finset.sum_congr rfl h1, ← LinearMap.sum_apply]
  exact hP'.sum_apply_of_mem_range_sum (hA' _ (hP'.orthSumMap_mem T x))

/-- **Blockwise intertwining gives intertwining** of `orthRangeSumEquiv`. -/
theorem orthRangeSumEquiv_intertwine {P : ι → M →ₗ[R] M} {P' : ι → M' →ₗ[R] M'}
    (hP : OrthIdem s P) (hP' : OrthIdem s P') (T : ∀ i, range (P i) ≃ₗ[R] range (P' i))
    (A : M →ₗ[R] M) (A' : M' →ₗ[R] M')
    (hpair : ∀ i ∈ s, ∀ i' ∈ s, ∀ x,
      (T i' ⟨P i' (A (P i x)), mem_range_self _ _⟩ : M') =
        P' i' (A' (T i ⟨P i x, mem_range_self _ _⟩)))
    (hA : ∀ y ∈ range (∑ i ∈ s, P i), A y ∈ range (∑ i ∈ s, P i))
    (hA' : ∀ y ∈ range (∑ i ∈ s, P' i), A' y ∈ range (∑ i ∈ s, P' i))
    (x : range (∑ i ∈ s, P i)) :
    (orthRangeSumEquiv hP hP' T ⟨A x, hA x x.2⟩ : M') = A' (orthRangeSumEquiv hP hP' T x) :=
  orthSumMap_intertwine hP hP' T A A' hpair hA' x.2

end Categorification
