/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Module.Submodule.Range

/-!
# Images of sums of orthogonal idempotents

For a finite family of orthogonal idempotents `P i` on `M` and `P' i` on `M'`, linear
equivalences `range (P i) ≃ range (P' i)` assemble to a linear equivalence
`range (∑ i, P i) ≃ range (∑ i, P' i)` (`orthRangeSumEquiv`), sending `x` to
`∑ i, T i (P i x)`.

This is used to sum the isomorphisms (T_w) over the red-ordered loadings `w` of the window in
the proof of B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v3, Lemma 7.19 (trace half).

## Main definitions

* `Categorification.orthRangeSumEquiv`.

## Main results

* `Categorification.apply_sum_of_additive`, `Categorification.orthRangeSumEquiv_apply`,
  `Categorification.orthRangeSumEquiv_proj`.
-/

namespace Categorification

open LinearMap

variable {R M M' : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M'] {ι : Type*} [DecidableEq ι] (s : Finset ι)

omit [DecidableEq ι] in
/-- An additive function commutes with finite sums. -/
theorem apply_sum_of_additive {A B : Type*} [AddCommMonoid A] [AddCommMonoid B] (F : A → B)
    (h0 : F 0 = 0) (hadd : ∀ a b, F (a + b) = F a + F b) (f : ι → A) :
    F (∑ i ∈ s, f i) = ∑ i ∈ s, F (f i) :=
  map_sum (⟨⟨F, h0⟩, hadd⟩ : A →+ B) f s

/-- A finite family of orthogonal idempotents. -/
def OrthIdem (P : ι → M →ₗ[R] M) : Prop :=
  ∀ i ∈ s, ∀ i' ∈ s, ∀ x, P i (P i' x) = if i = i' then P i' x else 0

variable {s}

theorem OrthIdem.apply_of_mem_range {P : ι → M →ₗ[R] M} (hP : OrthIdem s P) {i i' : ι}
    (hi : i ∈ s) (hi' : i' ∈ s) {y : M} (hy : y ∈ range (P i')) :
    P i y = if i = i' then y else 0 := by
  obtain ⟨x, rfl⟩ := hy
  exact hP i hi i' hi' x

theorem OrthIdem.sum_apply_of_mem_range {P : ι → M →ₗ[R] M} (hP : OrthIdem s P) {i' : ι}
    (hi' : i' ∈ s) {y : M} (hy : y ∈ range (P i')) : (∑ i ∈ s, P i) y = y := by
  rw [LinearMap.sum_apply]
  rw [Finset.sum_congr rfl fun i hi => hP.apply_of_mem_range hi hi' hy]
  rw [Finset.sum_ite_eq_of_mem' s i' (fun _ => y) hi']

theorem OrthIdem.mem_range_sum {P : ι → M →ₗ[R] M} (hP : OrthIdem s P) {i' : ι}
    (hi' : i' ∈ s) {y : M} (hy : y ∈ range (P i')) : y ∈ range (∑ i ∈ s, P i) :=
  ⟨y, hP.sum_apply_of_mem_range hi' hy⟩

theorem OrthIdem.sum_apply_of_mem_range_sum {P : ι → M →ₗ[R] M} (hP : OrthIdem s P) {x : M}
    (hx : x ∈ range (∑ i ∈ s, P i)) : (∑ i ∈ s, P i) x = x := by
  obtain ⟨u, rfl⟩ := hx
  simp only [LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_congr rfl fun d hd => hP d hd i hi u,
    Finset.sum_ite_eq_of_mem' s i (fun _ => P i u) hi]

variable (s) in
/-- The map `x ↦ ∑ i, T i (P i x)`. -/
def orthSumMap (P : ι → M →ₗ[R] M) (P' : ι → M' →ₗ[R] M')
    (T : ∀ i, range (P i) ≃ₗ[R] range (P' i)) : M →ₗ[R] M' :=
  ∑ i ∈ s, (range (P' i)).subtype ∘ₗ (T i).toLinearMap ∘ₗ (P i).rangeRestrict

omit [DecidableEq ι] in
variable (s) in
theorem orthSumMap_apply (P : ι → M →ₗ[R] M) (P' : ι → M' →ₗ[R] M')
    (T : ∀ i, range (P i) ≃ₗ[R] range (P' i)) (x : M) :
    orthSumMap s P P' T x = ∑ i ∈ s, (T i ⟨P i x, mem_range_self _ x⟩ : M') := by
  rw [orthSumMap, LinearMap.sum_apply]
  rfl

theorem OrthIdem.orthSumMap_mem {P : ι → M →ₗ[R] M} {P' : ι → M' →ₗ[R] M'}
    (hP' : OrthIdem s P') (T : ∀ i, range (P i) ≃ₗ[R] range (P' i)) (x : M) :
    orthSumMap s P P' T x ∈ range (∑ i ∈ s, P' i) := by
  rw [orthSumMap_apply]
  exact Submodule.sum_mem _ fun i hi => hP'.mem_range_sum hi (T i _).2

/-- `P' i'` picks out the `i'`-th summand of `orthSumMap`. -/
theorem OrthIdem.apply_orthSumMap {P : ι → M →ₗ[R] M} {P' : ι → M' →ₗ[R] M'}
    (hP' : OrthIdem s P') (T : ∀ i, range (P i) ≃ₗ[R] range (P' i)) {i' : ι} (hi' : i' ∈ s)
    (x : M) :
    P' i' (orthSumMap s P P' T x) = T i' ⟨P i' x, mem_range_self _ x⟩ := by
  rw [orthSumMap_apply, map_sum,
    Finset.sum_congr rfl fun i hi => hP'.apply_of_mem_range hi' hi (T i _).2,
    Finset.sum_ite_eq_of_mem s i' (fun i => (T i ⟨P i x, mem_range_self _ x⟩ : M')) hi']

theorem OrthIdem.orthSumMap_symm_orthSumMap {P : ι → M →ₗ[R] M} {P' : ι → M' →ₗ[R] M'}
    (hP : OrthIdem s P) (hP' : OrthIdem s P') (T : ∀ i, range (P i) ≃ₗ[R] range (P' i))
    {x : M} (hx : x ∈ range (∑ i ∈ s, P i)) :
    orthSumMap s P' P (fun i => (T i).symm) (orthSumMap s P P' T x) = x := by
  rw [orthSumMap_apply]
  have h : ∀ i ∈ s, ((T i).symm ⟨P' i (orthSumMap s P P' T x), mem_range_self _ _⟩ : M) =
      P i x := by
    intro i hi
    have e : (⟨P' i (orthSumMap s P P' T x), mem_range_self _ _⟩ : range (P' i)) =
        T i ⟨P i x, mem_range_self _ x⟩ :=
      Subtype.ext (hP'.apply_orthSumMap T hi x)
    rw [e, LinearEquiv.symm_apply_apply]
  rw [Finset.sum_congr rfl h, ← LinearMap.sum_apply]
  exact hP.sum_apply_of_mem_range_sum hx

/-- **Summing equivalences of the images of orthogonal idempotents**:
`range (∑ i, P i) ≃ range (∑ i, P' i)`, `x ↦ ∑ i, T i (P i x)`. -/
def orthRangeSumEquiv {P : ι → M →ₗ[R] M} {P' : ι → M' →ₗ[R] M'} (hP : OrthIdem s P)
    (hP' : OrthIdem s P') (T : ∀ i, range (P i) ≃ₗ[R] range (P' i)) :
    range (∑ i ∈ s, P i) ≃ₗ[R] range (∑ i ∈ s, P' i) where
  toFun x := ⟨orthSumMap s P P' T x, hP'.orthSumMap_mem T x⟩
  map_add' x y := Subtype.ext (map_add (orthSumMap s P P' T) (x : M) y)
  map_smul' c x := Subtype.ext (map_smul (orthSumMap s P P' T) c (x : M))
  invFun y := ⟨orthSumMap s P' P (fun i => (T i).symm) y,
    hP.orthSumMap_mem (fun i => (T i).symm) y⟩
  left_inv x := Subtype.ext (hP.orthSumMap_symm_orthSumMap hP' T x.2)
  right_inv y := Subtype.ext (by
    have h := hP'.orthSumMap_symm_orthSumMap hP (fun i => (T i).symm) y.2
    simp only [LinearEquiv.symm_symm] at h
    exact h)

theorem orthRangeSumEquiv_apply {P : ι → M →ₗ[R] M} {P' : ι → M' →ₗ[R] M'}
    (hP : OrthIdem s P) (hP' : OrthIdem s P') (T : ∀ i, range (P i) ≃ₗ[R] range (P' i))
    (x : range (∑ i ∈ s, P i)) :
    (orthRangeSumEquiv hP hP' T x : M') =
      ∑ i ∈ s, (T i ⟨P i x, mem_range_self _ _⟩ : M') :=
  orthSumMap_apply s P P' T x

/-- The `i`-th component of the summed equivalence is `T i` of the `i`-th component. -/
theorem orthRangeSumEquiv_proj {P : ι → M →ₗ[R] M} {P' : ι → M' →ₗ[R] M'}
    (hP : OrthIdem s P) (hP' : OrthIdem s P') (T : ∀ i, range (P i) ≃ₗ[R] range (P' i))
    {i : ι} (hi : i ∈ s) (x : range (∑ i ∈ s, P i)) :
    P' i (orthRangeSumEquiv hP hP' T x) = T i ⟨P i x, mem_range_self _ _⟩ :=
  hP'.apply_orthSumMap T hi x

end Categorification
