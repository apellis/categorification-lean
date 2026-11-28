/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.BalancedTensorSplit

/-!
# Internal direct sums of right modules stay internal after `- ⊗_A N`

Let `M` be a `(B, A)`-bimodule and `f q : M q → M` (`q` in a finite type) injective right
`A`-linear maps whose ranges form an internal direct sum of `M`. Then for every left
`A`-module `N` the maps `f q ⊗ 1 : M q ⊗_A N → M ⊗_A N` (`BalancedTensor.mapLeftOp`) are
injective and their ranges form an internal direct sum of `M ⊗_A N`
(`BalancedTensor.isInternal_range_mapLeftOp`). The components of an internal direct sum of
submodules stable under the right action of `A` are right `A`-linear
(`BalancedTensor.isInternal_component_op_smul`), so the decomposition is one of right
modules, and `- ⊗_A N` preserves it because it is additive.

This is used for Khovanov–Lauda I (arXiv:0803.4121v2), §2.6, Proposition 2.18, tensored with a
module: the subquotients of the Mackey filtration of an induced module.
-/

open MulOpposite

noncomputable section

namespace Categorification.BalancedTensor

variable {k : Type*} [CommRing k] {B : Type*} [Ring B] [Algebra k B] {A : Type*} [Ring A]
  {N : Type*} [AddCommGroup N] [Module k N] [Module A N]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  {M : Type*} [AddCommGroup M] [Module k M] [Module B M] [IsScalarTower k B M] [Module Aᵐᵒᵖ M]
  [SMulCommClass B Aᵐᵒᵖ M]

omit [Fintype ι] in
/-- An element is the sum of its components in an internal direct sum. -/
theorem isInternal_sum_component [Fintype ι] {R : ι → Submodule k M}
    (h : DirectSum.IsInternal R) (x : M) :
    ∑ q, ((LinearEquiv.ofBijective (DirectSum.coeLinearMap R) h).symm x q : M) = x := by
  have h1 : DirectSum.coeLinearMap R (∑ i, DirectSum.of (fun i => R i) i
      ((LinearEquiv.ofBijective (DirectSum.coeLinearMap R) h).symm x i)) = x := by
    rw [DirectSum.sum_univ_of]
    exact (LinearEquiv.ofBijective (DirectSum.coeLinearMap R) h).apply_symm_apply x
  simpa only [map_sum, DirectSum.coeLinearMap_of] using h1

/-- **The components of an internal direct sum of right-stable submodules are right linear.** -/
theorem isInternal_component_op_smul {R : ι → Submodule k M} (h : DirectSum.IsInternal R)
    (hR : ∀ q (a : A) (x : M), x ∈ R q → op a • x ∈ R q) (a : A) (x : M) (q : ι) :
    ((LinearEquiv.ofBijective (DirectSum.coeLinearMap R) h).symm (op a • x) q : M) =
      op a • ((LinearEquiv.ofBijective (DirectSum.coeLinearMap R) h).symm x q : M) := by
  conv_lhs => rw [← isInternal_sum_component h x, Finset.smul_sum, map_sum,
    DFinsupp.finsetSum_apply, Submodule.coe_sum]
  rw [Finset.sum_eq_single q]
  · exact congrArg Subtype.val (h.ofBijective_coeLinearMap_of_mem (hR q a _ (Subtype.prop _)))
  · intro q' _ hq'
    exact (congrArg Subtype.val
      (h.ofBijective_coeLinearMap_of_mem_ne hq' (hR q' a _ (Subtype.prop _)))).trans rfl
  · intro hq; exact absurd (Finset.mem_univ q) hq

variable {Mq : ι → Type*} [∀ q, AddCommGroup (Mq q)] [∀ q, Module k (Mq q)]
  [∀ q, Module B (Mq q)] [∀ q, IsScalarTower k B (Mq q)] [∀ q, Module Aᵐᵒᵖ (Mq q)]
  [∀ q, SMulCommClass B Aᵐᵒᵖ (Mq q)]

omit [Fintype ι] [DecidableEq ι] in
theorem mapLeftOp_zero (x : BalancedTensor k B A M N) {M' : Type*} [AddCommGroup M']
    [Module k M'] [Module B M'] [IsScalarTower k B M'] [Module Aᵐᵒᵖ M']
    [SMulCommClass B Aᵐᵒᵖ M'] :
    mapLeftOp B N (0 : M →ₗ[k] M') (fun a m => by simp) x = 0 := by
  induction x using induction_on with
  | zero => simp
  | tmul m n => rw [mapLeftOp_tmul, LinearMap.zero_apply, zero_tmul]
  | add x y hx hy => rw [map_add, hx, hy, add_zero]

omit [DecidableEq ι] in
theorem mapLeftOp_sum (f : ∀ q, Mq q →ₗ[k] M)
    (hf : ∀ q (a : A) (m : Mq q), f q (op a • m) = op a • f q m)
    (π : ∀ q, M →ₗ[k] Mq q) (hπ : ∀ q (a : A) (m : M), π q (op a • m) = op a • π q m)
    (x : BalancedTensor k B A M N) :
    ∑ q, mapLeftOp B N (f q) (hf q) (mapLeftOp B N (π q) (hπ q) x) =
      mapLeftOp B N (∑ q, f q ∘ₗ π q) (fun a m => by
        simp only [LinearMap.sum_apply, LinearMap.comp_apply, hπ, hf,
          Finset.smul_sum]) x := by
  induction x using induction_on with
  | zero => simp
  | tmul m n =>
    simp only [mapLeftOp_tmul, LinearMap.sum_apply, LinearMap.comp_apply]
    exact (map_sum ((mkBil k B A M N).flip n) _ _).symm
  | add x y hx hy => simp only [map_add, Finset.sum_add_distrib, hx, hy]

/-- **`- ⊗_A N` preserves a finite internal direct sum of right modules**: if the `f q` are
injective right `A`-linear maps whose ranges form an internal direct sum of `M`, then the
`f q ⊗ 1` are injective and their ranges form an internal direct sum of `M ⊗_A N`. -/
theorem isInternal_range_mapLeftOp (f : ∀ q, Mq q →ₗ[k] M)
    (hf : ∀ q (a : A) (m : Mq q), f q (op a • m) = op a • f q m)
    (hinj : ∀ q, Function.Injective (f q))
    (h : DirectSum.IsInternal fun q => LinearMap.range (f q)) :
    (∀ q, Function.Injective (mapLeftOp B N (f q) (hf q))) ∧
      DirectSum.IsInternal fun q => LinearMap.range (mapLeftOp B N (f q) (hf q)) := by
  obtain ⟨e, he⟩ : ∃ e,
      e = LinearEquiv.ofBijective (DirectSum.coeLinearMap fun q => LinearMap.range (f q)) h :=
    ⟨_, rfl⟩
  have hR : ∀ q (a : A) (x : M), x ∈ LinearMap.range (f q) →
      op a • x ∈ LinearMap.range (f q) := by
    rintro q a _ ⟨m, rfl⟩; exact ⟨op a • m, hf q a m⟩
  -- the projections
  let π : ∀ q, M →ₗ[k] Mq q := fun q =>
    (LinearEquiv.ofInjective (f q) (hinj q)).symm.toLinearMap ∘ₗ
      (DirectSum.component k ι (fun q => LinearMap.range (f q)) q) ∘ₗ e.symm.toLinearMap
  have hfπ : ∀ q x, f q (π q x) = (e.symm x q : M) := fun q x =>
    LinearEquiv.ofInjective_symm_apply (f q) (h := hinj q) _
  have hπ : ∀ q (a : A) (m : M), π q (op a • m) = op a • π q m := by
    intro q a m
    apply hinj q
    rw [hf, hfπ, hfπ, he]
    exact isInternal_component_op_smul h hR a m q
  have hπf : ∀ q (m : Mq q), π q (f q m) = m := by
    intro q m
    apply hinj q
    rw [hfπ, he, h.ofBijective_coeLinearMap_of_mem ⟨m, rfl⟩]
  have hπf' : ∀ q q', q' ≠ q → ∀ m : Mq q', π q (f q' m) = 0 := by
    intro q q' hq m
    apply hinj q
    rw [hfπ, he, h.ofBijective_coeLinearMap_of_mem_ne hq ⟨m, rfl⟩, Submodule.coe_zero, map_zero]
  have hsum : (∑ q, f q ∘ₗ π q) = LinearMap.id := by
    ext x
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, hfπ,
      LinearMap.id_apply]
    rw [he]
    exact isInternal_sum_component h x
  -- the identities after `- ⊗_A N`
  have hPF : ∀ q t, mapLeftOp B N (π q) (hπ q) (mapLeftOp B N (f q) (hf q) t) = t := by
    intro q t
    rw [mapLeftOp_comp]
    have : π q ∘ₗ f q = LinearMap.id := LinearMap.ext (hπf q)
    simp only [this]
    exact mapLeftOp_id t
  have hPF' : ∀ q q', q' ≠ q → ∀ t,
      mapLeftOp B N (π q) (hπ q) (mapLeftOp B N (f q') (hf q') t) = 0 := by
    intro q q' hq t
    rw [mapLeftOp_comp]
    have : π q ∘ₗ f q' = 0 := LinearMap.ext (hπf' q q' hq)
    simp only [this]
    exact mapLeftOp_zero t
  have hFP : ∀ t, ∑ q, mapLeftOp B N (f q) (hf q) (mapLeftOp B N (π q) (hπ q) t) = t := by
    intro t
    rw [mapLeftOp_sum]
    simp only [hsum]
    exact mapLeftOp_id t
  refine ⟨fun q => Function.LeftInverse.injective (hPF q), ?_⟩
  refine (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2 ⟨?_, ?_⟩
  · refine (iSupIndep_def).2 fun q => ?_
    rw [Submodule.disjoint_def]
    intro y hy hy'
    obtain ⟨t, rfl⟩ := hy
    have hker : (⨆ q' ∈ ({q}ᶜ : Set ι),
        LinearMap.range (mapLeftOp B N (f q') (hf q'))) ≤
        LinearMap.ker (mapLeftOp B N (π q) (hπ q)) := by
      refine iSup₂_le fun q' hq' => ?_
      rintro _ ⟨s, rfl⟩
      exact hPF' q q' hq' s
    have h0 := hker (by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hy')
    rw [LinearMap.mem_ker, hPF] at h0
    rw [h0, map_zero]
  · refine eq_top_iff.2 fun t _ => ?_
    rw [← hFP t]
    exact Submodule.sum_mem _ fun q _ =>
      Submodule.mem_iSup_of_mem q ⟨_, rfl⟩

end Categorification.BalancedTensor
