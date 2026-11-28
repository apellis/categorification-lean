/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DegreewiseTensor

/-!
# The degreewise description of `M ⊗_B X` on homogeneous elements

For a ring `B`, an `(A, B)`-bimodule `M` and a dg module `X` over `B` (concentrated in degree
`0`), the isomorphism `tensorFunctorCompComplexIso` identifying the underlying complex of
`M ⊗_B X` with `M ⊗_B -` applied degreewise sends `m ⊗ x`, for `x` homogeneous of degree `p`, to
`m ⊗ x` in degree `p` (`tensorFunctorCompComplexIso_hom_f_tmul`). Maps of complexes out of the
underlying complex of `M ⊗_B (N ⊗_C X)` are determined by their values on `m ⊗ (n ⊗ x)` with
`x` homogeneous (`complexFunctor_tensorTwo_hom_ext`).

These are used for B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.21, to identify the crossing on the dg derived
`𝔈_i²` with left multiplication on dg modules.

## Main results

* `complexEquivalence_unitIso_hom_apply_of_mem`.
* `tensorFunctorCompComplexIso_hom_f_tmul`.
* `complexFunctor_tensorTwo_hom_ext`.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory DG DG.DegreeZero

noncomputable section

namespace Categorification

universe u

section Unit

variable {S : Type u} [Ring S]

/-- **The unit of `complexEquivalence` on a homogeneous element** `z` of degree `p` is `z` in
the summand of degree `p`. -/
theorem complexEquivalence_unitIso_hom_apply_of_mem (Y : DGModuleCat.{u} S) {p : ℤ} (z : Y)
    (hz : z ∈ grading p) :
    (complexEquivalence S).unitIso.hom.app Y z =
      ComplexSum.of ((complexFunctor S).obj Y) p ⟨z, mem_gradingSubmodule.mpr hz⟩ := by
  have h := complexFunctor_map_f_apply ((complexEquivalence S).unitIso.hom.app Y) p
    ⟨z, mem_gradingSubmodule.mpr hz⟩
  have e : (complexFunctor S).map ((complexEquivalence S).unitIso.hom.app Y) =
      ((ofComplexCompIso S).app ((complexFunctor S).obj Y)).inv := by
    simp only [complexEquivalence, NatIso.ofComponents_hom_app,
      Functor.FullyFaithful.preimageIso_hom, Iso.symm_hom, Iso.app_inv]
    exact complexFunctorFullyFaithful.map_preimage _
  rw [e] at h
  exact h.symm

end Unit

section Tensor

variable {A B : Type u} [Ring A] [Ring B]
  (M : Type u) [AddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]

/-- **`tensorFunctorCompComplexIso` on `m ⊗ y`** for `y` homogeneous of degree `p`. -/
theorem tensorFunctorCompComplexIso_hom_f_tmul (Y : DGModuleCat.{u} B) {p : ℤ}
    (m : InDegreeZero M) (y : Y) (hy : y ∈ grading p)
    (h : TensorProductOver.tmul B m y ∈
      gradingSubmodule A ((DGModuleCat.tensorFunctor A (InDegreeZero M)).obj Y) p) :
    (((tensorFunctorCompComplexIso A M).hom.app Y).f p).hom ⟨TensorProductOver.tmul B m y, h⟩ =
      TensorProductOver.tmul B m
        (show InDegreeZero (gradingSubmodule B Y p) from ⟨y, mem_gradingSubmodule.mpr hy⟩) := by
  simp only [tensorFunctorCompComplexIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.leftUnitor_inv_app,
    Functor.rightUnitor_hom_app, Iso.symm_hom, Category.id_comp]
  change ComplexSum.component _ p (tensorComplexSumFwd (A := A) ((complexFunctor B).obj Y)
    (TensorProductOver.tmul B m ((complexEquivalence B).unitIso.hom.app Y y))) = _
  rw [complexEquivalence_unitIso_hom_apply_of_mem Y y hy, tensorComplexSumFwd_tmul_of,
    ComplexSum.component_of_same]

end Tensor

section Ext

variable {A B C : Type u} [Ring A] [Ring B] [Ring C]
  (M : Type u) [AddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]
  (N : Type u) [AddCommGroup N] [Module B N] [Module Cᵐᵒᵖ N] [SMulCommClass B Cᵐᵒᵖ N]

/-- `m ⊗ (n ⊗ x)` is homogeneous of the degree of `x`. -/
theorem tmul_tmul_mem_grading (X : DGModuleCat.{u} C) {p : ℤ} (m : InDegreeZero M)
    (n : InDegreeZero N) {x : X} (hx : x ∈ grading p) :
    TensorProductOver.tmul B m (TensorProductOver.tmul C n x) ∈ grading p := by
  have hm : m ∈ grading 0 := (InDegreeZero.mem_grading_iff (M := M)).mpr (Or.inl rfl)
  have hn : n ∈ grading 0 := (InDegreeZero.mem_grading_iff (M := N)).mpr (Or.inl rfl)
  simpa using TensorProductOver.tmul_mem_grading hm (TensorProductOver.tmul_mem_grading hn hx)

/-- **Maps of complexes out of the underlying complex of `M ⊗_B (N ⊗_C X)` are determined by
their values on `m ⊗ (n ⊗ x)` with `x` homogeneous.** -/
theorem complexFunctor_tensorTwo_hom_ext (X : DGModuleCat.{u} C)
    {K : CochainComplex (ModuleCat.{u} A) ℤ}
    {f g : (complexFunctor A).obj ((DGModuleCat.tensorFunctor A (InDegreeZero M)).obj
      ((DGModuleCat.tensorFunctor B (InDegreeZero N)).obj X)) ⟶ K}
    (h : ∀ (p : ℤ) (m : InDegreeZero M) (n : InDegreeZero N) (x : X) (hx : x ∈ grading p),
      (f.f p).hom ⟨TensorProductOver.tmul B m (TensorProductOver.tmul C n x),
          mem_gradingSubmodule.mpr (tmul_tmul_mem_grading M N X m n hx)⟩ =
        (g.f p).hom ⟨TensorProductOver.tmul B m (TensorProductOver.tmul C n x),
          mem_gradingSubmodule.mpr (tmul_tmul_mem_grading M N X m n hx)⟩) : f = g := by
  have key : (complexEquivalence A).unitIso.hom.app _ ≫ (complexEquivalence A).inverse.map f =
      (complexEquivalence A).unitIso.hom.app _ ≫ (complexEquivalence A).inverse.map g := by
    refine DGModuleCat.tensor_hom_ext₂ (A := B) (B := C) (C := A) (InDegreeZero N)
      (InDegreeZero M) fun m n x => ?_
    induction x using DG.induction_on with
    | h_zero =>
      rw [TensorProductOver.tmul_zero, TensorProductOver.tmul_zero, map_zero, map_zero]
    | @h_homogeneous p x =>
      have hz := tmul_tmul_mem_grading (B := B) M N X m n x.2
      change (DGModuleCat.ofComplex A).map f ((complexEquivalence A).unitIso.hom.app _ _) =
        (DGModuleCat.ofComplex A).map g ((complexEquivalence A).unitIso.hom.app _ _)
      rw [complexEquivalence_unitIso_hom_apply_of_mem _ _ hz, DGModuleCat.ofComplex_map_apply,
        DGModuleCat.ofComplex_map_apply, ComplexSum.map_of, ComplexSum.map_of]
      exact congrArg _ (h p m n x x.2)
    | h_add x x' hx hx' =>
      rw [TensorProductOver.tmul_add, TensorProductOver.tmul_add, map_add, map_add, hx, hx']
  exact (complexEquivalence A).inverse.map_injective ((cancel_epi _).mp key)

end Ext

end Categorification
