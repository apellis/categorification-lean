/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DerivedTensorComp

set_option backward.isDefEq.respectTransparency false

/-!
# Derived tensor products with bimodules in degree zero

The tensor product `M ⊗_B N` of two ordinary modules regarded as dg modules in degree `0` is
again concentrated in degree `0` with zero differential. So a linear isomorphism between two such
tensor products is an isomorphism of dg modules, and an isomorphism of dg bimodules induces an
isomorphism of the derived tensor products `X ⊗ᴸ_B -`.

These identify the two composites of B. Webster, *Knot invariants and higher representation
theory*, arXiv:1309.3796v2, Proposition 6.7, after `dgDerivedTensorCompIso` has rewritten each as
a single derived tensor product.

## Main definitions and results

* `Categorification.TensorProductOver.d_inDegreeZero`,
  `Categorification.TensorProductOver.mem_grading_zero_inDegreeZero`,
  `Categorification.TensorProductOver.eq_zero_of_mem_grading_inDegreeZero`: `M ⊗_B N` is in
  degree `0` with zero differential.
* `Categorification.DGModuleEquiv.ofDegreeZero`: a linear isomorphism between dg modules in
  degree `0` with zero differential is an isomorphism of dg modules.
* `Categorification.dgDerivedTensorIsoOfEquiv`: `X ⊗ᴸ_B - ≅ X' ⊗ᴸ_B -` for an isomorphism of dg
  bimodules `X ≅ X'`.
-/

open CategoryTheory DG MulOpposite

universe w u

noncomputable section

namespace Categorification

section DegreeZero

open DG.DegreeZero

variable {B : Type*} [Ring B] {M N : Type*} [AddCommGroup M] [Module Bᵐᵒᵖ M] [AddCommGroup N]
  [Module B N]

theorem TensorProductOver.d_inDegreeZero
    (y : TensorProductOver B (InDegreeZero M) (InDegreeZero N)) : d y = 0 := by
  induction y using TensorProductOver.induction_on with
  | zero => exact d_zero
  | tmul m n =>
    rw [TensorProductOver.d_tmul, InDegreeZero.d_apply, InDegreeZero.d_apply,
      TensorProductOver.zero_tmul, TensorProductOver.tmul_zero, add_zero]
  | add x y hx hy => rw [d_add, hx, hy, add_zero]

theorem TensorProductOver.mem_grading_zero_inDegreeZero
    (y : TensorProductOver B (InDegreeZero M) (InDegreeZero N)) : y ∈ grading (0 : ℤ) := by
  induction y using TensorProductOver.induction_on with
  | zero => exact zero_mem _
  | tmul m n =>
    simpa using TensorProductOver.tmul_mem_grading (A := B)
      ((InDegreeZero.mem_grading_iff _).mpr (Or.inl rfl) : m ∈ grading (0 : ℤ))
      ((InDegreeZero.mem_grading_iff _).mpr (Or.inl rfl) : n ∈ grading (0 : ℤ))
  | add x y hx hy => exact add_mem hx hy

theorem TensorProductOver.eq_zero_of_mem_grading_inDegreeZero {n : ℤ} (hn : n ≠ 0)
    {y : TensorProductOver B (InDegreeZero M) (InDegreeZero N)} (hy : y ∈ grading n) : y = 0 := by
  refine TensorProductOver.induction_on_mem_grading (P := fun y => y = 0) rfl ?_
    (fun x y hx hy => by rw [hx, hy, add_zero]) (fun x hx => by rw [hx, neg_zero]) hy
  intro i j m m' hm hm' hij
  rcases (InDegreeZero.mem_grading_iff _).mp hm with rfl | rfl
  · rcases (InDegreeZero.mem_grading_iff _).mp hm' with rfl | rfl
    · exact absurd hij.symm (by simpa using hn)
    · exact TensorProductOver.tmul_zero _
  · exact TensorProductOver.zero_tmul _

end DegreeZero

/-- A linear isomorphism between dg modules concentrated in degree `0` with zero differential is
an isomorphism of dg modules. -/
def DGModuleEquiv.ofDegreeZero {A : Type*} [Ring A] [DGAddCommGroup A] {X Y : Type*}
    [AddCommGroup X] [DGAddCommGroup X] [Module A X] [AddCommGroup Y] [DGAddCommGroup Y]
    [Module A Y] (e : X ≃ₗ[A] Y) (hX : ∀ {n : ℤ} {x : X}, x ∈ grading n → n ≠ 0 → x = 0)
    (hXd : ∀ x : X, d x = 0) (hY : ∀ y : Y, y ∈ grading (0 : ℤ)) (hYd : ∀ y : Y, d y = 0) :
    X ≃ᵈᵍ[A] Y where
  __ := e
  map_mem' {n x} hx := by
    by_cases hn : n = 0
    · subst hn; exact hY _
    · rw [hX hx hn]; exact (show e.toFun 0 = 0 from map_zero e) ▸ zero_mem _
  map_d' x := by rw [hXd]; exact (map_zero e).trans (hYd _).symm

section Iso

variable {A B : Type u} [Ring A] [DGAddCommGroup A] [DGRing A] [Ring B] [DGAddCommGroup B]
  [DGRing B] [HasDerivedCategory.{w, u} A] [HasDerivedCategory.{w, u} B]
  {X : Type u} [AddCommGroup X] [DGAddCommGroup X] [Module A X] [Module Bᵐᵒᵖ X]
  [DGBimodule A B X] {X' : Type u} [AddCommGroup X'] [DGAddCommGroup X'] [Module A X']
  [Module Bᵐᵒᵖ X'] [DGBimodule A B X']

/-- **The derived tensor products with isomorphic dg bimodules are isomorphic**:
`X ⊗ᴸ_B - ≅ X' ⊗ᴸ_B -` for an isomorphism of dg bimodules `e : X ≅ X'`. -/
def dgDerivedTensorIsoOfEquiv (e : X ≃ᵈᵍ[A] X')
    (he : ∀ (b : B) (x : X), e (op b • x) = op b • e x) :
    dgDerivedTensor.{w} A B X ≅ dgDerivedTensor.{w} A B X' :=
  Functor.isoWhiskerLeft (DG.DerivedCategory.kProjectiveEquivalence.{w} B).inverse
    (Functor.isoWhiskerLeft (DG.HomotopyCategory.subcategoryKProjective B).ι
      (Functor.isoWhiskerRight
        (DG.HomotopyCategory.liftNatIso _ _ (DGModuleCat.tensorFunctorIsoOfEquiv e he))
        DG.DerivedCategory.Qh))

end Iso

end Categorification
