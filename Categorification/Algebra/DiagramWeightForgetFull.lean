/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DiagramWeightForgetTensor
import Categorification.Algebra.WeightProjection

/-!
# Weight-preserving parts and the forgotten diagram tensor

For the diagram weight bimodule `D = diagramWeightBimodule G` of a homogeneous coefficient
bimodule `M`, forgetting the weights of `D ⊗_{C_B} X` gives `M ⊗_B (⨁ k, X⟨k⟩)`
(`Categorification.DiagramWeightForget.tensorWeightSumEquiv`). Under this identification,
tensoring a morphism `g : ⨁ k, X⟨k⟩ ⟶ ⨁ k, X'⟨k⟩` of dg `B`-modules with `M` and then taking
the weight-preserving part is the same as tensoring the weight-preserving part of `g` with `D`
(`Categorification.DiagramWeightForget.weightPartHom_conjLTensor`).

So tensoring with `D` on the homotopy category of dg modules over `C_B` is a retract of tensoring
with `M` on the homotopy category of dg `B`-modules, which transfers full faithfulness from the
ungraded braiding functors of B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v3, Theorem 6.15, to the graded ones of Definition 6.6.
-/

noncomputable section

namespace Categorification

open CategoryTheory DG MulOpposite DirectSum
open scoped DG.DegreeZero

universe u

variable {A B M : Type u} [Ring A] [Ring B] [InternalGrading A] [InternalGrading B]
  [BigradedDGRing A] [BigradedDGRing B] [AddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M]
  [SMulCommClass A Bᵐᵒᵖ M]
  (G : ℤ → AddSubgroup M)
  (hl : ∀ {i j : ℤ} {a : A} {x : M}, a ∈ wgrading i → x ∈ G j → a • x ∈ G (i+j))
  (hr : ∀ {i j : ℤ} {b : B} {x : M}, b ∈ wgrading i → x ∈ G j → op b • x ∈ G (j+i))
  (X : CatModule.{u} (WeightCategory B))

local notation "D" => diagramWeightBimodule G hl hr

namespace DiagramWeightForget

theorem ofTmul_apply_self (n : ℤ) (Y : WeightCategory B)
    (g : ((D).right ⟨n⟩).obj (DGOpposite.op Y)) (y : X.obj Y) :
    ofTmul G hl hr X n Y g y n = CatTensorProduct.tmul Y g y :=
  DirectSum.of_eq_same _ _

theorem ofTmul_apply_of_ne {n n' : ℤ} (h : n' ≠ n) {Y : WeightCategory B}
    (g : ((D).right ⟨n⟩).obj (DGOpposite.op Y)) (y : X.obj Y) :
    ofTmul G hl hr X n Y g y n' = 0 :=
  DirectSum.of_eq_of_ne _ _ _ h

variable [DirectSum.Decomposition G]

/-- The summand of weight `n` of the inverse comparison on `g ⊗ z`, for `g ∈ D(n, Y)`, only sees
the summand `Y` of `z`. -/
theorem backward_tmul_apply {n : ℤ} {Y : WeightCategory B}
    (g : ((D).right ⟨n⟩).obj (DGOpposite.op Y)) (z : X.WeightSum) :
    backward G hl hr X (TensorProductOver.tmul B (coeff G hl hr g) z) n =
      CatTensorProduct.tmul Y g (z Y.as) := by
  classical
  obtain ⟨Y⟩ := Y
  induction z using DirectSum.induction_on with
  | zero =>
    rw [TensorProductOver.tmul_zero, map_zero, DirectSum.zero_apply, DirectSum.zero_apply,
      CatTensorProduct.tmul_zero]
    rfl
  | add z z' hz hz' =>
    rw [TensorProductOver.tmul_add, map_add, DirectSum.add_apply, hz, hz', DirectSum.add_apply,
      CatTensorProduct.tmul_add]
    rfl
  | of j y =>
    have hg : coeff G hl hr g ∈ G (n - Y) := (show G (n - Y) from g).property
    rw [show coeff G hl hr g = ((⟨_, hg⟩ : G (n - Y)) : M) from rfl, backward_tmul_of]
    by_cases hj : j = Y
    · subst hj
      rw [ofTmul_congr G hl hr X (show j + (n - j) = n by ring) ⟨j⟩ _ g rfl y, ofTmul_apply_self,
        DirectSum.of_eq_same]
    · rw [ofTmul_apply_of_ne G hl hr X (show n ≠ j + (n - Y) by omega)]
      have h0 : (DirectSum.of (fun k => X.obj ⟨k⟩) j y) Y = 0 :=
        DirectSum.of_eq_of_ne _ _ _ (Ne.symm hj)
      change (0 : CatTensorProduct ((D).right ⟨n⟩) X) =
        CatTensorProduct.tmul ⟨Y⟩ g ((DirectSum.of (fun k => X.obj ⟨k⟩) j y) Y)
      rw [h0, CatTensorProduct.tmul_zero]

variable {X} {X' : CatModule.{u} (WeightCategory B)}

/-- A morphism `⨁ k, X⟨k⟩ ⟶ ⨁ k, X'⟨k⟩` tensored with `M`, read through the comparisons
`⨁ n, (D ⊗ X)⟨n⟩ ≅ M ⊗_B (⨁ k, X⟨k⟩)`. -/
def conjLTensor (g : X.WeightSum →ᵈᵍ[B] X'.WeightSum) :
    ((D).tensorObj X).WeightSum →ᵈᵍ[A] ((D).tensorObj X').WeightSum :=
  (tensorWeightSumEquiv G hl hr X').symm.toDGModuleHom.comp
    ((DGModuleHom.lTensor A (InDegreeZero M) g).comp
      (tensorWeightSumEquiv G hl hr X).toDGModuleHom)

/-- **Tensoring commutes with weight-preserving parts**: the weight-preserving part of
`M ⊗_B g` is `D ⊗ (weight-preserving part of g)`. -/
theorem weightPartHom_conjLTensor (g : X.WeightSum →ᵈᵍ[B] X'.WeightSum) :
    CatModule.weightPartHom (conjLTensor G hl hr g) =
      (D).tensorMap (CatModule.weightPartHom g) := by
  refine CatModule.hom_ext fun k t => ?_
  obtain ⟨n⟩ := k
  have h : (CatModule.weightPartHom (conjLTensor G hl hr g)).app ⟨n⟩ =
      ((D).tensorMap (CatModule.weightPartHom g)).app ⟨n⟩ := by
    refine CatTensorProduct.addHom_ext (N := (D).right ⟨n⟩) (M := X) fun Y g' y => ?_
    change backward G hl hr X' (DGModuleHom.lTensor A (InDegreeZero M) g
        (forward G hl hr X (ofTmul G hl hr X n Y g' y))) n = _
    rw [forward_ofTmul, DGModuleHom.lTensor_tmul, backward_tmul_apply]
    exact ((D).tensorMap_tmul (CatModule.weightPartHom g) ⟨n⟩ Y g' y).symm
  exact DFunLike.congr_fun h t

end DiagramWeightForget

end Categorification
