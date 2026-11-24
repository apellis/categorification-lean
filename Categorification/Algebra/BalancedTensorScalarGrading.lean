/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DerivedTensorHomology
import Categorification.Algebra.Graded.Tensor

/-!
# The tensor grading under central scalar restriction

The additive comparison of the integer and ground-ring balanced
tensors identifies their total degree components. This lets diagram
weight coends use graded calculations over the ground field.
-/

noncomputable section

namespace Categorification.Graded

open MulOpposite
open scoped TensorProduct

variable {k A M N : Type*} [CommRing k] [Ring A] [Algebra k A]
  [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M] [SMulCommClass k Aᵐᵒᵖ M]
  [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
  (hM : ∀ (c : k) (m : M), op (algebraMap k A c) • m = c • m)
  (G : ℤ → Submodule k M) (H : ℤ → Submodule k N)

private theorem integer_action (c : ℤ) (m : M) : op (algebraMap ℤ A c) • m = c • m := by
  change op (c : A) • m = c • m
  rw [op_intCast, Int.cast_smul_eq_zsmul]

/-- Restricting the coefficient ring of a balanced tensor to integers leaves its
underlying additive group unchanged. -/
def balancedTensorIntScalarAddEquiv :
    BalancedTensor ℤ ℤ A M N ≃+ BalancedTensor k k A M N :=
  (ordinaryBalancedTensorAddEquiv (k := ℤ) (A := ℤ) (B := A) (N := N)
    (integer_action (A := A))).symm.trans
      (ordinaryBalancedTensorAddEquiv (A := k) hM)

@[simp] theorem balancedTensorIntScalarAddEquiv_tmul (m : M) (n : N) :
    balancedTensorIntScalarAddEquiv hM (BalancedTensor.tmul m n) =
      BalancedTensor.tmul m n := by
  change ordinaryBalancedTensorAddEquiv (A := k) hM
    ((ordinaryBalancedTensorAddEquiv (k := ℤ) (A := ℤ) (B := A) (N := N) (integer_action (A := A))).symm (BalancedTensor.tmul m n)) = _
  rw [← ordinaryBalancedTensorAddEquiv_tmul (k := ℤ) (A := ℤ) (B := A) (integer_action (A := A)) m n, AddEquiv.symm_apply_apply,
    ordinaryBalancedTensorAddEquiv_tmul]

section Span

variable {R : Type*} [CommRing R] [Module R M] [Module R N]
  (G' : ℤ → Submodule R M) (H' : ℤ → Submodule R N)

-- Both gradings are spanned by the homogeneous pure tensors.
private theorem balancedGrading_eq_span (d : ℤ) :
    balancedGrading R A G' H' d = Submodule.span R
      {t | ∃ (i j : ℤ) (m : M) (n : N), i + j = d ∧
        m ∈ G' i ∧ n ∈ H' j ∧ BalancedTensor.tmul m n = t} := by
  change Submodule.map ((BalancedTensor.mk R R A M N).restrictScalars R)
    (Submodule.span R _) = _
  rw [Submodule.map_span]
  congr 1
  ext t
  constructor
  · rintro ⟨_, ⟨i, j, m, n, hd, hm, hn, rfl⟩, rfl⟩
    exact ⟨i, j, m, n, hd, hm, hn, rfl⟩
  · rintro ⟨i, j, m, n, hd, hm, hn, rfl⟩
    exact ⟨m ⊗ₜ[R] n, ⟨i, j, m, n, hd, hm, hn, rfl⟩, rfl⟩

end Span

private theorem spanInt_toAddSubgroup {V : Type*} [AddCommGroup V] (inst : Module ℤ V)
    (s : Set V) :
    letI := inst
    (Submodule.span ℤ s).toAddSubgroup = AddSubgroup.closure s := by
  obtain rfl : inst = AddCommGroup.uniqueIntModule.default := Subsingleton.elim _ _
  exact Submodule.span_int_eq_addSubgroupClosure s

/-- The additive comparison of scalar rings preserves the total degree. -/
theorem balancedTensorIntScalarAddEquiv_map_grade (d : ℤ) :
    ((balancedGrading ℤ A (fun i => (G i).restrictScalars ℤ)
      (fun i => (H i).restrictScalars ℤ) d).toAddSubgroup.map
        (balancedTensorIntScalarAddEquiv hM).toAddMonoidHom) =
      (balancedGrading k A G H d).toAddSubgroup := by
  let e := balancedTensorIntScalarAddEquiv (N := N) hM
  let P₀ : Set (BalancedTensor ℤ ℤ A M N) := {t |
    ∃ (i j : ℤ) (m : M) (n : N), i + j = d ∧ m ∈ G i ∧ n ∈ H j ∧
      BalancedTensor.tmul m n = t}
  let P : Set (BalancedTensor k k A M N) := {t |
    ∃ (i j : ℤ) (m : M) (n : N), i + j = d ∧ m ∈ G i ∧ n ∈ H j ∧
      BalancedTensor.tmul m n = t}
  have hP : e '' P₀ = P := by
    ext t
    constructor
    · rintro ⟨_, ⟨i, j, m, n, hd, hm, hn, rfl⟩, rfl⟩
      exact ⟨i, j, m, n, hd, hm, hn, (balancedTensorIntScalarAddEquiv_tmul hM m n).symm⟩
    · rintro ⟨i, j, m, n, hd, hm, hn, rfl⟩
      exact ⟨_, ⟨i, j, m, n, hd, hm, hn, rfl⟩, balancedTensorIntScalarAddEquiv_tmul hM m n⟩
  rw [balancedGrading_eq_span, balancedGrading_eq_span]
  change ((Submodule.span ℤ P₀).toAddSubgroup.map e.toAddMonoidHom) =
    (Submodule.span k P).toAddSubgroup
  calc
    _ = AddSubgroup.closure (e '' P₀) :=
      (congrArg (AddSubgroup.map e.toAddMonoidHom)
        (spanInt_toAddSubgroup (inferInstance : Module ℤ (BalancedTensor ℤ ℤ A M N)) P₀)).trans
        (AddMonoidHom.map_closure e.toAddMonoidHom P₀)
    _ = AddSubgroup.closure P := congrArg AddSubgroup.closure hP
    _ = (Submodule.span k P).toAddSubgroup := by
        let W : Submodule k (BalancedTensor k k A M N) :=
          { AddSubgroup.closure P with
            smul_mem' := fun c t ht => by
              induction ht using AddSubgroup.closure_induction with
              | mem x hx =>
                obtain ⟨i, j, m, n, hd, hm, hn, rfl⟩ := hx
                exact AddSubgroup.subset_closure ⟨i, j, c • m, n, hd, (G i).smul_mem _ hm, hn,
                  BalancedTensor.smul_tmul c m n⟩
              | zero => rw [smul_zero]; exact (AddSubgroup.closure P).zero_mem
              | add x y _ _ hx hy => rw [smul_add]; exact (AddSubgroup.closure P).add_mem hx hy
              | neg x _ hx => rw [smul_neg]; exact (AddSubgroup.closure P).neg_mem hx }
        apply le_antisymm
        · exact (AddSubgroup.closure_le ((Submodule.span k P).toAddSubgroup)).mpr (fun _ h => Submodule.subset_span h)
        · exact (show Submodule.span k P ≤ W from
            Submodule.span_le.mpr (fun _ h => AddSubgroup.subset_closure h))

end Categorification.Graded
