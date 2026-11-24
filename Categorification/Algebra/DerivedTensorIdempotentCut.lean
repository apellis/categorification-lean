/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DerivedTensorOrdinaryLinear
import Categorification.Algebra.IdempotentEquiv
import Categorification.Algebra.Graded.RightTwist
import Categorification.Algebra.Graded.Tensor

/-!
# Derived tensor with an idempotent left ideal

A balanced tensor with the regular left ideal of an idempotent is the
subspace fixed by the same idempotent on the right. The ordinary
comparison identifies it with degree zero of ambient derived tensor.
-/

namespace Categorification

open CategoryTheory CategoryTheory.Limits DG DG.DerivedCategory MulOpposite TensorProductOver
open scoped DG.DegreeZero

noncomputable section
universe w
variable {k A M : Type} [Field k] [Ring A] [Algebra k A]
  [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M] [IsScalarTower k Aᵐᵒᵖ M]
  [SMulCommClass k Aᵐᵒᵖ M]

private abbrev fixed (p : A) := BalancedTensor.idemPart k M (op p)
private abbrev I (p : A) := lIdeal p
private abbrev BT (p : A) := BalancedTensor k k A M (I p)
private abbrev action (p : A) : BT (k := k) (M := M) p →ₗ[k] M :=
  (BalancedTensor.rid k k A M).toLinearMap.comp
    (BalancedTensor.mapRight (I p).subtype)

private theorem action_tmul (p : A) (m : M) (z : I p) :
    action p (BalancedTensor.tmul (k := k) (B := k) (A := A) m z) = op (z : A) • m := by
  change BalancedTensor.rid k k A M
    (BalancedTensor.mapRight (I p).subtype (BalancedTensor.tmul m z)) = _
  simp only [BalancedTensor.mapRight_tmul, BalancedTensor.rid_tmul]
  rfl

private theorem action_fixed (p : A) (z : BT (k := k) (M := M) p) :
    action p z ∈ fixed (M := M) (k := k) p := by
  induction z using BalancedTensor.induction_on with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | tmul m z =>
    rw [action_tmul]
    change op p • (op (z : A) • m) = op (z : A) • m
    rw [← mul_smul, ← op_mul, z.property]
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

/-- Tensoring a right module with the left projective of an idempotent
extracts its fixed subspace at that idempotent. -/
def balancedTensorLeftIdealEquiv {p : A} (hp : IsIdempotentElem p) :
    BT (k := k) (M := M) p ≃ₗ[k] fixed (k := k) (M := M) p := by
  let e : I p := ⟨p, hp.eq⟩
  let f := (action (M := M) (k := k) p).codRestrict _ (action_fixed p)
  let g := (((BalancedTensor.mkBil k k A M (I p)).flip e).comp
    (fixed (M := M) (k := k) p).subtype)
  refine LinearEquiv.ofLinearMap f g ?_ ?_
  · apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact (action_tmul p (x : M) e).trans x.property
  · apply BalancedTensor.ext
    intro m z
    change BalancedTensor.tmul (action p (BalancedTensor.tmul (k := k) (B := k) (A := A) m z)) e = _
    rw [action_tmul, BalancedTensor.op_smul_tmul]
    congr 1
    exact Subtype.ext z.property

section Graded

open Categorification.Graded

variable {𝒜 : ℤ → Submodule k A} {𝓜 : ℤ → Submodule k M}

variable [SetLike.GradedSMul (oppositeGrade 𝒜) 𝓜] in

/-- At the actual idempotent cut, the balanced comparison preserves the
sum of the two diagram degrees. -/
theorem balancedTensorLeftIdealEquiv_preservesGrading {p : A} (hp : IsIdempotentElem p) :
    PreservesGrading (balancedGrading k A 𝓜 (Graded.submodule 𝒜 (lIdeal p)))
      (Graded.idem 𝓜 (op p)) (balancedTensorLeftIdealEquiv hp).toLinearMap := by
  intro d x hx
  apply balancedGrading_map_mem _ _ ?_ hx
  intro i j m z hm hz
  change action p (BalancedTensor.tmul m z) ∈ 𝓜 (i + j)
  rw [action_tmul]
  have hz' : op (z : A) ∈ oppositeGrade 𝒜 j := hz
  have h := SetLike.GradedSMul.smul_mem (A := oppositeGrade 𝒜) hz' hm
  change op (z : A) • m ∈ 𝓜 (j + i) at h
  simpa only [add_comm j i] using h

/-- When the idempotent is homogeneous of degree zero, the inverse
fixed-cut comparison preserves degree as well. -/
theorem balancedTensorLeftIdealEquiv_symm_preservesGrading {p : A} (hp : IsIdempotentElem p)
    (hp₀ : p ∈ 𝒜 0) :
    PreservesGrading (Graded.idem 𝓜 (op p))
      (balancedGrading k A 𝓜 (Graded.submodule 𝒜 (lIdeal p)))
      (balancedTensorLeftIdealEquiv hp).symm.toLinearMap := by
  intro d z hz
  let e : lIdeal p := ⟨p,hp.eq⟩
  change (BalancedTensor.tmul z.val e : BT (k := k) (M := M) p) ∈
    balancedGrading k A 𝓜 (Graded.submodule 𝒜 (lIdeal p)) d
  have hx : z.val ∈ 𝓜 d := hz
  have he : e ∈ Graded.submodule 𝒜 (lIdeal p) 0 := hp₀
  simpa only [add_zero] using tmul_mem_balancedGrading (B := k) hx he

end Graded

variable [HasDerivedCategory.{w,0} A] [HasDerivedCategory.{w,0} k]

private def tensorComparison (hM : ∀ (c : k) (m : M), op (algebraMap k A c) • m = c • m)
    (p : A) : TensorProductOver A M (I p) ≃ₗ[k] BT (k := k) (M := M) p where
  __ := ordinaryBalancedTensorAddEquiv (A := k) hM
  map_smul' c z := by
    let e := ordinaryBalancedTensorAddEquiv (A := k) (N := I p) hM
    change e (c • z) = c • e z
    induction z using TensorProductOver.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | tmul m z => rfl
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]

/-- Degree-zero ambient derived tensor with a left idempotent projective
is the actual fixed subspace of the right module. -/
def ambientDerivedTensorH0LeftIdealEquiv
    (hM : ∀ (c : k) (m : M), op (algebraMap k A c) • m = c • m)
    {p : A} (hp : IsIdempotentElem p) :
    (homologyFunctor k 0).obj
        ((derivedTensor k A M).obj (Q.obj (DGModuleCat.of A (InDegreeZero (I p))))) ≃ₗ[k]
      fixed (k := k) (M := M) p :=
  (ambientDerivedTensorH0Equiv (k := k) (A := A) (N := M) (I p)).trans
    ((tensorComparison hM p).trans (balancedTensorLeftIdealEquiv hp))

end
end Categorification
