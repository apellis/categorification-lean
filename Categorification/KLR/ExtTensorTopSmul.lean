/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.ExtTensorK0Equiv

/-!
# Pure tensors acting on simple tops of a tensor product algebra

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, proof of
Proposition 5.17, uses that an idempotent `e₁ ⊗ e₂` of `A ⊗ B` acts nonzero on a simple
`S_b ⊠ S_{b'}` exactly when `e₁` acts nonzero on `S_b` and `e₂` acts nonzero on `S_{b'}`.

## Main results

* `ExtTensor.exists_tmul_smul_ne_zero_iff`: over a field, `a ⊗ b` acts nonzero on `P ⊠ Q` iff
  `a` acts nonzero on `P` and `b` acts nonzero on `Q`.
* `TensorK0Hyp.exists_tmul_smul_top_ne_zero_iff`: the same for the simple top of an
  indecomposable class of `A ⊗ B` and the tops of its two factor classes.
-/

noncomputable section

namespace Categorification

open scoped TensorProduct

namespace ExtTensor

variable {k : Type*} [Field k] {A B : Type*} [Ring A] [Algebra k A] [Ring B] [Algebra k B]
  {P Q : Type*} [AddCommGroup P] [Module k P] [Module A P] [IsScalarTower k A P]
  [AddCommGroup Q] [Module k Q] [Module B Q] [IsScalarTower k B Q]

/-- Over a field, `a ⊗ b` acts nonzero on `P ⊠ Q` exactly when `a` acts nonzero on `P` and `b`
acts nonzero on `Q`. -/
theorem exists_tmul_smul_ne_zero_iff (a : A) (b : B) :
    (∃ x : ExtTensor k P Q, (a ⊗ₜ[k] b) • x ≠ 0) ↔ (∃ p : P, a • p ≠ 0) ∧ ∃ q : Q, b • q ≠ 0 := by
  constructor
  · rintro ⟨x, hx⟩
    by_contra h
    suffices hz : ∀ x : ExtTensor k P Q, (a ⊗ₜ[k] b) • x = 0 from hx (hz x)
    intro x
    induction x using ExtTensor.induction_on with
    | zero => exact smul_zero _
    | tmul p q =>
      rw [smul_tmul]
      rcases not_and_or.1 h with h | h
      · push Not at h
        rw [h p, zero_tmul]
      · push Not at h
        rw [h q, tmul_zero]
    | add x y hx' hy' => rw [smul_add, hx', hy', add_zero]
  · rintro ⟨⟨p, hp⟩, ⟨q, hq⟩⟩
    exact ⟨tmul p q, by rw [smul_tmul]; exact TensorSimple.tmul_ne_zero hp hq⟩

end ExtTensor

namespace Graded

open GProj

universe u

variable {k : Type*} [Field k] {A B : Type u} [Ring A] [Algebra k A] [Ring B] [Algebra k B]
  {𝒜 : ℤ → Submodule k A} {ℬ : ℤ → Submodule k B}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [HasGdim 𝒜] [HasGdim ℬ]

/-- A pure tensor `a ⊗ b` acts nonzero on the simple top of an indecomposable class `c` of
`A ⊗ B` exactly when `a` acts nonzero on the top of its first factor class and `b` on the top of
its second factor class. -/
theorem TensorK0Hyp.exists_tmul_smul_top_ne_zero_iff (H : TensorK0Hyp 𝒜 ℬ)
    (c : IndecClass (tensorGrading 𝒜 ℬ)) (a : A) (b : B) :
    (∃ y : c.top, (a ⊗ₜ[k] b) • y ≠ 0) ↔
      (∃ m : (H.fst c).top, a • m ≠ 0) ∧ ∃ n : (H.snd c).top, b • n ≠ 0 := by
  rw [← ExtTensor.exists_tmul_smul_ne_zero_iff (k := k)]
  obtain ⟨e⟩ := H.top_iso c
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨e.toLinearEquiv y, fun h0 => hy ?_⟩
    rw [← map_smul] at h0
    exact (LinearEquiv.map_eq_zero_iff _).1 h0
  · rintro ⟨x, hx⟩
    refine ⟨e.toLinearEquiv.symm x, fun h0 => hx ?_⟩
    rw [← map_smul] at h0
    exact (LinearEquiv.map_eq_zero_iff _).1 h0

end Graded

end Categorification
