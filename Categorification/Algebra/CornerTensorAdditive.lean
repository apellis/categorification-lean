/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.CornerTensor

/-!
# Additive maps from the corner tensor

A bi-additive family that respects ground scalars, sandwiching, and
middle balancing descends to the ordinary corner tensor, with arbitrary
additive target.
-/

noncomputable section

namespace Categorification.CornerTensor

open scoped TensorProduct

variable {k A P : Type*} [CommRing k] [Ring A] [Algebra k A] [AddCommGroup P]
  (e₂ e₁ e₀ : A) (F : A →+ A →+ P)
  (hs : ∀ (c : k) (x y : A), F (c • x) y = F x (c • y))
  (hc : ∀ x y, F x y = F (e₂ * x * e₁) (e₁ * y * e₀))
  (hb : ∀ x c y, F (x * (e₁ * c * e₁)) y = F x ((e₁ * c * e₁) * y))

include hc hb in
private theorem rel_le_additiveKer :
    (rel k A e₂ e₁ e₀).toAddSubgroup ≤ (TensorProduct.liftAddHom F hs).ker := by
  let g := TensorProduct.liftAddHom F hs
  let K : Submodule k (A ⊗[k] A) :=
    { carrier := {t | ∀ r : k, g (r • t) = 0}
      zero_mem' := fun r => by simp [map_zero]
      add_mem' := fun hx hy r => by rw [smul_add, map_add, hx r, hy r, add_zero]
      smul_mem' := fun r _ ht c => by rw [smul_smul]; exact ht (c * r) }
  have hK : rel k A e₂ e₁ e₀ ≤ K := by
    apply Submodule.span_le.mpr
    rintro _ (⟨x, y, rfl⟩ | ⟨x, b, y, rfl⟩) c
    · simp only [g, smul_sub, map_sub, TensorProduct.smul_tmul', TensorProduct.liftAddHom_tmul]
      rw [← smul_mul_assoc, ← mul_smul_comm, hc (c • x) y, sub_self]
    · simp only [g, smul_sub, map_sub, TensorProduct.smul_tmul', TensorProduct.liftAddHom_tmul]
      rw [← smul_mul_assoc, hb (c • x) b y, sub_self]
  intro t ht
  change g t = 0
  simpa only [one_smul] using hK ht 1

/-- The additive universal property of the ordinary corner tensor. -/
def liftAdd : CornerTensor k A e₂ e₁ e₀ →+ P :=
  QuotientAddGroup.lift (rel k A e₂ e₁ e₀).toAddSubgroup (TensorProduct.liftAddHom F hs)
    (rel_le_additiveKer e₂ e₁ e₀ F hs hc hb)

theorem liftAdd_tmul (x y : A) :
    liftAdd e₂ e₁ e₀ F hs hc hb (tmul x y) = F x y :=
  TensorProduct.liftAddHom_tmul F hs x y

end Categorification.CornerTensor
