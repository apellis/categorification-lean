/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.CornerTensor

/-!
# Refining a corner tensor product through an intermediate idempotent

Let `e₂, e₁, e', e₀` be idempotents of a `k`-algebra `A`. Suppose that multiplication
`e₂Ae₁ ⊗ e₁Ae' → e₂Ae'` is an isomorphism and that `e₁Ae' ⊗ e'Ae₀ → e₁Ae₀` is onto. Then the
multiplication `e₂Ae₁ ⊗ e₁Ae₀ → A` factors as `e₂Ae₁ ⊗ e₁Ae₀ ↞ e₂Ae' ⊗ e'Ae₀ → A`, through a
surjection (`factorMap`). Hence it is injective, or onto `e₂Ae₀`, as soon as
`e₂Ae' ⊗ e'Ae₀ → A` is (`mult_injective_of_factor`, `exists_mult_eq_of_factor`).

This is the induction step in the proof of Webster's Lemma 6.5 (arXiv:1309.3796v2): the tensor
product `B̃_w ⊗ B̃_{w'}` is compared with `B̃_{ww'}` one red crossing of `w'` at a time.

## Main definitions and results

* `CornerTensor.lmul` : `e₁Ae' ⊗ e'Ae₀ → fAe' ⊗ e'Ae₀`, `y ⊗ z ↦ x e₁ y ⊗ z`.
* `CornerTensor.rmul` : `e₂Ae₁ ⊗ e₁Ae' → e₂Ae₁ ⊗ e₁Ag`, `y ⊗ z ↦ y ⊗ z e' x`.
* `CornerTensor.factorMap` : `e₂Ae' ⊗ e'Ae₀ → e₂Ae₁ ⊗ e₁Ae₀`, `x ⊗ z ↦ s(x) e' z`, for a
  section `s` of `e₂Ae₁ ⊗ e₁Ae' → e₂Ae'`.
* `CornerTensor.mult_injective_of_factor`, `CornerTensor.exists_mult_eq_of_factor`.
-/

namespace Categorification

open scoped TensorProduct

noncomputable section

namespace CornerTensor

variable {k : Type*} [CommRing k] {A : Type*} [Ring A] [Algebra k A]

theorem mul_idem {e : A} (h : IsIdempotentElem e) (a : A) : a * e * e = a * e := by
  rw [mul_assoc, h.eq]

/-- Only the corner part of the second factor matters. -/
theorem tmul_corner_right {e₂ e₁ e₀ : A} (h₁ : IsIdempotentElem e₁) (h₀ : IsIdempotentElem e₀)
    (x y : A) : (tmul x (e₁ * y * e₀) : CornerTensor k A e₂ e₁ e₀) = tmul x y := by
  rw [tmul_corner x (e₁ * y * e₀), tmul_corner x y]
  simp only [← mul_assoc, h₁.eq, mul_idem h₀]

section LMul

variable {e₁ e' e₀ : A} (f : A) (h₁ : IsIdempotentElem e₁) (h' : IsIdempotentElem e')
  (h₀ : IsIdempotentElem e₀)

include h₁ h' h₀ in
/-- Left multiplication `y ⊗ z ↦ x e₁ y ⊗ z`. -/
def lmul (x : A) : CornerTensor k A e₁ e' e₀ →ₗ[k] CornerTensor k A f e' e₀ :=
  (rel k A e₁ e' e₀).liftQ
    (TensorProduct.lift ((tmulₗ k A f e' e₀).comp (LinearMap.mulLeft k (x * e₁)))) <| by
    rw [rel, Submodule.span_le]
    rintro t (⟨y, z, rfl⟩ | ⟨y, c, z, rfl⟩) <;>
      simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, TensorProduct.lift.tmul,
        LinearMap.comp_apply, LinearMap.mulLeft_apply, sub_eq_zero]
    · change (tmul (x * e₁ * y) z : CornerTensor k A f e' e₀) =
        tmul (x * e₁ * (e₁ * y * e')) (e' * z * e₀)
      rw [tmul_corner (x * e₁ * y) z, tmul_corner (x * e₁ * (e₁ * y * e')) (e' * z * e₀)]
      simp only [← mul_assoc, h'.eq, mul_idem h₁, mul_idem h', mul_idem h₀]
    · change (tmul (x * e₁ * (y * (e' * c * e'))) z : CornerTensor k A f e' e₀) =
        tmul (x * e₁ * y) (e' * c * e' * z)
      rw [← tmul_balance]
      simp only [mul_assoc]

theorem lmul_tmul (x y z : A) :
    lmul f h₁ h' h₀ x (tmul y z : CornerTensor k A e₁ e' e₀) = tmul (x * e₁ * y) z := by
  simp [lmul, tmul, tmulₗ, mkQ, mul_assoc]

theorem mult_lmul (hf : IsIdempotentElem f) (x : A) (t : CornerTensor k A e₁ e' e₀) :
    mult hf h' h₀ (lmul f h₁ h' h₀ x t) = f * x * mult h₁ h' h₀ t := by
  induction t using induction_on with
  | tmul y z =>
    rw [lmul_tmul, mult_tmul, mult_tmul]
    simp only [← mul_assoc]
  | add s t hs ht => rw [map_add, map_add, hs, ht, map_add, mul_add]

end LMul

section RMul

variable {e₂ e₁ e' : A} (g : A) (h₂ : IsIdempotentElem e₂) (h₁ : IsIdempotentElem e₁)
  (h' : IsIdempotentElem e')

include h₂ h₁ h' in
/-- Right multiplication `y ⊗ z ↦ y ⊗ z e' x`. -/
def rmul (x : A) : CornerTensor k A e₂ e₁ e' →ₗ[k] CornerTensor k A e₂ e₁ g :=
  (rel k A e₂ e₁ e').liftQ
    (TensorProduct.lift ((LinearMap.lcomp k _ (LinearMap.mulRight k (e' * x))).comp
      (tmulₗ k A e₂ e₁ g))) <| by
    rw [rel, Submodule.span_le]
    rintro t (⟨y, z, rfl⟩ | ⟨y, c, z, rfl⟩) <;>
      simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, TensorProduct.lift.tmul,
        LinearMap.comp_apply, LinearMap.lcomp_apply, LinearMap.mulRight_apply, sub_eq_zero]
    · change (tmul y (z * (e' * x)) : CornerTensor k A e₂ e₁ g) =
        tmul (e₂ * y * e₁) (e₁ * z * e' * (e' * x))
      rw [tmul_corner y (z * (e' * x)), tmul_corner (e₂ * y * e₁) (e₁ * z * e' * (e' * x))]
      simp only [← mul_assoc, h₂.eq, h₁.eq, mul_idem h₁, mul_idem h']
    · change (tmul (y * (e₁ * c * e₁)) (z * (e' * x)) : CornerTensor k A e₂ e₁ g) =
        tmul y (e₁ * c * e₁ * z * (e' * x))
      rw [tmul_balance]
      simp only [mul_assoc]

theorem rmul_tmul (x y z : A) :
    rmul g h₂ h₁ h' x (tmul y z : CornerTensor k A e₂ e₁ e') = tmul y (z * e' * x) := by
  simp [rmul, tmul, tmulₗ, mkQ, mul_assoc]

theorem mult_rmul (hg : IsIdempotentElem g) (x : A) (t : CornerTensor k A e₂ e₁ e') :
    mult h₂ h₁ hg (rmul g h₂ h₁ h' x t) = mult h₂ h₁ h' t * x * g := by
  induction t using induction_on with
  | tmul y z =>
    rw [rmul_tmul, mult_tmul, mult_tmul]
    simp only [← mul_assoc]
  | add s t hs ht => rw [map_add, map_add, hs, ht, map_add, add_mul, add_mul]

theorem rmul_add (x x' : A) :
    rmul (k := k) g h₂ h₁ h' (x + x') = rmul g h₂ h₁ h' x + rmul g h₂ h₁ h' x' := by
  refine ext fun y z => ?_
  rw [LinearMap.add_apply, rmul_tmul, rmul_tmul, rmul_tmul, mul_add, tmul_add_right]

theorem rmul_smul (r : k) (x : A) :
    rmul (k := k) g h₂ h₁ h' (r • x) = r • rmul g h₂ h₁ h' x := by
  refine ext fun y z => ?_
  rw [LinearMap.smul_apply, rmul_tmul, rmul_tmul, mul_smul_comm, tmul_smul_right]

end RMul

section Factor

variable {e₂ e₁ e' e₀ : A} (h₂ : IsIdempotentElem e₂) (h₁ : IsIdempotentElem e₁)
  (h' : IsIdempotentElem e') (h₀ : IsIdempotentElem e₀)
  (s : A →ₗ[k] CornerTensor k A e₂ e₁ e') (hs : ∀ x, mult h₂ h₁ h' (s x) = e₂ * x * e')
  (hinj : Function.Injective (mult h₂ h₁ h' : CornerTensor k A e₂ e₁ e' →ₗ[k] A))

include hs hinj in
theorem section_eq (x : A) (t : CornerTensor k A e₂ e₁ e')
    (ht : mult h₂ h₁ h' t = e₂ * x * e') : s x = t :=
  hinj (by rw [hs, ht])

/-- The bilinear map `x, z ↦ s(x) e' z`. -/
def factorMapₗ : A →ₗ[k] A →ₗ[k] CornerTensor k A e₂ e₁ e₀ :=
  LinearMap.mk₂ k (fun x z => rmul e₀ h₂ h₁ h' z (s x))
    (fun x x' z => by rw [map_add, map_add])
    (fun r x z => by rw [map_smul, map_smul])
    (fun x z z' => by rw [rmul_add, LinearMap.add_apply])
    (fun r x z => by rw [rmul_smul, LinearMap.smul_apply])

include hs hinj h₀ in
/-- The map `e₂Ae' ⊗ e'Ae₀ → e₂Ae₁ ⊗ e₁Ae₀`, `x ⊗ z ↦ s(x) e' z`. -/
def factorMap : CornerTensor k A e₂ e' e₀ →ₗ[k] CornerTensor k A e₂ e₁ e₀ :=
  (rel k A e₂ e' e₀).liftQ (TensorProduct.lift (factorMapₗ h₂ h₁ h' s)) <| by
    rw [rel, Submodule.span_le]
    rintro t (⟨x, z, rfl⟩ | ⟨x, c, z, rfl⟩) <;>
      simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, TensorProduct.lift.tmul,
        factorMapₗ, LinearMap.mk₂_apply, sub_eq_zero]
    · rw [section_eq h₂ h₁ h' s hs hinj (e₂ * x * e') (s x)
        (by rw [hs]; simp only [← mul_assoc, h₂.eq, mul_idem h'])]
      congr 1
      refine ext fun y w => ?_
      rw [rmul_tmul, rmul_tmul, ← tmul_corner_right h₁ h₀ y (w * e' * (e' * z * e₀)),
        ← tmul_corner_right h₁ h₀ y (w * e' * z)]
      simp only [← mul_assoc, mul_idem h', mul_idem h₀]
    · have hc : s (x * (e' * c * e')) = rmul e' h₂ h₁ h' (e' * c * e') (s x) :=
        section_eq h₂ h₁ h' s hs hinj _ _ (by
          rw [mult_rmul _ h₂ h₁ h' h', hs]
          simp only [← mul_assoc, mul_idem h'])
      rw [hc]
      induction s x using induction_on with
      | tmul y w =>
        rw [rmul_tmul, rmul_tmul, rmul_tmul]
        simp only [← mul_assoc, mul_idem h']
      | add t t' ht ht' => rw [map_add, map_add, map_add, ht, ht']

theorem factorMap_tmul (x z : A) :
    factorMap h₂ h₁ h' h₀ s hs hinj (tmul x z : CornerTensor k A e₂ e' e₀) =
      rmul e₀ h₂ h₁ h' z (s x) := by
  rw [tmul_def, factorMap, mkQ, Submodule.mkQ_apply, Submodule.liftQ_apply,
    TensorProduct.lift.tmul]
  rfl

/-- The factorization of the multiplication map. -/
theorem mult_factorMap (t : CornerTensor k A e₂ e' e₀) :
    mult h₂ h₁ h₀ (factorMap h₂ h₁ h' h₀ s hs hinj t) = mult h₂ h' h₀ t := by
  induction t using induction_on with
  | tmul x z =>
    rw [factorMap_tmul, mult_rmul _ h₂ h₁ h' h₀, hs, mult_tmul]
  | add t t' ht ht' => rw [map_add, map_add, ht, ht', map_add]

theorem factorMap_lmul (x : A) (t : CornerTensor k A e₁ e' e₀) :
    factorMap h₂ h₁ h' h₀ s hs hinj (lmul e₂ h₁ h' h₀ x t) = tmul x (mult h₁ h' h₀ t) := by
  induction t using induction_on with
  | tmul y z =>
    rw [lmul_tmul, factorMap_tmul, section_eq h₂ h₁ h' s hs hinj (x * e₁ * y) (tmul x (e₁ * y))
      (by rw [mult_tmul]; simp only [← mul_assoc, mul_idem h₁]), rmul_tmul, mult_tmul,
      ← tmul_corner_right h₁ h₀ x (e₁ * y * e' * z),
      ← tmul_corner_right h₁ h₀ x (e₁ * y * e' * z * e₀)]
    simp only [← mul_assoc, h₁.eq, mul_idem h₀]
  | add t t' ht ht' => rw [map_add, map_add, ht, ht', map_add, tmul_add_right]

include h₂ h' hs hinj in
/-- If `e₁Ae' ⊗ e'Ae₀ → e₁Ae₀` is onto, `factorMap` is onto. -/
theorem factorMap_surjective
    (hsurj : ∀ y, ∃ t : CornerTensor k A e₁ e' e₀, mult h₁ h' h₀ t = e₁ * y * e₀) :
    Function.Surjective (factorMap h₂ h₁ h' h₀ s hs hinj) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← span_tmul, Submodule.span_le]
  rintro _ ⟨x, y, rfl⟩
  obtain ⟨t, ht⟩ := hsurj y
  refine ⟨lmul e₂ h₁ h' h₀ x t, ?_⟩
  rw [factorMap_lmul, ht, tmul_corner_right h₁ h₀]

include hs hinj in
/-- **Refinement.** If `e₂Ae₁ ⊗ e₁Ae' → e₂Ae'` is injective with section `s`, `e₁Ae' ⊗ e'Ae₀ →
e₁Ae₀` is onto and `e₂Ae' ⊗ e'Ae₀ → A` is injective, then `e₂Ae₁ ⊗ e₁Ae₀ → A` is injective. -/
theorem mult_injective_of_factor
    (hsurj : ∀ y, ∃ t : CornerTensor k A e₁ e' e₀, mult h₁ h' h₀ t = e₁ * y * e₀)
    (hinj' : Function.Injective (mult h₂ h' h₀ : CornerTensor k A e₂ e' e₀ →ₗ[k] A)) :
    Function.Injective (mult h₂ h₁ h₀ : CornerTensor k A e₂ e₁ e₀ →ₗ[k] A) := by
  intro t t' htt
  obtain ⟨u, rfl⟩ := factorMap_surjective h₂ h₁ h' h₀ s hs hinj hsurj t
  obtain ⟨u', rfl⟩ := factorMap_surjective h₂ h₁ h' h₀ s hs hinj hsurj t'
  rw [mult_factorMap, mult_factorMap] at htt
  rw [hinj' htt]

include hs hinj in
/-- The same refinement for surjectivity onto the corner `e₂Ae₀`. -/
theorem exists_mult_eq_of_factor
    (hsurj' : ∀ y, ∃ t : CornerTensor k A e₂ e' e₀, mult h₂ h' h₀ t = e₂ * y * e₀) (y : A) :
    ∃ t : CornerTensor k A e₂ e₁ e₀, mult h₂ h₁ h₀ t = e₂ * y * e₀ := by
  obtain ⟨u, hu⟩ := hsurj' y
  exact ⟨factorMap h₂ h₁ h' h₀ s hs hinj u, by rw [mult_factorMap, hu]⟩

end Factor

end CornerTensor

end

end Categorification
