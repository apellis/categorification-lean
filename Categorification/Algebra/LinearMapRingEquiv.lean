/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Ring.Equiv

/-!
# Linear maps along a ring isomorphism

For a ring isomorphism `σ : R ≃+* S`, `R`-modules `P`, `Q`, `S`-modules `P'`, `Q'` and additive
isomorphisms `e : P ≃+ P'`, `e' : Q ≃+ Q'` that are semilinear along `σ`, composing with `e` and
`e'` is a bijection between `R`-linear maps `P → Q` and `S`-linear maps `P' → Q'`
(`LinearMap.ringEquivCongr`). This moves adjunctions between module functors along the
identifications of rings used for Webster's functors on modules.
-/

namespace Categorification

variable {R S : Type*} [Semiring R] [Semiring S] (σ : R ≃+* S)
  {P Q P' Q' : Type*} [AddCommMonoid P] [AddCommMonoid Q] [AddCommMonoid P'] [AddCommMonoid Q']
  [Module R P] [Module R Q] [Module S P'] [Module S Q']
  (e : P ≃+ P') (e' : Q ≃+ Q')
  (he : ∀ (r : R) (p : P), e (r • p) = σ r • e p)
  (he' : ∀ (r : R) (q : Q), e' (r • q) = σ r • e' q)

include he in
theorem symm_smul_of_semilinear (s : S) (p' : P') : e.symm (s • p') = σ.symm s • e.symm p' := by
  apply e.injective
  rw [he, σ.apply_symm_apply, e.apply_symm_apply, e.apply_symm_apply]

/-- Linear maps along a ring isomorphism: `f ↦ e' ∘ f ∘ e⁻¹`. -/
def LinearMap.ringEquivCongr : (P →ₗ[R] Q) ≃ (P' →ₗ[S] Q') where
  toFun f :=
    { toFun := fun p' => e' (f (e.symm p'))
      map_add' := fun x y => by rw [map_add, map_add, map_add]
      map_smul' := fun s p' => by
        rw [RingHom.id_apply, symm_smul_of_semilinear σ e he, f.map_smul, he',
          σ.apply_symm_apply] }
  invFun g :=
    { toFun := fun p => e'.symm (g (e p))
      map_add' := fun x y => by rw [map_add, map_add, map_add]
      map_smul' := fun r p => by
        rw [RingHom.id_apply, he, g.map_smul, symm_smul_of_semilinear σ e' he',
          σ.symm_apply_apply] }
  left_inv f := by
    ext p
    simp only [LinearMap.coe_mk, AddHom.coe_mk, AddEquiv.symm_apply_apply]
  right_inv g := by
    ext p'
    simp only [LinearMap.coe_mk, AddHom.coe_mk, AddEquiv.apply_symm_apply]

theorem LinearMap.ringEquivCongr_apply (f : P →ₗ[R] Q) (p' : P') :
    LinearMap.ringEquivCongr σ e e' he he' f p' = e' (f (e.symm p')) := rfl

theorem LinearMap.ringEquivCongr_symm_apply (g : P' →ₗ[S] Q') (p : P) :
    (LinearMap.ringEquivCongr σ e e' he he').symm g p = e'.symm (g (e p)) := rfl

end Categorification
