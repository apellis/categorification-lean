/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.K0Map
import Categorification.Algebra.Graded.HomFormEquiv

/-!
# Graded `K₀` and graded Hom under a graded isomorphism of algebras

Let `σ : A ≃ₐ[k] A'` be an isomorphism of `k`-algebras which, together with its inverse,
preserves the gradings `𝒜` and `𝒜'`. Restriction along `σ` (`GProj.restrict`, `K0.map`) is
then an isomorphism of graded Grothendieck groups `K₀(A) ≅ K₀(A')` of `ℤ[q, q⁻¹]`-modules
preserving the Euler form `([P], [Q]) ↦ gdim HOM(P, Q)`.

This is the formal device behind the passage between graded left and graded right projectives
along a graded anti-involution (Webster, arXiv:1309.3796v2, §4.7, which works with right
modules), see `K0.rightTwistEquiv`.

## Main definitions and results

* `GProj.restrictRestrict` : restricting back along `σ⁻¹` recovers `P`.
* `K0.restrictEquiv` : `K₀(A) ≃ K₀(A')` as `ℤ[q, q⁻¹]`-modules, `[P] ↦ [P]`.
* `K0.homForm_restrictEquiv` : it preserves the Euler form (`K0.homForm_map`).
-/

universe u v

noncomputable section

namespace Categorification.Graded

open GProj

section K0Restrict

variable {k : Type v} [CommRing k] {A A' : Type u} [Ring A] [Algebra k A] [Ring A']
  [Algebra k A'] {𝒜 : ℤ → Submodule k A} {𝒜' : ℤ → Submodule k A'}
  (σ : A ≃ₐ[k] A') (hσ : ∀ ⦃d : ℤ⦄ ⦃a : A'⦄, a ∈ 𝒜' d → σ.symm a ∈ 𝒜 d)
  (hσ' : ∀ ⦃d : ℤ⦄ ⦃a : A⦄, a ∈ 𝒜 d → σ.symm.symm a ∈ 𝒜' d)

/-- Restricting along `σ` and then along `σ⁻¹` recovers `P`. -/
def GProj.restrictRestrict (P : GProj 𝒜) : (restrict σ.symm hσ' (restrict σ hσ P)).Iso P where
  toLinearEquiv :=
    { AddEquiv.refl P.carrier with
      map_smul' := fun a x => by
        change (σ.symm (σ.symm.symm a) • (show P.carrier from x) : P.carrier) =
          (a • (show P.carrier from x) : P.carrier)
        rw [AlgEquiv.symm_symm, AlgEquiv.symm_apply_apply] }
  map_mem' _ _ hx := hx
  symm_map_mem' _ _ hy := hy

namespace K0

theorem map_symm_map (x : K0 𝒜) : map σ.symm hσ' (map σ hσ x) = x := by
  induction x using induction_on with
  | of P =>
    rw [map_of, map_of]
    exact of_eq_of_iso (restrictRestrict σ hσ hσ' P)
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | neg x hx => simp [hx]

/-- **Restriction along a graded algebra isomorphism identifies the graded Grothendieck
groups** as `ℤ[q, q⁻¹]`-modules. -/
def restrictEquiv : K0 𝒜 ≃ₗ[LaurentPolynomial ℤ] K0 𝒜' :=
  { map σ hσ with
    invFun := map σ.symm hσ'
    left_inv := map_symm_map σ hσ hσ'
    right_inv := map_symm_map σ.symm hσ' hσ }

@[simp] theorem restrictEquiv_of (P : GProj 𝒜) :
    restrictEquiv σ hσ hσ' (of P) = of (restrict σ hσ P) := map_of σ hσ P

end K0

end K0Restrict

/-- **Restriction preserves the Euler form** `([P], [Q]) ↦ gdim HOM(P, Q)` on `K₀`. -/
theorem K0.homForm_restrictEquiv {k : Type v} [Field k] {A A' : Type u} [Ring A] [Algebra k A]
    [Ring A'] [Algebra k A'] {𝒜 : ℤ → Submodule k A} {𝒜' : ℤ → Submodule k A'}
    [GradedAlgebra 𝒜] [HasGdim 𝒜] [GradedAlgebra 𝒜'] [HasGdim 𝒜'] (σ : A ≃ₐ[k] A')
    (hσ : ∀ ⦃d : ℤ⦄ ⦃a : A'⦄, a ∈ 𝒜' d → σ.symm a ∈ 𝒜 d)
    (hσ' : ∀ ⦃d : ℤ⦄ ⦃a : A⦄, a ∈ 𝒜 d → σ.symm.symm a ∈ 𝒜' d) (x y : K0 𝒜) :
    K0.homForm 𝒜' (K0.restrictEquiv σ hσ hσ' x) (K0.restrictEquiv σ hσ hσ' y) =
      K0.homForm 𝒜 x y :=
  K0.homForm_map σ hσ x y

end Categorification.Graded
