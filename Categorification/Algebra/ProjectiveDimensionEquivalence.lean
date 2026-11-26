/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# Projective dimension along equivalences

An equivalence of abelian categories with enough projectives preserves projective dimension
(`Functor.hasProjectiveDimensionLT_obj`). In particular restriction of scalars along a ring
isomorphism preserves the projective dimension of a module
(`hasProjectiveDimensionLT_restrictScalars`). This transports Webster, arXiv:1309.3796v2,
Corollary 5.22 from left to right modules along a graded anti-involution.
-/

namespace CategoryTheory

open Limits

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [EnoughProjectives C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-- **An equivalence preserves projective dimension.** -/
theorem Functor.hasProjectiveDimensionLT_obj (F : C ⥤ D) [F.IsEquivalence] :
    ∀ (n : ℕ) (X : C), HasProjectiveDimensionLT X n → HasProjectiveDimensionLT (F.obj X) n
  | 0, X, hX => by
    rw [hasProjectiveDimensionLT_zero_iff_isZero] at hX ⊢
    exact F.map_isZero hX
  | 1, X, hX => by
    rw [← projective_iff_hasProjectiveDimensionLT_one] at hX ⊢
    exact F.projective_obj_of_projective hX
  | n + 2, X, hX => by
    let S : ShortComplex C := ShortComplex.mk (kernel.ι (Projective.π X)) (Projective.π X)
      (kernel.condition _)
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _) }
    have hK : HasProjectiveDimensionLT S.X₁ (n + 1) :=
      (hS.hasProjectiveDimensionLT_X₃_iff n (inferInstanceAs (Projective (Projective.over X)))).mp
        hX
    have hS' : (S.map F).ShortExact := hS.map_of_exact F
    have : Projective (S.map F).X₂ := F.projective_obj _
    exact (hS'.hasProjectiveDimensionLT_X₃_iff n this).mpr
      (F.hasProjectiveDimensionLT_obj (n + 1) _ hK)

/-- **Restriction of scalars along a ring isomorphism preserves projective dimension.** If an
`S`-module `M` is an `R`-module through `e : R ≃+* S`, its projective dimensions over `R` and `S`
agree from above. -/
theorem hasProjectiveDimensionLT_of_ringEquiv {R S : Type u₁} [Ring R] [Ring S] (e : R ≃+* S)
    {M : Type u₁} [AddCommGroup M] [Module R M] [Module S M]
    (he : ∀ (r : R) (m : M), r • m = e r • m)
    (n : ℕ) (h : HasProjectiveDimensionLT (ModuleCat.of S M) n) :
    HasProjectiveDimensionLT (ModuleCat.of R M) n := by
  have h' := (ModuleCat.restrictScalars e.toRingHom).hasProjectiveDimensionLT_obj n _ h
  let φ : M ≃ₗ[R] (ModuleCat.restrictScalars e.toRingHom).obj (ModuleCat.of S M) :=
    { toFun := fun m => m
      invFun := fun m => m
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r m => he r m }
  exact hasProjectiveDimensionLT_of_iso φ.toModuleIso.symm n

/-- **Projective dimension along a semilinear isomorphism.** If `φ : M ≃ₛₗ[e] N` is semilinear
along a ring isomorphism `e : R ≃+* S`, the projective dimension of `M` over `R` is bounded by that
of `N` over `S`. -/
theorem hasProjectiveDimensionLT_of_semilinearEquiv {R S : Type u₁} [Ring R] [Ring S]
    (e : R ≃+* S) {M N : Type u₁} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    (φ : M ≃ₛₗ[(e : R →+* S)] N) (n : ℕ) (h : HasProjectiveDimensionLT (ModuleCat.of S N) n) :
    HasProjectiveDimensionLT (ModuleCat.of R M) n := by
  have h' := (ModuleCat.restrictScalars e.toRingHom).hasProjectiveDimensionLT_obj n _ h
  let ψ : M ≃ₗ[R] (ModuleCat.restrictScalars e.toRingHom).obj (ModuleCat.of S N) :=
    { toFun := fun m => φ m
      invFun := fun m => φ.symm m
      left_inv := φ.left_inv
      right_inv := φ.right_inv
      map_add' := φ.map_add
      map_smul' := fun r m => φ.map_smulₛₗ r m }
  exact hasProjectiveDimensionLT_of_iso ψ.toModuleIso.symm n

end CategoryTheory
