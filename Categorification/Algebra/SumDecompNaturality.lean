/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.SumDecompLinear

/-!
# Naturality of the linear equivalences of decompositions

The `R`-linear equivalence `U ≃ V × M^ι` of `SumDecomp.semilinearEquiv` commutes with maps
`U → U'`, `V → V'` and `M → M'` that are compatible with the identifications and with the
components of the two decompositions (`SumDecomp.semilinearEquiv_naturality`).

This is used to see that the commutation relations of Webster's functors `Eᵢ` and `Fᵢ`
(arXiv:1309.3796v3, Theorem 4.31) are natural in the module, as needed in the proof of
Proposition 5.5 there.
-/

namespace Categorification

open CategoryTheory

noncomputable section

universe u w

section Semilinear

variable {R : Type*} {S : Type u} [Ring R] [Ring S] (σ : R ≃+* S)
  {U V M U' V' M' : Type*} [AddCommGroup U] [AddCommGroup V] [AddCommGroup M] [Module R U]
  [Module R V] [Module R M] [AddCommGroup U'] [AddCommGroup V'] [AddCommGroup M']
  [Module R U'] [Module R V'] [Module R M']
  {T₁ T₂ T₃ T₁' T₂' T₃' : ModuleCat.{w} S} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Naturality of `SumDecomp.semilinearEquiv`**: maps compatible with the identifications
and with the components of the decompositions are carried to the product map. -/
theorem SumDecomp.semilinearEquiv_naturality (D : SumDecomp T₁ T₂ (fun _ : ι => T₃))
    (eU : U ≃ₗ[ℤ] T₁) (heU : ∀ (a : R) (x : U), eU (a • x) = σ a • eU x)
    (eV : V ≃ₗ[ℤ] T₂) (heV : ∀ (a : R) (x : V), eV (a • x) = σ a • eV x)
    (eM : M ≃ₗ[ℤ] T₃) (heM : ∀ (a : R) (x : M), eM (a • x) = σ a • eM x)
    (D' : SumDecomp T₁' T₂' (fun _ : ι => T₃'))
    (eU' : U' ≃ₗ[ℤ] T₁') (heU' : ∀ (a : R) (x : U'), eU' (a • x) = σ a • eU' x)
    (eV' : V' ≃ₗ[ℤ] T₂') (heV' : ∀ (a : R) (x : V'), eV' (a • x) = σ a • eV' x)
    (eM' : M' ≃ₗ[ℤ] T₃') (heM' : ∀ (a : R) (x : M'), eM' (a • x) = σ a • eM' x)
    (fU : U → U') (fV : V → V') (fM : M → M') (t₁ : T₁ → T₁') (t₂ : T₂ → T₂')
    (t₃ : T₃ → T₃') (hU : ∀ x, eU' (fU x) = t₁ (eU x)) (hV : ∀ y, eV' (fV y) = t₂ (eV y))
    (hM : ∀ m, eM' (fM m) = t₃ (eM m)) (h0 : ∀ y, D'.a0.hom (t₁ y) = t₂ (D.a0.hom y))
    (ha : ∀ s y, (D'.a s).hom (t₁ y) = t₃ ((D.a s).hom y)) (x : U) :
    SumDecomp.semilinearEquiv σ D' eU' heU' eV' heV' eM' heM' (fU x) =
      (fV (SumDecomp.semilinearEquiv σ D eU heU eV heV eM heM x).1,
        fun s => fM ((SumDecomp.semilinearEquiv σ D eU heU eV heV eM heM x).2 s)) := by
  refine Prod.ext ?_ (funext fun s => ?_)
  · apply eV'.injective
    change eV' (eV'.symm (D'.a0.hom (eU' (fU x)))) = eV' (fV (eV.symm (D.a0.hom (eU x))))
    rw [LinearEquiv.apply_symm_apply, hV, LinearEquiv.apply_symm_apply, hU, h0]
  · apply eM'.injective
    change eM' (eM'.symm ((D'.a s).hom (eU' (fU x)))) =
      eM' (fM (eM.symm ((D.a s).hom (eU x))))
    rw [LinearEquiv.apply_symm_apply, hM, LinearEquiv.apply_symm_apply, hU, ha]

end Semilinear

end

end Categorification
