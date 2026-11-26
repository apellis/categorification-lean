/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DerivedTensorCoefficient
import Categorification.Algebra.TensorProductOverFlat
import DG.Derived.DimensionShift

/-!
# The derived tensor product along a short exact sequence of coefficients

Let `P` be a K-projective dg `B`-module whose underlying `B`-module is projective. A short exact
sequence `0 → M₁ → M₂ → M₃ → 0` of `(A, B)`-bimodules gives a short exact sequence of dg
modules `M₁ ⊗_B P → M₂ ⊗_B P → M₃ ⊗_B P` (`coefficientTensor_shortExact`), hence long exact
sequences for the derived tensor products `Mᵢ ⊗ᴸ_B P`. This is the coefficient form of the
dimension shift used in B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v2, proof of Lemma 6.11 (step `f_n → s_n`), where the standard filtration of
the coefficient is resolved.

## Main results

* `coefficientTensor_shortExact`.
* `isZero_derivedTensorHomology_coefficient_quotient`: concentration in degree zero passes from
  `M₁` and `M₂` to `M₃` when the degree-zero cohomology of `M₁ ⊗ᴸ P` vanishes.
* `isZero_derivedTensorHomology_coefficient_middle`: vanishing in one degree passes from `M₁`
  and `M₃` to `M₂`.
-/

open CategoryTheory CategoryTheory.Limits DG DG.DerivedCategory MulOpposite
open scoped DG.DegreeZero

noncomputable section

namespace Categorification

universe w u

variable {A B : Type u} [Ring A] [Ring B]
  {M₁ M₂ M₃ : Type u} [AddCommGroup M₁] [Module A M₁] [Module Bᵐᵒᵖ M₁] [SMulCommClass A Bᵐᵒᵖ M₁]
  [AddCommGroup M₂] [Module A M₂] [Module Bᵐᵒᵖ M₂] [SMulCommClass A Bᵐᵒᵖ M₂]
  [AddCommGroup M₃] [Module A M₃] [Module Bᵐᵒᵖ M₃] [SMulCommClass A Bᵐᵒᵖ M₃]
  (f : M₁ →ₗ[A] M₂) (hf : ∀ (b : B) (m : M₁), f (op b • m) = op b • f m)
  (g : M₂ →ₗ[A] M₃) (hg : ∀ (b : B) (m : M₂), g (op b • m) = op b • g m)

/-- An ordinary bimodule map as a right linear map of the degree-zero dg modules. -/
private def rightLinearOf {M M' : Type u} [AddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M]
    [AddCommGroup M'] [Module A M'] [Module Bᵐᵒᵖ M'] (f : M →ₗ[A] M')
    (hf : ∀ (b : B) (m : M), f (op b • m) = op b • f m) :
    InDegreeZero M →ₗ[Bᵐᵒᵖ] InDegreeZero M' where
  toFun := f
  map_add' := map_add f
  map_smul' b m := hf b.unop m

/-- The tensor complexes along a short exact sequence of coefficients, for a dg module whose
underlying module is projective. -/
def coefficientTensorComplex (hfg : g.comp f = 0) (P : DGModuleCat.{u} B) :
    ShortComplex (DGModuleCat.{u} A) :=
  ShortComplex.mk ((ordinaryTensorCoefficientMap f hf).app P)
    ((ordinaryTensorCoefficientMap g hg).app P)
    (DGModuleCat.tensor_hom_ext (M := InDegreeZero M₁) fun m n => by
      change TensorProductOver.tmul B (g (f m)) n = (0 : TensorProductOver B _ _)
      rw [show g (f m) = 0 from LinearMap.congr_fun hfg m]
      exact TensorProductOver.zero_tmul n)


/-- **Tensoring a projective dg module with a short exact sequence of coefficients** gives a
short exact sequence of dg modules. -/
theorem coefficientTensor_shortExact (hfg : g.comp f = 0) (hinj : Function.Injective f)
    (hex : Function.Exact f g) (hsurj : Function.Surjective g) (P : DGModuleCat.{u} B)
    [Module.Projective B P] : (coefficientTensorComplex f hf g hg hfg P).ShortExact := by
  refine (DGModuleCat.shortExact_iff _).2 ⟨?_, ?_, ?_⟩
  · exact TensorProductOver.map_injective_of_projective (f := rightLinearOf f hf) hinj
  · exact TensorProductOver.exact_map_of_projective (f := rightLinearOf f hf)
      (g := rightLinearOf g hg) hex
  · exact TensorProductOver.map_surjective (f := rightLinearOf g hg) hsurj

variable [HasDerivedCategory.{w, u} A] [HasDerivedCategory.{w, u} B]

include hf hg in
/-- **Dimension shift in the coefficient**: for a short exact sequence `0 → M₁ → M₂ → M₃ → 0` of
coefficients and a K-projective `P` with projective underlying module, if `M₁ ⊗ᴸ P` vanishes in
every degree and `M₂ ⊗ᴸ P` in every nonzero degree, then `M₃ ⊗ᴸ P` vanishes in every nonzero
degree. -/
theorem isZero_derivedTensorHomology_coefficient_quotient (hfg : g.comp f = 0)
    (hinj : Function.Injective f) (hex : Function.Exact f g) (hsurj : Function.Surjective g)
    {P : DGModuleCat.{u} B} (hP : IsKProjective.{u} B P) [Module.Projective B P]
    (h₁ : ∀ n : ℤ, IsZero ((homologyFunctor ℤ n).obj
      ((derivedTensor.{w} A B M₁).obj (Q.obj P))))
    (h₂ : ∀ n : ℤ, n ≠ 0 → IsZero ((homologyFunctor ℤ n).obj
      ((derivedTensor.{w} A B M₂).obj (Q.obj P))))
    (n : ℤ) (hn : n ≠ 0) :
    IsZero ((homologyFunctor ℤ n).obj ((derivedTensor.{w} A B M₃).obj (Q.obj P))) := by
  let S := coefficientTensorComplex f hf g hg hfg P
  have hS := coefficientTensor_shortExact f hf g hg hfg hinj hex hsurj P
  have e (M : Type u) [AddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]
      (j : ℤ) :
      (homologyFunctor ℤ j).obj ((derivedTensor.{w} A B M).obj (Q.obj P)) ≅
        (homologyFunctor ℤ j).obj ((𝟭 _).obj (Q.obj
          ((DGModuleCat.tensorFunctor A (InDegreeZero M)).obj P))) :=
    (homologyFunctor ℤ j).mapIso (derivedTensorObjIso hP)
  refine (isZero_homology_obj_of_shortExact ℤ (𝟭 _) S hS
    (fun j _ => (h₁ j).of_iso (e M₁ j).symm) (fun j hj => (h₂ j hj).of_iso (e M₂ j).symm)
    ⟨fun a b _ => ((h₁ 0).of_iso (e M₁ 0).symm).eq_of_tgt a b⟩ n hn).of_iso (e M₃ n)

include hf hg in
/-- **Extensions in the coefficient**: vanishing of `Mᵢ ⊗ᴸ P` in degree `n` for `i = 1, 3`
gives vanishing for `M₂`. -/
theorem isZero_derivedTensorHomology_coefficient_middle (hfg : g.comp f = 0)
    (hinj : Function.Injective f) (hex : Function.Exact f g) (hsurj : Function.Surjective g)
    {P : DGModuleCat.{u} B} (hP : IsKProjective.{u} B P) [Module.Projective B P] (n : ℤ)
    (h₁ : IsZero ((homologyFunctor ℤ n).obj ((derivedTensor.{w} A B M₁).obj (Q.obj P))))
    (h₃ : IsZero ((homologyFunctor ℤ n).obj ((derivedTensor.{w} A B M₃).obj (Q.obj P)))) :
    IsZero ((homologyFunctor ℤ n).obj ((derivedTensor.{w} A B M₂).obj (Q.obj P))) := by
  let S := coefficientTensorComplex f hf g hg hfg P
  have hS := coefficientTensor_shortExact f hf g hg hfg hinj hex hsurj P
  have e (M : Type u) [AddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M] :
      (homologyFunctor ℤ n).obj ((derivedTensor.{w} A B M).obj (Q.obj P)) ≅
        (homologyFunctor ℤ n).obj ((𝟭 _).obj (Q.obj
          ((DGModuleCat.tensorFunctor A (InDegreeZero M)).obj P))) :=
    (homologyFunctor ℤ n).mapIso (derivedTensorObjIso hP)
  exact (isZero_homology_middle_of_shortExact ℤ (𝟭 _) S hS n (h₁.of_iso (e M₁).symm)
    (h₃.of_iso (e M₃).symm)).of_iso (e M₂)

end Categorification
