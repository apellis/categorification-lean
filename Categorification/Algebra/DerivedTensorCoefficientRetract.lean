/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DerivedTensorCoefficient
import Categorification.Algebra.OrdinaryProjectiveResolutionDG
import Categorification.Algebra.DerivedTensorFiltration

/-!
# Derived tensor products along a retract of the coefficient

If a bimodule `M₁` is a retract of `M₂` (maps `f : M₁ → M₂`, `g : M₂ → M₁` with `g ∘ f = id`),
then the cohomology of `M₁ ⊗ᴸ_B Y` is a retract of that of `M₂ ⊗ᴸ_B Y`; in particular it
vanishes in every degree where the latter does
(`isZero_derivedTensorHomology_coefficient_retract`). The derived tensor product is computed on
the projective resolution of `Y`, where the coefficient maps act by `f ⊗ id` and `g ⊗ id`.

This passes the vanishing of higher Tor from a standard module to its summands, as in B. Webster,
*Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.22 (the diagonal `E²` term, whose factors are summands of standard modules).
-/

open CategoryTheory CategoryTheory.Limits DG DG.DerivedCategory MulOpposite
open scoped DG.DegreeZero

noncomputable section

namespace Categorification

universe w u

variable {A B : Type u} [Ring A] [Ring B]
  {M₁ M₂ : Type u} [AddCommGroup M₁] [Module A M₁] [Module Bᵐᵒᵖ M₁] [SMulCommClass A Bᵐᵒᵖ M₁]
  [AddCommGroup M₂] [Module A M₂] [Module Bᵐᵒᵖ M₂] [SMulCommClass A Bᵐᵒᵖ M₂]
  (f : M₁ →ₗ[A] M₂) (hf : ∀ (b : B) (m : M₁), f (op b • m) = op b • f m)
  (g : M₂ →ₗ[A] M₁) (hg : ∀ (b : B) (m : M₂), g (op b • m) = op b • g m)

include hf hg in
/-- On every dg module, the coefficient maps of a retract compose to the identity. -/
theorem ordinaryTensorCoefficientMap_retract (hgf : g.comp f = LinearMap.id)
    (P : DGModuleCat.{u} B) :
    (ordinaryTensorCoefficientMap f hf).app P ≫ (ordinaryTensorCoefficientMap g hg).app P =
      𝟙 _ :=
  DGModuleCat.tensor_hom_ext (M := InDegreeZero M₁) fun m n => by
    change TensorProductOver.tmul B (g (f m)) n = TensorProductOver.tmul B m n
    rw [show g (f m) = m from LinearMap.congr_fun hgf m]
    rfl

variable [HasDerivedCategory.{w, u} A] [HasDerivedCategory.{w, u} B]

include hf hg in
/-- **Vanishing passes to a retract of the coefficient**: if `g ∘ f = id` for bimodule maps
`f : M₁ → M₂`, `g : M₂ → M₁`, and `M₂ ⊗ᴸ_B Y` has no cohomology in degree `n`, then neither has
`M₁ ⊗ᴸ_B Y`. -/
theorem isZero_derivedTensorHomology_coefficient_retract (hgf : g.comp f = LinearMap.id)
    (Y : ModuleCat.{u} B) (n : ℤ)
    (h₂ : IsZero ((homologyFunctor (A := A) ℤ n).obj ((derivedTensor.{w} A B M₂).obj
      (Q.obj ((degreeZeroModuleFunctor B).obj Y))))) :
    IsZero ((homologyFunctor (A := A) ℤ n).obj ((derivedTensor.{w} A B M₁).obj
      (Q.obj ((degreeZeroModuleFunctor B).obj Y)))) := by
  let P := projectiveResolution Y
  have hP := projectiveResolutionDGModel_kProjective (R := B) P
  have hiso : IsIso (Q.{w} (A := B) |>.map (projectiveResolutionDGAugToOrdinary P)) :=
    (isIso_Q_map_iff _).mpr (projectiveResolutionDGAugToOrdinary_quasiIso P)
  let I : Q.obj (projectiveResolutionDGModel P) ≅ Q.obj ((degreeZeroModuleFunctor B).obj Y) :=
    @asIso _ _ _ _ (Q.map (projectiveResolutionDGAugToOrdinary P)) hiso
  let H := homologyFunctor (A := A) ℤ n
  let e : ∀ (M : Type u) [AddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M]
      [SMulCommClass A Bᵐᵒᵖ M],
      H.obj ((derivedTensor.{w} A B M).obj (Q.obj ((degreeZeroModuleFunctor B).obj Y))) ≅
        H.obj (Q.obj ((DGModuleCat.tensorFunctor A (InDegreeZero M)).obj
          (projectiveResolutionDGModel P))) :=
    fun M _ _ _ _ => H.mapIso ((derivedTensor.{w} A B M).mapIso I.symm ≪≫ derivedTensorObjIso hP)
  let a := H.map (Q.map ((ordinaryTensorCoefficientMap f hf).app (projectiveResolutionDGModel P)))
  let b := H.map (Q.map ((ordinaryTensorCoefficientMap g hg).app (projectiveResolutionDGModel P)))
  have hab : a ≫ b = 𝟙 _ := by
    rw [← H.map_comp, ← Q.map_comp, ordinaryTensorCoefficientMap_retract f hf g hg hgf,
      Q.map_id, H.map_id]
  have : Mono a := mono_of_mono_fac hab
  exact (IsZero.of_mono a (h₂.of_iso (e M₂).symm)).of_iso (e M₁)

end Categorification
