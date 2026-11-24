/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.BalancedTensorExact
import Categorification.Algebra.DerivedTensorHomology
import Categorification.Algebra.OrdinaryProjectiveResolutionDG
import DG.Derived.ShortExactTriangle
import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# Short exact sequences in a derived tensor coefficient

Tensoring a short exact coefficient sequence with a projective ordinary
module preserves exactness. Apply this to the direct sum underlying an
ordinary projective resolution, then pass to the DG and derived models.
-/

namespace Categorification

open CategoryTheory DG MulOpposite TensorProductOver
open scoped DG.DegreeZero

noncomputable section

universe u

variable {k B : Type u} [CommRing k] [Ring B] [Algebra k B]
  {M M' M'' : Type u}
  [AddCommGroup M] [Module k M] [Module Bᵐᵒᵖ M] [IsScalarTower k Bᵐᵒᵖ M]
  [SMulCommClass k Bᵐᵒᵖ M]
  [AddCommGroup M'] [Module k M'] [Module Bᵐᵒᵖ M'] [IsScalarTower k Bᵐᵒᵖ M']
  [SMulCommClass k Bᵐᵒᵖ M']
  [AddCommGroup M''] [Module k M''] [Module Bᵐᵒᵖ M''] [IsScalarTower k Bᵐᵒᵖ M'']
  [SMulCommClass k Bᵐᵒᵖ M'']

private theorem coefficientGroundScalar {Y : Type u} [AddCommGroup Y] [Module k Y]
    [Module Bᵐᵒᵖ Y] [IsScalarTower k Bᵐᵒᵖ Y] (c : k) (y : Y) :
    op (algebraMap k B c) • y = c • y :=
  IsScalarTower.algebraMap_smul Bᵐᵒᵖ c y

variable (N : DGModuleCat.{u} B) [Module k N] [IsScalarTower k B N]

private abbrev dgCoeffMap (f : M →ₗ[k] M') (hf : BalancedTensor.IsBimoduleHom (A := B) f) :=
  (ordinaryTensorCoefficientMap f hf).app N

private abbrev dgCoeffLinear (f : M →ₗ[k] M') (hf : BalancedTensor.IsBimoduleHom (A := B) f) :
    TensorProductOver B M N →ₗ[k] TensorProductOver B M' N :=
  (dgCoeffMap N f hf).hom.toLinearMap

/-- Form the tensor sequence of an exact sequence of ordinary coefficients
with a fixed DG module. -/
abbrev dgTensorCoefficientShortComplex
    (f : M →ₗ[k] M') (hf : BalancedTensor.IsBimoduleHom (A := B) f)
    (g : M' →ₗ[k] M'') (hg : BalancedTensor.IsBimoduleHom (A := B) g)
    (hfg : Function.Exact f g) : ShortComplex (DGModuleCat.{u} k) :=
  ShortComplex.mk (dgCoeffMap N f hf) (dgCoeffMap N g hg) (by
    apply DGModuleCat.tensor_hom_ext (A := k) (M := InDegreeZero M)
    intro m n
    change tmul B (g (f m)) n = 0
    have h : g (f m) = 0 := (hfg (f m)).2 ⟨m,rfl⟩
    rw [h,zero_tmul])

private theorem compareDGCoefMap (f : M →ₗ[k] M')
    (hf : BalancedTensor.IsBimoduleHom (A := B) f)
    (z : TensorProductOver B M N) :
    ordinaryBalancedTensorAddEquiv (A := k) (M := M') (N := N)
        (coefficientGroundScalar (k := k) (B := B)) (dgCoeffLinear N f hf z) =
      BalancedTensor.mapLeftBimodule k N f hf
        (ordinaryBalancedTensorAddEquiv (A := k) (M := M) (N := N)
          (coefficientGroundScalar (k := k) (B := B)) z) := by
  induction z using TensorProductOver.induction_on with
  | zero => simp only [map_zero]
  | tmul m n => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Tensoring with a DG module whose underlying ordinary module is projective
preserves exactness of a short exact sequence in the coefficient. -/
theorem dgTensorCoefficientShortComplex_shortExact [Module.Projective B N]
    (f : M →ₗ[k] M') (hf : BalancedTensor.IsBimoduleHom (A := B) f)
    (g : M' →ₗ[k] M'') (hg : BalancedTensor.IsBimoduleHom (A := B) g)
    (hfg : Function.Exact f g) (hi : Function.Injective f) (hs : Function.Surjective g) :
    (dgTensorCoefficientShortComplex N f hf g hg hfg).ShortExact := by
  let e₀ : TensorProductOver B M N ≃+ BalancedTensor k k B M N :=
    ordinaryBalancedTensorAddEquiv (coefficientGroundScalar (k := k) (B := B))
  let e₁ : TensorProductOver B M' N ≃+ BalancedTensor k k B M' N :=
    ordinaryBalancedTensorAddEquiv (coefficientGroundScalar (k := k) (B := B))
  let e₂ : TensorProductOver B M'' N ≃+ BalancedTensor k k B M'' N :=
    ordinaryBalancedTensorAddEquiv (coefficientGroundScalar (k := k) (B := B))
  let fb := BalancedTensor.mapLeftBimodule k N f hf
  let gb := BalancedTensor.mapLeftBimodule k N g hg
  have hbi : Function.Injective fb := BalancedTensor.mapLeftBimodule_injective hf hi
  have hbe : Function.Exact fb gb := BalancedTensor.mapLeftBimodule_exact hf hg hfg
  have hbs : Function.Surjective gb := BalancedTensor.mapLeftBimodule_surjective hg hs
  have h₁ (z : TensorProductOver B M N) : e₁ (dgCoeffLinear N f hf z) = fb (e₀ z) :=
    compareDGCoefMap N f hf z
  have h₂ (z : TensorProductOver B M' N) : e₂ (dgCoeffLinear N g hg z) = gb (e₁ z) :=
    compareDGCoefMap N g hg z
  refine (DGModuleCat.shortExact_iff _).2 ⟨?_,?_,?_⟩
  · intro x y h
    change dgCoeffLinear N f hf x = dgCoeffLinear N f hf y at h
    exact e₀.injective (hbi ((h₁ x).symm.trans ((congrArg e₁ h).trans (h₁ y))))
  · intro z
    change dgCoeffLinear N g hg z = 0 ↔ ∃ x, dgCoeffLinear N f hf x = z
    constructor
    · intro h
      have hZ : gb (e₁ z) = 0 := (h₂ z).symm.trans
        ((congrArg e₂ h).trans (map_zero e₂))
      obtain ⟨u,hu⟩ := (hbe (e₁ z)).1 hZ
      refine ⟨e₀.symm u,e₁.injective ?_⟩
      rw [h₁,e₀.apply_symm_apply,hu]
    · rintro ⟨x,rfl⟩
      apply e₂.injective
      rw [h₂, h₁, map_zero]
      exact (hbe (fb (e₀ x))).2 ⟨e₀ x,rfl⟩
  · intro y
    obtain ⟨z,hz⟩ := hbs (e₂ y)
    refine ⟨e₁.symm z,e₂.injective ?_⟩
    change e₂ (dgCoeffLinear N g hg (e₁.symm z)) = e₂ y
    rw [h₂,e₁.apply_symm_apply,hz]

end
end Categorification

namespace Categorification

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated DG DG.DerivedCategory MulOpposite
open scoped DG.DegreeZero

noncomputable section

universe w u

variable {k B : Type u} [CommRing k] [Ring B]
  [DG.HasDerivedCategory.{w,u} k] [DG.HasDerivedCategory.{w,u} B]

private abbrev degreeZeroDerivedObject (X : ModuleCat.{u} B) :=
  Q.obj (DGModuleCat.of B (InDegreeZero X))

private def projectiveAugmentationIso
    {X : ModuleCat.{u} B} (P : ProjectiveResolution X) :
    Q.obj (projectiveResolutionDGModel P) ≅ degreeZeroDerivedObject X := by
  have : IsIso (Q.map (projectiveResolutionDGAugToOrdinary P)) :=
    (isIso_Q_map_iff _).2 (projectiveResolutionDGAugToOrdinary_quasiIso P)
  exact asIso (Q.map (projectiveResolutionDGAugToOrdinary P))

variable {M : Type u} [AddCommGroup M] [Module k M] [Module Bᵐᵒᵖ M]
  [SMulCommClass k Bᵐᵒᵖ M]
  {M' : Type u} [AddCommGroup M'] [Module k M'] [Module Bᵐᵒᵖ M']
  [SMulCommClass k Bᵐᵒᵖ M']

private def coefficientResolutionIso {X : ModuleCat.{u} B} (P : ProjectiveResolution X) :
    (derivedTensor.{w} k B M).obj (degreeZeroDerivedObject X) ≅
      Q.obj ((DGModuleCat.tensorFunctor k (InDegreeZero M)).obj (projectiveResolutionDGModel P)) :=
  ((derivedTensor.{w} k B M).mapIso (projectiveAugmentationIso P)).symm ≪≫
    derivedTensorObjIso (projectiveResolutionDGModel_kProjective P)

private theorem coefficientResolutionIso_naturality {X : ModuleCat.{u} B}
    (P : ProjectiveResolution X) (f : M →ₗ[k] M')
    (hf : BalancedTensor.IsBimoduleHom (A := B) f) :
    (derivedTensorCoefficientMap f hf).app (degreeZeroDerivedObject X) ≫
        (coefficientResolutionIso (k := k) (M := M') P).hom =
      (coefficientResolutionIso (k := k) (M := M) P).hom ≫
        Q.map ((ordinaryTensorCoefficientMap f hf).app (projectiveResolutionDGModel P)) := by
  let e := projectiveAugmentationIso P
  let F := derivedTensor.{w} k B M
  let G := derivedTensor.{w} k B M'
  let η := derivedTensorCoefficientMap f hf
  let eF := derivedTensorObjIso (A := k) (M := M) (projectiveResolutionDGModel_kProjective P)
  let eG := derivedTensorObjIso (A := k) (M := M') (projectiveResolutionDGModel_kProjective P)
  let t := Q.map ((ordinaryTensorCoefficientMap f hf).app (projectiveResolutionDGModel P))
  let a := F.mapIso e
  let b := G.mapIso e
  change η.app (degreeZeroDerivedObject X) ≫ (b.inv ≫ eG.hom) =
    (a.inv ≫ eF.hom) ≫ t
  apply (cancel_epi a.hom).1
  have hn : a.hom ≫ η.app (degreeZeroDerivedObject X) = η.app (Q.obj (projectiveResolutionDGModel P)) ≫ b.hom :=
    η.naturality e.hom
  rw [← Category.assoc, hn, Category.assoc, Iso.hom_inv_id_assoc]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact derivedTensorObjIso_coefficient_naturality f hf (projectiveResolutionDGModel_kProjective P)

variable [Algebra k B]

variable {M'' : Type u} [AddCommGroup M''] [Module k M''] [Module Bᵐᵒᵖ M'']
  [SMulCommClass k Bᵐᵒᵖ M'']
  [IsScalarTower k Bᵐᵒᵖ M] [IsScalarTower k Bᵐᵒᵖ M'] [IsScalarTower k Bᵐᵒᵖ M'']

/-- A short exact sequence in the coefficient gives a distinguished
triangle after derived tensor with an ordinary module. -/
theorem exists_distinguished_derivedTensorCoefficient
    (X : ModuleCat.{u} B)
    (f : M →ₗ[k] M') (hf : BalancedTensor.IsBimoduleHom (A := B) f)
    (g : M' →ₗ[k] M'') (hg : BalancedTensor.IsBimoduleHom (A := B) g)
    (hfg : Function.Exact f g) (hi : Function.Injective f) (hs : Function.Surjective g) :
    ∃ δ, Triangle.mk
      ((derivedTensorCoefficientMap f hf).app (degreeZeroDerivedObject X))
      ((derivedTensorCoefficientMap g hg).app (degreeZeroDerivedObject X)) δ ∈
        distTriang (DerivedCategory.{w,u} k) := by
  let P := projectiveResolution X
  let N := projectiveResolutionDGModel P
  let : Module k N := Module.compHom N (algebraMap k B)
  have : IsScalarTower k B N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Projective B N := projectiveResolutionDGModel_underlyingProjective P
  let S := dgTensorCoefficientShortComplex N f hf g hg hfg
  have hS : S.ShortExact := dgTensorCoefficientShortComplex_shortExact N f hf g hg hfg hi hs
  obtain ⟨δ,hδ⟩ := exists_distinguished_of_shortExact S hS
  let D := Triangle.mk (Q.map S.f) (Q.map S.g) δ
  let e₁ := coefficientResolutionIso (k := k) (M := M) P
  let e₂ := coefficientResolutionIso (k := k) (M := M') P
  let e₃ := coefficientResolutionIso (k := k) (M := M'') P
  let δ' := e₃.hom ≫ δ ≫ (shiftFunctor _ (1 : ℤ)).map e₁.inv
  let D' := Triangle.mk
    ((derivedTensorCoefficientMap f hf).app (degreeZeroDerivedObject X))
    ((derivedTensorCoefficientMap g hg).app (degreeZeroDerivedObject X)) δ'
  have eD : D' ≅ D := Triangle.isoMk _ _ e₁ e₂ e₃
    (coefficientResolutionIso_naturality P f hf)
    (coefficientResolutionIso_naturality P g hg)
    (by
      change δ' ≫ (shiftFunctor _ (1 : ℤ)).map e₁.hom = e₃.hom ≫ δ
      simp [δ', Category.assoc, ← Functor.map_comp])
  exact ⟨δ', isomorphic_distinguished _ hδ _ eD⟩

end
end Categorification
