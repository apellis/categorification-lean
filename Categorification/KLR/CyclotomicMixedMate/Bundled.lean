/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.KLR.CyclotomicMixedMate.NaturalInverse

/-! The original ordinary-adjunction mixed mate on removable-colour inputs.
Only the canonical ground-scalar rebundling is identified; all functors, weight
casts, signs and cuts are those of the original cyclotomic constructions. -/
noncomputable section
namespace Categorification.KLR.KLRAlgebra.AbsentColour.MixedNatIso
open CategoryTheory MixedMate MixedComparison
open scoped ModuleCat.Algebra
universe u v w
variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (a : I → Polynomial k)
  (γ : Multiset I) (i j : I)
local notation "C" => CycKLR k Q a ((Singleton.singleton i : Multiset I) + γ)
local notation "A" => CycKLR k Q a ((Singleton.singleton j : Multiset I) + γ)
local notation "R" => CycKLR k Q a γ

/-- Restrict i, then induce j, on the original module categories. -/
abbrev sourceFunctor : ModuleCat.{max u v w} C ⥤ ModuleCat.{max u v w} A :=
  restrictionFunctor Q i a γ ⋙ inductionFunctor Q j a γ

/-- Induce j, apply the original upper weight cast, then restrict i. -/
abbrev targetFunctor : ModuleCat.{max u v w} C ⥤ ModuleCat.{max u v w} A :=
  inductionFunctor Q j a ({i} + γ) ⋙ upperTransport Q a γ i j ⋙
    restrictionFunctor Q i a ({j} + γ)

/-- Canonical identification of the two compatible ground-scalar structures on
restriction inside induction. It fixes every elementary tensor. -/
def sourceEquiv (M : ModuleCat.{max u v w} C) :
    (sourceFunctor Q a γ i j).obj M ≃ₗ[A] Ind Q j a γ (Res Q i a γ M) :=
  BalancedTensor.congrRight
    (N := ((restrictionFunctor Q i a γ).obj M)) (N' := Res Q i a γ M)
    (LinearEquiv.refl R _)

theorem sourceEquiv_tmul (M : ModuleCat.{max u v w} C)
    (y : IndCorner Q j a γ) (m : (restrictionFunctor Q i a γ).obj M) :
    sourceEquiv Q a γ i j M (BalancedTensor.tmul y m) =
      BalancedTensor.tmul y (show Res Q i a γ M from m) := rfl

theorem sourceEquiv_natural {M M' : ModuleCat.{max u v w} C} (f : M ⟶ M') :
    (sourceEquiv Q a γ i j M').toLinearMap.comp ((sourceFunctor Q a γ i j).map f).hom =
      (mateSourceMap Q a γ i j M M' f.hom).comp (sourceEquiv Q a γ i j M).toLinearMap := by
  apply BalancedTensor.extB
  intro y m
  rfl

/-- The target already has exactly the original transported restricted structure. -/
theorem targetFunctor_map {M M' : ModuleCat.{max u v w} C} (f : M ⟶ M') :
    ((targetFunctor Q a γ i j).map f).hom = mateTargetMap Q a γ i j M M' f.hom := rfl

/-- Defined from the original ordinary mate, not manufactured from an equivalence. -/
def originalMate : sourceFunctor.{u,v,w} Q a γ i j ⟶ targetFunctor Q a γ i j where
  app M := ModuleCat.ofHom ((mate Q a γ i j M).comp (sourceEquiv Q a γ i j M).toLinearMap)
  naturality {M M'} f := by
    apply ModuleCat.hom_ext
    change (mate Q a γ i j M').comp
        ((sourceEquiv Q a γ i j M').toLinearMap.comp ((sourceFunctor Q a γ i j).map f).hom) = _
    rw [sourceEquiv_natural, ← LinearMap.comp_assoc, ← mate_natural]
    rfl

/-- Component equality under the explicit original-functor identification. -/
theorem originalMate_app (M : ModuleCat.{max u v w} C) :
    ((originalMate Q a γ i j).app M).hom =
      (mate Q a γ i j M).comp (sourceEquiv Q a γ i j M).toLinearMap := rfl

/-- The bundled component, returned to the unbundled source, is exactly the
original ordinary Hom-equivalence applied to crossing followed by counit. -/
theorem originalMate_app_homToRes (M : ModuleCat.{max u v w} C) :
    (((originalMate Q a γ i j).app M).hom).comp
        (sourceEquiv Q a γ i j M).symm.toLinearMap =
      homToRes Q i a ({j} + γ)
        ((liftedCounit Q a γ i j M).comp
          (crossingLinear Q a γ i j (Res Q i a γ M))) := by
  apply LinearMap.ext
  intro z
  change mate Q a γ i j M
    (sourceEquiv Q a γ i j M ((sourceEquiv Q a γ i j M).symm z)) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

variable (hij : i ≠ j) (hsym : KLRSymm Q)

/-- The accepted inverse transported back through the canonical tensor identification. -/
def originalInverse : targetFunctor.{u,v,w} Q a γ i j ⟶ sourceFunctor Q a γ i j where
  app M := ModuleCat.ofHom ((sourceEquiv Q a γ i j M).symm.toLinearMap.comp
    (mateInverse Q a γ i j hij hsym M))
  naturality {M M'} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change Target Q a γ i j M at z
    apply (sourceEquiv Q a γ i j M').injective
    change sourceEquiv Q a γ i j M'
        ((sourceEquiv Q a γ i j M').symm (mateInverse Q a γ i j hij hsym M'
          (mateTargetMap Q a γ i j M M' f.hom z))) =
      sourceEquiv Q a γ i j M' (((sourceFunctor Q a γ i j).map f).hom
        ((sourceEquiv Q a γ i j M).symm (mateInverse Q a γ i j hij hsym M z)))
    rw [LinearEquiv.apply_symm_apply]
    have hn := LinearMap.congr_fun (sourceEquiv_natural Q a γ i j f)
      ((sourceEquiv Q a γ i j M).symm (mateInverse Q a γ i j hij hsym M z))
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply] at hn
    exact (LinearMap.congr_fun
      (mateInverse_natural Q a γ i j M M' hij hsym f.hom) z).symm.trans hn.symm

/-- Natural isomorphism of the original composites on every removable-colour input. -/
def mixedNatIso : sourceFunctor.{u,v,w} Q a γ i j ≅ targetFunctor Q a γ i j where
  hom := originalMate Q a γ i j
  inv := originalInverse Q a γ i j hij hsym
  hom_inv_id := by
    apply NatTrans.ext
    funext M
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change (sourceEquiv Q a γ i j M).symm
      (mateInverse Q a γ i j hij hsym M
        (mate Q a γ i j M (sourceEquiv Q a γ i j M z))) = z
    rw [mateInverse_mate, LinearEquiv.symm_apply_apply]
  inv_hom_id := by
    apply NatTrans.ext
    funext M
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change mate Q a γ i j M (sourceEquiv Q a γ i j M
      ((sourceEquiv Q a γ i j M).symm (mateInverse Q a γ i j hij hsym M z))) = z
    rw [LinearEquiv.apply_symm_apply]
    exact mate_mateInverse Q a γ i j hij hsym M z

/-- Exactly the original ordinary mate under the original source identification. -/
theorem mixedNatIso_hom_app (M : ModuleCat.{max u v w} C) :
    ((mixedNatIso Q a γ i j hij hsym).hom.app M).hom =
      (mate Q a γ i j M).comp (sourceEquiv Q a γ i j M).toLinearMap := rfl

/-- The inverse is the accepted comparison inverse on the original target. -/
theorem mixedNatIso_inv_app (M : ModuleCat.{max u v w} C) :
    ((mixedNatIso Q a γ i j hij hsym).inv.app M).hom =
      (sourceEquiv Q a γ i j M).symm.toLinearMap.comp
        (mateInverse Q a γ i j hij hsym M) := rfl

/-- Agreement with the accepted equivalence, after canonical rebundling. -/
theorem mixedNatIso_hom_app_eq_equiv (M : ModuleCat.{max u v w} C) :
    ((mixedNatIso Q a γ i j hij hsym).hom.app M).hom =
      (originalMateEquiv Q a γ i j hij hsym M).toLinearMap.comp
        (sourceEquiv Q a γ i j M).toLinearMap := by
  rw [originalMateEquiv_eq_mate]
  rfl

include hij hsym in
/-- Invertibility of the original natural transformation, not an assumed mate. -/
theorem originalMate_isIso : IsIso (originalMate.{u,v,w} Q a γ i j) := by
  change IsIso (mixedNatIso Q a γ i j hij hsym).hom
  infer_instance

end Categorification.KLR.KLRAlgebra.AbsentColour.MixedNatIso
