/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DGDerivedTensorIsoIdOfRegular
import DG.Derived.PerfectCompact

set_option backward.isDefEq.respectTransparency false

/-!
# A derived tensor functor fixing the regular module, on Mathlib's derived category

Let `T` be a ring and `X` a dg `(T, T)`-bimodule. Write
`E : D(T) ≌ D(Mod T)` for the comparison equivalence between the derived category of dg modules
over `T` (in degree `0`) and Mathlib's derived category of `T`-modules
(`DG.DegreeZero.derivedComparisonEquivalence`). Let `S' : D(Mod T) ⥤ D(Mod T)` be a functor with
a comparison isomorphism `(X ⊗ᴸ_T -) ⋙ E ≅ E ⋙ S'`, i.e. `S'` is the derived tensor with `X` up
to the comparison. If `φ : S'(T) ≅ T`, where `T` is the regular module placed in degree `0`,
commutes with the right multiplications `ρ_t : T → T`, then `S' ≅ 𝟭`
(`Categorification.derivedTensorIsoIdOfRegularIsoModuleCat`).

This transports `Categorification.dgDerivedTensorIsoIdOfRegularIso` along `E`, using that
`E` sends the dg module `T` to `T` placed in degree `0`, compatibly with the right
multiplications (`Categorification.derivedComparisonObjSelfIso_rightMul`).

This is the generic step of B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v3, proof of Proposition 7.22, in the setting of the categorical action
`Stendhal.blackPresCL` (Mathlib's derived categories of right `T^λ`-modules; take
`T = (T^λ)ᵐᵒᵖ`, whose right multiplications are the left multiplications of `T^λ`).
-/

open CategoryTheory DG DG.DerivedCategory MulOpposite DG.DegreeZero
open scoped DG.DegreeZero

noncomputable section

namespace Categorification

attribute [local instance] tensorFunctorSignCommShift homotopyTensorFunctorSignCommShift

variable {T : Type} [Ring T]

/-- `DG.DegreeZero.complexFunctorObjSelfIso` commutes with the right multiplications. -/
theorem complexFunctorObjSelfIso_rightMul (t : T) :
    (complexFunctor T).map (regularRightMul T t) ≫ (complexFunctorObjSelfIso T).hom =
      (complexFunctorObjSelfIso T).hom ≫
        (HomologicalComplex.single (ModuleCat.{0} T) (ComplexShape.up ℤ) 0).map
          (moduleRightAct T t) := by
  apply HomologicalComplex.to_single_hom_ext
  simp [complexFunctorObjSelfIso, HomologicalComplex.single_map_f_self]
  rfl

variable [HasDerivedCategory.{0, 0} T] [_root_.HasDerivedCategory.{0} (ModuleCat.{0} T)]

/-- The comparison `D(T) ⥤ D(Mod T)` sends the dg module `T` to `T` placed in degree `0`
(`DG.DegreeZero.derivedComparisonObjSelfIso`) compatibly with the right multiplications. -/
theorem derivedComparisonObjSelfIso_rightMul (t : T) :
    (derivedComparison T).map (Q.map (regularRightMul T t)) ≫
        (derivedComparisonObjSelfIso T).hom =
      (derivedComparisonObjSelfIso T).hom ≫
        (_root_.DerivedCategory.singleFunctor (ModuleCat.{0} T) 0).map (moduleRightAct T t) := by
  have h₁ := (QCompDerivedComparisonIso T).hom.naturality (regularRightMul T t)
  have h₂ := congrArg _root_.DerivedCategory.Q.map (complexFunctorObjSelfIso_rightMul t)
  have h₃ := ((SingleFunctors.evaluation _ _ 0).mapIso
    (_root_.DerivedCategory.singleFunctorsPostcompQIso (ModuleCat.{0} T))).inv.naturality
      (moduleRightAct T t)
  simp only [Functor.map_comp] at h₂
  simp only [Functor.comp_map] at h₁
  simp only [derivedComparisonObjSelfIso, IsPerfect.singleFunctorObjIso, Iso.trans_hom,
    Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, Category.assoc]
  rw [reassoc_of% h₁]
  rw [reassoc_of% h₂]
  exact congrArg (fun k => _ ≫ _ ≫ k) h₃

variable {X : Type} [AddCommGroup X] [DGAddCommGroup X] [Module T X] [Module Tᵐᵒᵖ X]
  [DGBimodule T T X]

variable (T) in
/-- The regular module `T` placed in degree `0`, in Mathlib's derived category. -/
abbrev regularSingle : _root_.DerivedCategory (ModuleCat.{0} T) :=
  (_root_.DerivedCategory.singleFunctor (ModuleCat.{0} T) 0).obj (ModuleCat.of T T)

/-- **A derived tensor functor fixing the regular module is the identity, on Mathlib's derived
category.** Let `X` be a dg `(T, T)`-bimodule and `S' : D(Mod T) ⥤ D(Mod T)` with
`cS : (X ⊗ᴸ_T -) ⋙ E ≅ E ⋙ S'` for the comparison `E = DG.DegreeZero.derivedComparison T`. If
`φ : S'(T) ≅ T` commutes with the right multiplications `ρ_t` of `T` (`hφ`), then `S' ≅ 𝟭`. -/
def derivedTensorIsoIdOfRegularIsoModuleCat
    (S' : _root_.DerivedCategory (ModuleCat.{0} T) ⥤ _root_.DerivedCategory (ModuleCat.{0} T))
    (cS : dgDerivedTensor.{0} T T X ⋙ derivedComparison T ≅ derivedComparison T ⋙ S')
    (φ : S'.obj (regularSingle T) ≅ regularSingle T)
    (hφ : ∀ t : T, S'.map ((_root_.DerivedCategory.singleFunctor (ModuleCat.{0} T) 0).map
        (moduleRightAct T t)) ≫ φ.hom =
      φ.hom ≫ (_root_.DerivedCategory.singleFunctor (ModuleCat.{0} T) 0).map
        (moduleRightAct T t)) :
    S' ≅ 𝟭 _ :=
  let E := derivedComparisonEquivalence T
  let ψ := cS.app (Q.obj (DGModuleCat.of T T)) ≪≫ S'.mapIso (derivedComparisonObjSelfIso T) ≪≫
    φ ≪≫ (derivedComparisonObjSelfIso T).symm
  let φdg := E.fullyFaithfulFunctor.preimageIso ψ
  have hφdg : ∀ t : T, (dgDerivedTensor.{0} T T X).map (Q.map (regularRightMul T t)) ≫
      φdg.hom = φdg.hom ≫ Q.map (regularRightMul T t) := fun t => by
    apply E.functor.map_injective
    have h₁ := cS.hom.naturality (Q.map (regularRightMul T t))
    have h₂ := congrArg S'.map (derivedComparisonObjSelfIso_rightMul t)
    have h₃ : (_root_.DerivedCategory.singleFunctor (ModuleCat.{0} T) 0).map
        (moduleRightAct T t) ≫ (derivedComparisonObjSelfIso T).inv =
          (derivedComparisonObjSelfIso T).inv ≫ (derivedComparison T).map
            (Q.map (regularRightMul T t)) := by
      rw [Iso.comp_inv_eq, Category.assoc, derivedComparisonObjSelfIso_rightMul t,
        Iso.inv_hom_id_assoc]
    simp only [S'.map_comp] at h₂
    simp only [Functor.comp_map] at h₁
    simp only [Functor.map_comp, φdg, Functor.FullyFaithful.preimageIso_hom,
      Functor.FullyFaithful.map_preimage]
    simp only [ψ, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
    dsimp only [E, derivedComparisonEquivalence_functor]
    rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% (hφ t), h₃]
  let e := dgDerivedTensorIsoIdOfRegularIso φdg hφdg
  (Functor.leftUnitor S').symm ≪≫ Functor.isoWhiskerRight E.counitIso.symm S' ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft E.inverse cS.symm ≪≫
    Functor.isoWhiskerLeft E.inverse (Functor.isoWhiskerRight e _ ≪≫ Functor.leftUnitor _) ≪≫
    E.counitIso

end Categorification
