/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DegreewiseTensor
import Categorification.Algebra.DerivedTensorCoefficient

set_option backward.isDefEq.respectTransparency false

/-!
# Naturality of the degreewise comparison of derived tensor products in the bimodule

For a bimodule map `f : M → M'` of `(A, B)`-bimodules that are projective as right
`B`-modules, the comparison `derivedTensorComparisonIso` of `M ⊗ᴸ_B -` with the derived functor
of the exact functor `M ⊗_B -` carries the coefficient map `derivedTensorCoefficientMap f`
to the derived functor of the natural transformation `f ⊗_B -`
(`derivedTensorComparisonIso_coefficient_naturality`).

This is used for Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.21: it identifies the dots on the derived
functors `𝔈_i` (defined by conjugating the module-level dot along the comparison) with
coefficient maps, whose compatibility with the homological shift is known.

## Main results

* `ordTensorCoefficientMap f hf : ordTensor A B M ⟶ ordTensor A B M'`, `f ⊗_B -`.
* `QCompDerivedTensorIso_coefficient_naturality`.
* `tensorFunctorCompComplexIso_coefficient_naturality`.
* `derivedTensorComparisonIso_coefficient_naturality`.
-/

open CategoryTheory DG DG.DegreeZero MulOpposite
open scoped DG.DegreeZero

noncomputable section

namespace Categorification

universe w w' u

variable {A B : Type u} [Ring A] [Ring B]
  {M M' : Type u} [AddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]
  [AddCommGroup M'] [Module A M'] [Module Bᵐᵒᵖ M'] [SMulCommClass A Bᵐᵒᵖ M']
  (f : M →ₗ[A] M') (hf : ∀ (b : B) (m : M), f (op b • m) = op b • f m)

/-! ### `f ⊗_B -` on ordinary modules -/

/-- `f ⊗_B N`, linearly over `A`. -/
def ordTensorCoefficientHom (N : ModuleCat.{u} B) :
    TensorProductOver B (InDegreeZero M) (InDegreeZero N) →ₗ[A]
      TensorProductOver B (InDegreeZero M') (InDegreeZero N) where
  toFun := TensorProductOver.map
    ({ toFun := f, map_add' := map_add f, map_smul' := fun b m => hf b.unop m } :
      InDegreeZero M →ₗ[Bᵐᵒᵖ] InDegreeZero M')
    (LinearMap.id : InDegreeZero N →ₗ[B] InDegreeZero N)
  map_add' := map_add _
  map_smul' a t := by
    induction t using TensorProductOver.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | tmul m n =>
      change TensorProductOver.tmul B (show InDegreeZero M' from f (a • m)) n =
        a • TensorProductOver.tmul B (show InDegreeZero M' from f m) n
      rw [map_smul]; rfl
    | add t t' ht ht' => rw [smul_add, map_add, map_add, ht, ht', smul_add]

/-- **`f ⊗_B -`**, the natural transformation `M ⊗_B - ⟶ M' ⊗_B -` of functors on ordinary
modules induced by a bimodule map `f`. -/
def ordTensorCoefficientMap : ordTensor A B M ⟶ ordTensor A B M' where
  app N := ModuleCat.ofHom (ordTensorCoefficientHom f hf N)
  naturality _ _ _ := ModuleCat.hom_ext (LinearMap.toAddMonoidHom_injective
    (TensorProductOver.addHom_ext fun _ _ => rfl))

theorem ordTensorCoefficientMap_tmul (N : ModuleCat.{u} B) (m : InDegreeZero M)
    (n : InDegreeZero N) :
    ((ordTensorCoefficientMap f hf).app N).hom (TensorProductOver.tmul B m n) =
      TensorProductOver.tmul B (show InDegreeZero M' from f m) n := rfl

/-! ### On the homotopy and derived categories of dg modules -/

section DG

variable [HasDerivedCategory.{w, u} A] [HasDerivedCategory.{w, u} B]

open DG.DerivedCategory

/-- The coefficient map on the homotopy category, as the descent of
`ordinaryTensorCoefficientMap`. -/
private def homotopyCoeff :
    DG.HomotopyCategory.tensorFunctor (B := B) A (InDegreeZero M) ⟶
      DG.HomotopyCategory.tensorFunctor (B := B) A (InDegreeZero M') :=
  CategoryTheory.Quotient.natTransLift _
    ((DG.HomotopyCategory.tensorFunctorQuotientIso A (InDegreeZero M)).hom ≫
      Functor.whiskerRight (ordinaryTensorCoefficientMap f hf)
        (DG.HomotopyCategory.quotient A) ≫
      (DG.HomotopyCategory.tensorFunctorQuotientIso A (InDegreeZero M')).inv)

private theorem derivedTensorCoefficientMap_eq :
    derivedTensorCoefficientMap.{u, w} f hf =
      Functor.whiskerLeft (kProjectiveEquivalence.{w} B).inverse
        (Functor.whiskerLeft (DG.HomotopyCategory.subcategoryKProjective B).ι
          (Functor.whiskerRight (homotopyCoeff f hf) (Qh (A := A)))) := rfl

omit [HasDerivedCategory.{w, u} A] [HasDerivedCategory.{w, u} B] in
private theorem homotopyCoeff_app (X : DGModuleCat.{u} B) :
    (homotopyCoeff f hf).app ((DG.HomotopyCategory.quotient B).obj X) ≫
        (DG.HomotopyCategory.tensorFunctorQuotientIso A (InDegreeZero M')).hom.app X =
      (DG.HomotopyCategory.tensorFunctorQuotientIso A (InDegreeZero M)).hom.app X ≫
        (DG.HomotopyCategory.quotient A).map ((ordinaryTensorCoefficientMap f hf).app X) := by
  change ((DG.HomotopyCategory.tensorFunctorQuotientIso A (InDegreeZero M)).hom.app X ≫
    (DG.HomotopyCategory.quotient A).map ((ordinaryTensorCoefficientMap f hf).app X) ≫
      (DG.HomotopyCategory.tensorFunctorQuotientIso A (InDegreeZero M')).inv.app X) ≫ _ = _
  simp

variable [Module.Projective Bᵐᵒᵖ M] [Module.Projective Bᵐᵒᵖ M']

/-- The coefficient map on the functors induced by `M ⊗_B -`. -/
private def exactCoeff : exactDerivedTensor.{w} A B M ⟶ exactDerivedTensor.{w} A B M' :=
  Localization.liftNatTrans Qh (DG.HomotopyCategory.quasiIso B) _ _ _ _
    (Functor.whiskerRight (homotopyCoeff f hf) Qh)

private theorem derivedTensorIsoExact_naturality :
    derivedTensorCoefficientMap.{u, w} f hf ≫ (derivedTensorIsoExact.{w} A B M').hom =
      (derivedTensorIsoExact.{w} A B M).hom ≫ exactCoeff f hf := by
  ext Y
  have h := Localization.liftNatTrans_app Qh (DG.HomotopyCategory.quasiIso B) _ _
    (exactDerivedTensor.{w} A B M) (exactDerivedTensor.{w} A B M')
    (Functor.whiskerRight (homotopyCoeff f hf) Qh)
    ((DG.HomotopyCategory.subcategoryKProjective B).ι.obj
      ((kProjectiveEquivalence.{w} B).inverse.obj Y))
  change (exactCoeff f hf).app _ = _ at h
  have hnat := (exactCoeff f hf).naturality ((kProjectiveEquivalence.{w} B).counitIso.hom.app Y)
  dsimp only [derivedTensorIsoExact, NatTrans.comp_app, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app, Functor.associator_hom_app,
    Functor.leftUnitor_hom_app]
  simp only [Category.id_comp, Category.assoc]
  erw [Category.id_comp, Category.comp_id, hnat, h]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_app_assoc]
  rfl

/-- **`M ⊗ᴸ_B -` is computed by `M ⊗_B -` on the homotopy category, naturally in `M`.** -/
private theorem QhCompDerivedTensorIso_naturality (Z : DG.HomotopyCategory B) :
    (derivedTensorCoefficientMap.{u, w} f hf).app (Qh.obj Z) ≫
        (QhCompDerivedTensorIso.{w} A B M').hom.app Z =
      (QhCompDerivedTensorIso.{w} A B M).hom.app Z ≫ Qh.map ((homotopyCoeff f hf).app Z) := by
  have h₁ := congrArg (fun t => NatTrans.app t (Qh.obj Z)) (derivedTensorIsoExact_naturality f hf)
  have h₂ := Localization.liftNatTrans_app Qh (DG.HomotopyCategory.quasiIso B) _ _
    (exactDerivedTensor.{w} A B M) (exactDerivedTensor.{w} A B M')
    (Functor.whiskerRight (homotopyCoeff f hf) Qh) Z
  change (exactCoeff f hf).app _ = _ at h₂
  simp only [NatTrans.comp_app] at h₁
  simp only [QhCompDerivedTensorIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
  rw [← Category.assoc, h₁, Category.assoc, h₂]
  simp

/-- **`M ⊗ᴸ_B -` is computed by `M ⊗_B -` on every dg module, naturally in `M`**: the
comparison `QCompDerivedTensorIso` carries the derived coefficient map to the dg coefficient
map. -/
theorem QCompDerivedTensorIso_coefficient_naturality (X : DGModuleCat.{u} B) :
    (derivedTensorCoefficientMap.{u, w} f hf).app (Q.obj X) ≫
        (QCompDerivedTensorIso.{w} A B M').hom.app X =
      (QCompDerivedTensorIso.{w} A B M).hom.app X ≫
        Q.map ((ordinaryTensorCoefficientMap f hf).app X) := by
  have h := QhCompDerivedTensorIso_naturality f hf ((DG.HomotopyCategory.quotient B).obj X)
  have h' := congrArg (Qh (A := A)).map (homotopyCoeff_app f hf X)
  simp only [Functor.map_comp] at h'
  simp only [QCompDerivedTensorIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_hom, Category.id_comp, Category.comp_id, Category.assoc]
  erw [Category.id_comp, Category.id_comp]
  change (derivedTensorCoefficientMap.{u, w} f hf).app
      (Qh.obj ((DG.HomotopyCategory.quotient B).obj X)) ≫ _ = _
  rw [← Category.assoc, h, Category.assoc, h']
  rfl

end DG

/-! ### The degreewise description, naturally in the bimodule -/

section Degreewise

/-- **`M ⊗_B (⨁ₙ Kⁿ) ≅ ⨁ₙ (M ⊗_B Kⁿ)`, naturally in `M`.** -/
theorem tensorComplexSumIso_coefficient_naturality (K : CochainComplex (ModuleCat.{u} B) ℤ) :
    (ordinaryTensorCoefficientMap f hf).app ((DGModuleCat.ofComplex B).obj K) ≫
        (tensorComplexSumIso A M').hom.app K =
      (tensorComplexSumIso A M).hom.app K ≫ (DGModuleCat.ofComplex A).map
        ((NatTrans.mapHomologicalComplex (ordTensorCoefficientMap f hf)
          (ComplexShape.up ℤ)).app K) :=
  DGModuleCat.tensor_hom_ext fun m z => by
    change tensorComplexSumFwd (M := M') K
        (TensorProductOver.tmul B (show InDegreeZero M' from f m) z) =
      ComplexSum.map _ (tensorComplexSumFwd (M := M) K (TensorProductOver.tmul B m z))
    induction z using ComplexSum.induction_on with
    | zero => rw [TensorProductOver.tmul_zero, TensorProductOver.tmul_zero, map_zero, map_zero,
        map_zero]
    | of n x =>
      rw [tensorComplexSumFwd_tmul_of, tensorComplexSumFwd_tmul_of]
      erw [ComplexSum.map_of]
      rfl
    | add z z' hz hz' => rw [TensorProductOver.tmul_add, TensorProductOver.tmul_add, map_add,
        map_add, map_add, hz, hz']

/-- **The underlying complex of `M ⊗_B X` is `M ⊗_B -` applied degreewise, naturally in
`M`.** -/
theorem tensorFunctorCompComplexIso_coefficient_naturality (X : DGModuleCat.{u} B) :
    (complexFunctor A).map ((ordinaryTensorCoefficientMap f hf).app X) ≫
        (tensorFunctorCompComplexIso A M').hom.app X =
      (tensorFunctorCompComplexIso A M).hom.app X ≫
        (NatTrans.mapHomologicalComplex (ordTensorCoefficientMap f hf)
          (ComplexShape.up ℤ)).app ((complexFunctor B).obj X) := by
  have h₁ := (ordinaryTensorCoefficientMap f hf).naturality
    ((complexEquivalence B).unitIso.hom.app X)
  have h₂ := tensorComplexSumIso_coefficient_naturality f hf ((complexFunctor B).obj X)
  have h₃ := (ofComplexCompIso A).hom.naturality
    ((NatTrans.mapHomologicalComplex (ordTensorCoefficientMap f hf)
      (ComplexShape.up ℤ)).app ((complexFunctor B).obj X))
  simp only [tensorFunctorCompComplexIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.leftUnitor_inv_app,
    Functor.rightUnitor_hom_app, Iso.symm_hom, Category.id_comp]
  repeat erw [Category.id_comp]
  repeat erw [Category.comp_id]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc]
  erw [← h₁]
  rw [Functor.map_comp_assoc]
  congr 1
  rw [← Functor.map_comp_assoc]
  erw [h₂]
  rw [Functor.map_comp_assoc]
  erw [h₃]
  rfl

end Degreewise

/-! ### The comparison with Mathlib's derived categories, naturally in the bimodule -/

section Comparison

variable [Module.Projective Bᵐᵒᵖ M] [Module.Projective Bᵐᵒᵖ M'] [HasDerivedCategory.{w, u} A]
  [HasDerivedCategory.{w, u} B] [_root_.HasDerivedCategory.{w'} (ModuleCat.{u} A)]
  [_root_.HasDerivedCategory.{w'} (ModuleCat.{u} B)]

variable (A B M) in
private theorem derivedTensorComparisonIso_hom_app_Q (X : DGModuleCat.{u} B) :
    (derivedTensorComparisonIso.{w, w'} A B M).hom.app (DG.DerivedCategory.Q.obj X) =
      (QCompDerivedTensorComparisonIso.{w, w'} A B M).hom.app X :=
  congr_app ((Localization.whiskeringLeftFunctor' DG.DerivedCategory.Q (DGModuleCat.quasiIso B)
    (_root_.DerivedCategory (ModuleCat.{u} A))).map_preimage
      (QCompDerivedTensorComparisonIso.{w, w'} A B M).hom) X

/-- **The comparison of `M ⊗ᴸ_B -` with the derived functor of `M ⊗_B -` is natural in the
bimodule `M`**: it carries the derived coefficient map of a bimodule map `f` to the derived
functor of `f ⊗_B -`. -/
theorem derivedTensorComparisonIso_coefficient_naturality :
    Functor.whiskerRight (derivedTensorCoefficientMap.{u, w} f hf)
        (derivedComparison.{w, w'} A) ≫ (derivedTensorComparisonIso.{w, w'} A B M').hom =
      (derivedTensorComparisonIso.{w, w'} A B M).hom ≫
        Functor.whiskerLeft (derivedComparison.{w, w'} B)
          (NatTrans.mapDerivedCategory (ordTensorCoefficientMap f hf)) := by
  refine Localization.natTrans_ext DG.DerivedCategory.Q (DGModuleCat.quasiIso B) fun X => ?_
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    derivedTensorComparisonIso_hom_app_Q]
  have h₁ := congrArg (derivedComparison.{w, w'} A).map
    (QCompDerivedTensorIso_coefficient_naturality.{w} f hf X)
  have h₂ := (QCompDerivedComparisonIso.{w, w'} A).hom.naturality
    ((ordinaryTensorCoefficientMap f hf).app X)
  have h₃ := congrArg (_root_.DerivedCategory.Q (C := ModuleCat.{u} A)).map
    (tensorFunctorCompComplexIso_coefficient_naturality f hf X)
  have h₄ := NatTrans.mapDerivedCategory_app_Q_obj (ordTensorCoefficientMap f hf)
    ((complexFunctor B).obj X)
  have h₅ := (NatTrans.mapDerivedCategory (ordTensorCoefficientMap f hf)).naturality
    ((QCompDerivedComparisonIso.{w, w'} B).inv.app X)
  simp only [Functor.map_comp] at h₁ h₃
  simp only [QCompDerivedTensorComparisonIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Iso.symm_hom, Category.id_comp, Category.assoc]
  have h₄' : _root_.DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (ordTensorCoefficientMap f hf) (ComplexShape.up ℤ)).app ((complexFunctor B).obj X)) ≫
        (ordTensor A B M').mapDerivedCategoryFactors.inv.app ((complexFunctor B).obj X) =
      (ordTensor A B M).mapDerivedCategoryFactors.inv.app ((complexFunctor B).obj X) ≫
        (NatTrans.mapDerivedCategory (ordTensorCoefficientMap f hf)).app
          (_root_.DerivedCategory.Q.obj ((complexFunctor B).obj X)) := by
    rw [h₄]; simp
  erw [Category.comp_id]
  rw [reassoc_of% h₁]
  erw [reassoc_of% h₂]
  erw [reassoc_of% h₃]
  erw [reassoc_of% h₄']
  erw [← h₅]
  rfl

end Comparison

end Categorification
