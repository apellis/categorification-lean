/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DerivedTensorCompCommShift
import Categorification.WeightedKLR.Rigidity.CupCapProp721ComparisonSquare

/-!
# Two-step comparisons of derived tensor products and their endomorphisms

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21. The crossing on the dg derived `𝔈_i²` is defined as the conjugate of a derived
natural transformation of exact functors along the pasting of two comparison isomorphisms
`derivedTensorComparisonIso ≪≫ mapDerivedCategoryIsoOfIso e`. This file computes that pasting on
dg modules (`squarePaste_comparisonOfIso_hom_app_Q`) and deduces, generically, that such a
conjugate is induced on dg modules by any endomorphism `θ` of `(N ⊗_C -) ⋙ (M ⊗_B -)` that agrees
degreewise with the exact endomorphism (`whiskerLeft_Q_comparisonConj_of_degreewise`).

## Main results

* `CupCap.tensorComplexIsoOfIso`, `CupCap.tensorComplexTwoStep`.
* `CupCap.comparisonOfIso_hom_app_Q`.
* `CupCap.squarePaste_comparisonOfIso_hom_app_Q`.
* `CupCap.whiskerLeft_Q_comparisonConj_of_degreewise`.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits DG DG.DegreeZero

noncomputable section

namespace Categorification.Stendhal.CupCap

universe w w' u

section OneStep

variable {A B : Type u} [Ring A] [Ring B]
  (M : Type u) [AddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]
  {G : ModuleCat.{u} B ⥤ ModuleCat.{u} A} [G.Additive] (e : ordTensor A B M ≅ G)

/-- The underlying complex of `M ⊗_B X` is `G` applied degreewise, for `e : M ⊗_B - ≅ G`. -/
def tensorComplexIsoOfIso :
    DGModuleCat.tensorFunctor A (InDegreeZero M) ⋙ complexFunctor A ≅
      complexFunctor B ⋙ G.mapHomologicalComplex (ComplexShape.up ℤ) :=
  tensorFunctorCompComplexIso A M ≪≫
    Functor.isoWhiskerLeft _ (NatIso.mapHomologicalComplex e (ComplexShape.up ℤ))

variable [Module.Projective Bᵐᵒᵖ M] [DG.HasDerivedCategory.{w, u} A]
  [DG.HasDerivedCategory.{w, u} B] [_root_.HasDerivedCategory.{w'} (ModuleCat.{u} A)]
  [_root_.HasDerivedCategory.{w'} (ModuleCat.{u} B)]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

private theorem derivedTensorComparisonIso_hom_app_Q' (X : DGModuleCat.{u} B) :
    (derivedTensorComparisonIso.{w, w'} A B M).hom.app (DG.DerivedCategory.Q.obj X) =
      (QCompDerivedTensorComparisonIso.{w, w'} A B M).hom.app X :=
  congr_app ((Localization.whiskeringLeftFunctor' DG.DerivedCategory.Q (DGModuleCat.quasiIso B)
    (_root_.DerivedCategory (ModuleCat.{u} A))).map_preimage
      (QCompDerivedTensorComparisonIso.{w, w'} A B M).hom) X

/-- **The comparison `derivedTensorComparisonIso ≪≫ mapDerivedCategoryIsoOfIso e` on dg
modules.** -/
theorem comparisonOfIso_hom_app_Q (X : DGModuleCat.{u} B) :
    (derivedTensorComparisonIso.{w, w'} A B M ≪≫
        Functor.isoWhiskerLeft (derivedComparison.{w, w'} B) (mapDerivedCategoryIsoOfIso e)).hom.app
          (DG.DerivedCategory.Q.obj X) =
      (derivedComparison.{w, w'} A).map ((QCompDerivedTensorIso.{w} A B M).hom.app X) ≫
        (QCompDerivedComparisonIso.{w, w'} A).hom.app
          ((DGModuleCat.tensorFunctor A (InDegreeZero M)).obj X) ≫
        _root_.DerivedCategory.Q.map ((tensorComplexIsoOfIso M e).hom.app X) ≫
        G.mapDerivedCategoryFactors.inv.app ((complexFunctor B).obj X) ≫
        G.mapDerivedCategory.map ((QCompDerivedComparisonIso.{w, w'} B).inv.app X) := by
  have hnat := (mapDerivedCategoryIsoOfIso e).hom.naturality
    ((QCompDerivedComparisonIso.{w, w'} B).hom.app X)
  rw [mapDerivedCategoryIsoOfIso_hom_eq] at hnat
  have h2 : (NatTrans.mapDerivedCategory e.hom).app
        ((derivedComparison.{w, w'} B).obj (DG.DerivedCategory.Q.obj X)) =
      (ordTensor A B M).mapDerivedCategory.map ((QCompDerivedComparisonIso.{w, w'} B).hom.app X) ≫
        (NatTrans.mapDerivedCategory e.hom).app
          (_root_.DerivedCategory.Q.obj ((complexFunctor B).obj X)) ≫
        G.mapDerivedCategory.map ((QCompDerivedComparisonIso.{w, w'} B).inv.app X) := by
    erw [reassoc_of% hnat]
    rw [← Functor.map_comp, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  have hQ := NatTrans.mapDerivedCategory_app_Q_obj e.hom ((complexFunctor B).obj X)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, derivedTensorComparisonIso_hom_app_Q',
    mapDerivedCategoryIsoOfIso_hom_eq, h2, hQ]
  simp only [QCompDerivedTensorComparisonIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Iso.symm_hom, Category.id_comp, Category.assoc, tensorComplexIsoOfIso,
    Functor.map_comp]
  erw [← Functor.map_comp_assoc (ordTensor A B M).mapDerivedCategory, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]
  rfl

end OneStep

section Cancel

variable {C D E E' : Type*} [Category* C] [Category* D] [Category* E] [Category* E']

private theorem map_inv_hom_app_assoc {F G : C ⥤ D} (e : F ≅ G) (H : D ⥤ E) (x : C) {Z : E}
    (h : H.obj (G.obj x) ⟶ Z) : H.map (e.inv.app x) ≫ H.map (e.hom.app x) ≫ h = h := by
  rw [← H.map_comp_assoc]; simp

private theorem map_map_inv_hom_app_assoc {F G : C ⥤ D} (e : F ≅ G) (K : D ⥤ E) (H : E ⥤ E')
    (x : C) {Z : E'} (h : H.obj (K.obj (G.obj x)) ⟶ Z) :
    H.map (K.map (e.inv.app x)) ≫ H.map (K.map (e.hom.app x)) ≫ h = h := by
  rw [← H.map_comp_assoc, ← K.map_comp]; simp

end Cancel

section Comp

variable {C₁ C₂ C₃ : Type*} [Category* C₁] [Abelian C₁] [_root_.HasDerivedCategory.{w} C₁]
  [Category* C₂] [Abelian C₂] [_root_.HasDerivedCategory.{w} C₂]
  [Category* C₃] [Abelian C₃] [_root_.HasDerivedCategory.{w} C₃]
  (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (G : C₂ ⥤ C₃) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- `Functor.mapDerivedCategoryCompIso` on a complex, in inverse form. -/
@[reassoc]
theorem mapDerivedCategoryCompIso_inv_app_Q_obj' (K : CochainComplex C₁ ℤ) :
    _root_.DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).hom.app K) ≫
      (F ⋙ G).mapDerivedCategoryFactors.inv.app K ≫
        (Functor.mapDerivedCategoryCompIso F G).inv.app (_root_.DerivedCategory.Q.obj K) =
      G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex _).obj K) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app K) := by
  rw [← cancel_mono ((Functor.mapDerivedCategoryCompIso F G).hom.app _)]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_Q_obj, ← Functor.map_comp_assoc,
    Iso.inv_hom_id_app]
  simp

end Comp

section TwoStep

variable {A B C : Type u} [Ring A] [Ring B] [Ring C]
  (M : Type u) [AddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]
  (N : Type u) [AddCommGroup N] [Module B N] [Module Cᵐᵒᵖ N] [SMulCommClass B Cᵐᵒᵖ N]
  {GM : ModuleCat.{u} B ⥤ ModuleCat.{u} A} [GM.Additive] (eM : ordTensor A B M ≅ GM)
  {GN : ModuleCat.{u} C ⥤ ModuleCat.{u} B} [GN.Additive] (eN : ordTensor B C N ≅ GN)

/-- The underlying complex of `M ⊗_B (N ⊗_C X)` is `GN ⋙ GM` applied degreewise. -/
def tensorComplexTwoStep :
    (DGModuleCat.tensorFunctor B (InDegreeZero N) ⋙
        DGModuleCat.tensorFunctor A (InDegreeZero M)) ⋙ complexFunctor A ≅
      complexFunctor C ⋙ (GN ⋙ GM).mapHomologicalComplex (ComplexShape.up ℤ) :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (tensorComplexIsoOfIso M eM) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (tensorComplexIsoOfIso N eN) _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.mapHomologicalComplexCompIso (Iso.refl (GN ⋙ GM)) (ComplexShape.up ℤ))

theorem tensorComplexTwoStep_hom_app (X : DGModuleCat.{u} C) :
    (tensorComplexTwoStep M N eM eN).hom.app X =
      (tensorComplexIsoOfIso M eM).hom.app ((DGModuleCat.tensorFunctor B (InDegreeZero N)).obj X) ≫
        (GM.mapHomologicalComplex _).map ((tensorComplexIsoOfIso N eN).hom.app X) ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (GN ⋙ GM)) (ComplexShape.up ℤ)).hom.app
          ((complexFunctor C).obj X) := by
  simp [tensorComplexTwoStep]

variable [Module.Projective Bᵐᵒᵖ M] [Module.Projective Cᵐᵒᵖ N] [DG.HasDerivedCategory.{w, u} A]
  [DG.HasDerivedCategory.{w, u} B] [DG.HasDerivedCategory.{w, u} C]
  [_root_.HasDerivedCategory.{w'} (ModuleCat.{u} A)]
  [_root_.HasDerivedCategory.{w'} (ModuleCat.{u} B)]
  [_root_.HasDerivedCategory.{w'} (ModuleCat.{u} C)]
  [PreservesFiniteLimits GM] [PreservesFiniteColimits GM]
  [PreservesFiniteLimits GN] [PreservesFiniteColimits GN]

/-- **The pasted two-step comparison on dg modules.** -/
theorem squarePaste_comparisonOfIso_hom_app_Q (X : DGModuleCat.{u} C) :
    (squarePaste (derivedTensorComparisonIso.{w, w'} A B M ≪≫
        Functor.isoWhiskerLeft (derivedComparison.{w, w'} B) (mapDerivedCategoryIsoOfIso eM))
      (derivedTensorComparisonIso.{w, w'} B C N ≪≫
        Functor.isoWhiskerLeft (derivedComparison.{w, w'} C)
          (mapDerivedCategoryIsoOfIso eN))).hom.app (DG.DerivedCategory.Q.obj X) =
      (derivedComparison.{w, w'} A).map
          ((QCompDerivedTensorTwoIso.{w} (A := A) (B := B) (C := C) M N).hom.app X) ≫
        (QCompDerivedComparisonIso.{w, w'} A).hom.app
          ((DGModuleCat.tensorFunctor A (InDegreeZero M)).obj
            ((DGModuleCat.tensorFunctor B (InDegreeZero N)).obj X)) ≫
        _root_.DerivedCategory.Q.map ((tensorComplexTwoStep M N eM eN).hom.app X) ≫
        (GN ⋙ GM).mapDerivedCategoryFactors.inv.app ((complexFunctor C).obj X) ≫
        (Functor.mapDerivedCategoryCompIso GN GM).inv.app
          (_root_.DerivedCategory.Q.obj ((complexFunctor C).obj X)) ≫
        (GN.mapDerivedCategory ⋙ GM.mapDerivedCategory).map
          ((QCompDerivedComparisonIso.{w, w'} C).inv.app X) := by
  set cM := derivedTensorComparisonIso.{w, w'} A B M ≪≫
    Functor.isoWhiskerLeft (derivedComparison.{w, w'} B) (mapDerivedCategoryIsoOfIso eM)
  have hn := cM.hom.naturality ((QCompDerivedTensorIso.{w} B C N).hom.app X)
  have h3 : cM.hom.app ((derivedTensor.{w} B C N).obj (DG.DerivedCategory.Q.obj X)) =
      (derivedTensor.{w} A B M ⋙ derivedComparison.{w, w'} A).map
          ((QCompDerivedTensorIso.{w} B C N).hom.app X) ≫
        cM.hom.app (DG.DerivedCategory.Q.obj
          ((DGModuleCat.tensorFunctor B (InDegreeZero N)).obj X)) ≫
        (derivedComparison.{w, w'} B ⋙ GM.mapDerivedCategory).map
          ((QCompDerivedTensorIso.{w} B C N).inv.app X) := by
    erw [reassoc_of% hn]
    simp only [Functor.comp_map, ← Functor.map_comp, Iso.hom_inv_id_app]
    simp
  rw [squarePaste_hom_app, h3]
  have hf := GM.mapDerivedCategoryFactors.inv.naturality
    ((tensorComplexIsoOfIso N eN).hom.app X)
  simp only [cM]
  rw [comparisonOfIso_hom_app_Q, comparisonOfIso_hom_app_Q]
  simp only [Functor.comp_map, Category.assoc, Functor.map_comp,
    map_inv_hom_app_assoc, map_map_inv_hom_app_assoc, tensorComplexTwoStep_hom_app,
    QCompDerivedTensorTwoIso, Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_hom, Category.id_comp]
  rw [show (derivedComparison.{w, w'} A).map (𝟙 _) = 𝟙 _ from (derivedComparison A).map_id _,
    Category.id_comp, mapDerivedCategoryCompIso_inv_app_Q_obj'_assoc]
  erw [reassoc_of% hf]

/-- **A conjugate of a derived endomorphism along the pasted two-step comparison is induced on
dg modules by any dg endomorphism that agrees degreewise with the exact endomorphism.** For
`θ` on `(N ⊗_C -) ⋙ (M ⊗_B -)` and `θ₀` on `GN ⋙ GM` intertwined by `tensorComplexTwoStep`,
the conjugate of `θ₀` on derived categories corresponds to `θ` through
`QCompDerivedTensorTwoIso`. -/
theorem whiskerLeft_Q_comparisonConj_of_degreewise
    (θ : DGModuleCat.tensorFunctor B (InDegreeZero N) ⋙
        DGModuleCat.tensorFunctor A (InDegreeZero M) ⟶
      DGModuleCat.tensorFunctor B (InDegreeZero N) ⋙ DGModuleCat.tensorFunctor A (InDegreeZero M))
    (θ₀ : GN ⋙ GM ⟶ GN ⋙ GM)
    (hθ : ∀ X, (complexFunctor A).map (θ.app X) ≫ (tensorComplexTwoStep M N eM eN).hom.app X =
      (tensorComplexTwoStep M N eM eN).hom.app X ≫
        (NatTrans.mapHomologicalComplex θ₀ (ComplexShape.up ℤ)).app ((complexFunctor C).obj X)) :
    Functor.whiskerLeft DG.DerivedCategory.Q
        (comparisonConj (Functor.FullyFaithful.ofFullyFaithful (derivedComparison.{w, w'} A))
          (squarePaste (derivedTensorComparisonIso.{w, w'} A B M ≪≫
              Functor.isoWhiskerLeft (derivedComparison.{w, w'} B)
                (mapDerivedCategoryIsoOfIso eM))
            (derivedTensorComparisonIso.{w, w'} B C N ≪≫
              Functor.isoWhiskerLeft (derivedComparison.{w, w'} C)
                (mapDerivedCategoryIsoOfIso eN)))
          (squarePaste (derivedTensorComparisonIso.{w, w'} A B M ≪≫
              Functor.isoWhiskerLeft (derivedComparison.{w, w'} B)
                (mapDerivedCategoryIsoOfIso eM))
            (derivedTensorComparisonIso.{w, w'} B C N ≪≫
              Functor.isoWhiskerLeft (derivedComparison.{w, w'} C)
                (mapDerivedCategoryIsoOfIso eN)))
          ((Functor.mapDerivedCategoryCompIso GN GM).hom ≫ θ₀.mapDerivedCategory ≫
            (Functor.mapDerivedCategoryCompIso GN GM).inv)) ≫
        (QCompDerivedTensorTwoIso.{w} (A := A) (B := B) (C := C) M N).hom =
      (QCompDerivedTensorTwoIso.{w} (A := A) (B := B) (C := C) M N).hom ≫
        Functor.whiskerRight θ DG.DerivedCategory.Q := by
  set P := squarePaste (derivedTensorComparisonIso.{w, w'} A B M ≪≫
      Functor.isoWhiskerLeft (derivedComparison.{w, w'} B) (mapDerivedCategoryIsoOfIso eM))
    (derivedTensorComparisonIso.{w, w'} B C N ≪≫
      Functor.isoWhiskerLeft (derivedComparison.{w, w'} C) (mapDerivedCategoryIsoOfIso eN))
  set αh := (Functor.mapDerivedCategoryCompIso GN GM).hom ≫ θ₀.mapDerivedCategory ≫
    (Functor.mapDerivedCategoryCompIso GN GM).inv
  set iso2 := QCompDerivedTensorTwoIso.{w} (A := A) (B := B) (C := C) M N
  ext X
  apply (derivedComparison.{w, w'} A).map_injective
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.map_comp]
  rw [isComparisonConj_comparisonConj _ P P αh (DG.DerivedCategory.Q.obj X)]
  -- the key identity `R ≫ αh = Φ (Q θ) ≫ R`
  have hP := squarePaste_comparisonOfIso_hom_app_Q.{w, w'} M N eM eN X
  have hn₁ := αh.naturality ((QCompDerivedComparisonIso.{w, w'} C).inv.app X)
  have hn₂ := (QCompDerivedComparisonIso.{w, w'} A).hom.naturality (θ.app X)
  have hD := NatTrans.mapDerivedCategory_app_Q_obj θ₀ ((complexFunctor C).obj X)
  have hθ' := congrArg (_root_.DerivedCategory.Q (C := ModuleCat.{u} A)).map (hθ X)
  simp only [Functor.map_comp] at hθ'
  have key : P.hom.app (DG.DerivedCategory.Q.obj X) ≫
      αh.app ((derivedComparison.{w, w'} C).obj (DG.DerivedCategory.Q.obj X)) =
      (derivedComparison.{w, w'} A).map (iso2.hom.app X) ≫
        (derivedComparison.{w, w'} A).map (DG.DerivedCategory.Q.map (θ.app X)) ≫
        (derivedComparison.{w, w'} A).map (iso2.inv.app X) ≫
        P.hom.app (DG.DerivedCategory.Q.obj X) := by
    rw [hP]
    simp only [Category.assoc]
    erw [← Functor.map_comp_assoc (derivedComparison.{w, w'} A) (iso2.inv.app X),
      Iso.inv_hom_id_app]
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
    congr 1
    erw [hn₁]
    simp only [αh, NatTrans.comp_app, Category.assoc]
    erw [Iso.inv_hom_id_app_assoc, hD]
    simp only [Category.assoc]
    erw [Iso.inv_hom_id_app_assoc, ← reassoc_of% hθ', reassoc_of% hn₂]
    rfl
  rw [reassoc_of% key]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← Functor.map_comp (derivedComparison.{w, w'} A) (iso2.inv.app X), Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

end TwoStep

end Categorification.Stendhal.CupCap
