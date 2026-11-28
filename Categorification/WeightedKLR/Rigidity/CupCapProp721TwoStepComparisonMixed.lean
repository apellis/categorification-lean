/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721TwoStepComparison

/-!
# Two-step comparisons between different composites of derived tensor products

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21. The crossing of two black strands of different colours `a ≠ b` relates
`𝔈_a 𝔈_b` and `𝔈_b 𝔈_a`, two composites of derived tensor products through different
intermediate algebras. This file extends `CupCap.whiskerLeft_Q_comparisonConj_of_degreewise`
and `derivedTensorTwo_commShift_of_QComp` from endomorphisms of one composite
`(N ⊗_C -) ⋙ (M ⊗_B -)` to natural transformations into a second composite
`(N' ⊗_C -) ⋙ (M' ⊗_{B'} -)`.

## Main results

* `CupCap.whiskerLeft_Q_comparisonConj_between_of_degreewise`: a conjugate of a derived
  transformation `θ₀ : GN ⋙ GM ⟶ GN' ⋙ GM'` along the pasted two-step comparisons is induced on
  dg modules by any dg transformation that agrees degreewise with `θ₀`.
* `derivedTensorTwo_commShift_between_of_QComp`: such a conjugate commutes with the derived
  tensor shifts when the dg transformation does.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits DG DG.DegreeZero

noncomputable section

namespace Categorification

universe w w' u

section CommShift

variable {A B B' C : Type u} [Ring A] [Ring B] [Ring B'] [Ring C]
  [DG.HasDerivedCategory.{w, u} A] [DG.HasDerivedCategory.{w, u} B]
  [DG.HasDerivedCategory.{w, u} B'] [DG.HasDerivedCategory.{w, u} C]
  (M : Type u) [AddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]
  (N : Type u) [AddCommGroup N] [Module B N] [Module Cᵐᵒᵖ N] [SMulCommClass B Cᵐᵒᵖ N]
  (M' : Type u) [AddCommGroup M'] [Module A M'] [Module B'ᵐᵒᵖ M'] [SMulCommClass A B'ᵐᵒᵖ M']
  (N' : Type u) [AddCommGroup N'] [Module B' N'] [Module Cᵐᵒᵖ N'] [SMulCommClass B' Cᵐᵒᵖ N']
  [Module.Projective Bᵐᵒᵖ M] [Module.Projective Cᵐᵒᵖ N]
  [Module.Projective B'ᵐᵒᵖ M'] [Module.Projective Cᵐᵒᵖ N']

local instance (X : Type u) [AddCommGroup X] : Fact (∀ m : InDegreeZero X, m ∈ grading 0) :=
  ⟨fun _ => (InDegreeZero.mem_grading_iff (M := X)).mpr (Or.inl rfl)⟩

/-- **A transformation between composites of derived tensor functors commutes with the shift**
when it is induced on dg modules, through `QCompDerivedTensorTwoIso`, by a transformation of
dg tensor functors that commutes with the shift. -/
theorem derivedTensorTwo_commShift_between_of_QComp
    (α : derivedTensor.{w} B C N ⋙ derivedTensor.{w} A B M ⟶
      derivedTensor.{w} B' C N' ⋙ derivedTensor.{w} A B' M')
    (θ : DGModuleCat.tensorFunctor B (InDegreeZero N) ⋙
        DGModuleCat.tensorFunctor A (InDegreeZero M) ⟶
      DGModuleCat.tensorFunctor B' (InDegreeZero N') ⋙
        DGModuleCat.tensorFunctor A (InDegreeZero M'))
    [NatTrans.CommShift θ ℤ]
    (h : Functor.whiskerLeft DG.DerivedCategory.Q α ≫
        (QCompDerivedTensorTwoIso.{w} (A := A) (B := B') (C := C) M' N').hom =
      (QCompDerivedTensorTwoIso.{w} (A := A) (B := B) (C := C) M N).hom ≫
        Functor.whiskerRight θ DG.DerivedCategory.Q) :
    NatTrans.CommShift α ℤ := by
  have : NatTrans.CommShift (Functor.whiskerLeft DG.DerivedCategory.Q α) ℤ := by
    have h' : Functor.whiskerLeft DG.DerivedCategory.Q α =
        (QCompDerivedTensorTwoIso.{w} (A := A) (B := B) (C := C) M N).hom ≫
          Functor.whiskerRight θ DG.DerivedCategory.Q ≫
            (QCompDerivedTensorTwoIso.{w} (A := A) (B := B') (C := C) M' N').inv := by
      rw [← reassoc_of% h, Iso.hom_inv_id, Category.comp_id]
    rw [h']
    infer_instance
  have := Localization.essSurj (DG.DerivedCategory.Q (A := C)) (DGModuleCat.quasiIso C)
  exact natTransCommShift_of_whiskerLeft_essSurj DG.DerivedCategory.Q α

end CommShift

namespace Stendhal.CupCap

section TwoStep

variable {A B B' C : Type u} [Ring A] [Ring B] [Ring B'] [Ring C]
  (M : Type u) [AddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]
  (N : Type u) [AddCommGroup N] [Module B N] [Module Cᵐᵒᵖ N] [SMulCommClass B Cᵐᵒᵖ N]
  {GM : ModuleCat.{u} B ⥤ ModuleCat.{u} A} [GM.Additive] (eM : ordTensor A B M ≅ GM)
  {GN : ModuleCat.{u} C ⥤ ModuleCat.{u} B} [GN.Additive] (eN : ordTensor B C N ≅ GN)
  (M' : Type u) [AddCommGroup M'] [Module A M'] [Module B'ᵐᵒᵖ M'] [SMulCommClass A B'ᵐᵒᵖ M']
  (N' : Type u) [AddCommGroup N'] [Module B' N'] [Module Cᵐᵒᵖ N'] [SMulCommClass B' Cᵐᵒᵖ N']
  {GM' : ModuleCat.{u} B' ⥤ ModuleCat.{u} A} [GM'.Additive] (eM' : ordTensor A B' M' ≅ GM')
  {GN' : ModuleCat.{u} C ⥤ ModuleCat.{u} B'} [GN'.Additive] (eN' : ordTensor B' C N' ≅ GN')
  [Module.Projective Bᵐᵒᵖ M] [Module.Projective Cᵐᵒᵖ N]
  [Module.Projective B'ᵐᵒᵖ M'] [Module.Projective Cᵐᵒᵖ N']
  [DG.HasDerivedCategory.{w, u} A] [DG.HasDerivedCategory.{w, u} B]
  [DG.HasDerivedCategory.{w, u} B'] [DG.HasDerivedCategory.{w, u} C]
  [_root_.HasDerivedCategory.{w'} (ModuleCat.{u} A)]
  [_root_.HasDerivedCategory.{w'} (ModuleCat.{u} B)]
  [_root_.HasDerivedCategory.{w'} (ModuleCat.{u} B')]
  [_root_.HasDerivedCategory.{w'} (ModuleCat.{u} C)]
  [PreservesFiniteLimits GM] [PreservesFiniteColimits GM]
  [PreservesFiniteLimits GN] [PreservesFiniteColimits GN]
  [PreservesFiniteLimits GM'] [PreservesFiniteColimits GM']
  [PreservesFiniteLimits GN'] [PreservesFiniteColimits GN']

/-- **A conjugate of a derived transformation between two composites along the pasted two-step
comparisons is induced on dg modules by any dg transformation that agrees degreewise with the
exact one.** For `θ` from `(N ⊗_C -) ⋙ (M ⊗_B -)` to `(N' ⊗_C -) ⋙ (M' ⊗_{B'} -)` and `θ₀` from
`GN ⋙ GM` to `GN' ⋙ GM'`, intertwined by `CupCap.tensorComplexTwoStep`, the conjugate of `θ₀` on
derived categories corresponds to `θ` through `QCompDerivedTensorTwoIso`. -/
theorem whiskerLeft_Q_comparisonConj_between_of_degreewise
    (θ : DGModuleCat.tensorFunctor B (InDegreeZero N) ⋙
        DGModuleCat.tensorFunctor A (InDegreeZero M) ⟶
      DGModuleCat.tensorFunctor B' (InDegreeZero N') ⋙
        DGModuleCat.tensorFunctor A (InDegreeZero M'))
    (θ₀ : GN ⋙ GM ⟶ GN' ⋙ GM')
    (hθ : ∀ X, (complexFunctor A).map (θ.app X) ≫ (tensorComplexTwoStep M' N' eM' eN').hom.app X =
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
          (squarePaste (derivedTensorComparisonIso.{w, w'} A B' M' ≪≫
              Functor.isoWhiskerLeft (derivedComparison.{w, w'} B')
                (mapDerivedCategoryIsoOfIso eM'))
            (derivedTensorComparisonIso.{w, w'} B' C N' ≪≫
              Functor.isoWhiskerLeft (derivedComparison.{w, w'} C)
                (mapDerivedCategoryIsoOfIso eN')))
          ((Functor.mapDerivedCategoryCompIso GN GM).hom ≫ θ₀.mapDerivedCategory ≫
            (Functor.mapDerivedCategoryCompIso GN' GM').inv)) ≫
        (QCompDerivedTensorTwoIso.{w} (A := A) (B := B') (C := C) M' N').hom =
      (QCompDerivedTensorTwoIso.{w} (A := A) (B := B) (C := C) M N).hom ≫
        Functor.whiskerRight θ DG.DerivedCategory.Q := by
  set P := squarePaste (derivedTensorComparisonIso.{w, w'} A B M ≪≫
      Functor.isoWhiskerLeft (derivedComparison.{w, w'} B) (mapDerivedCategoryIsoOfIso eM))
    (derivedTensorComparisonIso.{w, w'} B C N ≪≫
      Functor.isoWhiskerLeft (derivedComparison.{w, w'} C) (mapDerivedCategoryIsoOfIso eN))
  set P' := squarePaste (derivedTensorComparisonIso.{w, w'} A B' M' ≪≫
      Functor.isoWhiskerLeft (derivedComparison.{w, w'} B') (mapDerivedCategoryIsoOfIso eM'))
    (derivedTensorComparisonIso.{w, w'} B' C N' ≪≫
      Functor.isoWhiskerLeft (derivedComparison.{w, w'} C) (mapDerivedCategoryIsoOfIso eN'))
  set αh := (Functor.mapDerivedCategoryCompIso GN GM).hom ≫ θ₀.mapDerivedCategory ≫
    (Functor.mapDerivedCategoryCompIso GN' GM').inv
  set iso2 := QCompDerivedTensorTwoIso.{w} (A := A) (B := B) (C := C) M N
  set iso2' := QCompDerivedTensorTwoIso.{w} (A := A) (B := B') (C := C) M' N'
  ext X
  apply (derivedComparison.{w, w'} A).map_injective
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.map_comp]
  rw [isComparisonConj_comparisonConj _ P P' αh (DG.DerivedCategory.Q.obj X)]
  have hP := squarePaste_comparisonOfIso_hom_app_Q.{w, w'} M N eM eN X
  have hP' := squarePaste_comparisonOfIso_hom_app_Q.{w, w'} M' N' eM' eN' X
  have hn₁ := αh.naturality ((QCompDerivedComparisonIso.{w, w'} C).inv.app X)
  have hn₂ := (QCompDerivedComparisonIso.{w, w'} A).hom.naturality (θ.app X)
  have hD := NatTrans.mapDerivedCategory_app_Q_obj θ₀ ((complexFunctor C).obj X)
  have hθ' := congrArg (_root_.DerivedCategory.Q (C := ModuleCat.{u} A)).map (hθ X)
  simp only [Functor.map_comp] at hθ'
  have key : P.hom.app (DG.DerivedCategory.Q.obj X) ≫
      αh.app ((derivedComparison.{w, w'} C).obj (DG.DerivedCategory.Q.obj X)) =
      (derivedComparison.{w, w'} A).map (iso2.hom.app X) ≫
        (derivedComparison.{w, w'} A).map (DG.DerivedCategory.Q.map (θ.app X)) ≫
        (derivedComparison.{w, w'} A).map (iso2'.inv.app X) ≫
        P'.hom.app (DG.DerivedCategory.Q.obj X) := by
    rw [hP, hP']
    simp only [Category.assoc]
    erw [← Functor.map_comp_assoc (derivedComparison.{w, w'} A) (iso2'.inv.app X),
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
  rw [← Functor.map_comp (derivedComparison.{w, w'} A) (iso2'.inv.app X), Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

end TwoStep

end Stendhal.CupCap

end Categorification
