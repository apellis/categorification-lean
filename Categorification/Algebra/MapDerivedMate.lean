/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.MapDerivedSigma
import Categorification.TwoRep.MateNat

/-!
# Mates of squares of exact functors on derived categories

Brundan, arXiv:1501.00350v1, (1.7): for adjunctions `L₁ ⊣ R₁`, `L₂ ⊣ R₂` and a square
`τ : G ⋙ L₂ ⟶ L₁ ⋙ H`, the mixed sideways crossing is the mate `R₁ ⋙ G ⟶ H ⋙ R₂`
(`TwoRep.mateNat`). For exact functors between abelian categories, the mate of the derived
adjunctions (`Adjunction.mapDerivedCategory`) and the derived square (`NatTrans.derivedComp τ`)
is the derived mate (`derivedComp_mateNat`). In particular, an invertible mate among exact
functors has an invertible derived mate (`isIso_mateNat_derived`).

This generalizes `NatTrans.derivedComp_functorSigma` (the case `G = L₁`, `H = L₂`).
-/

noncomputable section

namespace CategoryTheory

open Category Limits Categorification.TwoRep

universe w₁ w₂ w₃ w₄

variable {C₁ : Type*} [Category* C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type*} [Category* C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  {C₃ : Type*} [Category* C₃] [Abelian C₃] [HasDerivedCategory.{w₃} C₃]
  {C₄ : Type*} [Category* C₄] [Abelian C₄] [HasDerivedCategory.{w₄} C₄]

namespace NatTrans

variable {L₁ : C₁ ⥤ C₂} {R₁ : C₂ ⥤ C₁} {G : C₁ ⥤ C₃} {L₂ : C₃ ⥤ C₄} {R₂ : C₄ ⥤ C₃}
  {H : C₂ ⥤ C₄}
  [L₁.Additive] [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
  [R₁.Additive] [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [L₂.Additive] [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
  [R₂.Additive] [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
  [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]

/-- **The derived mate.** The mate of the derived adjunctions and the derived square is the
derived mate, through `mapDerivedCategoryCompIso`. -/
theorem derivedComp_mateNat (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (τ : G ⋙ L₂ ⟶ L₁ ⋙ H) :
    mateNat adj₂.mapDerivedCategory.unit (derivedComp τ) adj₁.mapDerivedCategory.counit =
      derivedComp (mateNat adj₂.unit τ adj₁.counit) := by
  refine derivedCategory_ext fun X => ?_
  let V := (R₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj X
  let Y := (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj V
  let a := R₁.mapDerivedCategoryFactors.app X
  let bG := G.mapDerivedCategoryFactors.app V
  let bL := L₁.mapDerivedCategoryFactors.app V
  let ψG : G.mapDerivedCategory.obj (R₁.mapDerivedCategory.obj (DerivedCategory.Q.obj X)) ≅
      DerivedCategory.Q.obj Y := G.mapDerivedCategory.mapIso a ≪≫ bG
  let ψL : L₁.mapDerivedCategory.obj (R₁.mapDerivedCategory.obj (DerivedCategory.Q.obj X)) ≅
      DerivedCategory.Q.obj ((L₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj V) :=
    L₁.mapDerivedCategory.mapIso a ≪≫ bL
  have hR : (derivedComp (mateNat adj₂.unit τ adj₁.counit)).app (DerivedCategory.Q.obj X) =
      ψG.hom ≫ DerivedCategory.Q.map ((mapHomologicalComplex (mateNat adj₂.unit τ adj₁.counit)
        (ComplexShape.up ℤ)).app X) ≫
        R₂.mapDerivedCategoryFactors.inv.app ((H.mapHomologicalComplex _).obj X) ≫
          R₂.mapDerivedCategory.map (H.mapDerivedCategoryFactors.inv.app X) := by
    rw [derivedComp_app_Q_obj]
    simp only [ψG, Iso.trans_hom, Functor.mapIso_hom, Category.assoc, a, bG, Iso.app_hom]
    rfl
  have h1 : adj₁.mapDerivedCategory.counit.app (DerivedCategory.Q.obj X) =
      ψL.hom ≫ DerivedCategory.Q.map (adj₁.mapCochainComplex.counit.app X) := by
    rw [Adjunction.mapDerivedCategory_counit_app]
    simp only [ψL, Iso.trans_hom, Functor.mapIso_hom, Category.assoc, a, bL, Iso.app_hom]
    rfl
  have h2 := adj₂.mapDerivedCategory.unit.naturality ψG.inv
  have h3 := Adjunction.mapDerivedCategory_unit_app adj₂ Y
  have h4 := (derivedComp τ).naturality a.inv
  have h5 := derivedComp_app_Q_obj τ V
  have K : L₂.mapDerivedCategory.map ψG.inv ≫ (derivedComp τ).app
        (R₁.mapDerivedCategory.obj (DerivedCategory.Q.obj X)) ≫
        H.mapDerivedCategory.map ψL.hom =
      L₂.mapDerivedCategoryFactors.hom.app Y ≫
        DerivedCategory.Q.map ((τ.mapHomologicalComplex (ComplexShape.up ℤ)).app V) ≫
          H.mapDerivedCategoryFactors.inv.app
            ((L₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj V) := by
    have c1 : H.mapDerivedCategory.map (L₁.mapDerivedCategory.map a.inv) ≫
        H.mapDerivedCategory.map (L₁.mapDerivedCategory.map a.hom) = 𝟙 _ := by
      rw [← Functor.map_comp, ← Functor.map_comp, a.inv_hom_id, Functor.map_id, Functor.map_id]
    have c2 : L₂.mapDerivedCategory.map bG.inv ≫ L₂.mapDerivedCategory.map bG.hom = 𝟙 _ := by
      rw [← Functor.map_comp, bG.inv_hom_id, Functor.map_id]
    have c3 : H.mapDerivedCategory.map bL.inv ≫ H.mapDerivedCategory.map bL.hom = 𝟙 _ := by
      rw [← Functor.map_comp, bL.inv_hom_id, Functor.map_id]
    simp only [Functor.comp_map] at h4
    simp only [ψG, ψL, Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv, Functor.mapIso_hom,
      Functor.map_comp, Category.assoc]
    rw [reassoc_of% h4, reassoc_of% c1, h5]
    simp only [bG, bL, Iso.app_hom, Iso.app_inv, Category.assoc] at c2 c3 ⊢
    rw [reassoc_of% c2, c3]
    erw [Category.comp_id]
  have h2' : adj₂.mapDerivedCategory.unit.app
        (G.mapDerivedCategory.obj (R₁.mapDerivedCategory.obj (DerivedCategory.Q.obj X))) =
      ψG.hom ≫ adj₂.mapDerivedCategory.unit.app (DerivedCategory.Q.obj Y) ≫
        R₂.mapDerivedCategory.map (L₂.mapDerivedCategory.map ψG.inv) := by
    simp only [Functor.id_map, Functor.comp_map] at h2
    rw [← h2, Iso.hom_inv_id_assoc]
  have hσ : (mapHomologicalComplex (mateNat adj₂.unit τ adj₁.counit)
      (ComplexShape.up ℤ)).app X = adj₂.mapCochainComplex.unit.app Y ≫
        (R₂.mapHomologicalComplex _).map ((τ.mapHomologicalComplex (ComplexShape.up ℤ)).app V ≫
          (H.mapHomologicalComplex _).map (adj₁.mapCochainComplex.counit.app X)) := by
    ext n
    simp [mateNat_app]
    rfl
  have nE := H.mapDerivedCategoryFactors.inv.naturality (adj₁.mapCochainComplex.counit.app X)
  have nR := R₂.mapDerivedCategoryFactors.inv.naturality
    ((τ.mapHomologicalComplex (ComplexShape.up ℤ)).app V ≫
      (H.mapHomologicalComplex _).map (adj₁.mapCochainComplex.counit.app X))
  simp only [Functor.comp_map] at nE nR
  have cE : R₂.mapDerivedCategory.map (L₂.mapDerivedCategoryFactors.inv.app Y) ≫
      R₂.mapDerivedCategory.map (L₂.mapDerivedCategoryFactors.hom.app Y) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id]
  rw [hR, mateNat_app, h1, h2', h3, hσ]
  have K' := congrArg R₂.mapDerivedCategory.map K
  simp only [Functor.map_comp] at K' ⊢
  simp only [Category.assoc]
  rw [reassoc_of% K', reassoc_of% cE]
  have nE' := congrArg R₂.mapDerivedCategory.map nE
  simp only [Functor.map_comp] at nE' nR
  simp only [Category.assoc] at nR
  erw [← nE']
  erw [reassoc_of% nR]
  rfl

/-- `derivedComp` of an isomorphism is an isomorphism. -/
theorem isIso_derivedComp {τ : G ⋙ L₂ ⟶ L₁ ⋙ H} [IsIso τ] : IsIso (derivedComp τ) := by
  have : IsIso (mapDerivedCategory τ) :=
    ⟨mapDerivedCategory (inv τ), by rw [← mapDerivedCategory_comp, IsIso.hom_inv_id,
        mapDerivedCategory_id], by rw [← mapDerivedCategory_comp, IsIso.inv_hom_id,
        mapDerivedCategory_id]⟩
  unfold derivedComp
  infer_instance

/-- **An invertible mate of exact functors has an invertible derived mate.** -/
theorem isIso_mateNat_derived (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (τ : G ⋙ L₂ ⟶ L₁ ⋙ H)
    [IsIso (mateNat adj₂.unit τ adj₁.counit)] :
    IsIso (mateNat adj₂.mapDerivedCategory.unit (derivedComp τ)
      adj₁.mapDerivedCategory.counit) := by
  rw [derivedComp_mateNat]
  exact isIso_derivedComp

end NatTrans

end CategoryTheory
