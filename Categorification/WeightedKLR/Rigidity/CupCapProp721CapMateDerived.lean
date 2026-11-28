/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.MapDerivedAdjunctionUnit

/-!
# Mates of derived squares

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21: the compatibility of `𝕂 ∘ 𝔈_i ≅ 𝔈_i ∘ 𝕂` and `𝕂 ∘ 𝔉_i ≅ 𝔉_i ∘ 𝕂` with the units
and counits of `𝔉_i ⊣ 𝔈_i` passes from module categories to Mathlib's derived categories. This
file gives the generic step: for adjunctions `L₁ ⊣ R₁`, `L₂ ⊣ R₂` of exact functors and a square
`α : G ⋙ L₂ ⟶ L₁ ⋙ H` of exact functors with mate `β`, the mate of the derived square of `α` along
the derived adjunctions (`Adjunction.mapDerivedCategory`) is the derived square of `β`
(`CupCap.mateEquiv_mapDerivedCategory`). A mate is recognised by its compatibility with the
counits (`CupCap.mateEquiv_eq_of_counit`).

## Main results

* `CupCap.mateEquiv_eq_of_counit`: `β` is the mate of `α` iff it is compatible with the counits.
* `CupCap.mapDerivedCategoryCompIso_comp_id_hom`, `CupCap.mapDerivedCategoryCompIso_id_comp_hom`:
  `mapDerivedCategoryCompIso` with an identity functor is `mapDerivedCategoryIdIso`.
* `CupCap.mateEquiv_mapDerivedCategory`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open CategoryTheory Limits Functor

section Mate

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
  {G : A ⥤ B} {H : C ⥤ D} {L₁ : A ⥤ C} {R₁ : C ⥤ A} {L₂ : B ⥤ D} {R₂ : D ⥤ B}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

/-- **A mate is recognised by its compatibility with the counits**: if
`L₂ β_d ≫ ε₂ = α_{R₁ d} ≫ H ε₁` for every `d`, then `β` is the mate of `α`. -/
theorem mateEquiv_eq_of_counit (α : TwoSquare G L₁ L₂ H) (β : TwoSquare R₁ H G R₂)
    (h : ∀ d : C, L₂.map (β.natTrans.app d) ≫ adj₂.counit.app (H.obj d) =
      α.natTrans.app (R₁.obj d) ≫ H.map (adj₁.counit.app d)) :
    mateEquiv adj₁ adj₂ α = β := by
  ext d
  apply (adj₂.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, h d]
  exact mateEquiv_counit adj₁ adj₂ α d

end Mate

section Derived

universe w₁ w₂ w₃ w₄

variable {C₁ C₂ : Type*} [Category* C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  [Category* C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

omit [HasDerivedCategory C₁] [HasDerivedCategory C₂] in
private theorem mapHomologicalComplexIdIso_hom_app_eq (X : CochainComplex C₂ ℤ) :
    (mapHomologicalComplexIdIso C₂ (ComplexShape.up ℤ)).hom.app X = 𝟙 _ := by
  ext n
  simp

omit [HasDerivedCategory C₁] [HasDerivedCategory C₂] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] in
private theorem mapHomologicalComplexCompIso_refl_hom_app {C₃ : Type*} [Category* C₃]
    [Abelian C₃] (G : C₂ ⥤ C₃) [G.Additive] (X : CochainComplex C₁ ℤ) :
    (mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).hom.app X = 𝟙 _ := by
  ext n
  simp

private theorem Q_map_mapHomologicalComplexIdIso (X : CochainComplex C₂ ℤ) :
    DerivedCategory.Q.map ((mapHomologicalComplexIdIso C₂ (ComplexShape.up ℤ)).hom.app X) =
      𝟙 _ := by
  rw [mapHomologicalComplexIdIso_hom_app_eq]
  exact DerivedCategory.Q.map_id _

omit [HasDerivedCategory C₁] [HasDerivedCategory C₂] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] in
private theorem Q_map_mapHomologicalComplexCompIso {C₃ : Type*} [Category* C₃] [Abelian C₃]
    [HasDerivedCategory C₃] (G : C₂ ⥤ C₃) [G.Additive] (X : CochainComplex C₁ ℤ) :
    DerivedCategory.Q.map
      ((mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).hom.app X) =
      𝟙 _ := by
  rw [mapHomologicalComplexCompIso_refl_hom_app]
  exact DerivedCategory.Q.map_id _

/-- `mapDerivedCategoryCompIso F (𝟭 _)` is the whiskering of `mapDerivedCategoryIdIso`. -/
theorem mapDerivedCategoryCompIso_comp_id_hom :
    (mapDerivedCategoryCompIso F (𝟭 C₂)).hom =
      whiskerLeft F.mapDerivedCategory (mapDerivedCategoryIdIso C₂).hom := by
  refine NatTrans.derivedCategory_ext fun X => ?_
  have hn := (mapDerivedCategoryIdIso C₂).hom.naturality (F.mapDerivedCategoryFactors.hom.app X)
  simp only [Functor.comp_obj, Functor.id_map] at hn
  rw [mapDerivedCategoryIdIso_hom_app, Q_map_mapHomologicalComplexIdIso] at hn
  erw [Category.comp_id] at hn
  rw [mapDerivedCategoryCompIso_hom_app_Q_obj, whiskerLeft_app,
    ← cancel_mono ((F ⋙ 𝟭 C₂).mapDerivedCategoryFactors.hom.app X),
    Q_map_mapHomologicalComplexCompIso]
  erw [Category.id_comp]
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id_app]
  exact (congrArg (_ ≫ ·) (Category.comp_id _)).trans hn

/-- `mapDerivedCategoryCompIso (𝟭 _) F` is the whiskering of `mapDerivedCategoryIdIso`. -/
theorem mapDerivedCategoryCompIso_id_comp_hom :
    (mapDerivedCategoryCompIso (𝟭 C₁) F).hom =
      whiskerRight (mapDerivedCategoryIdIso C₁).hom F.mapDerivedCategory := by
  refine NatTrans.derivedCategory_ext fun X => ?_
  rw [mapDerivedCategoryCompIso_hom_app_Q_obj, whiskerRight_app,
    mapDerivedCategoryIdIso_hom_app, Q_map_mapHomologicalComplexCompIso,
    Q_map_mapHomologicalComplexIdIso]
  erw [Category.id_comp, Category.comp_id]
  refine Eq.trans (congrArg (_ ≫ ·) ?_) (Category.comp_id _)
  exact Iso.hom_inv_id_app F.mapDerivedCategoryFactors X

variable {C₃ : Type*} [Category* C₃] [Abelian C₃] [HasDerivedCategory.{w₃} C₃]
  {C₄ : Type*} [Category* C₄] [Abelian C₄] [HasDerivedCategory.{w₄} C₄]

omit [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.Additive] in
private theorem compIso_middle_hom (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (G : C₂ ⥤ C₃) [G.Additive] [PreservesFiniteLimits G]
    [PreservesFiniteColimits G] (H : C₃ ⥤ C₄) [H.Additive] [PreservesFiniteLimits H]
    [PreservesFiniteColimits H] {Z : DerivedCategory C₁ ⥤ DerivedCategory C₄}
    (k : (F ⋙ G ⋙ H).mapDerivedCategory ⟶ Z) :
    (mapDerivedCategoryCompIso (F ⋙ G) H).inv ≫
        whiskerRight (mapDerivedCategoryCompIso F G).inv H.mapDerivedCategory ≫
          whiskerLeft F.mapDerivedCategory (mapDerivedCategoryCompIso G H).hom ≫
            (mapDerivedCategoryCompIso F (G ⋙ H)).hom ≫ k = k := by
  rw [← Category.assoc (whiskerLeft _ _), ← mapDerivedCategoryCompIso_assoc, Category.assoc,
    ← Category.assoc (whiskerRight _ _), ← whiskerRight_comp, Iso.inv_hom_id, whiskerRight_id',
    Category.id_comp, Iso.inv_hom_id_assoc]

omit [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.Additive] in
private theorem compIso_middle_inv (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (G : C₂ ⥤ C₃) [G.Additive] [PreservesFiniteLimits G]
    [PreservesFiniteColimits G] (H : C₃ ⥤ C₄) [H.Additive] [PreservesFiniteLimits H]
    [PreservesFiniteColimits H] {Z : DerivedCategory C₁ ⥤ DerivedCategory C₄}
    (k : ((F ⋙ G) ⋙ H).mapDerivedCategory ⟶ Z) :
    (mapDerivedCategoryCompIso F (G ⋙ H)).inv ≫
        whiskerLeft F.mapDerivedCategory (mapDerivedCategoryCompIso G H).inv ≫
          whiskerRight (mapDerivedCategoryCompIso F G).hom H.mapDerivedCategory ≫
            (mapDerivedCategoryCompIso (F ⋙ G) H).hom ≫ k = k := by
  rw [← Category.assoc (whiskerRight _ _), mapDerivedCategoryCompIso_assoc, Category.assoc,
    ← Category.assoc (whiskerLeft _ _), ← whiskerLeft_comp, Iso.inv_hom_id, whiskerLeft_id',
    Category.id_comp, Iso.inv_hom_id_assoc]

section MateDerived

omit [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

variable {G : C₁ ⥤ C₃} [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  {H : C₂ ⥤ C₄} [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  {L₁ : C₁ ⥤ C₂} [L₁.Additive] [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
  {R₁ : C₂ ⥤ C₁} [R₁.Additive] [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
  {L₂ : C₃ ⥤ C₄} [L₂.Additive] [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
  {R₂ : C₄ ⥤ C₃} [R₂.Additive] [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

/-- **Mates pass to derived categories**: for adjunctions `L₁ ⊣ R₁`, `L₂ ⊣ R₂` of exact functors
and a square `α : G ⋙ L₂ ⟶ L₁ ⋙ H` of exact functors with mate `β`, the mate of the derived
square `G^D ⋙ L₂^D ⟶ L₁^D ⋙ H^D` along the derived adjunctions is the derived square of `β`. -/
theorem mateEquiv_mapDerivedCategory (α : G ⋙ L₂ ⟶ L₁ ⋙ H) (β : R₁ ⋙ G ⟶ H ⋙ R₂)
    (hβ : (mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ α)).natTrans = β) :
    (mateEquiv adj₁.mapDerivedCategory adj₂.mapDerivedCategory (TwoSquare.mk _ _ _ _
      ((mapDerivedCategoryCompIso G L₂).hom ≫ α.mapDerivedCategory ≫
        (mapDerivedCategoryCompIso L₁ H).inv))).natTrans =
      (mapDerivedCategoryCompIso R₁ G).hom ≫ β.mapDerivedCategory ≫
        (mapDerivedCategoryCompIso H R₂).inv := by
  have hmod : whiskerRight β L₂ ≫ whiskerLeft H adj₂.counit =
      whiskerLeft R₁ α ≫ whiskerRight adj₁.counit H := by
    ext d
    rw [← hβ]
    exact mateEquiv_counit adj₁ adj₂ (TwoSquare.mk _ _ _ _ α) d
  have key : whiskerRight ((mapDerivedCategoryCompIso R₁ G).hom ≫ β.mapDerivedCategory ≫
        (mapDerivedCategoryCompIso H R₂).inv) L₂.mapDerivedCategory ≫
        whiskerLeft H.mapDerivedCategory adj₂.mapDerivedCategory.counit =
      whiskerLeft R₁.mapDerivedCategory ((mapDerivedCategoryCompIso G L₂).hom ≫
        α.mapDerivedCategory ≫ (mapDerivedCategoryCompIso L₁ H).inv) ≫
        whiskerRight adj₁.mapDerivedCategory.counit H.mapDerivedCategory := by
    rw [Adjunction.mapDerivedCategory_counit_eq, Adjunction.mapDerivedCategory_counit_eq]
    simp only [whiskerRight_comp, whiskerLeft_comp, Category.assoc]
    rw [NatTrans.whiskerRight_mapDerivedCategory, NatTrans.whiskerLeft_mapDerivedCategory,
      NatTrans.whiskerLeft_mapDerivedCategory, NatTrans.whiskerRight_mapDerivedCategory,
      ← mapDerivedCategoryCompIso_comp_id_hom, ← mapDerivedCategoryCompIso_id_comp_hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [compIso_middle_hom H R₂ L₂, compIso_middle_inv R₁ L₁ H,
      ← NatTrans.mapDerivedCategory_comp, hmod, NatTrans.mapDerivedCategory_comp,
      ← Category.assoc (whiskerRight _ _), mapDerivedCategoryCompIso_assoc, Category.assoc]
  exact congrArg TwoSquare.natTrans (mateEquiv_eq_of_counit adj₁.mapDerivedCategory
    adj₂.mapDerivedCategory _ (TwoSquare.mk _ _ _ _ _) fun d => NatTrans.congr_app key d)

end MateDerived

end Derived

end Categorification.Stendhal.CupCap
