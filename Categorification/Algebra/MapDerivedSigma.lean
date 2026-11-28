/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.MapDerivedAdjunctionUnit
import Categorification.Algebra.MapDerivedNatTransTriple
import Categorification.TwoRep.RouqLocTransport

/-!
# Rouquier's rightward crossing on derived categories

Brundan, arXiv:1501.00350v1, (1.6): for adjunctions `E₁ ⊣ R₁`, `E₂ ⊣ R₂` and a crossing
`τ : E₁ E₂ ⟶ E₁ E₂`, the rightward crossing `σ : R₁ E₁ ⟶ E₂ R₂` is the composite of the unit of
`E₂ ⊣ R₂`, `τ` and the counit of `E₁ ⊣ R₁`. For exact functors between abelian categories, the
rightward crossing of the derived adjunctions (`Adjunction.mapDerivedCategory`) and the derived
crossing (`NatTrans.derivedComp τ`) is the derived rightward crossing
(`derivedComp_functorSigma`). The dotted caps and cups of the derived adjunctions are the
derived dotted caps and cups (`derived_dottedCap`, `derived_dottedCup`), so explicit inverses of
Brundan's maps (1.8), (1.9) among exact functors pass to derived categories
(`TwoRep.SumInvTo.derivedSigma`, `TwoRep.SumInvFrom.derivedSigma`).
-/

noncomputable section

namespace CategoryTheory

open Category Limits

universe w₁ w₂ w₃

variable {C₁ : Type*} [Category* C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type*} [Category* C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  {C₃ : Type*} [Category* C₃] [Abelian C₃] [HasDerivedCategory.{w₃} C₃]

namespace NatTrans

/-- Rouquier's rightward crossing of natural transformations, `R₁ ⋙ E₁ ⟶ E₂ ⋙ R₂`, from the
unit `η` of `E₂ ⊣ R₂`, the crossing `τ` and the counit `ε` of `E₁ ⊣ R₁` (the form of
`TwoRep.AdditiveCat.sigma_hom`). -/
def functorSigma {𝒜 ℬ 𝒞 : Type*} [Category 𝒜] [Category ℬ] [Category 𝒞]
    {E₁ : 𝒜 ⥤ ℬ} {R₁ : ℬ ⥤ 𝒜} {E₂ : ℬ ⥤ 𝒞} {R₂ : 𝒞 ⥤ ℬ}
    (η : 𝟭 ℬ ⟶ E₂ ⋙ R₂) (τ : E₁ ⋙ E₂ ⟶ E₁ ⋙ E₂) (ε : R₁ ⋙ E₁ ⟶ 𝟭 ℬ) :
    R₁ ⋙ E₁ ⟶ E₂ ⋙ R₂ :=
  Functor.whiskerLeft (R₁ ⋙ E₁) η ≫ Functor.whiskerRight (Functor.whiskerLeft R₁ τ) R₂ ≫
    Functor.whiskerRight ε (E₂ ⋙ R₂)

theorem functorSigma_app {𝒜 ℬ 𝒞 : Type*} [Category 𝒜] [Category ℬ] [Category 𝒞]
    {E₁ : 𝒜 ⥤ ℬ} {R₁ : ℬ ⥤ 𝒜} {E₂ : ℬ ⥤ 𝒞} {R₂ : 𝒞 ⥤ ℬ}
    (η : 𝟭 ℬ ⟶ E₂ ⋙ R₂) (τ : E₁ ⋙ E₂ ⟶ E₁ ⋙ E₂) (ε : R₁ ⋙ E₁ ⟶ 𝟭 ℬ) (Y : ℬ) :
    (functorSigma η τ ε).app Y = η.app (E₁.obj (R₁.obj Y)) ≫ R₂.map (τ.app (R₁.obj Y)) ≫
      R₂.map (E₂.map (ε.app Y)) := by
  simp [functorSigma]

omit [HasDerivedCategory C₁] [HasDerivedCategory C₂] [HasDerivedCategory C₃] in
theorem mapHomologicalComplexCompIso_refl_hom_app {𝒜 ℬ 𝒞 : Type*} [Category 𝒜]
    [Category ℬ] [Category 𝒞] [Preadditive 𝒜] [Preadditive ℬ] [Preadditive 𝒞]
    (F : 𝒜 ⥤ ℬ) (G : ℬ ⥤ 𝒞) [F.Additive] [G.Additive] (X : CochainComplex 𝒜 ℤ) :
    (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).hom.app X =
      𝟙 _ := by
  ext n
  simp

theorem mapDerivedCategoryCompIso_hom_app_Q_obj' (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (V : CochainComplex C₁ ℤ) :
    (Functor.mapDerivedCategoryCompIso F G).hom.app (DerivedCategory.Q.obj V) =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app V) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex _).obj V) ≫
          (F ⋙ G).mapDerivedCategoryFactors.inv.app V := by
  have hc := Functor.mapDerivedCategoryCompIso_hom_app_Q_obj F G V
  rw [mapHomologicalComplexCompIso_refl_hom_app] at hc
  erw [Functor.map_id, Category.id_comp] at hc
  exact hc

theorem mapDerivedCategoryCompIso_inv_app_Q_obj (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (V : CochainComplex C₁ ℤ) :
    (Functor.mapDerivedCategoryCompIso F G).inv.app (DerivedCategory.Q.obj V) =
      (F ⋙ G).mapDerivedCategoryFactors.hom.app V ≫
        G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex _).obj V) ≫
          G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app V) := by
  rw [← cancel_epi ((Functor.mapDerivedCategoryCompIso F G).hom.app _), Iso.hom_inv_id_app,
    mapDerivedCategoryCompIso_hom_app_Q_obj']
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app_assoc]
  rw [← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id]
  rfl

section

variable {C₂' : Type*} [Category* C₂'] [Abelian C₂'] [HasDerivedCategory C₂']
  {F₁ : C₁ ⥤ C₂} {F₂ : C₂ ⥤ C₃} {F₁' : C₁ ⥤ C₂'} {F₂' : C₂' ⥤ C₃}
  [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [F₁'.Additive] [PreservesFiniteLimits F₁'] [PreservesFiniteColimits F₁']
  [F₂'.Additive] [PreservesFiniteLimits F₂'] [PreservesFiniteColimits F₂']

/-- A transformation of derived composites `derivedComp τ` at `Q V`, through the factorizations
of the derived functors. -/
theorem derivedComp_app_Q_obj (τ : F₁ ⋙ F₂ ⟶ F₁' ⋙ F₂') (V : CochainComplex C₁ ℤ) :
    (derivedComp τ).app (DerivedCategory.Q.obj V) =
      F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.hom.app V) ≫
        F₂.mapDerivedCategoryFactors.hom.app ((F₁.mapHomologicalComplex _).obj V) ≫
          DerivedCategory.Q.map ((τ.mapHomologicalComplex (ComplexShape.up ℤ)).app V) ≫
            F₂'.mapDerivedCategoryFactors.inv.app ((F₁'.mapHomologicalComplex _).obj V) ≫
              F₂'.mapDerivedCategory.map (F₁'.mapDerivedCategoryFactors.inv.app V) := by
  simp only [derivedComp, comp_app, mapDerivedCategoryCompIso_hom_app_Q_obj',
    mapDerivedCategoryCompIso_inv_app_Q_obj, mapDerivedCategory_app_Q_obj, Category.assoc,
    Iso.inv_hom_id_app_assoc]

end

variable {E₁ : C₁ ⥤ C₂} {R₁ : C₂ ⥤ C₁} {E₂ : C₂ ⥤ C₃} {R₂ : C₃ ⥤ C₂}
  [E₁.Additive] [PreservesFiniteLimits E₁] [PreservesFiniteColimits E₁]
  [R₁.Additive] [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
  [E₂.Additive] [PreservesFiniteLimits E₂] [PreservesFiniteColimits E₂]
  [R₂.Additive] [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]

/-- **The derived rightward crossing.** The rightward crossing of the derived adjunctions and the
derived crossing is the derived rightward crossing, through `mapDerivedCategoryCompIso`. -/
theorem derivedComp_functorSigma (adj₁ : E₁ ⊣ R₁) (adj₂ : E₂ ⊣ R₂)
    (τ : E₁ ⋙ E₂ ⟶ E₁ ⋙ E₂) :
    functorSigma adj₂.mapDerivedCategory.unit (derivedComp τ) adj₁.mapDerivedCategory.counit =
      derivedComp (functorSigma adj₂.unit τ adj₁.counit) := by
  refine derivedCategory_ext fun X => ?_
  let V := (R₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj X
  let Y := (E₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj V
  let a := R₁.mapDerivedCategoryFactors.app X
  let b := E₁.mapDerivedCategoryFactors.app V
  let ψ : E₁.mapDerivedCategory.obj (R₁.mapDerivedCategory.obj (DerivedCategory.Q.obj X)) ≅
      DerivedCategory.Q.obj Y := E₁.mapDerivedCategory.mapIso a ≪≫ b
  -- the right side
  have hR : (derivedComp (functorSigma adj₂.unit τ adj₁.counit)).app (DerivedCategory.Q.obj X) =
      ψ.hom ≫ DerivedCategory.Q.map ((mapHomologicalComplex (functorSigma adj₂.unit τ adj₁.counit)
        (ComplexShape.up ℤ)).app X) ≫
        R₂.mapDerivedCategoryFactors.inv.app ((E₂.mapHomologicalComplex _).obj X) ≫
          R₂.mapDerivedCategory.map (E₂.mapDerivedCategoryFactors.inv.app X) := by
    rw [derivedComp_app_Q_obj]
    simp only [ψ, Iso.trans_hom, Functor.mapIso_hom, Category.assoc, a, b, Iso.app_hom]
    rfl
  -- the left side
  have h1 : adj₁.mapDerivedCategory.counit.app (DerivedCategory.Q.obj X) =
      ψ.hom ≫ DerivedCategory.Q.map (adj₁.mapCochainComplex.counit.app X) := by
    rw [Adjunction.mapDerivedCategory_counit_app]
    simp only [ψ, Iso.trans_hom, Functor.mapIso_hom, Category.assoc, a, b, Iso.app_hom]
    rfl
  have h2 := adj₂.mapDerivedCategory.unit.naturality ψ.inv
  have h3 := Adjunction.mapDerivedCategory_unit_app adj₂ Y
  have h4 := (derivedComp τ).naturality a.inv
  have h5 := derivedComp_app_Q_obj τ V
  have K : E₂.mapDerivedCategory.map ψ.inv ≫ (derivedComp τ).app
        (R₁.mapDerivedCategory.obj (DerivedCategory.Q.obj X)) ≫
        E₂.mapDerivedCategory.map ψ.hom =
      E₂.mapDerivedCategoryFactors.hom.app Y ≫
        DerivedCategory.Q.map ((τ.mapHomologicalComplex (ComplexShape.up ℤ)).app V) ≫
          E₂.mapDerivedCategoryFactors.inv.app Y := by
    have c1 : E₂.mapDerivedCategory.map (E₁.mapDerivedCategory.map a.inv) ≫
        E₂.mapDerivedCategory.map (E₁.mapDerivedCategory.map a.hom) = 𝟙 _ := by
      rw [← Functor.map_comp, ← Functor.map_comp, a.inv_hom_id, Functor.map_id, Functor.map_id]
    have c2 : E₂.mapDerivedCategory.map b.inv ≫ E₂.mapDerivedCategory.map b.hom = 𝟙 _ := by
      rw [← Functor.map_comp, b.inv_hom_id, Functor.map_id]
    have c3 : E₂.mapDerivedCategory.map b.hom ≫ E₂.mapDerivedCategory.map b.inv = 𝟙 _ := by
      rw [← Functor.map_comp, b.hom_inv_id, Functor.map_id]
    simp only [Functor.comp_map] at h4
    simp only [ψ, Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv, Functor.mapIso_hom,
      Functor.map_comp, Category.assoc]
    rw [reassoc_of% h4, reassoc_of% c1, h5]
    simp only [b, Iso.app_hom, Iso.app_inv, Category.assoc] at c2 c3 ⊢
    rw [reassoc_of% c2, c2]
    erw [Category.comp_id]
  have h2' : adj₂.mapDerivedCategory.unit.app
        (E₁.mapDerivedCategory.obj (R₁.mapDerivedCategory.obj (DerivedCategory.Q.obj X))) =
      ψ.hom ≫ adj₂.mapDerivedCategory.unit.app (DerivedCategory.Q.obj Y) ≫
        R₂.mapDerivedCategory.map (E₂.mapDerivedCategory.map ψ.inv) := by
    simp only [Functor.id_map, Functor.comp_map] at h2
    rw [← h2, Iso.hom_inv_id_assoc]
  have hσ : (mapHomologicalComplex (functorSigma adj₂.unit τ adj₁.counit)
      (ComplexShape.up ℤ)).app X = adj₂.mapCochainComplex.unit.app Y ≫
        (R₂.mapHomologicalComplex _).map ((τ.mapHomologicalComplex (ComplexShape.up ℤ)).app V ≫
          (E₂.mapHomologicalComplex _).map (adj₁.mapCochainComplex.counit.app X)) := by
    ext n
    simp [functorSigma_app]
    rfl
  have nE := E₂.mapDerivedCategoryFactors.inv.naturality (adj₁.mapCochainComplex.counit.app X)
  have nR := R₂.mapDerivedCategoryFactors.inv.naturality
    ((τ.mapHomologicalComplex (ComplexShape.up ℤ)).app V ≫
      (E₂.mapHomologicalComplex _).map (adj₁.mapCochainComplex.counit.app X))
  simp only [Functor.comp_map] at nE nR
  have cE : R₂.mapDerivedCategory.map (E₂.mapDerivedCategoryFactors.inv.app Y) ≫
      R₂.mapDerivedCategory.map (E₂.mapDerivedCategoryFactors.hom.app Y) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id]
  rw [hR, functorSigma_app, h1, h2', h3, hσ]
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

end NatTrans

end CategoryTheory

namespace Categorification.TwoRep

open CategoryTheory Limits NatTrans

universe w₁ w₂ w₃

variable {C₁ : Type*} [Category* C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type*} [Category* C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  {C₃ : Type*} [Category* C₃] [Abelian C₃] [HasDerivedCategory.{w₃} C₃]

theorem mapDerivedCategory_powComp {F : C₁ ⥤ C₂} [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (x : F ⟶ F) (m : ℕ) :
    (powComp x m).mapDerivedCategory = powComp x.mapDerivedCategory m := by
  induction m with
  | zero => exact mapDerivedCategory_id
  | succ m ih => rw [powComp_succ, powComp_succ, mapDerivedCategory_comp, ih]

variable {E₁ : C₁ ⥤ C₂} {R₁ : C₂ ⥤ C₁} {E₂ : C₂ ⥤ C₃} {R₂ : C₃ ⥤ C₂}
  [E₁.Additive] [PreservesFiniteLimits E₁] [PreservesFiniteColimits E₁]
  [R₁.Additive] [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
  [E₂.Additive] [PreservesFiniteLimits E₂] [PreservesFiniteColimits E₂]
  [R₂.Additive] [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]

/-- **The derived dotted cap** `R₁ x^m ε` is the derived functor of the dotted cap, through
`mapDerivedCategoryCompIso` and `mapDerivedCategoryIdIso`. -/
theorem derived_dottedCap (adj₁ : E₁ ⊣ R₁) (x : E₁ ⟶ E₁) (m : ℕ) :
    Functor.whiskerLeft R₁.mapDerivedCategory (powComp x.mapDerivedCategory m) ≫
        adj₁.mapDerivedCategory.counit =
      (Functor.mapDerivedCategoryCompIso R₁ E₁).hom ≫
        (Functor.whiskerLeft R₁ (powComp x m) ≫ adj₁.counit).mapDerivedCategory ≫
          (Functor.mapDerivedCategoryIdIso C₂).hom := by
  rw [← mapDerivedCategory_powComp, whiskerLeft_mapDerivedCategory,
    Adjunction.mapDerivedCategory_counit_eq, mapDerivedCategory_comp]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- **The derived dotted cup** `η x^m R₂` is the derived functor of the dotted cup, through
`mapDerivedCategoryIdIso` and `mapDerivedCategoryCompIso`. -/
theorem derived_dottedCup (adj₂ : E₂ ⊣ R₂) (x : E₂ ⟶ E₂) (m : ℕ) :
    adj₂.mapDerivedCategory.unit ≫
        Functor.whiskerRight (powComp x.mapDerivedCategory m) R₂.mapDerivedCategory =
      (Functor.mapDerivedCategoryIdIso C₂).inv ≫
        (adj₂.unit ≫ Functor.whiskerRight (powComp x m) R₂).mapDerivedCategory ≫
          (Functor.mapDerivedCategoryCompIso E₂ R₂).inv := by
  rw [← mapDerivedCategory_powComp, whiskerRight_mapDerivedCategory,
    Adjunction.mapDerivedCategory_unit_eq, mapDerivedCategory_comp]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

variable {n : ℕ}

/-- **Brundan (1.8) passes to derived categories**: an explicit inverse of the rightward
crossing and the dotted caps among exact functors gives one for the derived adjunctions, the
derived dot and the derived crossing `derivedComp τ`. -/
def SumInvTo.derivedSigma {adj₁ : E₁ ⊣ R₁} {adj₂ : E₂ ⊣ R₂} {τ : E₁ ⋙ E₂ ⟶ E₁ ⋙ E₂}
    {x : E₁ ⟶ E₁}
    (S : SumInvTo (functorSigma adj₂.unit τ adj₁.counit)
      (fun m => Functor.whiskerLeft R₁ (powComp x m) ≫ adj₁.counit) n) :
    SumInvTo (functorSigma adj₂.mapDerivedCategory.unit (derivedComp τ)
        adj₁.mapDerivedCategory.counit)
      (fun m => Functor.whiskerLeft R₁.mapDerivedCategory (powComp x.mapDerivedCategory m) ≫
        adj₁.mapDerivedCategory.counit) n :=
  S.mapDerivedCategory.conj (Functor.mapDerivedCategoryCompIso R₁ E₁)
    (Functor.mapDerivedCategoryCompIso E₂ R₂).symm (Functor.mapDerivedCategoryIdIso C₂)
    (by rw [derivedComp_functorSigma]; rfl) fun m => derived_dottedCap adj₁ x m

/-- **Brundan (1.9) passes to derived categories**: an explicit inverse of the rightward
crossing and the dotted cups among exact functors gives one for the derived adjunctions, the
derived dot and the derived crossing `derivedComp τ`. -/
def SumInvFrom.derivedSigma {adj₁ : E₁ ⊣ R₁} {adj₂ : E₂ ⊣ R₂} {τ : E₁ ⋙ E₂ ⟶ E₁ ⋙ E₂}
    {x : E₂ ⟶ E₂}
    (S : SumInvFrom (functorSigma adj₂.unit τ adj₁.counit)
      (fun m => adj₂.unit ≫ Functor.whiskerRight (powComp x m) R₂) n) :
    SumInvFrom (functorSigma adj₂.mapDerivedCategory.unit (derivedComp τ)
        adj₁.mapDerivedCategory.counit)
      (fun m => adj₂.mapDerivedCategory.unit ≫
        Functor.whiskerRight (powComp x.mapDerivedCategory m) R₂.mapDerivedCategory) n :=
  S.mapDerivedCategory.conj (Functor.mapDerivedCategoryCompIso E₂ R₂).symm
    (Functor.mapDerivedCategoryCompIso R₁ E₁) (Functor.mapDerivedCategoryIdIso C₂).symm
    (by rw [derivedComp_functorSigma]; rfl) fun m => derived_dottedCup adj₂ x m

/-- Components `E₂ R₂ ⟶ 𝟭` of exact functors, passed to derived categories through
`mapDerivedCategoryCompIso` and `mapDerivedCategoryIdIso`. -/
def derivedCoeff (c : E₂ ⋙ R₂ ⟶ 𝟭 C₂) :
    E₂.mapDerivedCategory ⋙ R₂.mapDerivedCategory ⟶ 𝟭 _ :=
  (Functor.mapDerivedCategoryCompIso E₂ R₂).hom ≫ c.mapDerivedCategory ≫
    (Functor.mapDerivedCategoryIdIso C₂).hom

/-- **A decomposition of `E₂ R₂` into copies of the identity by the dotted units passes to
derived categories**: the total relation. -/
theorem derivedCoeff_total (adj₂ : E₂ ⊣ R₂) (x : E₂ ⟶ E₂) (c : ℕ → (E₂ ⋙ R₂ ⟶ 𝟭 C₂))
    (total : ∑ m ∈ Finset.range n,
      c m ≫ adj₂.unit ≫ Functor.whiskerRight (powComp x m) R₂ = 𝟙 _) :
    ∑ m ∈ Finset.range n, derivedCoeff (c m) ≫ adj₂.mapDerivedCategory.unit ≫
      Functor.whiskerRight (powComp x.mapDerivedCategory m) R₂.mapDerivedCategory = 𝟙 _ := by
  simp only [derived_dottedCup, derivedCoeff, Category.assoc, Iso.hom_inv_id_assoc]
  have e : ∀ m, (Functor.mapDerivedCategoryCompIso E₂ R₂).hom ≫ (c m).mapDerivedCategory ≫
      (adj₂.unit ≫ Functor.whiskerRight (powComp x m) R₂).mapDerivedCategory ≫
        (Functor.mapDerivedCategoryCompIso E₂ R₂).inv =
      (Functor.mapDerivedCategoryCompIso E₂ R₂).hom ≫
      (c m ≫ adj₂.unit ≫ Functor.whiskerRight (powComp x m) R₂).mapDerivedCategory ≫
        (Functor.mapDerivedCategoryCompIso E₂ R₂).inv := fun m => by
    simp only [mapDerivedCategory_comp, Category.assoc]
  rw [Finset.sum_congr rfl fun m _ => e m, ← Preadditive.comp_sum, ← Preadditive.sum_comp,
    ← mapDerivedCategory_sum, total, mapDerivedCategory_id,
    Category.id_comp, Iso.hom_inv_id]

/-- **A decomposition of `E₂ R₂` into copies of the identity by the dotted units passes to
derived categories**: the entries. -/
theorem derivedCoeff_entry (adj₂ : E₂ ⊣ R₂) (x : E₂ ⟶ E₂) (c : E₂ ⋙ R₂ ⟶ 𝟭 C₂) (m : ℕ)
    (e : 𝟭 C₂ ⟶ 𝟭 C₂) (he : (adj₂.unit ≫ Functor.whiskerRight (powComp x m) R₂) ≫ c = e) :
    (adj₂.mapDerivedCategory.unit ≫
      Functor.whiskerRight (powComp x.mapDerivedCategory m) R₂.mapDerivedCategory) ≫
        derivedCoeff c = (Functor.mapDerivedCategoryIdIso C₂).inv ≫ e.mapDerivedCategory ≫
          (Functor.mapDerivedCategoryIdIso C₂).hom := by
  rw [derived_dottedCup, derivedCoeff, ← he]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, mapDerivedCategory_comp]

end Categorification.TwoRep
