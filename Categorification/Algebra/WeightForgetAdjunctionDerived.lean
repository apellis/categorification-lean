/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.WeightProjection
import Mathlib.CategoryTheory.Localization.Adjunction

/-!
# The derived adjunction for forgetting the weights

Forgetting the weights of dg modules over `C_A = DG.WeightCategory A` is left adjoint to the
constant dg module (`DG.CatModule.weightForgetAdjunction`). Both functors preserve
quasi-isomorphisms, so the adjunction descends to derived categories:
`DG.CatModule.weightForgetDerivedAdjunction : weightForgetDerived A ⊣ weightConstDerived A`
(Mathlib's `CategoryTheory.Adjunction.localization`).

The componentwise projection `weightConst (⨁ k, M⟨k⟩) ⟶ M` descends to a retraction
`weightProjDerived` of the derived unit. So every morphism `f : Φ X ⟶ Φ Y` of the derived category
of dg `A`-modules between the images of the forgetful functor `Φ` has a *weight-preserving part*
`weightPartDerived f : X ⟶ Y`, the adjoint of `f` followed by the projection. It satisfies
`weightPartDerived (Φ.map g) = g` (`DG.CatModule.weightPartDerived_map`). On morphisms of dg
modules it is the weight-preserving part of `DG.CatModule.weightPartHom`
(`DG.CatModule.weightPartDerived_Q_map`).

This is used to transfer B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v3, Theorem 6.15, from the ungraded braiding functors to the graded ones of
Definition 6.6.
-/

open CategoryTheory

universe w₁ w₂ u

noncomputable section

namespace DG

namespace CatModule

open WeightCategory

variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A] [InternalGrading A]
  [BigradedDGRing A]

omit [DGRing A] in
variable {A} in
/-- The constant dg module preserves quasi-isomorphisms. -/
theorem isQuasiIso_weightConstFunctor_map {N N' : DGModuleCat.{u} A} {g : N ⟶ N'}
    (hg : g.hom.IsQuasiIso) : IsQuasiIso ((weightConstFunctor A).map g) :=
  fun _ n => hg n

variable [CatModule.HasDerivedCategory.{w₁, u} (WeightCategory A)]
  [DG.HasDerivedCategory.{w₂, u} A]

/-- **The derived constant dg module** `D(A) ⥤ D(C_A)`. -/
def weightConstDerived :
    DG.DerivedCategory.{w₂, u} A ⥤ CatModule.DerivedCategory.{w₁, u} (WeightCategory A) :=
  Localization.lift (W := DGModuleCat.quasiIso A)
    (weightConstFunctor A ⋙ CatModule.DerivedCategory.Q)
    (fun _ _ _ hf => Localization.inverts CatModule.DerivedCategory.Q (CatModule.quasiIso _) _
      (isQuasiIso_weightConstFunctor_map hf))
    DG.DerivedCategory.Q

instance weightConstDerivedLifting :
    Localization.Lifting DG.DerivedCategory.Q (DGModuleCat.quasiIso A)
      (weightConstFunctor A ⋙ CatModule.DerivedCategory.Q) (weightConstDerived A) :=
  Localization.liftingLift _ _ _

/-- The derived constant dg module is induced by the constant dg module. -/
def QCompWeightConstDerivedIso :
    DG.DerivedCategory.Q ⋙ weightConstDerived A ≅
      weightConstFunctor A ⋙ CatModule.DerivedCategory.Q :=
  Localization.Lifting.iso DG.DerivedCategory.Q (DGModuleCat.quasiIso A) _ _

instance weightForgetCatCommSq :
    CatCommSq (weightForget A) CatModule.DerivedCategory.Q DG.DerivedCategory.Q
      (weightForgetDerived A) :=
  ⟨(QCompWeightForgetDerivedIso A).symm⟩

instance weightConstCatCommSq :
    CatCommSq (weightConstFunctor A) DG.DerivedCategory.Q CatModule.DerivedCategory.Q
      (weightConstDerived A) :=
  ⟨(QCompWeightConstDerivedIso A).symm⟩

/-- **The derived adjunction** `weightForgetDerived A ⊣ weightConstDerived A`. -/
def weightForgetDerivedAdjunction : weightForgetDerived A ⊣ weightConstDerived A :=
  (weightForgetAdjunction A).localization CatModule.DerivedCategory.Q
    (CatModule.quasiIso (WeightCategory A)) DG.DerivedCategory.Q (DGModuleCat.quasiIso A)
    (weightForgetDerived A) (weightConstDerived A)

theorem weightForgetDerivedAdjunction_unit_app (M : CatModule.{u} (WeightCategory A)) :
    (weightForgetDerivedAdjunction A).unit.app (CatModule.DerivedCategory.Q.obj M) =
      CatModule.DerivedCategory.Q.map ((weightForgetAdjunction A).unit.app M) ≫
        (QCompWeightConstDerivedIso A).inv.app ((weightForget A).obj M) ≫
          (weightConstDerived A).map ((QCompWeightForgetDerivedIso A).inv.app M) :=
  Adjunction.localization_unit_app _ _ _ _ _ _ _ _

/-- The lifting of `(Φ ⋙ Ψ) ⋙ Q` used to descend the projections. -/
instance weightForgetConstLifting :
    Localization.Lifting CatModule.DerivedCategory.Q (CatModule.quasiIso (WeightCategory A))
      ((weightForget A ⋙ weightConstFunctor A) ⋙ CatModule.DerivedCategory.Q)
      (weightForgetDerived A ⋙ weightConstDerived A) :=
  ⟨(Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (QCompWeightForgetDerivedIso A) (weightConstDerived A) ≪≫
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (weightForget A) (QCompWeightConstDerivedIso A) ≪≫
          (Functor.associator _ _ _).symm⟩

/-- **The derived projection** `Ψ (Φ X) ⟶ X`, descended from `DG.CatModule.weightProj`. -/
def weightProjDerived : weightForgetDerived A ⋙ weightConstDerived A ⟶ 𝟭 _ :=
  Localization.liftNatTrans CatModule.DerivedCategory.Q (CatModule.quasiIso (WeightCategory A))
    ((weightForget A ⋙ weightConstFunctor A) ⋙ CatModule.DerivedCategory.Q)
    CatModule.DerivedCategory.Q (weightForgetDerived A ⋙ weightConstDerived A) (𝟭 _)
    (Functor.whiskerRight (weightProjNatTrans A) CatModule.DerivedCategory.Q ≫
      (Functor.leftUnitor _).hom)

theorem weightProjDerived_app (M : CatModule.{u} (WeightCategory A)) :
    (weightProjDerived A).app (CatModule.DerivedCategory.Q.obj M) =
      (weightConstDerived A).map ((QCompWeightForgetDerivedIso A).hom.app M) ≫
        (QCompWeightConstDerivedIso A).hom.app ((weightForget A).obj M) ≫
          CatModule.DerivedCategory.Q.map (weightProj M) := by
  simp [weightProjDerived, Localization.liftNatTrans_app, Localization.Lifting.iso,
    weightProjNatTrans]

/-- The derived projection retracts the derived unit. -/
@[reassoc (attr := simp)]
theorem unit_app_comp_weightProjDerived_app
    (X : CatModule.DerivedCategory.{w₁, u} (WeightCategory A)) :
    (weightForgetDerivedAdjunction A).unit.app X ≫ (weightProjDerived A).app X = 𝟙 X := by
  have h : (weightForgetDerivedAdjunction A).unit ≫ weightProjDerived A = 𝟙 _ := by
    refine Localization.natTrans_ext CatModule.DerivedCategory.Q
      (CatModule.quasiIso (WeightCategory A)) fun M => ?_
    rw [NatTrans.comp_app, weightForgetDerivedAdjunction_unit_app, weightProjDerived_app,
      NatTrans.id_app]
    simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.comp_obj]
    simp only [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]
    rw [← Functor.map_comp, unit_app_comp_weightProj]
    exact CategoryTheory.Functor.map_id _ _
  exact NatTrans.congr_app h X

variable {A}

/-- **The weight-preserving part of a morphism of the derived category of dg `A`-modules**
between images of the forgetful functor: its adjoint, followed by the derived projection. -/
def weightPartDerived {X Y : CatModule.DerivedCategory.{w₁, u} (WeightCategory A)}
    (f : (weightForgetDerived A).obj X ⟶ (weightForgetDerived A).obj Y) : X ⟶ Y :=
  (weightForgetDerivedAdjunction A).homEquiv X _ f ≫ (weightProjDerived A).app Y

/-- The weight-preserving part of the image of a morphism is the morphism. -/
@[simp]
theorem weightPartDerived_map {X Y : CatModule.DerivedCategory.{w₁, u} (WeightCategory A)}
    (g : X ⟶ Y) : weightPartDerived ((weightForgetDerived A).map g) = g := by
  have := (weightForgetDerivedAdjunction A).unit.naturality_assoc g ((weightProjDerived A).app Y)
  simp only [Functor.comp_map, Functor.id_map, unit_app_comp_weightProjDerived_app] at this
  rw [weightPartDerived, Adjunction.homEquiv_unit, Category.assoc, ← this]
  exact Category.comp_id g

theorem weightPartDerived_map_comp {X X' Y : CatModule.DerivedCategory.{w₁, u} (WeightCategory A)}
    (a : X' ⟶ X) (f : (weightForgetDerived A).obj X ⟶ (weightForgetDerived A).obj Y) :
    weightPartDerived ((weightForgetDerived A).map a ≫ f) = a ≫ weightPartDerived f := by
  rw [weightPartDerived, weightPartDerived, Adjunction.homEquiv_naturality_left,
    Category.assoc]

theorem weightPartDerived_comp_map {X Y Y' : CatModule.DerivedCategory.{w₁, u} (WeightCategory A)}
    (f : (weightForgetDerived A).obj X ⟶ (weightForgetDerived A).obj Y) (b : Y ⟶ Y') :
    weightPartDerived (f ≫ (weightForgetDerived A).map b) = weightPartDerived f ≫ b := by
  rw [weightPartDerived, weightPartDerived, Adjunction.homEquiv_naturality_right,
    Category.assoc, Category.assoc]
  congr 1
  exact (weightProjDerived A).naturality b

/-- **On morphisms of dg modules, the derived weight-preserving part is the weight-preserving
part** `DG.CatModule.weightPartHom`. -/
theorem weightPartDerived_Q_map {M M' : CatModule.{u} (WeightCategory A)}
    (ψ : (weightForget A).obj M ⟶ (weightForget A).obj M') :
    weightPartDerived ((QCompWeightForgetDerivedIso A).hom.app M ≫ DG.DerivedCategory.Q.map ψ ≫
        (QCompWeightForgetDerivedIso A).inv.app M') =
      CatModule.DerivedCategory.Q.map (weightPartHom ψ.hom) := by
  rw [weightPartDerived, Adjunction.homEquiv_unit, weightForgetDerivedAdjunction_unit_app,
    weightProjDerived_app, ← unit_app_comp_map_comp_weightProj]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app_assoc,
    Iso.inv_hom_id_app]
  have := (QCompWeightConstDerivedIso A).hom.naturality_assoc ψ
    (CatModule.DerivedCategory.Q.map (weightProj M'))
  simp only [Functor.comp_obj, Functor.comp_map] at this
  erw [Category.comp_id, this, Iso.inv_hom_id_app_assoc]
  simp only [Functor.map_comp]

end CatModule

end DG
