/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DiagramWeightForgetFull
import Categorification.Algebra.DiagramWeightForgetDerived
import Categorification.Algebra.WeightForgetAdjunctionDerived

/-!
# Full faithfulness of graded derived diagram tensors

Let `M` be a homogeneous coefficient bimodule with weight decomposition `G`, and
`D = diagramWeightBimodule G`. If the derived tensor `M ⊗ᴸ_B - : D(B) ⥤ D(A)` is fully faithful,
then so is the graded derived tensor `D ⊗ᴸ - : D(C_B) ⥤ D(C_A)`
(`Categorification.diagramWeightDerivedTensorFullyFaithful`).

The proof transfers full faithfulness along weight-preserving parts
(`CategoryTheory.Functor.FullyFaithful.ofRetractions`). Morphisms between weight sums have
weight-preserving parts on both sides: on the homotopy category of K-projective dg modules over
`C_B` (`DG.CatModule.weightPartHom`) and on the derived category of dg modules over `C_A`
(`DG.CatModule.weightPartDerived`). The two derived tensors are compared through forgetting
the weights (`Categorification.diagramWeightForgetDerivedIso`). The comparison is compatible
with weight-preserving parts (`Categorification.DiagramWeightForget.weightPartHom_conjLTensor`).

This is the full faithfulness half of transferring B. Webster, *Knot invariants and higher
representation theory*, arXiv:1309.3796v3, Theorem 6.15, to the graded braiding functors of
Definition 6.6.
-/

noncomputable section

open CategoryTheory

namespace CategoryTheory.Functor.FullyFaithful

variable {C' C D' D : Type*} [Category C'] [Category C] [Category D'] [Category D]
  {F' : C' ⥤ D'} {F : C ⥤ D} {Φ₁ : C' ⥤ C} {Φ₂ : D' ⥤ D}

/-- **Full faithfulness transfers along retractions.** Let `σ : F' ⋙ Φ₂ ≅ Φ₁ ⋙ F`, and let `r₁`,
`r₂` be retractions of `Φ₁` and `Φ₂` on morphisms, compatible with `σ`:
`r₂ (σ ≫ F f ≫ σ⁻¹) = F' (r₁ f)`. If `F` is fully faithful, then so is `F'`. -/
def ofRetractions (σ : F' ⋙ Φ₂ ≅ Φ₁ ⋙ F)
    (r₁ : ∀ {X Y : C'}, (Φ₁.obj X ⟶ Φ₁.obj Y) → (X ⟶ Y))
    (hr₁ : ∀ {X Y : C'} (g : X ⟶ Y), r₁ (Φ₁.map g) = g)
    (r₂ : ∀ {X Y : D'}, (Φ₂.obj X ⟶ Φ₂.obj Y) → (X ⟶ Y))
    (hr₂ : ∀ {X Y : D'} (g : X ⟶ Y), r₂ (Φ₂.map g) = g)
    (h : ∀ {X Y : C'} (f : Φ₁.obj X ⟶ Φ₁.obj Y),
      r₂ (σ.hom.app X ≫ F.map f ≫ σ.inv.app Y) = F'.map (r₁ f))
    (hF : F.FullyFaithful) : F'.FullyFaithful where
  preimage {X Y} c := r₁ (hF.preimage (σ.inv.app X ≫ Φ₂.map c ≫ σ.hom.app Y))
  map_preimage {X Y} c := by
    rw [← h, hF.map_preimage]
    simp only [Category.assoc, Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc]
    exact (congrArg r₂ (Category.comp_id _)).trans (hr₂ c)
  preimage_map {X Y} a := by
    have := σ.hom.naturality a
    simp only [Functor.comp_map] at this
    rw [this, Iso.inv_hom_id_app_assoc, hF.preimage_map, hr₁]

end CategoryTheory.Functor.FullyFaithful

namespace Categorification

open DG MulOpposite
open scoped DG.DegreeZero

universe u v w

/-! ### Weight-preserving parts on the homotopy category -/

section Homotopy

variable {B : Type u} [Ring B] [InternalGrading B] [BigradedDGRing B]

/-- The weight-preserving part of a morphism of the homotopy category of dg `B`-modules between
weight sums. -/
def weightPartHomotopy {P P' : CatModule.HomotopyCategory.{u} (WeightCategory B)}
    (f : (CatModule.weightForgetHomotopy B).obj P ⟶ (CatModule.weightForgetHomotopy B).obj P') :
    P ⟶ P' :=
  (CatModule.HomotopyCategory.quotient _).map
    (CatModule.weightPartHom
      (Classical.choose ((DG.HomotopyCategory.quotient B).map_surjective
        (X := (CatModule.weightForget B).obj P.as)
        (Y := (CatModule.weightForget B).obj P'.as) f)).hom)

theorem weightPartHomotopy_quotient_map {P P' : CatModule.{u} (WeightCategory B)}
    (ψ : (CatModule.weightForget B).obj P ⟶ (CatModule.weightForget B).obj P') :
    weightPartHomotopy (P := (CatModule.HomotopyCategory.quotient _).obj P)
        (P' := (CatModule.HomotopyCategory.quotient _).obj P')
        ((DG.HomotopyCategory.quotient B).map ψ) =
      (CatModule.HomotopyCategory.quotient _).map (CatModule.weightPartHom ψ.hom) := by
  have h := Classical.choose_spec ((DG.HomotopyCategory.quotient B).map_surjective
    (X := (CatModule.weightForget B).obj P) (Y := (CatModule.weightForget B).obj P')
    ((DG.HomotopyCategory.quotient B).map ψ))
  rw [DG.HomotopyCategory.quotient_map_eq_iff] at h
  exact (CatModule.HomotopyCategory.quotient_map_eq_iff _ _).mpr h.weightPartHom

theorem weightPartHomotopy_map {P P' : CatModule.HomotopyCategory.{u} (WeightCategory B)}
    (g : P ⟶ P') : weightPartHomotopy ((CatModule.weightForgetHomotopy B).map g) = g := by
  obtain ⟨g, rfl⟩ := (CatModule.HomotopyCategory.quotient _).map_surjective
    (X := P.as) (Y := P'.as) g
  exact (weightPartHomotopy_quotient_map ((CatModule.weightForget B).map g)).trans
    (congrArg _ (CatModule.weightPartHom_weightSumMap g))

end Homotopy

/-! ### The graded derived diagram tensor -/

section Tensor

variable {A B M : Type u} [Ring A] [Ring B] [InternalGrading A] [InternalGrading B]
  [BigradedDGRing A] [BigradedDGRing B] [AddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M]
  [SMulCommClass A Bᵐᵒᵖ M]
  (G : ℤ → AddSubgroup M) [DirectSum.Decomposition G]
  (hl : ∀ {i j : ℤ} {a : A} {x : M}, a ∈ wgrading i → x ∈ G j → a • x ∈ G (i+j))
  (hr : ∀ {i j : ℤ} {b : B} {x : M}, b ∈ wgrading i → x ∈ G j → op b • x ∈ G (j+i))
  [CatModule.HasDerivedCategory.{v,u} (WeightCategory A)]
  [CatModule.HasDerivedCategory.{v,u} (WeightCategory B)]
  [DG.HasDerivedCategory.{w,u} A] [DG.HasDerivedCategory.{w,u} B]

local notation "D" => diagramWeightBimodule G hl hr
local notation "KB" => CatModule.HomotopyCategory.subcategoryKProjective (WeightCategory B)
local notation "KB'" => DG.HomotopyCategory.subcategoryKProjective B

omit [CatModule.HasDerivedCategory.{v,u} (WeightCategory A)]
  [CatModule.HasDerivedCategory.{v,u} (WeightCategory B)]
  [DG.HasDerivedCategory.{w,u} A] [DG.HasDerivedCategory.{w,u} B] in
/-- The component of `Categorification.diagramWeightForgetTensorIso` at `P`. -/
abbrev weightForgetTensorIsoApp (P : CatModule.{u} (WeightCategory B)) :
    (CatModule.weightForget A).obj ((D).tensorObj P) ≅
      (DGModuleCat.tensorFunctor A (InDegreeZero M)).obj ((CatModule.weightForget B).obj P) :=
  (diagramWeightForgetTensorIso G hl hr).app P

omit [DG.HasDerivedCategory.{w,u} B] [CatModule.HasDerivedCategory.{v,u} (WeightCategory B)] in
theorem diagramWeightForgetKProjectiveIso_naturality {P P' : CatModule.{u} (WeightCategory B)}
    (g : P ⟶ P') :
    (CatModule.weightForgetDerived A).map
        (CatModule.DerivedCategory.Q.map ((D).tensorMap g)) ≫
      ((CatModule.QCompWeightForgetDerivedIso.{v, w} A).hom.app ((D).tensorObj P') ≫
        DG.DerivedCategory.Q.map (weightForgetTensorIsoApp G hl hr P').hom) =
      ((CatModule.QCompWeightForgetDerivedIso A).hom.app ((D).tensorObj P) ≫
        DG.DerivedCategory.Q.map (weightForgetTensorIsoApp G hl hr P).hom) ≫
        DG.DerivedCategory.Q.map ((DGModuleCat.tensorFunctor A (InDegreeZero M)).map
          ((CatModule.weightForget B).map g)) := by
  have h₁ : (CatModule.weightForgetDerived A).map
        (CatModule.DerivedCategory.Q.map ((D).tensorMap g)) ≫
      (CatModule.QCompWeightForgetDerivedIso.{v, w} A).hom.app ((D).tensorObj P') =
      (CatModule.QCompWeightForgetDerivedIso A).hom.app ((D).tensorObj P) ≫
        DG.DerivedCategory.Q.map ((CatModule.weightForget A).map ((D).tensorMap g)) :=
    (CatModule.QCompWeightForgetDerivedIso.{v, w} A).hom.naturality ((D).tensorMap g)
  have h₂ : (CatModule.weightForget A).map ((D).tensorMap g) ≫
      (weightForgetTensorIsoApp G hl hr P').hom =
      (weightForgetTensorIsoApp G hl hr P).hom ≫
        (DGModuleCat.tensorFunctor A (InDegreeZero M)).map ((CatModule.weightForget B).map g) :=
    (diagramWeightForgetTensorIso G hl hr).hom.naturality g
  rw [← Category.assoc, h₁, Category.assoc, ← Functor.map_comp, h₂, Functor.map_comp,
    Category.assoc]

omit [DG.HasDerivedCategory.{w,u} B] [CatModule.HasDerivedCategory.{v,u} (WeightCategory B)] in
theorem weightPartDerived_diagramWeightForget {P P' : CatModule.{u} (WeightCategory B)}
    (ψ : (CatModule.weightForget B).obj P ⟶ (CatModule.weightForget B).obj P') :
    CatModule.weightPartDerived
      (((CatModule.QCompWeightForgetDerivedIso.{v, w} A).hom.app ((D).tensorObj P) ≫
        DG.DerivedCategory.Q.map (weightForgetTensorIsoApp G hl hr P).hom) ≫
      DG.DerivedCategory.Q.map ((DGModuleCat.tensorFunctor A (InDegreeZero M)).map ψ) ≫
      (DG.DerivedCategory.Q.map (weightForgetTensorIsoApp G hl hr P').inv ≫
        (CatModule.QCompWeightForgetDerivedIso A).inv.app ((D).tensorObj P'))) =
    CatModule.DerivedCategory.Q.map ((D).tensorMap (CatModule.weightPartHom ψ.hom)) := by
  refine Eq.trans ?_ ((CatModule.weightPartDerived_Q_map
    (DGModuleCat.ofHom (DiagramWeightForget.conjLTensor G hl hr ψ.hom))).trans
      (congrArg _ (DiagramWeightForget.weightPartHom_conjLTensor G hl hr ψ.hom)))
  congr 1
  simp only [Category.assoc, ← Functor.map_comp_assoc]
  rfl

/-- The comparison of the graded and ungraded tensors on K-projective dg modules, through
forgetting the weights. -/
def diagramWeightForgetKProjectiveIso :
    ((KB).ι ⋙ diagramWeightTensorHomotopy G hl hr ⋙ CatModule.DerivedCategory.Qh) ⋙
        CatModule.weightForgetDerived.{v, w} A ≅
      weightForgetKProjective ⋙ ((KB').ι ⋙
        DG.HomotopyCategory.tensorFunctor A (InDegreeZero M) ⋙ DG.DerivedCategory.Qh.{w}) :=
  NatIso.ofComponents
    (fun X => (CatModule.QCompWeightForgetDerivedIso A).app ((D).tensorObj X.obj.as) ≪≫
      DG.DerivedCategory.Q.mapIso (weightForgetTensorIsoApp G hl hr X.obj.as))
    fun {X Y} f => by
      obtain ⟨g, hg⟩ := (CatModule.HomotopyCategory.quotient _).map_surjective
        (X := X.obj.as) (Y := Y.obj.as) f.hom
      obtain rfl : f = ObjectProperty.homMk ((CatModule.HomotopyCategory.quotient _).map g) :=
        ObjectProperty.hom_ext _ hg.symm
      exact diagramWeightForgetKProjectiveIso_naturality G hl hr g

omit [DG.HasDerivedCategory.{w,u} B] [CatModule.HasDerivedCategory.{v,u} (WeightCategory B)] in
/-- The derived weight-preserving part is compatible with the comparison
`diagramWeightForgetKProjectiveIso`. -/
theorem weightPartDerived_diagramWeightForgetKProjectiveIso {X Y : (KB).FullSubcategory}
    (f : weightForgetKProjective.obj X ⟶ weightForgetKProjective.obj Y) :
    CatModule.weightPartDerived ((diagramWeightForgetKProjectiveIso G hl hr).hom.app X ≫
        ((KB').ι ⋙ DG.HomotopyCategory.tensorFunctor A (InDegreeZero M) ⋙
          DG.DerivedCategory.Qh.{w}).map f ≫
        (diagramWeightForgetKProjectiveIso G hl hr).inv.app Y) =
      ((KB).ι ⋙ diagramWeightTensorHomotopy G hl hr ⋙ CatModule.DerivedCategory.Qh.{v}).map
        (ObjectProperty.homMk (weightPartHomotopy f.hom)) := by
  obtain ⟨ψ, hψ⟩ := (DG.HomotopyCategory.quotient B).map_surjective
    (X := (CatModule.weightForget B).obj X.obj.as)
    (Y := (CatModule.weightForget B).obj Y.obj.as) f.hom
  obtain rfl : f = ObjectProperty.homMk ((DG.HomotopyCategory.quotient B).map ψ) :=
    ObjectProperty.hom_ext _ hψ.symm
  have hw : weightPartHomotopy (P := X.obj) (P' := Y.obj)
      ((DG.HomotopyCategory.quotient B).map ψ) =
      (CatModule.HomotopyCategory.quotient _).map (CatModule.weightPartHom ψ.hom) :=
    weightPartHomotopy_quotient_map ψ
  change _ = ((KB).ι ⋙ diagramWeightTensorHomotopy G hl hr ⋙
    CatModule.DerivedCategory.Qh.{v}).map (ObjectProperty.homMk (weightPartHomotopy (P := X.obj)
      (P' := Y.obj) ((DG.HomotopyCategory.quotient B).map ψ)))
  rw [hw]
  exact weightPartDerived_diagramWeightForget G hl hr ψ

/-- **Full faithfulness of the graded tensor on K-projective dg modules**, from full
faithfulness of the ungraded one. -/
def diagramWeightTensorKProjectiveFullyFaithful
    (hF : ((KB').ι ⋙ DG.HomotopyCategory.tensorFunctor A (InDegreeZero M) ⋙
      DG.DerivedCategory.Qh.{w}).FullyFaithful) :
    ((KB).ι ⋙ diagramWeightTensorHomotopy G hl hr ⋙
      CatModule.DerivedCategory.Qh.{v}).FullyFaithful :=
  Functor.FullyFaithful.ofRetractions (diagramWeightForgetKProjectiveIso G hl hr)
    (fun f => ObjectProperty.homMk (weightPartHomotopy f.hom))
    (fun g => ObjectProperty.hom_ext _ (weightPartHomotopy_map g.hom))
    (fun f => CatModule.weightPartDerived f) (fun g => CatModule.weightPartDerived_map g)
    (fun f => weightPartDerived_diagramWeightForgetKProjectiveIso G hl hr f) hF

/-- **Full faithfulness of the graded derived diagram tensor**: if `M ⊗ᴸ_B - : D(B) ⥤ D(A)` is
fully faithful, then so is `D ⊗ᴸ - : D(C_B) ⥤ D(C_A)`. -/
def diagramWeightDerivedTensorFullyFaithful (h : (derivedTensor.{w} A B M).FullyFaithful) :
    (diagramWeightDerivedTensor.{u, v} G hl hr).FullyFaithful :=
  let E' := DG.DerivedCategory.kProjectiveEquivalence.{w} B
  let R := (KB').ι ⋙ DG.HomotopyCategory.tensorFunctor A (InDegreeZero M) ⋙
    DG.DerivedCategory.Qh.{w}
  let e : E'.functor ⋙ derivedTensor.{w} A B M ≅ R :=
    (Functor.associator E'.functor E'.inverse R).symm ≪≫
      Functor.isoWhiskerRight E'.unitIso.symm R ≪≫ Functor.leftUnitor R
  (CatModule.DerivedCategory.kProjectiveEquivalence (WeightCategory B)).fullyFaithfulInverse.comp
    (diagramWeightTensorKProjectiveFullyFaithful G hl hr ((E'.fullyFaithfulFunctor.comp h).ofIso e))

end Tensor

end Categorification
