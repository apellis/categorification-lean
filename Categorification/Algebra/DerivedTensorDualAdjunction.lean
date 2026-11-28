/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DualTensorAdjunction
import Categorification.Algebra.ExactDerivedTensor
import DG.Category.Derived.DGBimodule
import DG.Category.Tensor.SingleObj

/-!
# `M^∨ ⊗ᴸ_A - ⊣ M ⊗ᴸ_B -` for a finitely generated projective coefficient

Let `M` be an `(A, B)`-bimodule which is finitely generated and projective as a right
`B`-module, and `M^∨ = Hom_{Bᵐᵒᵖ}(M, B)` its dual (`Categorification.RightDualModule`). Then the
derived tensor product with `M^∨` is left adjoint to the derived tensor product with `M`:

`M^∨ ⊗ᴸ_A - ⊣ M ⊗ᴸ_B - : D(A) ⇄ D(B)`

(`Categorification.derivedTensorDualAdjunction`), both functors being the library's
`Categorification.derivedTensor`. The proof transports the derived tensor–Hom adjunction of
dg bimodules over one-object dg categories
(`DG.CatModule.DerivedCategory.derivedTensorAdjunction`) along two identifications:

* `Categorification.catDerivedTensorDualIso`: the dg-category derived tensor product with the
  bimodule `M^∨` (K-projective on the left) agrees with the library's `derivedTensor`;
* `Categorification.derivedRHomIsoDerivedTensorDual`: the derived Hom `RHOM_B(M^∨, -)` agrees with
  `M ⊗ᴸ_B -`, from the dg adjunction `M^∨ ⊗_A - ⊣ M ⊗_B -`
  (`Categorification.RightDualModule.dualTensorAdjunction`) and uniqueness of adjoints.

This is the statement "the right adjoint of tensoring with a finitely generated projective
module is tensoring with its dual", used to pass to left adjoints of the standardization functors
in B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
Lemma 7.19.
-/

noncomputable section

namespace Categorification

open CategoryTheory DG MulOpposite
open scoped DG.DegreeZero

universe w u

section Comparison

variable (X : Type u) [Ring X] [CatModule.HasDerivedCategory.{w, u} (SingleObj X)]
  [DG.HasDerivedCategory.{w, u} X]

/-- The comparison `D(SingleObj X) ≌ D(X)` on the localization functors:
`Q ⋙ 𝔼 ≅ ev ⋙ Q`, with `ev` the evaluation at the unique object. -/
def singleObjQIso :
    CatModule.DerivedCategory.Q ⋙ (CatModule.DerivedCategory.singleObjEquivalence X).functor ≅
      CatModule.toDGModuleCat X ⋙ DG.DerivedCategory.Q :=
  Functor.isoWhiskerRight (CatModule.DerivedCategory.quotientCompQhIso _).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (CatModule.DerivedCategory.QhCompToDGDerivedCategoryIso X) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (CatModule.HomotopyCategory.toDGHomotopyCategoryFactors X) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (DG.DerivedCategory.quotientCompQhIso X)

/-- `toCatModule ⋙ Q ⋙ 𝔼 ≅ Q` on dg `X`-modules. -/
def toCatModuleQIso :
    DGModuleCat.toCatModule X ⋙ CatModule.DerivedCategory.Q ⋙
        (CatModule.DerivedCategory.singleObjEquivalence X).functor ≅
      DG.DerivedCategory.Q :=
  Functor.isoWhiskerLeft _ (singleObjQIso X) ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (CatModule.singleObjEquivalence X).counitIso _ ≪≫
    Functor.leftUnitor _

/-- `Q ⋙ 𝔼⁻¹ ≅ toCatModule ⋙ Q` on dg `X`-modules. -/
def QCompSingleObjInverseIso :
    DG.DerivedCategory.Q ⋙ (CatModule.DerivedCategory.singleObjEquivalence X).inverse ≅
      DGModuleCat.toCatModule X ⋙ CatModule.DerivedCategory.Q :=
  Functor.isoWhiskerRight (toCatModuleQIso X).symm _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
      (CatModule.DerivedCategory.singleObjEquivalence X).unitIso.symm) ≪≫
    Functor.isoWhiskerLeft _ (Functor.rightUnitor _)

variable {X} in
/-- Natural isomorphisms out of `D(X)` are determined after precomposition with `Q`. -/
def isoOfQIso {E : Type*} [Category E] {F G : DG.DerivedCategory.{w, u} X ⥤ E}
    (e : DG.DerivedCategory.Q ⋙ F ≅ DG.DerivedCategory.Q ⋙ G) : F ≅ G :=
  (Localization.whiskeringLeftFunctor' DG.DerivedCategory.Qh
    (DG.HomotopyCategory.quasiIso X) E).preimageIso
    (Quotient.natIsoLift _ (Functor.associator _ _ _ ≪≫ e ≪≫ (Functor.associator _ _ _).symm))

end Comparison

section Bimodule

variable (A B : Type u) [Ring A] [Ring B] (N : Type u) [AddCommGroup N] [Module B N]
  [Module Aᵐᵒᵖ N] [SMulCommClass B Aᵐᵒᵖ N]

local notation "N₀" => InDegreeZero N
local notation "𝔅" => DGBimodule.catBimodule B A (InDegreeZero N)

/-- The tensor product over `SingleObj A` with the bimodule `N` is `N ⊗_A -`, on one dg
module. -/
def catTensorObjIso (X : DGModuleCat.{u} A) :
    (𝔅).tensorObj (DGModuleCat.toCatModuleObj X) ≅
      DGModuleCat.toCatModuleObj ((DGModuleCat.tensorFunctor (B := A) B N₀).obj X) := by
  let e := CatTensorProduct.singleObjEquiv N₀ X
  refine CatModule.isoMk (fun _ => e.toAddEquiv) ?_ (fun {_} x => e.map_d x) ?_
  · intro _ j x
    exact ⟨fun hx => (e.symm_apply_apply x) ▸ e.symm.map_mem hx, fun hx => e.map_mem hx⟩
  · intro Y Y' b z
    let Z := DGModuleCat.toCatModuleObj X
    let U := TensorProductOver A N₀ X
    let F (j : SingleObj B) : CatTensorProduct ((𝔅).right j) Z →+ U :=
      e.toAddEquiv.toAddMonoidHom
    have elem (j : SingleObj B) (t : SingleObj A) (n : N₀) (x : X) :
        F j (CatTensorProduct.tmul t n x) = TensorProductOver.tmul A n x :=
      CatTensorProduct.singleObjEquiv_tmul N₀ X t n x
    have commute : (F Y').comp ((𝔅).tensorAct Z b) =
        (DistribSMul.toAddMonoidHom U (show B from b)).comp (F Y) := by
      apply CatTensorProduct.addHom_ext
      intro t n x
      change F Y' ((𝔅).tensorAct Z b (CatTensorProduct.tmul t n x)) =
        (show B from b) • F Y (CatTensorProduct.tmul t n x)
      rw [CatBimodule.tensorAct_tmul]
      exact (elem Y' t ((show B from b) • (show N₀ from n)) x).trans
        ((TensorProductOver.smul_tmul _ _ _).symm.trans
          (congrArg ((show B from b) • ·) (elem Y t n x).symm))
    exact DFunLike.congr_fun commute z

theorem catTensorObjIso_hom_tmul (X : DGModuleCat.{u} A) (Y : SingleObj B) (t : SingleObj A)
    (n : N₀) (x : X) :
    (catTensorObjIso A B N X).hom.app Y (CatTensorProduct.tmul t n x) =
      TensorProductOver.tmul A n x :=
  CatTensorProduct.singleObjEquiv_tmul N₀ X t n x

/-- The tensor product over `SingleObj A` with the bimodule `N` is `N ⊗_A -`, naturally. -/
def catTensorNatIso :
    DGModuleCat.toCatModule A ⋙ (𝔅).tensorFunctor ≅
      DGModuleCat.tensorFunctor (B := A) B N₀ ⋙ DGModuleCat.toCatModule B :=
  NatIso.ofComponents (catTensorObjIso A B N) fun {X X'} f => CatModule.hom_ext fun Y z => by
    induction z using CatTensorProduct.induction_on with
    | zero => exact (map_zero _).trans (map_zero _).symm
    | tmul t n x =>
      have h := CatBimodule.tensorMap_tmul (𝔅) ((DGModuleCat.toCatModule A).map f) Y t n x
      refine ((congrArg ((catTensorObjIso A B N X').hom.app Y) h).trans
        (catTensorObjIso_hom_tmul A B N X' Y t n _)).trans ?_
      exact (congrArg (DGModuleHom.lTensor B N₀ f.hom)
        (catTensorObjIso_hom_tmul A B N X Y t n x)).symm
    | add z z' hz hz' =>
      exact (map_add _ _ _).trans ((congrArg₂ (· + ·) hz hz').trans (map_add _ _ _).symm)

/-- The tensor product over `SingleObj A` with the bimodule `N`, conjugated by
`CatModule (SingleObj _) ≌ DGModuleCat _`, is `N ⊗_A -`. -/
def catTensorFunctorIso :
    (CatModule.singleObjEquivalence A).inverse ⋙ (𝔅).tensorFunctor ⋙
        (CatModule.singleObjEquivalence B).functor ≅
      DGModuleCat.tensorFunctor (B := A) B N₀ :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (catTensorNatIso A B N) _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (CatModule.singleObjEquivalence B).counitIso ≪≫
    Functor.rightUnitor _

end Bimodule

section Hom

variable (A B : Type u) [Ring A] [Ring B] (M : Type u) [AddCommGroup M] [Module A M]
  [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M] [Module.Projective Bᵐᵒᵖ M] [Module.Finite Bᵐᵒᵖ M]

local notation "M₀" => InDegreeZero M
local notation "P₀" => InDegreeZero (RightDualModule B M)
local notation "𝔅" => DGBimodule.catBimodule B A (InDegreeZero (RightDualModule B M))

/-- The Hom functor `HOM_B(M^∨, -)` over `SingleObj B`, conjugated by
`CatModule (SingleObj _) ≌ DGModuleCat _`, is `M ⊗_B -`: both are right adjoint to
`M^∨ ⊗_A -`. -/
def catHomFunctorIso :
    (CatModule.singleObjEquivalence B).inverse ⋙ (𝔅).homFunctor ⋙
        (CatModule.singleObjEquivalence A).functor ≅
      DGModuleCat.tensorFunctor (B := B) A M₀ :=
  ((((CatModule.singleObjEquivalence A).symm.toAdjunction.comp
      (CatBimodule.tensorHomAdjunction 𝔅)).comp
        (CatModule.singleObjEquivalence B).toAdjunction).ofNatIsoLeft
    (catTensorFunctorIso A B (RightDualModule B M))).rightAdjointUniq
    (RightDualModule.dualTensorAdjunction A M)

end Hom

section Derived

variable (A B : Type u) [Ring A] [Ring B] (M : Type u) [AddCommGroup M] [Module A M]
  [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M] [Module.Projective Bᵐᵒᵖ M] [Module.Finite Bᵐᵒᵖ M]

local notation "P₀" => InDegreeZero (RightDualModule B M)
local notation "𝔅" => DGBimodule.catBimodule B A (InDegreeZero (RightDualModule B M))

/-- The dual `M^∨` in degree `0` is K-projective as a left dg `B`-module. -/
theorem rightDual_isKProjective : IsKProjective.{u} B P₀ :=
  InDegreeZero.isKProjective

/-- Every left module of the bimodule `M^∨` over `SingleObj B` is K-projective. -/
theorem rightDual_catBimodule_left_isKProjective (Y : SingleObj A) :
    CatModule.IsKProjective ((𝔅).left Y) :=
  DGBimodule.catBimodule_left_isKProjective B A P₀ (rightDual_isKProjective B M) Y

variable [CatModule.HasDerivedCategory.{w, u} (SingleObj A)]
  [CatModule.HasDerivedCategory.{w, u} (SingleObj B)]
  [DG.HasDerivedCategory.{w, u} A] [DG.HasDerivedCategory.{w, u} B]

/-- The derived Hom `RHOM_B(M^∨, -) : D(B) ⥤ D(A)`, transported from the one-object dg
categories. -/
def derivedRHomDual : DG.DerivedCategory.{w, u} B ⥤ DG.DerivedCategory.{w, u} A :=
  (CatModule.DerivedCategory.singleObjEquivalence B).inverse ⋙
    CatModule.DerivedCategory.rhom.{w, w} 𝔅 (rightDual_catBimodule_left_isKProjective A B M) ⋙
    (CatModule.DerivedCategory.singleObjEquivalence A).functor

/-- **`RHOM_B(M^∨, -) ≅ M ⊗ᴸ_B -`** for `M` finitely generated projective as a right
`B`-module. -/
def derivedRHomIsoDerivedTensorDual : derivedRHomDual A B M ≅ derivedTensor.{w} A B M :=
  isoOfQIso ((Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (QCompSingleObjInverseIso B) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (CatModule.DerivedCategory.QCompRhomIso.{w, w} 𝔅
        (rightDual_catBimodule_left_isKProjective A B M)) _ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (singleObjQIso A)) ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (catHomFunctorIso A B M) _ ≪≫
    (QCompDerivedTensorIso.{w} A B M).symm)

/-- The derived tensor product `M^∨ ⊗ᴸ_A -` with the bimodule over the one-object dg categories,
transported to `D(A) ⥤ D(B)`. -/
def catDerivedTensorDual : DG.DerivedCategory.{w, u} A ⥤ DG.DerivedCategory.{w, u} B :=
  (CatModule.DerivedCategory.singleObjEquivalence A).inverse ⋙
    CatModule.DerivedCategory.derivedTensor.{w, w} 𝔅
      (rightDual_catBimodule_left_isKProjective A B M) ⋙
    (CatModule.DerivedCategory.singleObjEquivalence B).functor

/-- The derived tensor–Hom adjunction `M^∨ ⊗ᴸ_A - ⊣ RHOM_B(M^∨, -)`, transported. -/
def catDerivedTensorDualAdjunction : catDerivedTensorDual A B M ⊣ derivedRHomDual A B M :=
  (((CatModule.DerivedCategory.singleObjEquivalence A).symm.toAdjunction).comp
    (CatModule.DerivedCategory.derivedTensorAdjunction.{w, w} 𝔅
      (rightDual_catBimodule_left_isKProjective A B M))).comp
    ((CatModule.DerivedCategory.singleObjEquivalence B).toAdjunction)

/-- The comparison `(B ⊗^L -)(Q P) ⟶ Q (B ⊗ P)` for the bimodule `M^∨` over the one-object dg
categories, natural in the dg module `P`; it is invertible for K-projective `P`. -/
def catDerivedTensorDualComparison :
    CatModule.DerivedCategory.Q ⋙ CatModule.DerivedCategory.derivedTensor.{w, w} 𝔅
        (rightDual_catBimodule_left_isKProjective A B M) ⟶
      (𝔅).tensorFunctor ⋙ CatModule.DerivedCategory.Q where
  app P := CatModule.DerivedCategory.derivedTensorObjIsoInv.{w, w} 𝔅
    (rightDual_catBimodule_left_isKProjective A B M) P
  naturality {P P'} g := by
    let hB := rightDual_catBimodule_left_isKProjective A B M
    let adj := CatModule.DerivedCategory.derivedTensorAdjunction.{w, w} 𝔅 hB
    let T := CatModule.DerivedCategory.tensorUnitMap.{w, w} 𝔅 hB
    let adjB := CatBimodule.tensorHomAdjunction 𝔅
    apply (adj.homEquiv _ _).injective
    change adj.homEquiv _ _ ((CatModule.DerivedCategory.derivedTensor.{w, w} 𝔅 hB).map
        (CatModule.DerivedCategory.Q.map g) ≫ (adj.homEquiv _ _).symm (T P')) =
      adj.homEquiv _ _ ((adj.homEquiv _ _).symm (T P) ≫
        CatModule.DerivedCategory.Q.map ((𝔅).tensorMap g))
    rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply, CatModule.DerivedCategory.tensorUnitMap_comp_rhom_map]
    have hu : adjB.unit.app P ≫ (𝔅).homFunctor.map ((𝔅).tensorMap g) = g ≫ adjB.unit.app P' :=
      adjB.unit_naturality g
    have he : adjB.homEquiv P _ ((𝔅).tensorMap g) = g ≫ adjB.unit.app P' :=
      (adjB.homEquiv_unit _ _ _).trans hu
    refine Eq.trans ?_ (congrArg (fun φ => CatModule.DerivedCategory.Q.map φ ≫
      (CatModule.DerivedCategory.QCompRhomIso.{w, w} 𝔅 hB).inv.app _) he).symm
    change CatModule.DerivedCategory.Q.map g ≫ CatModule.DerivedCategory.Q.map (adjB.unit.app P') ≫
        _ = CatModule.DerivedCategory.Q.map (g ≫ adjB.unit.app P') ≫ _
    rw [Functor.map_comp]
    exact (Category.assoc _ _ _).symm

omit [DG.HasDerivedCategory.{w, u} A] [DG.HasDerivedCategory.{w, u} B] in
theorem isIso_catDerivedTensorDualComparison_app {P : CatModule.{u} (SingleObj A)}
    (hP : CatModule.IsKProjective P) : IsIso ((catDerivedTensorDualComparison A B M).app P) :=
  (CatModule.DerivedCategory.derivedTensorObjIso.{w, w} 𝔅
    (rightDual_catBimodule_left_isKProjective A B M) hP).isIso_inv

/-- Rewriting `Q ⋙ (𝔼⁻¹ ⋙ L ⋙ 𝔼)` through the dg modules over `SingleObj A`. -/
def QCompCatDerivedTensorDualIso :
    DG.DerivedCategory.Q ⋙ catDerivedTensorDual A B M ≅
      DGModuleCat.toCatModule A ⋙ (CatModule.DerivedCategory.Q ⋙
        CatModule.DerivedCategory.derivedTensor.{w, w} 𝔅
          (rightDual_catBimodule_left_isKProjective A B M)) ⋙
        (CatModule.DerivedCategory.singleObjEquivalence B).functor :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (QCompSingleObjInverseIso A) _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _).symm

/-- Rewriting `toCatModule ⋙ (𝔅 ⊗ - ⋙ Q) ⋙ 𝔼` as `M^∨ ⊗_A - ⋙ Q`. -/
def catTensorCompQIso :
    DGModuleCat.toCatModule A ⋙ ((𝔅).tensorFunctor ⋙ CatModule.DerivedCategory.Q) ⋙
        (CatModule.DerivedCategory.singleObjEquivalence B).functor ≅
      DGModuleCat.tensorFunctor (B := A) B P₀ ⋙ DG.DerivedCategory.Q :=
  Functor.isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (singleObjQIso B) ≪≫ (Functor.associator _ _ _).symm) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (catTensorFunctorIso A B (RightDualModule B M)) _

/-- The comparison `(M^∨ ⊗^L -)(Q X) ⟶ Q (M^∨ ⊗_A X)` on dg `A`-modules, for the derived tensor
product over the one-object dg categories; it is invertible for K-projective `X`. -/
def catDerivedTensorDualQComparison :
    DG.DerivedCategory.Q ⋙ catDerivedTensorDual A B M ⟶
      DGModuleCat.tensorFunctor (B := A) B P₀ ⋙ DG.DerivedCategory.Q :=
  (QCompCatDerivedTensorDualIso A B M).hom ≫
    Functor.whiskerLeft _ (Functor.whiskerRight (catDerivedTensorDualComparison A B M) _) ≫
    (catTensorCompQIso A B M).hom

theorem isIso_catDerivedTensorDualQComparison_app {X : DGModuleCat.{u} A}
    (hX : IsKProjective.{u} A X) : IsIso ((catDerivedTensorDualQComparison A B M).app X) := by
  have : IsIso ((catDerivedTensorDualComparison A B M).app ((DGModuleCat.toCatModule A).obj X)) :=
    isIso_catDerivedTensorDualComparison_app A B M hX.toCatModuleObj
  simp only [catDerivedTensorDualQComparison, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  infer_instance

/-- The comparison on dg `A`-modules, written through the quotient to the homotopy category. -/
def catDerivedTensorDualQhAux :
    DG.HomotopyCategory.quotient A ⋙ DG.DerivedCategory.Qh ⋙ catDerivedTensorDual A B M ⟶
      DG.HomotopyCategory.quotient A ⋙ DG.HomotopyCategory.tensorFunctor B P₀ ⋙
        DG.DerivedCategory.Qh :=
  (Functor.associator _ _ _).inv ≫ catDerivedTensorDualQComparison A B M ≫
    (Functor.isoWhiskerRight (DG.HomotopyCategory.tensorFunctorQuotientIso B P₀).symm _ ≪≫
      Functor.associator _ _ _).hom

theorem isIso_catDerivedTensorDualQhAux_app {X : DGModuleCat.{u} A}
    (hX : IsKProjective.{u} A X) : IsIso ((catDerivedTensorDualQhAux A B M).app X) := by
  have := isIso_catDerivedTensorDualQComparison_app A B M hX
  change IsIso ((Functor.associator _ _ _).inv.app X ≫
    (catDerivedTensorDualQComparison A B M).app X ≫ _)
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_inv ((Functor.associator _ _ _).app X))
    (@IsIso.comp_isIso _ _ _ _ _ _ _ this (Iso.isIso_hom ((Functor.isoWhiskerRight
      (DG.HomotopyCategory.tensorFunctorQuotientIso B P₀).symm _ ≪≫
        Functor.associator _ _ _).app X)))

/-- The comparison descended to the homotopy category of dg `A`-modules. -/
def catDerivedTensorDualQhComparison :
    DG.DerivedCategory.Qh ⋙ catDerivedTensorDual A B M ⟶
      DG.HomotopyCategory.tensorFunctor B P₀ ⋙ DG.DerivedCategory.Qh :=
  Quotient.natTransLift _ (catDerivedTensorDualQhAux A B M)

/-- **The derived tensor products with `M^∨` agree**: the one over the one-object dg
categories (left adjoint to `RHOM_B(M^∨, -)`) is the library's `derivedTensor`, computed on
K-projective resolutions. -/
def catDerivedTensorDualIso :
    catDerivedTensorDual A B M ≅ derivedTensor.{w} B A (RightDualModule B M) := by
  let E := DG.DerivedCategory.kProjectiveEquivalence.{w} A
  let ι := (DG.HomotopyCategory.subcategoryKProjective A).ι
  let θ := Functor.whiskerLeft ι (catDerivedTensorDualQhComparison A B M)
  have hθ : IsIso θ := by
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ θ fun X => ?_
    obtain ⟨Xo, hX⟩ := X
    obtain ⟨X', rfl⟩ := DG.HomotopyCategory.quotient_obj_surjective Xo
    exact isIso_catDerivedTensorDualQhAux_app A B M
      ((DG.HomotopyCategory.quotient_obj_mem_subcategoryKProjective_iff X').mp hX)
  exact (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight E.counitIso.symm _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft E.inverse (@asIso _ _ _ _ θ hθ)

/-- **`M^∨ ⊗ᴸ_A - ⊣ M ⊗ᴸ_B -`**: for rings `A`, `B` and an `(A, B)`-bimodule `M` which is
finitely generated and projective as a right `B`-module, the derived tensor product with the
dual `M^∨ = Hom_{Bᵐᵒᵖ}(M, B)` is left adjoint to the derived tensor product with `M`. -/
def derivedTensorDualAdjunction :
    derivedTensor.{w} B A (RightDualModule B M) ⊣ derivedTensor.{w} A B M :=
  ((catDerivedTensorDualAdjunction A B M).ofNatIsoLeft
    (catDerivedTensorDualIso A B M)).ofNatIsoRight (derivedRHomIsoDerivedTensorDual A B M)

end Derived

end Categorification
