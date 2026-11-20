/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KLR.MatEndModuleComp
import Categorification.Algebra.SumDecompLinear

/-!
# Decompositions of restriction after induction on matrix rings

Let `φ₁` be the matrix map of an additive functor `F₁` out of a family `X`, and `φ₂` the matrix
map of an additive functor `F₂` into `X`, both with adjoints on completions. Restriction after
induction along `φ₁` and induction after restriction along `φ₂` are module functors of
endofunctors `G` and `G'` of the completion (`MatEnd.resIndModuleEquivOfIso`,
`MatEnd.indResModuleEquivOfIso`). A decomposition of the module functor of `G` as that of `G'`
plus copies of the module functor of an endofunctor equal to the identity gives an isomorphism
of modules over the matrix ring of `X`,
`Res_{φ₁} (Ind M φ₁) ≅ Ind (Res_{φ₂} M) φ₂ × M^ι₀` (`MatEnd.resIndEquivIndResProd`), and
dually (`MatEnd.indResEquivResIndProd`).

This is the form of the commutation relations between `Eᵢ` and `Fᵢ` on all modules used in
Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5.
-/

noncomputable section

namespace Categorification

open CategoryTheory

namespace HomTensor

variable {A : Type*} [Category A] [Preadditive A] (O : A) (M : Type*) [AddCommGroup M]
  [Module (End O)ᵐᵒᵖ M]

attribute [local instance] bimodule

/-- A module is the module functor of an additive endofunctor equal to the identity. -/
def unitModuleEquivOfEq (G : A ⥤ A) [G.Additive] (h : G = 𝟭 A) :
    M ≃ₗ[(End O)ᵐᵒᵖ] BalancedTensor ℤ (End O)ᵐᵒᵖ (End O)ᵐᵒᵖ (O ⟶ G.obj O) M :=
  (unitModuleEquiv ℤ O M).symm.trans (natModuleEquiv O O M (eqToIso h.symm))

end HomTensor

namespace KLR.Diagram.MatEnd

open CategoryTheory.Idempotents MulOpposite InductionAlong

universe v w

attribute [local instance] HomTensor.bimodule

variable {C : Type*} [Category.{v} C] [Preadditive C] {D₁ : Type*} [Category.{v} D₁]
  [Preadditive D₁] {C₂ : Type*} [Category.{v} C₂] [Preadditive C₂]
  {ι κ₁ κ₂ : Type w} [Fintype ι] [DecidableEq ι] [Fintype κ₁] [DecidableEq κ₁]
  [Fintype κ₂] [DecidableEq κ₂] {X : ι → C} {Y₁ : κ₁ → D₁} {Z : κ₂ → C₂}
  (F₁ : C ⥤ D₁) [F₁.Additive] {e₁ : ι → κ₁} (he₁ : Function.Injective e₁)
  (h₁ : ∀ i, F₁.obj (X i) = Y₁ (e₁ i))
  {E₁ : Karoubi (Mat_ D₁) ⥤ Karoubi (Mat_ C)} (adj₁ : mapKaroubi F₁.mapMat_ ⊣ E₁) [E₁.Additive]
  {G : Karoubi (Mat_ C) ⥤ Karoubi (Mat_ C)} [G.Additive] (eG : G ≅ mapKaroubi F₁.mapMat_ ⋙ E₁)
  (F₂ : C₂ ⥤ C) [F₂.Additive] {e₂ : κ₂ → ι} (he₂ : Function.Injective e₂)
  (h₂ : ∀ j, F₂.obj (Z j) = X (e₂ j))
  {E₂ : Karoubi (Mat_ C) ⥤ Karoubi (Mat_ C₂)} (adj₂ : mapKaroubi F₂.mapMat_ ⊣ E₂) [E₂.Additive]
  {J : Type*} [Fintype J]
  (π : J → (E₂.obj ((toKaroubi _).obj (familySum X)) ⟶ (toKaroubi _).obj (familySum Z)))
  (ι' : J → ((toKaroubi _).obj (familySum Z) ⟶ E₂.obj ((toKaroubi _).obj (familySum X))))
  (hπ : ∑ j, π j ≫ ι' j = 𝟙 _)
  {G' : Karoubi (Mat_ C) ⥤ Karoubi (Mat_ C)} [G'.Additive]
  (eG' : G' ≅ E₂ ⋙ mapKaroubi F₂.mapMat_)
  {H : Karoubi (Mat_ C) ⥤ Karoubi (Mat_ C)} [H.Additive] (hH : H = 𝟭 _)
  {ι₀ : Type} [Fintype ι₀] [DecidableEq ι₀]
  (M : Type (max w v)) [AddCommGroup M] [Module (MatEnd X)ᵐᵒᵖ M]

/-- **Restriction after induction against induction after restriction**: a decomposition of
the module functor of `G ≅ F₁' ⋙ E₁` as that of `G' ≅ E₂ ⋙ F₂'` plus `ι₀` copies of the module
functor of the identity gives `Res_{φ₁} (Ind M φ₁) ≅ Ind (Res_{φ₂} M) φ₂ × M^ι₀` as modules over
the matrix ring of `X`. -/
def resIndEquivIndResProd
    (Dc : letI := HomTensor.transferModule (karoubiMatrixOp X) M
      SumDecomp (HomTensor.tensorObj ((toKaroubi _).obj (familySum X))
          ((toKaroubi _).obj (familySum X)) M G)
        (HomTensor.tensorObj ((toKaroubi _).obj (familySum X))
          ((toKaroubi _).obj (familySum X)) M G')
        (fun _ : ι₀ => HomTensor.tensorObj ((toKaroubi _).obj (familySum X))
          ((toKaroubi _).obj (familySum X)) M H)) :
    Res (mapEmbOp F₁ he₁ h₁) (Ind M (mapEmbOp F₁ he₁ h₁)) ≃ₗ[(MatEnd X)ᵐᵒᵖ]
      Ind (Res (mapEmbOp F₂ he₂ h₂) M) (mapEmbOp F₂ he₂ h₂) × (ι₀ → M) :=
  letI := HomTensor.transferModule (karoubiMatrixOp X) M
  SumDecomp.semilinearEquiv (karoubiMatrixOp X) Dc
    (resIndModuleEquivOfIso F₁ he₁ h₁ M adj₁ eG)
    (fun a m => resIndModuleEquivOfIso_smul F₁ he₁ h₁ M adj₁ eG a m)
    (indResModuleEquivOfIso F₂ he₂ h₂ adj₂ M π ι' hπ eG')
    (fun b x => indResModuleEquivOfIso_smul F₂ he₂ h₂ adj₂ M π ι' hπ eG' b x)
    ((HomTensor.unitModuleEquivOfEq _ M H hH).restrictScalars ℤ)
    (fun a x => by
      rw [← HomTensor.transferModule_smul (σ := karoubiMatrixOp X) a x]
      exact (HomTensor.unitModuleEquivOfEq _ M H hH).map_smul (karoubiMatrixOp X a) x)

/-- **Induction after restriction against restriction after induction**: a decomposition of
the module functor of `G' ≅ E₂ ⋙ F₂'` as that of `G ≅ F₁' ⋙ E₁` plus `ι₀` copies of the module
functor of the identity gives `Ind (Res_{φ₂} M) φ₂ ≅ Res_{φ₁} (Ind M φ₁) × M^ι₀` as modules over
the matrix ring of `X`. -/
def indResEquivResIndProd
    (Dc : letI := HomTensor.transferModule (karoubiMatrixOp X) M
      SumDecomp (HomTensor.tensorObj ((toKaroubi _).obj (familySum X))
          ((toKaroubi _).obj (familySum X)) M G')
        (HomTensor.tensorObj ((toKaroubi _).obj (familySum X))
          ((toKaroubi _).obj (familySum X)) M G)
        (fun _ : ι₀ => HomTensor.tensorObj ((toKaroubi _).obj (familySum X))
          ((toKaroubi _).obj (familySum X)) M H)) :
    Ind (Res (mapEmbOp F₂ he₂ h₂) M) (mapEmbOp F₂ he₂ h₂) ≃ₗ[(MatEnd X)ᵐᵒᵖ]
      Res (mapEmbOp F₁ he₁ h₁) (Ind M (mapEmbOp F₁ he₁ h₁)) × (ι₀ → M) :=
  letI := HomTensor.transferModule (karoubiMatrixOp X) M
  SumDecomp.semilinearEquiv (karoubiMatrixOp X) Dc
    (indResModuleEquivOfIso F₂ he₂ h₂ adj₂ M π ι' hπ eG')
    (fun b x => indResModuleEquivOfIso_smul F₂ he₂ h₂ adj₂ M π ι' hπ eG' b x)
    (resIndModuleEquivOfIso F₁ he₁ h₁ M adj₁ eG)
    (fun a m => resIndModuleEquivOfIso_smul F₁ he₁ h₁ M adj₁ eG a m)
    ((HomTensor.unitModuleEquivOfEq _ M H hH).restrictScalars ℤ)
    (fun a x => by
      rw [← HomTensor.transferModule_smul (σ := karoubiMatrixOp X) a x]
      exact (HomTensor.unitModuleEquivOfEq _ M H hH).map_smul (karoubiMatrixOp X a) x)

end KLR.Diagram.MatEnd

end Categorification
