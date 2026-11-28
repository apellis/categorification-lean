/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KLR.MatEndModuleUnit
import Categorification.Algebra.InductionAlongSigma

/-!
# Rouquier's rightward crossing along two matrix maps as a module map

Consider two composable additive functors `F₁ : C₀ ⥤ C₁` and `F₂ : C₁ ⥤ C₂` with finite families
`X₀`, `X₁`, `X₂` such that `F₁ (X₀ i) = X₁ (e₁ i)` and `F₂ (X₁ j) = X₂ (e₂ j)`, their matrix maps
`φ₁`, `φ₂`, the functors `F₁'`, `F₂'` induced on completed additive envelopes with right adjoints
`E₁`, `E₂`, and an element `c` of the matrix ring of `X₂` commuting with the image of `φ₂ ∘ φ₁`.
The explicit rightward crossing `Ind_{φ₁} Res_{φ₁} M → Res_{φ₂} Ind_{φ₂} M`,
`z ⊗ m ↦ φ₂(z) c φ₂(1) ⊗ m` (`InductionAlong.sigmaLin`), is, under the module functors of
`E₁ ⋙ F₁'` (`MatEnd.indResModuleEquiv`) and `F₂' ⋙ E₂` (`MatEnd.resIndModuleEquiv`), the module map
of a natural transformation `σ : E₁ ⋙ F₁' ⟶ F₂' ⋙ E₂`, provided that the two agree on the
generator `φ₁(1) ⊗ -` (`MatEnd.resIndModuleEquiv_sigmaLin`).

This identifies the rightward crossing of Webster's functors on modules over `T^λ`
(arXiv:1309.3796v3, §4.6) with the rightward crossing of the categorical action (Brundan,
arXiv:1501.00350v1, (1.6); Webster, Theorem 4.31).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KLR.Diagram

open CategoryTheory CategoryTheory.Idempotents Preadditive MulOpposite InductionAlong

namespace MatEnd

universe v w

attribute [local instance] HomTensor.bimodule

variable {C₀ : Type*} [Category.{v} C₀] [Preadditive C₀] {C₁ : Type*} [Category.{v} C₁]
  [Preadditive C₁] {C₂ : Type*} [Category.{v} C₂] [Preadditive C₂]
  {ι₀ ι₁ ι₂ : Type w} [Fintype ι₀] [DecidableEq ι₀] [Fintype ι₁] [DecidableEq ι₁]
  [Fintype ι₂] [DecidableEq ι₂] {X₀ : ι₀ → C₀} {X₁ : ι₁ → C₁} {X₂ : ι₂ → C₂}
  (F₁ : C₀ ⥤ C₁) [F₁.Additive] (F₂ : C₁ ⥤ C₂) [F₂.Additive] {e₁ : ι₀ → ι₁} {e₂ : ι₁ → ι₂}
  (he₁ : Function.Injective e₁) (h₁ : ∀ i, F₁.obj (X₀ i) = X₁ (e₁ i))
  (he₂ : Function.Injective e₂) (h₂ : ∀ j, F₂.obj (X₁ j) = X₂ (e₂ j))

theorem karoubiMatrixOpY_eq : karoubiMatrixOpY X₁ = karoubiMatrixOp X₁ := rfl

variable {E₂ : Karoubi (Mat_ C₂) ⥤ Karoubi (Mat_ C₁)} (adj₂ : mapKaroubi F₂.mapMat_ ⊣ E₂)
  [E₂.Additive]

omit [E₂.Additive] in
/-- The unit at the completed sum of `X₁` intertwines the two matrix actions. -/
theorem homEquiv_sect_matrixOp (b : (MatEnd X₁)ᵐᵒᵖ) :
    adj₂.homEquiv _ _ (karoubiSect F₂ h₂) ≫
        E₂.map (karoubiMatrixOpY X₂ (mapEmbOp F₂ he₂ h₂ b)).unop =
      (karoubiMatrixOpY X₁ b).unop ≫ adj₂.homEquiv _ _ (karoubiSect F₂ h₂) := by
  rw [← Adjunction.homEquiv_naturality_right, karoubiSect_matrixOpY F₂ he₂ h₂ b,
    Adjunction.homEquiv_naturality_left]
  rfl

variable {c : (MatEnd X₂)ᵐᵒᵖ}
  (hc : ∀ a, c * mapEmbOp F₂ he₂ h₂ (mapEmbOp F₁ he₁ h₁ a) =
    mapEmbOp F₂ he₂ h₂ (mapEmbOp F₁ he₁ h₁ a) * c)

theorem sigmaElt_smul (b : (MatEnd X₁)ᵐᵒᵖ) (w : Corner (mapEmbOp F₁ he₁ h₁)) :
    sigmaElt (mapEmbOp F₁ he₁ h₁) (mapEmbOp F₂ he₂ h₂) c (b • w) =
      mapEmbOp F₂ he₂ h₂ b • sigmaElt (mapEmbOp F₁ he₁ h₁) (mapEmbOp F₂ he₂ h₂) c w :=
  Subtype.ext (by
    change mapEmbOp F₂ he₂ h₂ (b * w.1) * (c * mapEmbOp F₂ he₂ h₂ 1) =
      mapEmbOp F₂ he₂ h₂ b * (mapEmbOp F₂ he₂ h₂ w.1 * (c * mapEmbOp F₂ he₂ h₂ 1))
    rw [map_mul, mul_assoc])

variable {E₁ : Karoubi (Mat_ C₁) ⥤ Karoubi (Mat_ C₀)} (adj₁ : mapKaroubi F₁.mapMat_ ⊣ E₁)
  [E₁.Additive]
  (σK : E₁ ⋙ mapKaroubi F₁.mapMat_ ⟶ mapKaroubi F₂.mapMat_ ⋙ E₂)
  (hσ : adj₂.homEquiv _ _ (karoubiSect F₂ h₂) ≫ E₂.map (karoubiCorner F₂ he₂ h₂
      (sigmaElt (mapEmbOp F₁ he₁ h₁) (mapEmbOp F₂ he₂ h₂) c (unitGen (mapEmbOp F₁ he₁ h₁)))) =
    (karoubiGen F₁ he₁ h₁ ≫ (mapKaroubi F₁.mapMat_).map (adj₁.homEquiv _ _ (karoubiSect F₁ h₁))) ≫
      σK.app ((toKaroubi _).obj (familySum X₁)))

omit [E₂.Additive] [E₁.Additive] in
include hσ in
/-- The generator condition `hσ` at every corner element. -/
theorem sigma_corner (z : Corner (mapEmbOp F₁ he₁ h₁)) :
    adj₂.homEquiv _ _ (karoubiSect F₂ h₂) ≫ E₂.map (karoubiCorner F₂ he₂ h₂
      (sigmaElt (mapEmbOp F₁ he₁ h₁) (mapEmbOp F₂ he₂ h₂) c z)) =
    (karoubiCorner F₁ he₁ h₁ z ≫
      (mapKaroubi F₁.mapMat_).map (adj₁.homEquiv _ _ (karoubiSect F₁ h₁))) ≫
      σK.app ((toKaroubi _).obj (familySum X₁)) := by
  have hz : z = z.1 • unitGen (mapEmbOp F₁ he₁ h₁) := Subtype.ext z.2.symm
  rw [hz, sigmaElt_smul, karoubiCorner_smul, E₂.map_comp, ← Category.assoc,
    homEquiv_sect_matrixOp, Category.assoc, hσ, karoubiCorner_smul]
  simp only [Category.assoc]

include hσ in
/-- **Rouquier's rightward crossing along two matrix maps is a module map**: under
`indResModuleEquiv` and `resIndModuleEquiv`, `z ⊗ m ↦ φ₂(z) c φ₂(1) ⊗ m` is the module map of
`σK`. -/
theorem resIndModuleEquiv_sigmaLin (M : Type (max w v)) [AddCommGroup M]
    [Module (MatEnd X₁)ᵐᵒᵖ M] {J : Type*} [Fintype J]
    (π : J → (E₁.obj ((toKaroubi _).obj (familySum X₁)) ⟶ (toKaroubi _).obj (familySum X₀)))
    (ι' : J → ((toKaroubi _).obj (familySum X₀) ⟶ E₁.obj ((toKaroubi _).obj (familySum X₁))))
    (hπ : ∑ j, π j ≫ ι' j = 𝟙 _)
    (x : Ind (Res (mapEmbOp F₁ he₁ h₁) M) (mapEmbOp F₁ he₁ h₁)) :
    letI := HomTensor.transferModule (karoubiMatrixOp X₁) M
    resIndModuleEquiv F₂ he₂ h₂ M adj₂
        (sigmaLin (mapEmbOp F₁ he₁ h₁) (mapEmbOp F₂ he₂ h₂) hc M x) =
      HomTensor.natModuleMap ℤ ((toKaroubi _).obj (familySum X₁))
        ((toKaroubi _).obj (familySum X₁)) M σK
        (indResModuleEquiv F₁ he₁ h₁ adj₁ M π ι' hπ x) := by
  let _ := HomTensor.transferModule (karoubiMatrixOp X₁) M
  let _ := HomTensor.transferModule (karoubiMatrixOpY X₂) (Ind M (mapEmbOp F₂ he₂ h₂))
  induction x using Ind.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | add s t hs ht => rw [map_add, map_add, hs, ht, map_add, map_add]
  | tmul z m =>
    change HomTensor.compModuleEquiv ℤ (mapKaroubi F₂.mapMat_) E₂ _ _ _
        (fun _ : Unit => karoubiSect F₂ h₂) (fun _ => karoubiGen F₂ he₂ h₂)
        (karoubiSect_gen_sum F₂ he₂ h₂) M
        (BalancedTensor.tmul (resRegularHom F₂ he₂ h₂ adj₂ (resUnit _))
          (indModuleEquiv F₂ he₂ h₂ M (Ind.tmul
            (sigmaElt (mapEmbOp F₁ he₁ h₁) (mapEmbOp F₂ he₂ h₂) c z) m.val))) =
      BalancedTensor.tmul (show (toKaroubi _).obj (familySum X₁) ⟶
        (mapKaroubi F₂.mapMat_ ⋙ E₂).obj ((toKaroubi _).obj (familySum X₁)) from
        (karoubiCorner F₁ he₁ h₁ z ≫ (mapKaroubi F₁.mapMat_).map (adj₁.homEquiv _ _
          (karoubiSect F₁ h₁ ≫ (karoubiMatrixOpY X₁ (mapEmbOp F₁ he₁ h₁ 1)).unop))) ≫
          σK.app ((toKaroubi _).obj (familySum X₁))) m.val
    rw [indModuleEquiv_tmul, HomTensor.compModuleEquiv_tmul]
    congr 1
    change adj₂.homEquiv _ _ (karoubiSect F₂ h₂ ≫
        (karoubiMatrixOpY X₂ (mapEmbOp F₂ he₂ h₂ 1)).unop) ≫ E₂.map (karoubiCorner F₂ he₂ h₂
          (sigmaElt (mapEmbOp F₁ he₁ h₁) (mapEmbOp F₂ he₂ h₂) c z)) = _
    rw [karoubiSect_matrixOpY_one, karoubiSect_matrixOpY_one]
    exact sigma_corner F₁ F₂ he₁ h₁ he₂ h₂ adj₂ adj₁ σK hσ z

end MatEnd

end Categorification.KLR.Diagram
