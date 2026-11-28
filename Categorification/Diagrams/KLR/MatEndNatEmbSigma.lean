/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KLR.MatEndNatEmb
import Categorification.Diagrams.KLR.MatEndModuleSigma

/-!
# The crossing element of two composable matrix maps

Consider composable additive functors `F₁ : C₀ ⥤ C₁`, `F₂ : C₁ ⥤ C₂` with finite families
`X₀`, `X₁`, `X₂`, injective `e₁`, `e₂` and `F₁ (X₀ i) = X₁ (e₁ i)`, `F₂ (X₁ j) = X₂ (e₂ j)`.

* The matrix map of `F₁ ⋙ F₂` along `e₂ ∘ e₁` is the composite of the matrix maps
  (`MatEnd.mapEmb_comp`), and its corner generator is the composite of the corner generators
  (`MatEnd.karoubiGen_comp`).
* A natural endomorphism `τ₀` of `F₁ ⋙ F₂` gives an element `natEmb τ₀` commuting with the image
  of the composite matrix map (`MatEnd.natEmb_comp_commute`).
* For Karoubi adjunctions `F₁' ⊣ E₁`, `F₂' ⊣ E₂`, the rightward crossing
  `σ = (η₂ on the right) · τ₀ · (ε₁ on the left)` of Brundan, arXiv:1501.00350v1, (1.6), with
  `τ₀` completed, satisfies the generator condition of `MatEnd.resIndModuleEquiv_sigmaLin`
  (`MatEnd.sigma_generator`). So the explicit crossing `z ⊗ m ↦ φ₂(z) c φ₂(1) ⊗ m` with
  `c = natEmb τ₀` is the module map of `σ`.

This identifies the rightward crossing of Webster's induction and restriction functors on
modules over `T^λ` (arXiv:1309.3796v3, §4.6) with that of the completed black action.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KLR.Diagram

open CategoryTheory CategoryTheory.Idempotents Preadditive MulOpposite InductionAlong

namespace MatEnd

universe v w

variable {C₀ : Type*} [Category.{v} C₀] [Preadditive C₀] {C₁ : Type*} [Category.{v} C₁]
  [Preadditive C₁] {C₂ : Type*} [Category.{v} C₂] [Preadditive C₂]
  {ι₀ ι₁ ι₂ : Type w} [Fintype ι₀] [DecidableEq ι₀] [Fintype ι₁] [DecidableEq ι₁]
  [Fintype ι₂] [DecidableEq ι₂] {X₀ : ι₀ → C₀} {X₁ : ι₁ → C₁} {X₂ : ι₂ → C₂}
  (F₁ : C₀ ⥤ C₁) (F₂ : C₁ ⥤ C₂) {e₁ : ι₀ → ι₁} {e₂ : ι₁ → ι₂}
  (he₁ : Function.Injective e₁) (h₁ : ∀ i, F₁.obj (X₀ i) = X₁ (e₁ i))
  (he₂ : Function.Injective e₂) (h₂ : ∀ j, F₂.obj (X₁ j) = X₂ (e₂ j))

omit [Preadditive C₀] [Preadditive C₁] [Preadditive C₂] [Fintype ι₀] [DecidableEq ι₀]
  [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂] in
include h₁ h₂ in
/-- The object equations of the composite functor along `e₂ ∘ e₁`. -/
theorem compEq (i : ι₀) : (F₁ ⋙ F₂).obj (X₀ i) = X₂ ((e₂ ∘ e₁) i) :=
  (congrArg F₂.obj (h₁ i)).trans (h₂ (e₁ i))

omit [Preadditive C₀] [Preadditive C₁] [Preadditive C₂] [Fintype ι₀] [DecidableEq ι₀]
  [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂] in
theorem conjF_conjF {i j : ι₀} (g : X₀ i ⟶ X₀ j) :
    conjF F₂ h₂ (conjF F₁ h₁ g) = conjF (F₁ ⋙ F₂) (compEq F₁ F₂ h₁ h₂) g := by
  simp [conjF, eqToHom_map]

variable [F₁.Additive] [F₂.Additive]

omit [Preadditive C₀] [DecidableEq ι₀] [F₁.Additive] in
/-- The matrix map of a composite functor is the composite of the matrix maps. -/
theorem mapEmb_comp (f : MatEnd X₀) :
    mapEmb (F₁ ⋙ F₂) (compEq F₁ F₂ h₁ h₂) f = mapEmb F₂ h₂ (mapEmb F₁ h₁ f) := by
  let m : MatEnd X₁ →+ MatEnd X₂ := ⟨⟨mapEmb F₂ h₂, mapEmb_zero F₂ h₂⟩, mapEmb_add F₂ h₂⟩
  change _ = m (mapEmb F₁ h₁ f)
  rw [mapEmb, mapEmb, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  change _ = mapEmb F₂ h₂ _
  rw [mapEmb_single, conjF_conjF]
  rfl

theorem mapEmbOp_comp (a : (MatEnd X₀)ᵐᵒᵖ) :
    mapEmbOp (F₁ ⋙ F₂) (he₂.comp he₁) (compEq F₁ F₂ h₁ h₂) a =
      mapEmbOp F₂ he₂ h₂ (mapEmbOp F₁ he₁ h₁ a) :=
  unop_injective (mapEmb_comp F₁ F₂ h₁ h₂ a.unop)

/-- The corner generator of the composite matrix map is the composite of the corner
generators. -/
theorem karoubiGen_comp :
    karoubiGen (F₁ ⋙ F₂) (he₂.comp he₁) (compEq F₁ F₂ h₁ h₂) =
      karoubiGen F₂ he₂ h₂ ≫ (mapKaroubi F₂.mapMat_).map (karoubiGen F₁ he₁ h₁) := by
  apply Karoubi.hom_ext
  change toFamilyHom X₂ _ (cornerEquiv (F₁ ⋙ F₂) (he₂.comp he₁) (compEq F₁ F₂ h₁ h₂)
      (unitGen (mapEmbOp (F₁ ⋙ F₂) (he₂.comp he₁) (compEq F₁ F₂ h₁ h₂)))) =
    toFamilyHom X₂ (fun j => F₂.obj (X₁ j)) (cornerEquiv F₂ he₂ h₂ (unitGen (mapEmbOp F₂ he₂ h₂)))
      ≫ toFamilyHom (fun j => F₂.obj (X₁ j)) (fun i => F₂.obj (F₁.obj (X₀ i)))
        (fun j i => F₂.map (cornerEquiv F₁ he₁ h₁ (unitGen (mapEmbOp F₁ he₁ h₁)) j i))
  rw [toFamilyHom_comp]
  congr 1
  funext a i
  simp only [cornerEquiv_apply, unitGen, mapEmbOp_apply, unop_one]
  change mapEmb (F₁ ⋙ F₂) (compEq F₁ F₂ h₁ h₂) 1 a (e₂ (e₁ i)) ≫ _ = _
  rw [mapEmb_comp F₁ F₂ h₁ h₂, show mapEmb F₂ h₂ (mapEmb F₁ h₁ 1) = mapEmb F₂ h₂ (mapEmb F₁ h₁ 1) *
      mapEmb F₂ h₂ 1 by rw [← mapEmb_mul F₂ he₂ h₂, mul_one], mapEmb_mul_apply_emb F₂ he₂ h₂,
    Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [conjF, eqToHom_map]

variable (τ₀ : F₁ ⋙ F₂ ⟶ F₁ ⋙ F₂)

/-- **The crossing element commutes with the image of the composite matrix map.** This is the
hypothesis `hc` of `InductionAlong.sigmaLin`. -/
theorem natEmb_comp_commute (a : (MatEnd X₀)ᵐᵒᵖ) :
    op (natEmb (F₁ ⋙ F₂) (compEq F₁ F₂ h₁ h₂) τ₀) *
        mapEmbOp F₂ he₂ h₂ (mapEmbOp F₁ he₁ h₁ a) =
      mapEmbOp F₂ he₂ h₂ (mapEmbOp F₁ he₁ h₁ a) *
        op (natEmb (F₁ ⋙ F₂) (compEq F₁ F₂ h₁ h₂) τ₀) := by
  rw [← mapEmbOp_comp F₁ F₂ he₁ h₁ he₂ h₂]
  exact (intertwines_natEmb (F₁ ⋙ F₂) (he₂.comp he₁) (compEq F₁ F₂ h₁ h₂) τ₀ a).symm

/-- The generator condition at the matrix level: `sect₂ ≫ (φ₂(φ₁ 1) c φ₂(1))` is
`F₂'(gen₁) ≫ τ₀ ≫ F₂'(sect₁)`. -/
theorem karoubiSect_corner_sigmaElt :
    karoubiSect F₂ h₂ ≫ karoubiCorner F₂ he₂ h₂ (sigmaElt (mapEmbOp F₁ he₁ h₁)
      (mapEmbOp F₂ he₂ h₂) (op (natEmb (F₁ ⋙ F₂) (compEq F₁ F₂ h₁ h₂) τ₀))
      (unitGen (mapEmbOp F₁ he₁ h₁))) =
    (mapKaroubi F₂.mapMat_).map (karoubiGen F₁ he₁ h₁) ≫
      (completionMap₂ τ₀).app ((toKaroubi _).obj (familySum X₀)) ≫
      (mapKaroubi F₂.mapMat_).map (karoubiSect F₁ h₁) := by
  set c := op (natEmb (F₁ ⋙ F₂) (compEq F₁ F₂ h₁ h₂) τ₀)
  have hcancel : ∀ f g : (mapKaroubi F₂.mapMat_).obj ((toKaroubi _).obj (familySum X₁)) ⟶
      (mapKaroubi F₂.mapMat_).obj ((toKaroubi _).obj (familySum X₁)),
      karoubiGen F₂ he₂ h₂ ≫ f = karoubiGen F₂ he₂ h₂ ≫ g → f = g := fun f g hfg => by
    rw [← Category.id_comp f, ← Category.id_comp g, ← karoubiSect_gen F₂ he₂ h₂,
      Category.assoc, Category.assoc, hfg]
  apply hcancel
  rw [← Category.assoc, karoubiGen_sect, ← karoubiCorner_smul, ← Category.assoc,
    ← karoubiGen_comp F₁ F₂ he₁ h₁ he₂ h₂]
  have hgen := karoubiCorner_cornerMul_natEmb (F₁ ⋙ F₂) (he₂.comp he₁) (compEq F₁ F₂ h₁ h₂) τ₀
  rw [← Category.assoc, ← hgen]
  have hcm : cornerMul (intertwines_natEmb (F₁ ⋙ F₂) (he₂.comp he₁) (compEq F₁ F₂ h₁ h₂) τ₀)
      (unitGen (mapEmbOp (F₁ ⋙ F₂) (he₂.comp he₁) (compEq F₁ F₂ h₁ h₂))) =
      c • unitGen (mapEmbOp (F₁ ⋙ F₂) (he₂.comp he₁) (compEq F₁ F₂ h₁ h₂)) :=
    Subtype.ext (intertwines_natEmb (F₁ ⋙ F₂) (he₂.comp he₁) (compEq F₁ F₂ h₁ h₂) τ₀ 1)
  have e3 : (karoubiMatrixOpY X₂ c).unop ≫ karoubiGen (F₁ ⋙ F₂) (he₂.comp he₁)
      (compEq F₁ F₂ h₁ h₂) ≫ (mapKaroubi F₂.mapMat_).map (karoubiSect F₁ h₁) =
      (karoubiMatrixOpY X₂ c).unop ≫
        (karoubiMatrixOpY X₂ (mapEmbOp F₂ he₂ h₂ (mapEmbOp F₁ he₁ h₁ 1))).unop ≫
          karoubiGen F₂ he₂ h₂ := by
    rw [karoubiGen_comp F₁ F₂ he₁ h₁ he₂ h₂, Category.assoc, ← Functor.map_comp,
      karoubiGen_sect F₁ he₁ h₁, karoubiMatrixOpY_eq (X₁ := X₁), karoubiGen_map F₂ he₂ h₂]
  rw [hcm, karoubiCorner_smul (F₁ ⋙ F₂), Category.assoc]
  refine Eq.trans ?_ e3.symm
  rw [← karoubiCorner_smul F₂ he₂ h₂, ← karoubiCorner_smul F₂ he₂ h₂]
  congr 1
  apply Subtype.ext
  change mapEmbOp F₂ he₂ h₂ 1 * (mapEmbOp F₂ he₂ h₂ (mapEmbOp F₁ he₁ h₁ 1) *
      (c * mapEmbOp F₂ he₂ h₂ 1)) =
    c * (mapEmbOp F₂ he₂ h₂ (mapEmbOp F₁ he₁ h₁ 1) * mapEmbOp F₂ he₂ h₂ 1)
  rw [← mul_assoc, ← map_mul, one_mul, ← mul_assoc, ← mul_assoc,
    natEmb_comp_commute F₁ F₂ he₁ h₁ he₂ h₂ τ₀ 1]

variable {E₁ : Karoubi (Mat_ C₁) ⥤ Karoubi (Mat_ C₀)} (adj₁ : mapKaroubi F₁.mapMat_ ⊣ E₁)
  {E₂ : Karoubi (Mat_ C₂) ⥤ Karoubi (Mat_ C₁)} (adj₂ : mapKaroubi F₂.mapMat_ ⊣ E₂)
  (σK : E₁ ⋙ mapKaroubi F₁.mapMat_ ⟶ mapKaroubi F₂.mapMat_ ⋙ E₂)

/-- **The generator condition for the rightward crossing.** If `σK` is the rightward crossing
`η₂ · τ₀ · ε₁` of Brundan, arXiv:1501.00350v1, (1.6), at the completed sum of `X₁` (with `τ₀`
completed), then it satisfies the hypothesis `hσ` of `MatEnd.resIndModuleEquiv_sigmaLin` for the
crossing element `c = natEmb τ₀`. -/
theorem sigma_generator
    (hσK : σK.app ((toKaroubi _).obj (familySum X₁)) =
      adj₂.unit.app ((mapKaroubi F₁.mapMat_).obj (E₁.obj ((toKaroubi _).obj (familySum X₁)))) ≫
        E₂.map ((completionMap₂ τ₀).app (E₁.obj ((toKaroubi _).obj (familySum X₁)))) ≫
        E₂.map ((mapKaroubi F₂.mapMat_).map (adj₁.counit.app ((toKaroubi _).obj (familySum X₁))))) :
    adj₂.homEquiv _ _ (karoubiSect F₂ h₂) ≫ E₂.map (karoubiCorner F₂ he₂ h₂
        (sigmaElt (mapEmbOp F₁ he₁ h₁) (mapEmbOp F₂ he₂ h₂)
          (op (natEmb (F₁ ⋙ F₂) (compEq F₁ F₂ h₁ h₂) τ₀)) (unitGen (mapEmbOp F₁ he₁ h₁)))) =
      (karoubiGen F₁ he₁ h₁ ≫
        (mapKaroubi F₁.mapMat_).map (adj₁.homEquiv _ _ (karoubiSect F₁ h₁))) ≫
        σK.app ((toKaroubi _).obj (familySum X₁)) := by
  rw [hσK, Adjunction.homEquiv_unit, Category.assoc, ← E₂.map_comp,
    karoubiSect_corner_sigmaElt F₁ F₂ he₁ h₁ he₂ h₂ τ₀, ← adj₂.unit_naturality_assoc]
  simp only [← E₂.map_comp]
  congr 2
  rw [Functor.map_comp, Category.assoc]
  congr 1
  erw [← Category.assoc, (completionMap₂ τ₀).naturality]
  rw [Category.assoc]
  congr 1
  change _ = (mapKaroubi F₂.mapMat_).map ((mapKaroubi F₁.mapMat_).map
    (adj₁.homEquiv _ _ (karoubiSect F₁ h₁))) ≫ _
  symm
  refine ((mapKaroubi F₂.mapMat_).map_comp _ _).symm.trans (congrArg _ ?_)
  erw [← Adjunction.homEquiv_counit, Equiv.symm_apply_apply]

end MatEnd

end Categorification.KLR.Diagram
