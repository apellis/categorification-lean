/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KLR.MatEndModuleSumInv
import Categorification.TwoRep.SumInvPointwise

/-!
# Brundan's inversion relation (1.9) on modules, when the crossing has zero source

Brundan, arXiv:1501.00350v1, (1.9), in the setting of `MatEnd.resIndSumInvFrom`, at a family
`X₁` on which the source `G` of the crossing `σK : G ⟶ F₂' ⋙ E₂` vanishes. This is the boundary
case of Webster's functors on modules (arXiv:1309.3796v3, §4.6, Theorem 4.31), where `Eᵢ`
vanishes on modules whose content does not contain `i`:

* `HomTensor.natModuleHom_eq_zero_of_app`: the module map of a natural transformation vanishes
  when its component at the generating object does;
* `MatEnd.resIndSumInvFromOfIsZero`: an explicit inverse of `(σK, η₂ α₂^m E₂)` among functors
  of the completed additive envelope, with `G` zero on the generating object, gives an
  explicit inverse of `(0, m ↦ φ₂(1) d₂^m ⊗ m) : 0 ⊕ M^n ⟶ Res (Ind M)` on every module `M`
  over the matrix ring of `X₁`; that is, the dotted units identify `M^n` with `Res (Ind M)`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.HomTensor

open CategoryTheory CategoryTheory.Limits

attribute [local instance] bimodule

universe v₁ v₂ u₁ u₂ w

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] {D : Type u₂} [Category.{v₂} D]
  [Preadditive D] (O : C) (O' : D) (M : Type w) [AddCommGroup M] [Module (End O)ᵐᵒᵖ M]
  {F G : C ⥤ D} [F.Additive] [G.Additive]

/-- The module map of a natural transformation depends only on its component at the
generating object; in particular it vanishes when that component does. -/
theorem natModuleHom_eq_zero_of_app (α : F ⟶ G) (h : α.app O = 0) :
    natModuleHom O O' M α = 0 := by
  ext1
  refine BalancedTensor.extB fun β m => ?_
  change BalancedTensor.tmul (β ≫ α.app O) m = 0
  rw [h, Limits.comp_zero, BalancedTensor.zero_tmul]

end Categorification.HomTensor

namespace Categorification.KLR.Diagram

open CategoryTheory CategoryTheory.Idempotents CategoryTheory.Limits Preadditive MulOpposite
  InductionAlong TwoRep

namespace MatEnd

universe v w

attribute [local instance] HomTensor.bimodule
attribute [local instance 2000] InductionAlong.instModuleInd InductionAlong.Res.instModule

variable {C₁ : Type*} [Category.{v} C₁] [Preadditive C₁] {C₂ : Type*} [Category.{v} C₂]
  [Preadditive C₂] {ι₁ ι₂ : Type w} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
  {X₁ : ι₁ → C₁} {X₂ : ι₂ → C₂} (F₂ : C₁ ⥤ C₂) [F₂.Additive] {e₂ : ι₁ → ι₂}
  (he₂ : Function.Injective e₂) (h₂ : ∀ j, F₂.obj (X₁ j) = X₂ (e₂ j))
  {E₂ : Karoubi (Mat_ C₂) ⥤ Karoubi (Mat_ C₁)} (adj₂ : mapKaroubi F₂.mapMat_ ⊣ E₂)
  [E₂.Additive]
  {G : Karoubi (Mat_ C₁) ⥤ Karoubi (Mat_ C₁)} [G.Additive]
  (σK : G ⟶ mapKaroubi F₂.mapMat_ ⋙ E₂)
  (hG : IsZero (G.obj ((toKaroubi _).obj (familySum X₁))))
  {d₂ : (MatEnd X₂)ᵐᵒᵖ} (hd₂ : Intertwines (mapEmbOp F₂ he₂ h₂) (mapEmbOp F₂ he₂ h₂) d₂)
  {α₂ : mapKaroubi F₂.mapMat_ ⟶ mapKaroubi F₂.mapMat_}
  (hα₂ : karoubiCorner F₂ he₂ h₂ (cornerMul hd₂ (unitGen (mapEmbOp F₂ he₂ h₂))) =
    karoubiGen F₂ he₂ h₂ ≫ α₂.app ((toKaroubi _).obj (familySum X₁)))
  (M : ModuleCat.{max w v} (MatEnd X₁)ᵐᵒᵖ) {n : ℕ}

/-- **Brundan (1.9) on all modules, when the crossing has zero source**: an explicit inverse of
`(σK, η₂ α₂^m E₂)` among functors of the completed additive envelope, where the source of `σK`
vanishes on the generating object, gives an explicit inverse of
`(0, m ↦ φ₂(1) d₂^m ⊗ m) : 0 ⊕ M^n ⟶ Res (Ind M)` on every module over the matrix ring of
`X₁`. -/
def resIndSumInvFromOfIsZero
    (S : SumInvFrom σK (fun m => adj₂.unit ≫ Functor.whiskerRight
      ((show End (mapKaroubi F₂.mapMat_) from α₂) ^ m) E₂) n) :
    SumInvFrom (X := ModuleCat.of _ (Res (mapEmbOp F₂ he₂ h₂) (Ind M (mapEmbOp F₂ he₂ h₂))))
      (Y := ModuleCat.of (MatEnd X₁)ᵐᵒᵖ PUnit.{max w v + 1}) (Z := M) 0
      (fun m => ModuleCat.ofHom (Res.map (natMap hd₂ ^ m : Module.End _ _) ∘ₗ
        unitMap (φ := mapEmbOp F₂ he₂ h₂) M)) n :=
  letI := HomTensor.transferModule (karoubiMatrixOp X₁) M
  let O := (toKaroubi _).obj (familySum X₁)
  let S' := HomTensor.sumInvFromModule O O M S
  let S'' : SumInvFrom (Y := ModuleCat.of (End O)ᵐᵒᵖ PUnit.{max w v + 1}) 0
      (fun m => HomTensor.natModuleHom O O M (adj₂.unit ≫ Functor.whiskerRight
        ((show End (mapKaroubi F₂.mapMat_) from α₂) ^ m) E₂)) n :=
    SumInvFrom.ofIsZero _ _ (ModuleCat.isZero_of_subsingleton _) S'.g'
      (by
        have h0 : S'.f' ≫ HomTensor.natModuleHom O O M σK = 0 := by
          change HomTensor.natModuleHom O O M S.f' ≫ HomTensor.natModuleHom O O M σK = 0
          rw [← HomTensor.natModuleHom_comp]
          refine HomTensor.natModuleHom_eq_zero_of_app O O M _ ?_
          rw [NatTrans.comp_app, hG.eq_of_tgt (S.f'.app O) 0, zero_comp]
        have ht := S'.total
        rw [h0, zero_add] at ht
        exact ht)
      S'.gg
  S''.transferAdd (resIndModuleEquiv F₂ he₂ h₂ M adj₂).toAddEquiv (AddEquiv.refl _)
    (HomTensor.unitModuleEquiv ℤ O M).symm.toAddEquiv
    (fun _ => (map_zero _).trans rfl)
    (fun m z => by
      exact resIndModuleEquiv_dottedCup F₂ he₂ h₂ hd₂ hα₂ adj₂ M m z)

end MatEnd

end Categorification.KLR.Diagram
