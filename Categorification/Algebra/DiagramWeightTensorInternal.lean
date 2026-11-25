/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.WeightCoendReindex
import Categorification.Algebra.DiagramWeightBimodule

/-!
# Internal translation of a graded diagram tensor

Webster, arXiv:1309.3796v2, §7.1, Definition 7.4, and §7.2, Proposition 7.11. Reindex both diagram weights by the same integer. The coefficient
retains its weight difference, so the dg coend on a translated source
identifies with the translated dg tensor. Internal translation preserves
K-projective representatives and descends to the derived tensor.
-/
noncomputable section
namespace Categorification
open DG CategoryTheory CategoryTheory.Limits CatModule
universe u w
variable (B : Type u) [Ring B] [DGAddCommGroup B] [InternalGrading B] [BigradedDGRing B] [DGRing B]
local notation "C" => WeightCategory B

/-- Translation of a diagram weight preserves K-projectivity. -/
theorem isKProjective_weightTranslation (k : ℤ) {P : CatModule.{w} C} (hP : IsKProjective P) :
    IsKProjective ((CatModule.precomp (WeightCategory.shiftFunctor B k)).obj P) := by
  let E := CatModule.HomotopyCategory.internalShiftEquiv.{w} B k
  let Q : CatModule.{w} C ⥤ CatModule.HomotopyCategory C := CatModule.HomotopyCategory.quotient C
  let A : ObjectProperty (CatModule.HomotopyCategory.{w} C) := CatModule.HomotopyCategory.subcategoryAcyclic C
  let K : ObjectProperty (CatModule.HomotopyCategory.{w} C) := CatModule.HomotopyCategory.subcategoryKProjective C
  have hk : K (Q.obj P) := (CatModule.HomotopyCategory.quotient_obj_mem_subcategoryKProjective_iff P).mpr hP
  have ac {Y : CatModule.HomotopyCategory.{w} C} (hY : A Y) : A (E.inverse.obj Y) := by
    obtain ⟨N,rfl⟩ := CatModule.HomotopyCategory.quotient_obj_surjective Y
    have hn := (CatModule.HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff N).mp hY
    exact A.prop_of_iso ((CatModule.HomotopyCategory.precompFactors (WeightCategory.shiftFunctor B (-k))).app N).symm
      ((CatModule.HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff _).mpr (hn.precomp _))
  apply (CatModule.HomotopyCategory.quotient_obj_mem_subcategoryKProjective_iff _).mp
  apply K.prop_of_iso ((CatModule.HomotopyCategory.precompFactors (WeightCategory.shiftFunctor B k)).app P)
  change K (E.functor.obj (Q.obj P))
  intro Y f hY
  have h₁ := hk (E.unitIso.hom.app _ ≫ E.inverse.map f) (ac hY)
  apply E.inverse.map_injective
  rw [Functor.map_zero]
  exact (cancel_epi (E.unitIso.hom.app _)).mp (h₁.trans (by rw [comp_zero]))
end Categorification


namespace Categorification
open CategoryTheory DG DGOpposite
open scoped DG.DegreeZero CatModule
universe u
variable {A B P : Type u} [Ring A] [Ring B] [InternalGrading A] [InternalGrading B]
  [BigradedDGRing A] [BigradedDGRing B] [AddCommGroup P] [Module A P] [Module Bᵐᵒᵖ P]
  [SMulCommClass A Bᵐᵒᵖ P]
  (G : ℤ → AddSubgroup P)
  (hl : ∀ {i j : ℤ} {a : A} {x : P}, a ∈ wgrading i → x ∈ G j → a • x ∈ G (i+j))
  (hr : ∀ {i j : ℤ} {b : B} {x : P}, b ∈ wgrading i → x ∈ G j → MulOpposite.op b • x ∈ G (j+i))
local notation "D" => diagramWeightBimodule G hl hr
local notation "C" => WeightCategory B
local notation "Acat" => WeightCategory A

private def translatedWeights (R : Type u) (k : ℤ) : WeightCategory R ≃ WeightCategory R where
  toFun X := ⟨X.as+k⟩
  invFun X := ⟨X.as-k⟩
  left_inv _ := WeightCategory.ext (add_sub_cancel_right _ _)
  right_inv _ := WeightCategory.ext (sub_add_cancel _ _)

variable (k : ℤ) (X : WeightCategory A) (L : CatModule.{u} (WeightCategory B))
local notation "E" => translatedWeights B k
local notation "W" => translatedWeights A k X
local notation "Q" => Functor.obj (CatModule.precomp (WeightCategory.shiftFunctor B k)) L
local notation "T" => Functor.obj (CatModule.precomp (WeightCategory.shiftFunctor A k)) (CatBimodule.tensorObj D L)

private def fiberTranslate (Y : C) :
    (D).obj X Y ≃+ (D).obj W ((E) Y) where
  toFun p := ⟨p.val, by simpa only [translatedWeights, Equiv.coe_fn_mk, add_sub_add_right_eq_sub] using p.property⟩
  invFun p := ⟨p.val, by simpa only [translatedWeights, Equiv.coe_fn_mk, add_sub_add_right_eq_sub] using p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

private def homTranslate (Y Z : C) : (Y ⟶ Z) ≃ ((E) Y ⟶ (E) Z) where
  toFun := (WeightCategory.shiftFunctor B k).map
  invFun f := ⟨f.val, by simpa only [translatedWeights,Equiv.coe_fn_mk,add_sub_add_right_eq_sub] using f.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

local notation "rE" => fiberTranslate G hl hr k X
private theorem rightTranslate {Y Z : C} (f : Y ⟶ Z) (p : (D).obj X Z) :
    (rE) Y (((D).right X).ract f p) =
      ((D).right W).ract (homTranslate k Y Z f) ((rE) Z p) := by
  rw [CatBimodule.right_ract,CatBimodule.right_ract]
  rfl

private abbrev sameFiber (Y : C) : (Q).obj Y ≃+ L.obj ((E) Y) := AddEquiv.refl _
private def shiftTensorWeight :
    DGAddEquiv (CatTensorProduct ((D).right X) Q) (CatTensorProduct ((D).right W) L) :=
  weightCoendReindexDGEquiv ((D).right X) Q ((D).right W) L E rE (sameFiber k L)
    (homTranslate k) (rightTranslate G hl hr k X) (fun _ _ => rfl)
    (fun Y {_} {_} hg => by
      rcases (InDegreeZero.mem_grading_iff (M := G (X.as-Y.as))).mp hg with hi | hz
      · exact (InDegreeZero.mem_grading_iff (M := G ((W).as-((E) Y).as))).mpr (Or.inl hi)
      · exact (InDegreeZero.mem_grading_iff (M := G ((W).as-((E) Y).as))).mpr (Or.inr ((congrArg ((rE) Y) hz).trans (map_zero _))))
    (fun _ {_} {_} hm => hm) (fun _ _ => rfl) (fun _ _ => rfl)

private theorem shiftTensorWeight_tmul (Y : C) (b : (D).obj X Y) (m : (Q).obj Y) :
    shiftTensorWeight G hl hr k X L (CatTensorProduct.tmul (N := (D).right X) (M := Q) Y b m) =
      CatTensorProduct.tmul (N := (D).right W) (M := L) ((E) Y) ((rE) Y b) (sameFiber k L Y m) :=
  weightCoendReindexAddEquiv_tmul ((D).right X) Q ((D).right W) L E rE (sameFiber k L)
    (homTranslate k) (rightTranslate G hl hr k X) (fun _ _ => rfl) Y b m

/-- Simultaneous translation of both diagram weights identifies tensoring
an internally shifted module with the internal shift of its tensor. -/
def diagramWeightTensorInternalIso :
    (D).tensorObj Q ≅ T := by
  let ρ (U : Acat) := shiftTensorWeight G hl hr k U L
  refine CatModule.isoMk (fun U => (ρ U).toAddEquiv) ?_ ?_ ?_
  · intro U i x
    exact ⟨fun h => (ρ U).symm_apply_apply x ▸ (ρ U).symm.map_mem h, (ρ U).map_mem⟩
  · intro U x
    exact (ρ U).map_d x
  · intro U V f x
    have h : (ρ V).toAddEquiv.toAddMonoidHom.comp ((D).tensorAct Q f) =
        ((D).tensorAct L ((WeightCategory.shiftFunctor A k).map f)).comp (ρ U).toAddEquiv.toAddMonoidHom := by
      apply CatTensorProduct.addHom_ext
      intro Y b m
      change shiftTensorWeight G hl hr k V L ((D).tensorAct Q f (CatTensorProduct.tmul Y b m)) =
        (D).tensorAct L ((WeightCategory.shiftFunctor A k).map f)
          (shiftTensorWeight G hl hr k U L (CatTensorProduct.tmul Y b m))
      let sf := (WeightCategory.shiftFunctor A k).map f
      refine (congrArg (shiftTensorWeight G hl hr k V L) (CatBimodule.tensorAct_tmul (B := D) Q f Y b m)).trans ?_
      refine (shiftTensorWeight_tmul G hl hr k V L Y ((D).lact f b) m).trans ?_
      refine Eq.trans ?_ ((congrArg ((D).tensorAct L sf) (shiftTensorWeight_tmul G hl hr k U L Y b m)).symm)
      exact (CatBimodule.tensorAct_tmul (B := D) L sf ((E) Y)
        (fiberTranslate G hl hr k U Y b) (sameFiber k L Y m)).symm
    exact DFunLike.congr_fun h x


universe v
variable [CatModule.HasDerivedCategory.{v,u} (WeightCategory A)]
  [CatModule.HasDerivedCategory.{v,u} (WeightCategory B)]
local notation "DF" => diagramWeightDerivedTensor G hl hr
local notation "input" => CatModule.DerivedCategory.internalShift B k
local notation "output" => CatModule.DerivedCategory.internalShift A k

/-- The derived tensor with a graded diagram coefficient commutes objectwise
with internal weight translation on its input. -/
def diagramWeightDerivedTensorInternalIso (Y : CatModule.DerivedCategory.{v,u} (WeightCategory B)) :
    (DF).obj ((input).obj Y) ≅ (output).obj ((DF).obj Y) := by
  let Q₁ : CatModule.{u} (WeightCategory A) ⥤ CatModule.DerivedCategory.{v,u} (WeightCategory A) := CatModule.DerivedCategory.Q
  let Q₂ : CatModule.{u} (WeightCategory B) ⥤ CatModule.DerivedCategory.{v,u} (WeightCategory B) := CatModule.DerivedCategory.Q
  let L := CatModule.DerivedCategory.kProjRep Y
  let e : Y ≅ Q₂.obj L := CatModule.DerivedCategory.kProjRepIso Y
  have hL : CatModule.IsKProjective L := CatModule.DerivedCategory.isKProjective_kProjRep Y
  have hT := isKProjective_weightTranslation B k hL
  exact (DF).mapIso ((input).mapIso e ≪≫
    (CatModule.DerivedCategory.QCompInternalShiftIso B k).app L) ≪≫
    diagramWeightDerivedTensorObjIso G hl hr hT ≪≫
    Q₁.mapIso (diagramWeightTensorInternalIso G hl hr k L) ≪≫
    ((CatModule.DerivedCategory.QCompInternalShiftIso A k).app ((D).tensorObj L)).symm ≪≫
    (output).mapIso ((diagramWeightDerivedTensorObjIso G hl hr hL).symm ≪≫ (DF).mapIso e.symm)

end Categorification
