/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.FundamentalBraidRedSwap
import Categorification.Algebra.WeightCoendRelabel

/-!
# Relabelling the two fundamental crossing bimodules

The calculation of the double positive braid in Webster, arXiv:1309.3796v2,
§7.2 before Definition 7.12 uses the same transposition on the two
diagonal corners and on the rectangular crossing coefficient.
-/
noncomputable section
namespace Categorification.Stendhal.FundamentalCorner
open KLR KLRAlgebra BraidedStendhalAlgebra CategoryTheory DG CatModule Coevaluation
open scoped DG.DegreeZero
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance] fundamentalBraidCoendSourceCornerGrades fundamentalBraidCoendTargetCornerGrades
  fundamentalBraidCoendSourceInternal fundamentalBraidCoendTargetInternal
  fundamentalBraidCoendSourceBigraded fundamentalBraidCoendTargetBigraded
  fundamentalBraidSourceOrderedInternal fundamentalBraidSourceOrderedBigraded
  fundamentalTargetScalarInternal fundamentalTargetScalarBigraded
local notation "ν" => ({()} : Multiset Unit)
local notation "σ" => Equiv.swap (0 : Fin 2) 1
local notation "K" => ViolOrderCorner (k := ℚ) (Q := Q) (Λ := wt) («ν» := ν) (List.finRange 2)
local notation "U" => ViolOrderCorner (k := ℚ) (Q := Q) (Λ := wt) («ν» := ν) [1,0]
local notation "V" => ViolQuotient ℚ Q wt ν
local notation "G" => violAuxiliaryGrade («ν» := ν) grading
local notation "π" => violMk ℚ Q wt ν
local notation "p" κ:arg => π (redProj ℚ Q wt ν κ)
local notation "κ₀" => List.finRange 2
local notation "κ₁" => ([1,0] : List (Fin 2))
local notation "h" κ:arg => isIdempotentElem_violMk_redProj ℚ Q wt ν κ

local notation "S" => fundamentalBraidRedSwap
local notation "hs" => fundamentalBraidRedSwap_source
local notation "ht" => fundamentalBraidRedSwap_target
local notation "hG" κ:arg => redProj_mem_violAuxiliaryGrade grading κ
local notation "Bs" => diagramCornerWeightRightBimodule G (h κ₀) (h κ₁) (hG κ₀) (hG κ₁)
local notation "Bt" => diagramCornerWeightRightBimodule G (h κ₁) (h κ₀) (hG κ₁) (hG κ₀)

private theorem sourceWeightSwap {j : ℤ} (x : Kᵐᵒᵖ) :
    (fundamentalBraidSourceSwap x.unop).val ∈ G j ↔ x.unop.val ∈ G j :=
  fundamentalBraidRedSwap_weight x.unop.val
private theorem targetWeightSwap {j : ℤ} (x : Uᵐᵒᵖ) :
    (fundamentalBraidTargetSwap x.unop).val ∈ G j ↔ x.unop.val ∈ G j :=
  fundamentalBraidRedSwap_weight x.unop.val

/-- The red transposition on the weights of the ordered diagram corner. -/
abbrev fundamentalBraidSourceSwapFunctor :=
  weightFunctorOfRingEquiv fundamentalBraidSourceSwap.op sourceWeightSwap
/-- The red transposition on the weights of the reversed diagram corner. -/
abbrev fundamentalBraidTargetSwapFunctor :=
  weightFunctorOfRingEquiv fundamentalBraidTargetSwap.op targetWeightSwap

instance fundamentalBraidSourceSwap_additive : fundamentalBraidSourceSwapFunctor.Additive :=
  weightFunctorOfRingEquiv_additive fundamentalBraidSourceSwap.op sourceWeightSwap

instance fundamentalBraidSourceSwap_isDGFunctor : fundamentalBraidSourceSwapFunctor.IsDGFunctor :=
  weightFunctorOfRingEquiv_isDGFunctor fundamentalBraidSourceSwap.op sourceWeightSwap

instance fundamentalBraidTargetSwap_additive : fundamentalBraidTargetSwapFunctor.Additive :=
  weightFunctorOfRingEquiv_additive fundamentalBraidTargetSwap.op targetWeightSwap

instance fundamentalBraidTargetSwap_isDGFunctor : fundamentalBraidTargetSwapFunctor.IsDGFunctor :=
  weightFunctorOfRingEquiv_isDGFunctor fundamentalBraidTargetSwap.op targetWeightSwap

local notation "FA" => fundamentalBraidSourceSwapFunctor
local notation "FB" => fundamentalBraidTargetSwapFunctor

private def swapRectangular {e e' f f' : V} (hswap : S e = f) (hswap' : S e' = f')
    (x : cornerBimodule e e') : cornerBimodule f f' :=
  ⟨S x.val, (congrArg₂ (· * ·) hswap.symm (rfl : S x.val = S x.val)).trans
    ((map_mul S e x.val).symm.trans (congrArg S x.property.1)),
    (congrArg₂ (· * ·) (rfl : S x.val = S x.val) hswap'.symm).trans
    ((map_mul S x.val e').symm.trans (congrArg S x.property.2))⟩

private def swapFiber (X : WeightCategory Kᵐᵒᵖ) (Y : WeightCategory Uᵐᵒᵖ) :
    DGAddEquiv ((Bt).obj X Y) ((Bs).obj ((FA).obj X) ((FB).obj Y)) where
  toFun z := ⟨swapRectangular ht hs z.val, (fundamentalBraidRedSwap_weight z.val.val).mpr z.property⟩
  invFun z := ⟨swapRectangular hs ht z.val, (fundamentalBraidRedSwap_weight z.val.val).mpr z.property⟩
  left_inv z := Subtype.ext (Subtype.ext (fundamentalBraidRedSwap_twice z.val.val))
  right_inv z := Subtype.ext (Subtype.ext (fundamentalBraidRedSwap_twice z.val.val))
  map_add' u v := Subtype.ext (Subtype.ext (map_add S u.val.val v.val.val))
  map_mem' {i z} hz := by
    rcases (InDegreeZero.mem_grading_iff (M := diagramCornerWeight (e := p κ₁) (e' := p κ₀) G (X.as-Y.as))).mp hz with hi | hz
    · exact (InDegreeZero.mem_grading_iff (M := diagramCornerWeight (e := p κ₀) (e' := p κ₁) G (X.as-Y.as))).mpr (Or.inl hi)
    · subst z
      exact (InDegreeZero.mem_grading_iff (M := diagramCornerWeight (e := p κ₀) (e' := p κ₁) G (X.as-Y.as))).mpr (Or.inr (Subtype.ext (Subtype.ext (map_zero S))))
  map_d' z := Subtype.ext (Subtype.ext (map_zero S))

private theorem swapRight {X : WeightCategory Kᵐᵒᵖ} {Y Z : WeightCategory Uᵐᵒᵖ}
    (f : Y ⟶ Z) (z : (Bt).obj X Z) :
    swapFiber X Y ((Bt).ract f z) = (Bs).ract ((FB).map f) (swapFiber X Z z) :=
  Subtype.ext (Subtype.ext (map_mul S f.val.unop.val z.val.val))

private theorem swapLeft {X X' : WeightCategory Kᵐᵒᵖ} {Y : WeightCategory Uᵐᵒᵖ}
    (f : X ⟶ X') (z : (Bt).obj X Y) :
    swapFiber X' Y ((Bt).lact f z) = (Bs).lact ((FA).map f) (swapFiber X Y z) :=
  Subtype.ext (Subtype.ext (map_mul S z.val.val f.val.unop.val))

/-- Exchanging both red labels identifies the dg tensor with the positive
crossing in the reverse red order and the restriction of the forward tensor. -/
def fundamentalBraidSwapTensorIso (M : CatModule.{0} (WeightCategory Kᵐᵒᵖ)) :
    (Bt).tensorObj ((CatModule.precomp FB).obj M) ≅ (CatModule.precomp FA).obj ((Bs).tensorObj M) :=
  weightCoendRelabelIso fundamentalBraidSourceSwap.op fundamentalBraidTargetSwap.op
    sourceWeightSwap targetWeightSwap Bt Bs swapFiber swapRight swapLeft M

universe v
variable [CatModule.HasDerivedCategory.{v,0} (WeightCategory Kᵐᵒᵖ)]
  [CatModule.HasDerivedCategory.{v,0} (WeightCategory Uᵐᵒᵖ)]
local notation "F₁" => diagramCornerWeightDerivedRightTensor G (h κ₀) (h κ₁) (hG κ₀) (hG κ₁)
local notation "F₂" => diagramCornerWeightDerivedRightTensor G (h κ₁) (h κ₀) (hG κ₁) (hG κ₀)
local notation "inF" => CatModule.DerivedCategory.restrict FB
local notation "outF" => CatModule.DerivedCategory.restrict FA

/-- Derived right tensor by the positive fundamental crossing commutes
objectwise with simultaneous transposition of the red labels. -/
def fundamentalBraidSwapDerivedIso (X : CatModule.DerivedCategory.{v,0} (WeightCategory Kᵐᵒᵖ)) :
    (F₂).obj ((inF).obj X) ≅ (outF).obj ((F₁).obj X) := by
  let Q₀ : CatModule.{0} (WeightCategory Kᵐᵒᵖ) ⥤ CatModule.DerivedCategory.{v,0} _ := CatModule.DerivedCategory.Q
  let M := CatModule.DerivedCategory.kProjRep X
  let e : X ≅ Q₀.obj M := CatModule.DerivedCategory.kProjRepIso X
  have hM : CatModule.IsKProjective M := CatModule.DerivedCategory.isKProjective_kProjRep X
  have hM' := isKProjective_precomp_weightRingEquiv fundamentalBraidTargetSwap.op targetWeightSwap hM
  exact (F₂).mapIso ((inF).mapIso e ≪≫ (CatModule.DerivedCategory.QCompRestrictIso FB).app M) ≪≫
    diagramWeightDerivedTensorObjIso _ _ _ hM' ≪≫ Q₀.mapIso (fundamentalBraidSwapTensorIso M) ≪≫
    ((CatModule.DerivedCategory.QCompRestrictIso FA).app ((Bs).tensorObj M)).symm ≪≫
    (outF).mapIso ((diagramWeightDerivedTensorObjIso _ _ _ hM).symm ≪≫ (F₁).mapIso e.symm)

end Categorification.Stendhal.FundamentalCorner
