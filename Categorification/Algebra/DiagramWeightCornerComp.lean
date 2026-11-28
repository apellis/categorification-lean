/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DiagramWeightCorner
import Categorification.Algebra.DiagramWeightCompForget
import Categorification.Algebra.CornerTensorDerived

set_option backward.isDefEq.respectTransparency false

/-!
# Composites of graded derived right tensors with rectangular corners

For degree-zero idempotents `e₂, e₁, e₀` of a graded algebra, the graded derived right tensors
with the rectangular corners compose, `(- ⊗ᴸ e₂Ae₁) ⊗ᴸ e₁Ae₀ ≅ - ⊗ᴸ e₂Ae₀`, when the
multiplication `e₂Ae₁ ⊗ e₁Ae₀ ⟶ e₂Ae₀` is bijective in each pair of weights and the ungraded
`Tor^{e₁Ae₁}_{>0}(e₂Ae₁, e₁Ae₀)` vanish, the hypothesis of the ungraded
`derivedRightTensorCornerCompIso`. This is the graded form of the mechanism of
Webster, arXiv:1309.3796v3, Lemma 6.12 (second clause).
-/

noncomputable section

namespace Categorification

open CategoryTheory DG DirectSum MulOpposite Categorification.Graded
open scoped DG.DegreeZero

universe u

variable {k : Type*} {A : Type u} [Field k] [Ring A] [Algebra k A]
  (G : ℤ → Submodule k A) [GradedAlgebra G]
  {e₂ e₁ e₀ : A} (h₂ : IsIdempotentElem e₂) (h₁ : IsIdempotentElem e₁) (h₀ : IsIdempotentElem e₀)
  (he₂ : e₂ ∈ G 0) (he₁ : e₁ ∈ G 0) (he₀ : e₀ ∈ G 0)

local notation "OW" h:arg => Graded.oppositeGrade (Graded.cornerGrading G h)
local notation "D₁" => diagramCornerWeightRightBimodule G h₁ h₀ he₁ he₀
local notation "D₂" => diagramCornerWeightRightBimodule G h₂ h₁ he₂ he₁
local notation "G₁" => diagramCornerWeight (e := e₁) (e' := e₀) G
local notation "G₂" => diagramCornerWeight (e := e₂) (e' := e₁) G
local notation "G₃" => diagramCornerWeight (e := e₂) (e' := e₀) G

attribute [local instance] cornerBimodule.instModuleLeft cornerBimodule.instModuleRight
attribute [local instance 1200] Ring.toIntAlgebra

/-- **Composites of graded derived right tensors with rectangular corners**: when the weight
coend products `e₂Ae₁ ⊗ e₁Ae₀ ⟶ e₂Ae₀` are bijective and `Tor^{e₁Ae₁}_{>0}(e₂Ae₁, e₁Ae₀) = 0`
(ungraded), `(- ⊗ᴸ e₂Ae₁) ⊗ᴸ e₁Ae₀ ≅ - ⊗ᴸ e₂Ae₀` in the internal grading. -/
def diagramCornerWeightDerivedRightTensorCompIso :
    letI := Graded.cornerGradedAlgebra G h₂ he₂
    letI := Graded.cornerGradedAlgebra G h₁ he₁
    letI := Graded.cornerGradedAlgebra G h₀ he₀
    letI := gradedAlgebraInternalGrading (OW h₂)
    letI := gradedAlgebraInternalGrading (OW h₁)
    letI := gradedAlgebraInternalGrading (OW h₀)
    letI := gradedAlgebraBigradedDGRing (OW h₂)
    letI := gradedAlgebraBigradedDGRing (OW h₁)
    letI := gradedAlgebraBigradedDGRing (OW h₀)
    [CatModule.HasDerivedCategory.{u,u} (WeightCategory h₂.Cornerᵐᵒᵖ)] →
    [CatModule.HasDerivedCategory.{u,u} (WeightCategory h₁.Cornerᵐᵒᵖ)] →
    [CatModule.HasDerivedCategory.{u,u} (WeightCategory h₀.Cornerᵐᵒᵖ)] →
    [DG.HasDerivedCategory.{u,u} h₂.Cornerᵐᵒᵖ] →
    [DG.HasDerivedCategory.{u,u} h₁.Cornerᵐᵒᵖ] →
    [DG.HasDerivedCategory.{u,u} h₀.Cornerᵐᵒᵖ] →
    IsInternal G₁ → IsInternal G₂ → IsInternal G₃ →
    (∀ (X : WeightCategory h₀.Cornerᵐᵒᵖ) (Z : WeightCategory h₂.Cornerᵐᵒᵖ),
      Function.Bijective (diagramCornerWeightRightCoendProduct G h₂ h₁ he₂ he₁ h₀ he₀ X Z)) →
    (∀ n : ℤ, n ≠ 0 → Limits.IsZero ((DG.DerivedCategory.homologyFunctor (A := h₀.Cornerᵐᵒᵖ) ℤ n).obj
      ((derivedRightTensor.{u} h₁.Corner h₀.Corner (cornerBimodule e₁ e₀)).obj
        (DG.DerivedCategory.Q.obj (DGModuleCat.of h₁.Cornerᵐᵒᵖ (cornerOpDZ h₂ e₁)))))) →
    (diagramCornerWeightDerivedRightTensor.{u, u} G h₂ h₁ he₂ he₁ ⋙
        diagramCornerWeightDerivedRightTensor.{u, u} G h₁ h₀ he₁ he₀ ≅
      diagramCornerWeightDerivedRightTensor.{u, u} G h₂ h₀ he₂ he₀) := by
  letI := Graded.cornerGradedAlgebra G h₂ he₂
  letI := Graded.cornerGradedAlgebra G h₁ he₁
  letI := Graded.cornerGradedAlgebra G h₀ he₀
  letI := gradedAlgebraInternalGrading (OW h₂)
  letI := gradedAlgebraInternalGrading (OW h₁)
  letI := gradedAlgebraInternalGrading (OW h₀)
  letI := gradedAlgebraBigradedDGRing (OW h₂)
  letI := gradedAlgebraBigradedDGRing (OW h₁)
  letI := gradedAlgebraBigradedDGRing (OW h₀)
  intro _ _ _ _ _ _ d₁ d₂ d₃ hbij hv
  let := d₁.chooseDecomposition
  let := d₂.chooseDecomposition
  let := d₃.chooseDecomposition
  exact diagramWeightDerivedTensorCompIso
    (A := h₀.Cornerᵐᵒᵖ) (B := h₁.Cornerᵐᵒᵖ) (C := h₂.Cornerᵐᵒᵖ) G₁ G₂ G₃
    (hgL := diagramCornerWeight_smul_mem G (e := e₁) h₀)
    (hgR := diagramCornerWeight_op_smul_mem G (e' := e₀) h₁)
    (hhL := diagramCornerWeight_smul_mem G (e := e₂) h₁)
    (hhR := diagramCornerWeight_op_smul_mem G (e' := e₁) h₂)
    (hPL := diagramCornerWeight_smul_mem G (e := e₂) h₀)
    (hPR := diagramCornerWeight_op_smul_mem G (e' := e₀) h₂)
    (β := cornerRightProduct) (hw := cornerRightProduct_mem G)
    (hb := fun b x y => Subtype.ext (by
      change y.val * (op b • x : cornerBimodule e₁ e₀).val =
        (b • y : cornerBimodule e₂ e₁).val * x.val
      rw [cornerBimodule.coe_smul_right h₁]
      exact (mul_assoc _ _ _).symm))
    (hβL := fun a x y => Subtype.ext (by
      change y.val * (a • x : cornerBimodule e₁ e₀).val =
        (a • cornerRightProduct x y : cornerBimodule e₂ e₀).val
      rw [cornerBimodule.coe_smul_right h₀, cornerBimodule.coe_smul_right h₀]
      exact (mul_assoc _ _ _).symm))
    (hβR := fun c x y => Subtype.ext (by
      change (op c • y : cornerBimodule e₂ e₁).val * x.val =
        (op c • cornerRightProduct x y : cornerBimodule e₂ e₀).val
      have h1 : (op c • y : cornerBimodule e₂ e₁).val = c.unop.val * y.val :=
        cornerBimodule.coe_smul_left h₂ c.unop y
      have h2 : (op c • cornerRightProduct x y : cornerBimodule e₂ e₀).val =
          c.unop.val * (cornerRightProduct x y).val :=
        cornerBimodule.coe_smul_left h₂ c.unop _
      rw [h1, h2]
      exact mul_assoc _ _ _))
    hbij (fun Z => isIso_diagramWeightTensor_map_counit_of_torVanishing G₁ G₂
      (diagramCornerWeight_smul_mem G (e := e₁) h₀) (diagramCornerWeight_op_smul_mem G (e' := e₀) h₁)
      (diagramCornerWeight_smul_mem G (e := e₂) h₁) (diagramCornerWeight_op_smul_mem G (e' := e₁) h₂)
      Z hv)

end Categorification
