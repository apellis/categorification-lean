/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapTraceE
import Categorification.Algebra.DerivedTensorComparisonNatural
import Categorification.Algebra.MapDerivedNatTrans

/-!
# The dot on the derived `𝔈_i` is a coefficient map, and commutes with the shift

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21. The dot `dgBlackDot` on the dg derived functor `𝔈_i = - ⊗ᴸ e' T^λ_{ν+i}` was
defined as the conjugate, along the comparison with Mathlib's derived categories, of the derived
dot `derivedBlackDot`. Here it is identified with the coefficient map of left multiplication by
the dot on the bimodule `e' T^λ_{ν+i}` (`dgBlackDot_eq_derivedTensorCoefficientMap`), using the
naturality of the comparison in the bimodule (`derivedTensorComparisonIso_coefficient_naturality`).
Coefficient maps commute with the homological shift, hence so does the dot
(`dgBlackDot_commShift`). This discharges the second of the two inputs of
`CupCap.dgBlackFDotMate_commShift`.

## Main results

* `InductionAlong.RCorner.leftMul`: left multiplication on `e B` by an element commuting with
  the image of `φ`; `InductionAlong.resOrdIso_leftMul`: under `resOrdIso` it is the action on
  restricted modules.
* `dgBlackDot_eq_derivedTensorCoefficientMap`, `dgBlackDot_commShift`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory MulOpposite DG.DegreeZero

namespace Categorification

namespace InductionAlong

universe u

variable {A B : Type u} [Ring A] [Ring B] {φ : A →ₙ+* B}

/-- **Left multiplication on `e B` by an element `c` commuting with the image of `φ`**, a map
of `(A, B)`-bimodules. -/
def RCorner.leftMul (c : B) (hc : ∀ a, c * φ a = φ a * c) : RCorner φ →ₗ[A] RCorner φ where
  toFun z := ⟨c * z.1, by
    rw [mem_rIdeal, ← mul_assoc, ← hc 1, mul_assoc, (mem_rIdeal.mp z.2)]⟩
  map_add' z z' := Subtype.ext (mul_add c z.1 z'.1)
  map_smul' a z := Subtype.ext (by
    change c * (φ a * z.1) = φ a * (c * z.1)
    rw [← mul_assoc, hc, mul_assoc])

theorem RCorner.leftMul_op_smul (c : B) (hc : ∀ a, c * φ a = φ a * c) (b : B) (z : RCorner φ) :
    RCorner.leftMul c hc (op b • z) = op b • RCorner.leftMul c hc z :=
  Subtype.ext (mul_assoc c z.1 b).symm

/-- **Under `resOrdIso`, left multiplication on `e B` is the action of `c` on restricted
modules.** -/
theorem resOrdIso_leftMul (c : B) (hc : ∀ a, c * φ a = φ a * c)
    (α : resFunctor.{u, u} φ ⟶ resFunctor.{u, u} φ)
    (hα : ∀ (M : ModuleCat.{u} B) (r : Res φ M), ((α.app M).hom r).val = c • r.val) :
    ordTensorCoefficientMap (RCorner.leftMul c hc) (RCorner.leftMul_op_smul c hc) ≫
        (resOrdIso φ).hom = (resOrdIso φ).hom ≫ α := by
  ext M : 2
  refine ModuleCat.hom_ext (LinearMap.toAddMonoidHom_injective
    (DG.TensorProductOver.addHom_ext fun z m => Res.ext ?_))
  change (c * (z : RCorner φ).1) • (m : M) = ((α.app M).hom _).val
  rw [hα, mul_smul]
  rfl

end InductionAlong

namespace Stendhal

open InductionAlong KLR

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (ν : Multiset I) (i : I)

/-- **The dot on the bimodule `e' T^λ_{ν+i}`** of `𝔈_i`: left multiplication by the dot on the
newest black strand. -/
def rCornerDot : RCorner (appendBlackOp Q Λ i ν) →ₗ[(TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ]
    RCorner (appendBlackOp Q Λ i ν) :=
  RCorner.leftMul (op (appendedDot Q Λ i ν)) (op_appendedDot_commute Q Λ i ν)

theorem rCornerDot_op_smul
    (b : (TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν))ᵐᵒᵖ)
    (z : RCorner (appendBlackOp Q Λ i ν)) :
    rCornerDot Q Λ ν i (op b • z) = op b • rCornerDot Q Λ ν i z :=
  RCorner.leftMul_op_smul _ _ b z

universe w w'

variable [DG.HasDerivedCategory.{w} (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ]
  [DG.HasDerivedCategory.{w}
    (TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν))ᵐᵒᵖ]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ)]
  [HasDerivedCategory.{w'}
    (ModuleCat.{0} (TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν))ᵐᵒᵖ)]

/-- **The dot on the dg derived `𝔈_i` is the coefficient map of the dot on `e' T^λ_{ν+i}`**
(Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21). -/
theorem dgBlackDot_eq_derivedTensorCoefficientMap :
    CupCap.dgBlackDot.{w, w'} (Q := Q) (Λ := Λ) ν i =
      derivedTensorCoefficientMap.{0, w} (rCornerDot Q Λ ν i) (rCornerDot_op_smul Q Λ ν i) := by
  have hres := resOrdIso_leftMul (op (appendedDot Q Λ i ν)) (op_appendedDot_commute Q Λ i ν)
    (blackDot Q Λ i ν) fun _ _ => rfl
  have hder := congrArg NatTrans.mapDerivedCategory hres
  rw [NatTrans.mapDerivedCategory_comp, NatTrans.mapDerivedCategory_comp] at hder
  have hnat := derivedTensorComparisonIso_coefficient_naturality.{w, w'} (rCornerDot Q Λ ν i)
    (rCornerDot_op_smul Q Λ ν i)
  ext x
  apply (derivedComparison.{w, w'} (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ).map_injective
  let y := (derivedComparison.{w, w'}
    (TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν))ᵐᵒᵖ).obj x
  let R := mapDerivedCategoryIsoOfIso.{w', w'} (resOrdIso (appendBlackOp Q Λ i ν))
  let D := derivedTensorComparisonIso.{w, w'} (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ
    (TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν))ᵐᵒᵖ
    (RCorner (appendBlackOp Q Λ i ν))
  have h₁ := congr_app hnat x
  have h₂ := congr_app hder y
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h₁ h₂
  have h₁' : (derivedComparison.{w, w'} (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ).map
      ((derivedTensorCoefficientMap.{0, w} (rCornerDot Q Λ ν i)
        (rCornerDot_op_smul Q Λ ν i)).app x) =
      D.hom.app x ≫ (NatTrans.mapDerivedCategory (ordTensorCoefficientMap (rCornerDot Q Λ ν i)
        (rCornerDot_op_smul Q Λ ν i))).app y ≫ D.inv.app x := by
    rw [← reassoc_of% h₁]; simp [D]
  have h₂' : R.hom.app y ≫ (derivedBlackDot Q Λ i ν).app y ≫ R.inv.app y =
      (NatTrans.mapDerivedCategory (ordTensorCoefficientMap (rCornerDot Q Λ ν i)
        (rCornerDot_op_smul Q Λ ν i))).app y := by
    rw [← cancel_mono (R.hom.app y)]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    simp only [R, CupCap.mapDerivedCategoryIsoOfIso_hom_eq]
    erw [Category.comp_id]
    exact h₂.symm
  refine (CupCap.isComparisonConj_comparisonConj _ _ _ _ x).trans ?_
  rw [h₁', ← h₂']
  simp [derivedBlackEComparisonIso, D, R]
  rfl

/-- **The dot on the dg derived `𝔈_i` commutes with the homological shift** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.21): it is a coefficient map. -/
instance dgBlackDot_commShift :
    NatTrans.CommShift (CupCap.dgBlackDot.{w, w'} (Q := Q) (Λ := Λ) ν i) ℤ := by
  rw [dgBlackDot_eq_derivedTensorCoefficientMap]
  exact derivedTensorCoefficientMap_commShift _ _

end Stendhal

end Categorification
