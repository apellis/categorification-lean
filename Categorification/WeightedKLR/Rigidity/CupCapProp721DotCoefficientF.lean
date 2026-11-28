/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721DotCoefficient

/-!
# The dot on the derived `𝔉_i` is a coefficient map, and commutes with the shift

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21. The dot `dgBlackFDot` on the dg derived functor `𝔉_i = - ⊗ᴸ T^λ_{ν+i} e'` was
defined as the conjugate, along the comparison with Mathlib's derived categories, of the derived
dot `indDotOfEq` on induction. Here it is identified with the coefficient map of right
multiplication by the dot on the bimodule `T^λ_{ν+i} e'`
(`dgBlackFDot_eq_derivedTensorCoefficientMap`), using the naturality of the comparison in the
bimodule (`derivedTensorComparisonIso_coefficient_naturality`). Coefficient maps commute with the
homological shift, hence so does the dot (`dgBlackFDot_commShift`). This is the `𝔉_i` analogue
of `Stendhal.dgBlackDot_commShift`.

## Main results

* `InductionAlong.Corner.rightMul`: right multiplication on `B e` by an element intertwining `φ`
  with itself; `InductionAlong.indOrdIso_rightMul`: under `indOrdIso` it is the corresponding
  natural transformation of induction.
* `dgBlackFDot_eq_derivedTensorCoefficientMap`, `dgBlackFDot_commShift`.

Route hypotheses: `C`, `hRq : IsRouquierQ C Q` over a field (Webster's setting for
Theorem 4.31), under which `T^λ_{ν+i} e'` is projective over `T^λ_ν`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory MulOpposite DG.DegreeZero

namespace Categorification

namespace InductionAlong

universe u

variable {A B : Type u} [Ring A] [Ring B] {φ : A →ₙ+* B}

/-- **Right multiplication on `B e` by an element `x` intertwining `φ` with itself**, a map of
`(B, A)`-bimodules. -/
def Corner.rightMul {x : B} (hx : Intertwines φ φ x) : Corner φ →ₗ[B] Corner φ where
  toFun := cornerMul hx
  map_add' z z' := Subtype.ext (add_mul z.1 z'.1 x)
  map_smul' b z := Subtype.ext (mul_assoc b z.1 x)

theorem Corner.rightMul_op_smul {x : B} (hx : Intertwines φ φ x) (a : A) (z : Corner φ) :
    Corner.rightMul hx (op a • z) = op a • Corner.rightMul hx z :=
  Subtype.ext (by
    change z.1 * φ a * x = z.1 * x * φ a
    rw [mul_assoc, hx a, mul_assoc])

/-- **Under `indOrdIso`, right multiplication on `B e` is the natural transformation of
induction given by `x`**, for any natural transformation `α` acting on generators by
`z ⊗ n ↦ z x ⊗ n`. -/
theorem indOrdIso_rightMul {x : B} (hx : Intertwines φ φ x)
    (α : functor.{u, u} φ ⟶ functor.{u, u} φ)
    (hα : ∀ (N : ModuleCat.{u} A) (z : Corner φ) (n : N),
      (α.app N).hom (Ind.tmul z n) = Ind.tmul (cornerMul hx z) n) :
    ordTensorCoefficientMap (Corner.rightMul hx) (Corner.rightMul_op_smul hx) ≫
        (indOrdIso φ).hom = (indOrdIso φ).hom ≫ α := by
  ext N : 2
  refine ModuleCat.hom_ext (LinearMap.toAddMonoidHom_injective
    (DG.TensorProductOver.addHom_ext fun z n => ?_))
  change Ind.tmul (cornerMul hx (z : Corner φ)) (n : N) = (α.app N).hom (Ind.tmul _ _)
  rw [hα]

end InductionAlong

namespace Stendhal

open InductionAlong KLR

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (ν : Multiset I) (i : I)

/-- **The dot on the bimodule `T^λ_{ν+i} e'`** of `𝔉_i`: right multiplication by the dot on the
newest black strand. -/
def cornerDot : Corner (appendBlackOp Q Λ i ν) →ₗ[(TensorProductAlgebra k Q Λ
    ((Singleton.singleton i : Multiset I) + ν))ᵐᵒᵖ] Corner (appendBlackOp Q Λ i ν) :=
  Corner.rightMul (intertwines_of_commute (op_appendedDot_commute Q Λ i ν))

theorem cornerDot_op_smul (a : (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ)
    (z : Corner (appendBlackOp Q Λ i ν)) :
    cornerDot Q Λ ν i (op a • z) = op a • cornerDot Q Λ ν i z :=
  Corner.rightMul_op_smul _ a z

universe w w'

variable [DG.HasDerivedCategory.{w} (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ]
  [DG.HasDerivedCategory.{w}
    (TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν))ᵐᵒᵖ]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ)]
  [HasDerivedCategory.{w'}
    (ModuleCat.{0} (TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν))ᵐᵒᵖ)]
  (C : QuantumGroup.CartanDatum I) (hRq : IsRouquierQ C Q)

/-- **The dot on the dg derived `𝔉_i` is the coefficient map of the dot on `T^λ_{ν+i} e'`**
(Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21), for Rouquier polynomials over a
field. -/
theorem dgBlackFDot_eq_derivedTensorCoefficientMap :
    CupCap.dgBlackFDot.{w, w'} (Q := Q) (Λ := Λ) ν i C hRq =
      haveI := projective_blackCorner (Q := Q) (Λ := Λ) i ν C hRq
      derivedTensorCoefficientMap.{0, w} (cornerDot Q Λ ν i) (cornerDot_op_smul Q Λ ν i) := by
  have := projective_blackCorner (Q := Q) (Λ := Λ) i ν C hRq
  have := blackF_preservesFiniteLimits Q Λ i ν C hRq
  have := blackF_preservesFiniteColimits Q Λ i ν C hRq
  have : Limits.PreservesFiniteLimits
      (blackFOfEq Q Λ i (rfl : ({i} : Multiset I) + ν = _)) :=
    blackF_preservesFiniteLimits Q Λ i ν C hRq
  have : Limits.PreservesFiniteColimits
      (blackFOfEq Q Λ i (rfl : ({i} : Multiset I) + ν = _)) :=
    blackF_preservesFiniteColimits Q Λ i ν C hRq
  have := functor_preservesFiniteLimits (appendBlackOp Q Λ i ν)
  have := functor_preservesFiniteColimits (appendBlackOp Q Λ i ν)
  have hind := indOrdIso_rightMul (intertwines_of_commute (op_appendedDot_commute Q Λ i ν))
    (indDotOfEq Q Λ i (rfl : ({i} : Multiset I) + ν = _) : blackF Q Λ i ν ⟶ blackF Q Λ i ν)
    fun X z x => CupCap.indDotOfEq_rfl_tmul X z x
  have hder := congrArg NatTrans.mapDerivedCategory hind
  rw [NatTrans.mapDerivedCategory_comp, NatTrans.mapDerivedCategory_comp] at hder
  have hnat := derivedTensorComparisonIso_coefficient_naturality.{w, w'} (cornerDot Q Λ ν i)
    (cornerDot_op_smul Q Λ ν i)
  ext x
  apply (derivedComparison.{w, w'}
    (TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν))ᵐᵒᵖ).map_injective
  let y := (derivedComparison.{w, w'} (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ).obj x
  let R := mapDerivedCategoryIsoOfIso.{w', w'} (indOrdIso (appendBlackOp Q Λ i ν))
  let D := derivedTensorComparisonIso.{w, w'}
    (TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν))ᵐᵒᵖ
    (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ (Corner (appendBlackOp Q Λ i ν))
  have h₁ := congr_app hnat x
  have h₂ := congr_app hder y
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h₁ h₂
  have h₁' : (derivedComparison.{w, w'}
      (TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν))ᵐᵒᵖ).map
      ((derivedTensorCoefficientMap.{0, w} (cornerDot Q Λ ν i)
        (cornerDot_op_smul Q Λ ν i)).app x) =
      D.hom.app x ≫ (NatTrans.mapDerivedCategory (ordTensorCoefficientMap (cornerDot Q Λ ν i)
        (cornerDot_op_smul Q Λ ν i))).app y ≫ D.inv.app x := by
    rw [← reassoc_of% h₁]; simp [D]
  have h₂' : R.hom.app y ≫ (NatTrans.mapDerivedCategory
      (indDotOfEq Q Λ i (rfl : ({i} : Multiset I) + ν = _) :
        blackF Q Λ i ν ⟶ blackF Q Λ i ν)).app y ≫ R.inv.app y =
      (NatTrans.mapDerivedCategory (ordTensorCoefficientMap (cornerDot Q Λ ν i)
        (cornerDot_op_smul Q Λ ν i))).app y := by
    rw [← cancel_mono (R.hom.app y)]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    simp only [R, CupCap.mapDerivedCategoryIsoOfIso_hom_eq]
    erw [Category.comp_id]
    exact h₂.symm
  refine (CupCap.isComparisonConj_comparisonConj _ _ _ _ x).trans ?_
  rw [h₁', ← h₂']
  simp [derivedBlackFComparisonIso, D, R]
  rfl

/-- **The dot on the dg derived `𝔉_i` commutes with the homological shift** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.21): it is a coefficient map. The shift
compatibility of `𝔉_i` is that of a derived tensor functor (`CupCap.derivedBlackF_commShift`). -/
instance dgBlackFDot_commShift :
    NatTrans.CommShift (CupCap.dgBlackFDot.{w, w'} (Q := Q) (Λ := Λ) ν i C hRq) ℤ := by
  have := projective_blackCorner (Q := Q) (Λ := Λ) i ν C hRq
  rw [dgBlackFDot_eq_derivedTensorCoefficientMap]
  exact derivedTensorCoefficientMap_commShift _ _

end Stendhal

end Categorification
