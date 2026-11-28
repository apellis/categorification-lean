/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.SingleRedBlackInductionIdeal
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapFDot

set_option backward.isDefEq.respectTransparency false

/-!
# Black induction of right multiplications between the projectives `e(𝐢) T^λ`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §4.6, one
red strand. Under `SingleRed.blackFOfEqRedFirstIdealIso` (`F_i (e(𝐢) T^λ_μ) ≅ e(𝐢 i) T^λ_β`),
`F_i` sends the right multiplication by `c` (a map `e(𝐢) T → e(𝐢') T` of right modules) to the
right multiplication by the image of `c` under the black-strand map
(`SingleRed.blackFOfEq_map_idemRightMul`), and the dot `indDotOfEq` on the new strand acts on
`e(𝐢 i) T^λ_β` as the right multiplication by that dot (`SingleRed.indDotOfEq_app_redFirstIdeal`).
-/

noncomputable section

namespace Categorification.Stendhal.SingleRed

open CategoryTheory MulOpposite KLR KLRAlgebra KLRAlgebra.AbsentColour InductionAlong
  QuantumGroup

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] (Q : I → I → MvPolynomial (Fin 2) k)
  (Λ : Fin 1 → I →₀ ℕ)

/-- **`F_i` of a right multiplication** between the projectives `e(𝐢) T^λ_μ` is the right
multiplication by the image under the black-strand map (Webster, arXiv:1309.3796v3, §4.6). -/
theorem blackFOfEq_map_idemRightMul (i : I) {μ β : Multiset I} (h : ({i} : Multiset I) + μ = β)
    (s s' : Seq μ) (c : (TensorProductAlgebra k Q Λ μ)ᵐᵒᵖ) :
    (blackFOfEq Q Λ i h).map (ModuleCat.ofHom (idemRightMul (redFirstIdem Q Λ μ s)
        (redFirstIdem Q Λ μ s') c (redFirstIdem_isIdempotentElem Q Λ μ s'))) ≫
        (blackFOfEqRedFirstIdealIso Q Λ i h s').hom =
      (blackFOfEqRedFirstIdealIso Q Λ i h s).hom ≫
        ModuleCat.ofHom (idemRightMul (redFirstIdem Q Λ β (appendSeq i h s))
          (redFirstIdem Q Λ β (appendSeq i h s')) (appendBlackOpOfEq Q Λ i h c)
          (redFirstIdem_isIdempotentElem Q Λ β _)) := by
  ext1
  refine Ind.ext fun z a => Subtype.ext ?_
  change z.1 * appendBlackOpOfEq Q Λ i h (a.1 * c * redFirstIdem Q Λ μ s') =
    z.1 * appendBlackOpOfEq Q Λ i h a.1 * appendBlackOpOfEq Q Λ i h c *
      redFirstIdem Q Λ β (appendSeq i h s')
  rw [map_mul, map_mul, appendBlackOpOfEq_redFirstIdem]
  simp only [mul_assoc]

/-- **The dot on the new strand of `F_i (e(𝐢) T^λ_μ)`** is, under
`blackFOfEqRedFirstIdealIso`, the right multiplication of `e(𝐢 i) T^λ_β` by the dot on the
appended strand (Webster, arXiv:1309.3796v3, §4.6). -/
theorem indDotOfEq_app_redFirstIdeal (i : I) {μ β : Multiset I}
    (h : ({i} : Multiset I) + μ = β) (s : Seq μ) :
    (indDotOfEq Q Λ i h).app
        (ModuleCat.of (TensorProductAlgebra k Q Λ μ)ᵐᵒᵖ (idemLeftIdeal (redFirstIdem Q Λ μ s))) ≫
        (blackFOfEqRedFirstIdealIso Q Λ i h s).hom =
      (blackFOfEqRedFirstIdealIso Q Λ i h s).hom ≫
        ModuleCat.ofHom (idemRightMul (redFirstIdem Q Λ β (appendSeq i h s))
          (redFirstIdem Q Λ β (appendSeq i h s)) (castOp Q Λ h (op (appendedDot Q Λ i μ)))
          (redFirstIdem_isIdempotentElem Q Λ β _)) := by
  rw [CupCap.indDotOfEq_app]
  ext1
  refine Ind.ext fun z a => Subtype.ext ?_
  have hc := CupCap.castOp_appendedDot_commute Q Λ i h
  have ha : a.1 * redFirstIdem Q Λ μ s = a.1 := a.2
  change z.1 * castOp Q Λ h (op (appendedDot Q Λ i μ)) * appendBlackOpOfEq Q Λ i h a.1 =
    z.1 * appendBlackOpOfEq Q Λ i h a.1 * castOp Q Λ h (op (appendedDot Q Λ i μ)) *
      redFirstIdem Q Λ β (appendSeq i h s)
  rw [← appendBlackOpOfEq_redFirstIdem]
  have hpq : appendBlackOpOfEq Q Λ i h a.1 * appendBlackOpOfEq Q Λ i h (redFirstIdem Q Λ μ s) =
      appendBlackOpOfEq Q Λ i h a.1 := by rw [← map_mul, ha]
  simp only [mul_assoc]
  rw [hc (redFirstIdem Q Λ μ s), ← mul_assoc (appendBlackOpOfEq Q Λ i h a.1), hpq, hc]

variable [∀ β : Multiset I,
  HasDerivedCategory.{0} (ModuleCat.{0} (TensorProductAlgebra k Q Λ β)ᵐᵒᵖ)]
  {C : CartanDatum I} (hQ : IsRouquierQ C Q)

/-- **Derived `F_i` of a right multiplication** between `e(𝐢) T^λ_μ` in degree `0`
(Webster, arXiv:1309.3796v3, §4.6; derived form of `blackFOfEq_map_idemRightMul`). -/
theorem derivedFOfEq_map_single_idemRightMul (i : I) {μ β : Multiset I}
    (h : ({i} : Multiset I) + μ = β) (s s' : Seq μ) (c : (TensorProductAlgebra k Q Λ μ)ᵐᵒᵖ) :
    (derivedFOfEq Λ hQ i h).map ((DerivedCategory.singleFunctor _ 0).map
        (ModuleCat.ofHom (idemRightMul (redFirstIdem Q Λ μ s)
          (redFirstIdem Q Λ μ s') c (redFirstIdem_isIdempotentElem Q Λ μ s')))) ≫
        (derivedFOfEqSingleRedFirstIdealIso Q Λ hQ i h s').hom =
      (derivedFOfEqSingleRedFirstIdealIso Q Λ hQ i h s).hom ≫
        (DerivedCategory.singleFunctor _ 0).map
          (ModuleCat.ofHom (idemRightMul (redFirstIdem Q Λ β (appendSeq i h s))
            (redFirstIdem Q Λ β (appendSeq i h s')) (appendBlackOpOfEq Q Λ i h c)
            (redFirstIdem_isIdempotentElem Q Λ β _))) := by
  have := blackFOfEq_preservesFiniteLimits Λ hQ i h
  have := blackFOfEq_preservesFiniteColimits Λ hQ i h
  dsimp only [derivedFOfEqSingleRedFirstIdealIso, derivedFOfEq, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom]
  rw [Category.assoc, ← Functor.comp_map,
    ((blackFOfEq Q Λ i h).mapDerivedCategorySingleFunctor 0).hom.naturality_assoc,
    Functor.comp_map, ← Functor.map_comp, blackFOfEq_map_idemRightMul, Functor.map_comp]

/-- **The derived dot on the new strand** of `F_i (e(𝐢) T^λ_μ)` in degree `0` is the right
multiplication by the dot on the appended strand (Webster, arXiv:1309.3796v3, §4.6; derived
form of `indDotOfEq_app_redFirstIdeal`). -/
theorem derivedIndDotOfEq_app_single_redFirstIdeal (i : I) {μ β : Multiset I}
    (h : ({i} : Multiset I) + μ = β) (s : Seq μ) :
    (derivedIndDotOfEq Λ hQ i h).app ((DerivedCategory.singleFunctor _ 0).obj
        (ModuleCat.of (TensorProductAlgebra k Q Λ μ)ᵐᵒᵖ (idemLeftIdeal (redFirstIdem Q Λ μ s)))) ≫
        (derivedFOfEqSingleRedFirstIdealIso Q Λ hQ i h s).hom =
      (derivedFOfEqSingleRedFirstIdealIso Q Λ hQ i h s).hom ≫
        (DerivedCategory.singleFunctor _ 0).map
          (ModuleCat.ofHom (idemRightMul (redFirstIdem Q Λ β (appendSeq i h s))
            (redFirstIdem Q Λ β (appendSeq i h s)) (castOp Q Λ h (op (appendedDot Q Λ i μ)))
            (redFirstIdem_isIdempotentElem Q Λ β _))) := by
  have := blackFOfEq_preservesFiniteLimits Λ hQ i h
  have := blackFOfEq_preservesFiniteColimits Λ hQ i h
  dsimp only [derivedFOfEqSingleRedFirstIdealIso, derivedIndDotOfEq, Iso.trans_hom,
    Iso.app_hom, Functor.mapIso_hom]
  rw [NatTrans.mapDerivedCategory_app_singleFunctor_obj, Category.assoc, Category.assoc,
    Iso.inv_hom_id_app_assoc, ← Functor.map_comp, indDotOfEq_app_redFirstIdeal,
    Functor.map_comp, Category.assoc]

end Categorification.Stendhal.SingleRed
