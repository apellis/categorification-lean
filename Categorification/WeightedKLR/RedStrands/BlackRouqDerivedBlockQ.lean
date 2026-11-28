/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackRouqModuleBoundaryQ
import Categorification.WeightedKLR.RedStrands.BlackRouqData
import Categorification.Algebra.MapDerivedSigma

/-!
# Brundan's inversion relations for Webster's functors on derived categories of `T^λ`-modules

Brundan, arXiv:1501.00350v1, (1.8) and (1.9), for Webster's functors on the derived categories
`D(T^λ_μ)` of right modules over the blocks of the tensor product algebra (arXiv:1309.3796v3,
§4.6, Theorem 4.31): the derived induction `Fᵢ` (`derivedFOfEq`), its right adjoint (the derived
restriction, `derivedAdjOfEq`), the derived dot and the derived crossing (`derivedIndDotOfEq`,
`derivedIndCrossOfEq`; the same-colour crossing acts as `-ψ`, the convention of
Khovanov–Lauda III).

* `derivedBlackSumInvToQ` (`⟨i, λ⟩ ≤ 0`) and `derivedBlackSumInvFromQ` (`0 ≤ ⟨i, λ⟩`), with `λ`
  the right weight of content `i + ν`: explicit inverses of the rightward crossing with the
  dotted counits (resp. units), from `clBlackModuleSumInvToQ`/`FromQ` by
  `TwoRep.SumInvTo.derivedSigma`/`SumInvFrom.derivedSigma`;
* `blackModuleSumInvFromOfNotMemQ`: for `i ∉ μ`, the module-level splitting of the dotted
  units `𝟭 ⟶ Eᵢ Fᵢ` into `n = ⟨i, λ_μ⟩` copies of the identity, from
  `clBlackModuleSumInvFromOfNotMemQ`; its derived form is `blackDerivedCoeff` with
  `blackRouq_boundary_total` and `blackRouq_boundary_entry` (in `BlackRouqLocQ`).

The presentation `P` is subject to the hypotheses of Webster's Theorem 4.30 in the library:
negligible cover relations (`CoverRelsNegligible`) and well-founded domains (`WFDom`). Induction
is exact for Rouquier polynomials over a field (Theorem 4.31, `hQ`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory CategoryTheory.Idempotents QuantumGroup QuantumGroup.UDot StringDiagrams
  KLR TwoRep CyclotomicAction DoubleDiagram KL3.Diagram InductionAlong MulOpposite NatTrans

open scoped Classical

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 2000] InductionAlong.instModuleInd InductionAlong.Res.instModule

universe u w w₂

variable {I : Type u} {ℓ : ℕ} {Λ : Fin ℓ → I →₀ ℕ} {C : CartanDatum I}
  {k : Type u} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {hQ : IsRouquierQ C Q}

local notation "RDc" => coordinateDatum Λ C

variable {P : Presentation.{u, u}
    (signature (coordinateDatum Λ C) (redWeight (cyclotomicCoverWeightDatum Λ C))) k}
  (hP : CoverRelsNegligible.{u, u, w} Λ C hQ (coverDotCentral Λ C hQ)
    (blockWeight (cyclotomicCoverWeightDatum Λ C) (cyclotomicCoverHighest (I := I) (ℓ := ℓ)) 0 :
      I ⊕ Fin ℓ → ℤ) P)
  (hwf : P.WFDom)
  [∀ β : Multiset I,
    HasDerivedCategory.{w₂} (ModuleCat.{u} (TensorProductAlgebra k Q Λ β)ᵐᵒᵖ)]
  (i : I) (ν : Multiset I)

/-- **Brundan (1.8) for Webster's functors on derived categories** (Webster,
arXiv:1309.3796v3, §4.6, Theorem 4.31, with the repaired Lemma 4.29 and Theorem 4.30): for
`⟨i, λ⟩ ≤ 0`, with `λ` the right weight of content `i + ν`, the rightward crossing of the derived
`Fᵢ ⊣ Eᵢ` and the derived crossing (acting as `-ψ`), together with the derived dotted counits,
has an explicit inverse, for a presentation `P` with negligible cover relations
(`CoverRelsNegligible`) and well-founded domains (`WFDom`). -/
def derivedBlackSumInvToQ (hsym : KLRSymm Q)
    (hn : ip (RDc) i (downRightWeight (RDc) (coordinateRedWeights Λ C) ({i} + ν)) ≤ 0) :
    SumInvTo (functorSigma
        (derivedAdjOfEq Λ hQ i (rfl : ({i} : Multiset I) + ({i} + ν) = _)).unit
        (derivedIndCrossOfEq Λ hQ hsym i i rfl rfl rfl rfl)
        (derivedAdjOfEq Λ hQ i (rfl : ({i} : Multiset I) + ν = _)).counit)
      (fun m => Functor.whiskerLeft (derivedEOfEq Q Λ i (rfl : ({i} : Multiset I) + ν = _))
        (powComp (derivedIndDotOfEq Λ hQ i rfl) m) ≫ (derivedAdjOfEq Λ hQ i rfl).counit)
      (-ip (RDc) i (downRightWeight (RDc) (coordinateRedWeights Λ C) ({i} + ν))).toNat :=
  haveI := blackFOfEq_preservesFiniteLimits Λ hQ i (rfl : ({i} : Multiset I) + ν = _)
  haveI := blackFOfEq_preservesFiniteColimits Λ hQ i (rfl : ({i} : Multiset I) + ν = _)
  haveI := blackFOfEq_preservesFiniteLimits Λ hQ i (rfl : ({i} : Multiset I) + ({i} + ν) = _)
  haveI := blackFOfEq_preservesFiniteColimits Λ hQ i (rfl : ({i} : Multiset I) + ({i} + ν) = _)
  SumInvTo.derivedSigma (clBlackModuleSumInvToQ hP hwf i ν hsym hn)

/-- **Brundan (1.9) for Webster's functors on derived categories** (Webster,
arXiv:1309.3796v3, §4.6, Theorem 4.31, with the repaired Lemma 4.29 and Theorem 4.30): for
`0 ≤ ⟨i, λ⟩`, with `λ` the right weight of content `i + ν`, the rightward crossing of the derived
`Fᵢ ⊣ Eᵢ` and the derived crossing (acting as `-ψ`), together with the derived dotted units, has
an explicit inverse, for a presentation `P` with negligible cover relations
(`CoverRelsNegligible`) and well-founded domains (`WFDom`). -/
def derivedBlackSumInvFromQ (hsym : KLRSymm Q)
    (hn : 0 ≤ ip (RDc) i (downRightWeight (RDc) (coordinateRedWeights Λ C) ({i} + ν))) :
    SumInvFrom (functorSigma
        (derivedAdjOfEq Λ hQ i (rfl : ({i} : Multiset I) + ({i} + ν) = _)).unit
        (derivedIndCrossOfEq Λ hQ hsym i i rfl rfl rfl rfl)
        (derivedAdjOfEq Λ hQ i (rfl : ({i} : Multiset I) + ν = _)).counit)
      (fun m => (derivedAdjOfEq Λ hQ i (rfl : ({i} : Multiset I) + ({i} + ν) = _)).unit ≫
        Functor.whiskerRight (powComp (derivedIndDotOfEq Λ hQ i rfl) m)
          (derivedEOfEq Q Λ i rfl))
      (ip (RDc) i (downRightWeight (RDc) (coordinateRedWeights Λ C) ({i} + ν))).toNat :=
  haveI := blackFOfEq_preservesFiniteLimits Λ hQ i (rfl : ({i} : Multiset I) + ν = _)
  haveI := blackFOfEq_preservesFiniteColimits Λ hQ i (rfl : ({i} : Multiset I) + ν = _)
  haveI := blackFOfEq_preservesFiniteLimits Λ hQ i (rfl : ({i} : Multiset I) + ({i} + ν) = _)
  haveI := blackFOfEq_preservesFiniteColimits Λ hQ i (rfl : ({i} : Multiset I) + ({i} + ν) = _)
  SumInvFrom.derivedSigma (clBlackModuleSumInvFromQ hP hwf i ν hsym hn)

omit [∀ β : Multiset I,
  HasDerivedCategory.{w₂} (ModuleCat.{u} (TensorProductAlgebra k Q Λ β)ᵐᵒᵖ)] in
/-- The dotted units of `Fᵢ ⊣ Eᵢ` on modules of any content `μ`, on each module. -/
theorem blackDottedCupOfContent_app (m : ℕ) (μ : Multiset I)
    (M : ModuleCat.{u} (TensorProductAlgebra k Q Λ μ)ᵐᵒᵖ) :
    ((blackAdjOfEq Q Λ i (rfl : ({i} : Multiset I) + μ = _)).unit ≫
        Functor.whiskerRight (powComp (indDotOfEq Q Λ i rfl) m) (blackEOfEq Q Λ i rfl)).app M =
      by exact ModuleCat.ofHom (Res.map (φ := appendBlackOp Q Λ i μ)
        ((natMap (N := M) (φ := appendBlackOp Q Λ i μ)
          (intertwines_of_commute (op_appendedDot_commute Q Λ i μ))) ^ m : Module.End _ _) ∘ₗ
        unitMap (φ := appendBlackOp Q Λ i μ) M) := by
  rw [NatTrans.comp_app, Functor.whiskerRight_app, powComp_indDotOfEq_self_app]
  rfl

/-- **Brundan (1.9) outside the content, in the functor category** (Webster,
arXiv:1309.3796v3, §4.6, Theorem 4.31, with the repaired Lemma 4.29 and Theorem 4.30): for
`i ∉ μ`, the dotted units `η x^m Eᵢ` identify `Eᵢ Fᵢ` with `n = ⟨i, λ_μ⟩` copies of the identity
functor of right `T^λ_μ`-modules, for a presentation `P` with negligible cover relations
(`CoverRelsNegligible`) and well-founded domains (`WFDom`). The source of the first component is
the zero functor. -/
def blackModuleSumInvFromOfNotMemQ (μ : Multiset I) (hi : i ∉ μ) :
    SumInvFrom (0 : (Functor.const _).obj
        (ModuleCat.of (TensorProductAlgebra k Q Λ μ)ᵐᵒᵖ PUnit.{u + 1}) ⟶
          blackFOfEq Q Λ i (rfl : ({i} : Multiset I) + μ = _) ⋙ blackEOfEq Q Λ i rfl)
      (fun m => (blackAdjOfEq Q Λ i (rfl : ({i} : Multiset I) + μ = _)).unit ≫
        Functor.whiskerRight (powComp (indDotOfEq Q Λ i rfl) m) (blackEOfEq Q Λ i rfl))
      (ip (RDc) i (downRightWeight (RDc) (coordinateRedWeights Λ C) μ)).toNat :=
  SumInvFrom.ofApp fun M => (clBlackModuleSumInvFromOfNotMemQ hP hwf i μ M hi).congr rfl
    (funext fun m => (blackDottedCupOfContent_app i m μ M).symm) rfl

end Categorification.Stendhal
