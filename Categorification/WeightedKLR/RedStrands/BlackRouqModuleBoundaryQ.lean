/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackRouqBoundaryQ
import Categorification.WeightedKLR.RedStrands.BlackRouqModuleSumInvQ
import Categorification.WeightedKLR.RedStrands.BlackModuleEFOutsideContentCLQ
import Categorification.Algebra.InductionAlongSumInvTransportZero

/-!
# Brundan's relation (1.9) for Webster's functors on `T^λ`-modules outside the content

Brundan, arXiv:1501.00350v1, (1.9), for Webster's functors on right modules over the tensor
product algebra `T^λ_μ` (arXiv:1309.3796v3, §4.6, Theorem 4.31) when `i ∉ μ`: there `Eᵢ`
vanishes, and the dotted units `η x^m Eᵢ` (`x` the dot on the new strand) identify `M^{⊕ n}`
with `Eᵢ Fᵢ M`, for `n = ⟨i, λ⟩ ≥ 0` with `λ` the right weight of content `μ`
(`clBlackModuleSumInvFromOfNotMemQ`). This is the boundary case of the local Rouquier data.

It comes from the statement on the all-down matrix ring (`blackMatrixSumInvFromOfNotMemQ`),
transported through the repaired Lemma 4.29 (`clOpEquivQ`), under which the new-strand dot is
the black-action dot (`clOpEquivQ_appendedDot`). The presentation `P` is subject to the
hypotheses of Webster's Theorem 4.30 in the library: negligible cover relations
(`CoverRelsNegligible`) and well-founded domains (`WFDom`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory CategoryTheory.Idempotents QuantumGroup QuantumGroup.UDot StringDiagrams
  KLR TwoRep CyclotomicAction DoubleDiagram KL3.Diagram InductionAlong MulOpposite

open scoped Classical

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 2000] InductionAlong.instModuleInd InductionAlong.Res.instModule

universe u w

variable {I : Type u} {ℓ : ℕ} {Λ : Fin ℓ → I →₀ ℕ} {C : CartanDatum I}
  {k : Type u} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {hQ : IsRouquierQ C Q}

local notation "RDc" => coordinateDatum Λ C
local notation "KL" => blackScalarsQ Λ C hQ

variable {P : Presentation.{u, u}
    (signature (coordinateDatum Λ C) (redWeight (cyclotomicCoverWeightDatum Λ C))) k}
  (hP : CoverRelsNegligible.{u, u, w} Λ C hQ (coverDotCentral Λ C hQ)
    (blockWeight (cyclotomicCoverWeightDatum Λ C) (cyclotomicCoverHighest (I := I) (ℓ := ℓ)) 0 :
      I ⊕ Fin ℓ → ℤ) P)
  (hwf : P.WFDom)
  (i : I) (μ : Multiset I)

local notation "Pin" => addDownRelations (RDc) (Subtype.val ∘ coordinateRedWeights Λ C)
  (affineCoverQ (clDownwardQ KL) Λ) (signedCapPresentationOf (RDc)
    (redWeight (cyclotomicCoverWeightDatum Λ C)) (CLQ.pres (RDc) k KL) P (clDownwardQ KL) Λ
    fun i j => (CL.CLScalars.t KL i j : k))

/-- **Brundan (1.9) for Webster's functors on `T^λ_μ`-modules, outside the content**
(Webster, arXiv:1309.3796v3, §4.6, Theorem 4.31, with the repaired Lemma 4.29 and
Theorem 4.30): for `i ∉ μ`, with `λ` the right weight of content `μ` and `n = ⟨i, λ⟩ ≥ 0`,
the dotted units `m ↦ φ(1) x^m ⊗ m` (`x` the dot on the new strand) identify `M^{⊕ n}` with
`Eᵢ Fᵢ M` for every right module `M`, for a presentation `P` with negligible cover relations
(`CoverRelsNegligible`) and well-founded domains (`WFDom`). -/
def clBlackModuleSumInvFromOfNotMemQ
    (M : ModuleCat.{u} (TensorProductAlgebra k Q Λ μ)ᵐᵒᵖ) (hi : i ∉ μ) :
    SumInvFrom (X := ModuleCat.of _ (Res (appendBlackOp Q Λ i μ) (Ind M (appendBlackOp Q Λ i μ))))
      (Y := ModuleCat.of _ PUnit.{u + 1}) (Z := M) 0
      (fun m => ModuleCat.ofHom (Res.map (φ := appendBlackOp Q Λ i μ)
        ((natMap (N := M) (φ := appendBlackOp Q Λ i μ)
          (intertwines_of_commute (op_appendedDot_commute Q Λ i μ))) ^ m : Module.End _ _) ∘ₗ
        unitMap (φ := appendBlackOp Q Λ i μ) M))
      (ip (RDc) i (downRightWeight (RDc) (coordinateRedWeights Λ C) μ)).toNat := by
  have hd' := blackMatrixDotQ_intertwines (Pin) (CL.CLScalars.t KL) i μ
    (clDownwardBlockQ_reflectedBlack P)
  have hdd := clOpEquivQ_appendedDot_eq hP hwf i μ
  have S := blackMatrixSumInvFromOfNotMemQ (Pin) (CL.CLScalars.t KL) i μ
    (clDownwardBlockQ_reflectedBlack P) (ModuleCat.of _ (ClMatViewOfQ hP hwf μ M)) hi
  exact sumInvFrom_transportOfZero (φ₁ := appendBlackOp Q Λ i μ)
    (d := op (appendedDot Q Λ i μ)) (clOpEquivQ hP hwf μ) (clOpEquivQ hP hwf ({i} + μ))
    (clOpEquiv_appendBlackQ hP hwf i μ) M (ModuleCat.of _ (ClMatViewOfQ hP hwf μ M))
    (toClMatViewOfQ hP hwf μ M) (toClMatViewOf_smulQ hP hwf μ M)
    (intertwines_of_commute (op_appendedDot_commute Q Λ i μ)) hd' hdd S

end Categorification.Stendhal
