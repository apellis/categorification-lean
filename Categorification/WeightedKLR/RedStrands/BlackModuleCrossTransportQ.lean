/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackModuleCrossTransport
import Categorification.WeightedKLR.RedStrands.DoubleCLBlackActionQ
import Categorification.WeightedKLR.RedStrands.BlackModuleCrossQ
import Categorification.WeightedKLR.RedStrands.BlackModuleEFTransportQ

/-!
# The commutation of `Eⱼ` and `Fᵢ` on modules over `T^λ`, for `i ≠ j`

The relation `Eⱼ Fᵢ ≅ Fᵢ Eⱼ` (`i ≠ j`) of the categorical action (Webster, arXiv:1309.3796v3,
Theorem 4.31) on all right modules over the tensor product algebra `T^λ` at standard
Khovanov–Lauda black scalars, an input of the dimension count in the proof of Proposition 5.5
there (`clBlackModuleCrossEquivQ`). It is transported from the all-down matrix ring
(`blackModuleCrossEquivQ`) through the repaired Lemma 4.29 (`clOpEquivQ`).

The contents `j + (i + ρ)` and `i + (j + ρ)` are equal but not definitionally, so `Eⱼ` out of
content `i + ρ` is restriction along `appendBlackOp` followed by the cast `castOp` of `T^λ`.

This is the version of `BlackModuleCrossTransport` in which the black strands carry the relations of
Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3, Definition 1.1, `r = 1`; `CLQ.pres RD k sc`) instead
of the KL III relations. Each declaration carries the suffix `Q`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory CategoryTheory.Idempotents QuantumGroup QuantumGroup.UDot StringDiagrams
  KLR TwoRep CyclotomicAction DoubleDiagram KL3.Diagram InductionAlong MulOpposite

open scoped Classical

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Cast

universe u

variable {I : Type u} [DecidableEq I] {k : Type u} [CommRing k] {sc : KL3.Diagram.CL.CLScalars C k} {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)

end Cast

section CL

universe u w

variable {I : Type u} {ℓ : ℕ} {Λ : Fin ℓ → I →₀ ℕ} {C : CartanDatum I}
  {k : Type u} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {hQ : IsRouquierQ C Q}

local notation "RDc" => coordinateDatum Λ C
local notation "KL" => blackScalarsQ Λ C hQ
local notation "T" => TensorProductAlgebra k (Q) Λ

variable {P : Presentation.{u, u}
    (signature (coordinateDatum Λ C) (redWeight (cyclotomicCoverWeightDatum Λ C))) k}
  (hP : CoverRelsNegligible.{u, u, w} Λ C hQ (coverDotCentral Λ C hQ)
    (blockWeight (cyclotomicCoverWeightDatum Λ C) (cyclotomicCoverHighest (I := I) (ℓ := ℓ)) 0 :
      I ⊕ Fin ℓ → ℤ) P)
  (hwf : P.WFDom)

local notation "Pin" => addDownRelations (RDc) (Subtype.val ∘ coordinateRedWeights Λ C)
  (affineCoverQ (clDownwardQ KL) Λ) (signedCapPresentationOf (RDc) (redWeight (cyclotomicCoverWeightDatum Λ C)) (CLQ.pres (RDc) k KL) P (clDownwardQ KL) Λ fun i j => (CL.CLScalars.t KL i j : k))
local notation "PD" => clDownwardBlockQ Λ C hQ P

/-- `clOpEquiv_appendBlackQ` with the content of the target given by an equality. -/
theorem clOpEquiv_appendBlackOfEqQ (j : I) {μ ν' : Multiset I} (hc : {j} + μ = ν')
    (hw : wt (RDc) (downRightWeight (RDc) (coordinateRedWeights Λ C) μ) [(false, j)] =
      downRightWeight (RDc) (coordinateRedWeights Λ C) ν') (z : (T μ)ᵐᵒᵖ) :
    KLR.Diagram.MatEnd.mapEmbOp (blackAct (PD) [(false, j)] hw)
        ((downIdxCast_injective hc).comp (appendDown_injective j))
        (blackAct_downObj_cast (PD) j hc hw) (clOpEquivQ hP hwf μ z) =
      clOpEquivQ hP hwf ν' (appendBlackOpOfEq (Q) Λ j hc z) := by
  subst hc
  exact clOpEquiv_appendBlackQ hP hwf j μ z

variable (i j : I) (ρ : Multiset I) (M : Type u) [AddCommGroup M]
  [Module (TensorProductAlgebra k (Q) Λ ({j} + ρ))ᵐᵒᵖ M]

local notation "MV" => ClMatViewQ hP hwf j ρ M

/-- **`Eⱼ Fᵢ` against `Fᵢ Eⱼ` on `T^λ`-modules**, `i ≠ j` (Webster, arXiv:1309.3796v3,
Theorem 4.31, input of the proof of Proposition 5.5): for every right `T^λ_{j+ρ}`-module `M`,
`Eⱼ Fᵢ M ≅ Fᵢ Eⱼ M` as right `T^λ_{i+ρ}`-modules. Transported from the all-down matrix ring
(`blackModuleCrossEquivQ`) through the repaired Lemma 4.29. -/
def clBlackModuleCrossEquivQ (hji : j ≠ i) :
    InductionAlong.Res (appendBlackOpOfEq (Q) Λ j (cross_content i j ρ))
        (InductionAlong.Ind M (appendBlackOp (Q) Λ i ({j} + ρ))) ≃ₗ[(T ({i} + ρ))ᵐᵒᵖ]
      InductionAlong.Ind (InductionAlong.Res (appendBlackOp (Q) Λ j ρ) M)
        (appendBlackOp (Q) Λ i ρ) :=
  resIndCrossEquivTransport (clOpEquivQ hP hwf ρ) (clOpEquivQ hP hwf ({j} + ρ))
    (clOpEquivQ hP hwf ({i} + ρ)) (clOpEquivQ hP hwf ({i} + ({j} + ρ)))
    (clOpEquiv_appendBlackQ hP hwf j ρ) (clOpEquiv_appendBlackQ hP hwf i ({j} + ρ))
    (clOpEquiv_appendBlackQ hP hwf i ρ)
    (clOpEquiv_appendBlackOfEqQ hP hwf j (cross_content i j ρ)
      (cross_wt_down (Λ := coordinateRedWeights Λ C) i j ρ))
    (toClMatViewQ hP hwf j ρ M) (toClMatView_smulQ hP hwf j ρ M)
    (blackModuleCrossEquivQ (Pin) (CL.CLScalars.t KL) i j ρ hji (clDownwardBlockQ_reflectedBlack P) (MV))

end CL

end Categorification.Stendhal
