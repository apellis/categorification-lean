/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackModuleCross
import Categorification.WeightedKLR.RedStrands.BlackModuleEFTransport

/-!
# The commutation of `Eⱼ` and `Fᵢ` on modules over `T^λ`, for `i ≠ j`

The relation `Eⱼ Fᵢ ≅ Fᵢ Eⱼ` (`i ≠ j`) of the categorical action (Webster, arXiv:1309.3796v3,
Theorem 4.31) on all right modules over the tensor product algebra `T^λ` at standard
Khovanov–Lauda black scalars, an input of the dimension count in the proof of Proposition 5.5
there (`clBlackModuleCrossEquiv`). It is transported from the all-down matrix ring
(`blackModuleCrossEquiv`) through the repaired Lemma 4.29 (`clOpEquiv`).

The contents `j + (i + ρ)` and `i + (j + ρ)` are equal but not definitionally, so `Eⱼ` out of
content `i + ρ` is restriction along `appendBlackOp` followed by the cast `castOp` of `T^λ`.
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

variable {I : Type u} [DecidableEq I] {k : Type u} [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)

/-- The tensor product algebras of two equal contents, identified. -/
def castOp {ν ν' : Multiset I} (h : ν = ν') :
    (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ ≃+* (TensorProductAlgebra k Q Λ ν')ᵐᵒᵖ :=
  h ▸ RingEquiv.refl _

/-- `appendBlackOp` with the content of the target given by an equality. -/
def appendBlackOpOfEq (j : I) {μ ν' : Multiset I} (hc : {j} + μ = ν') :
    (TensorProductAlgebra k Q Λ μ)ᵐᵒᵖ →ₙ+* (TensorProductAlgebra k Q Λ ν')ᵐᵒᵖ :=
  (castOp Q Λ hc).toRingHom.toNonUnitalRingHom.comp (appendBlackOp Q Λ j μ)

theorem appendBlackOpOfEq_apply (j : I) {μ ν' : Multiset I} (hc : {j} + μ = ν') (z) :
    appendBlackOpOfEq Q Λ j hc z = castOp Q Λ hc (appendBlackOp Q Λ j μ z) :=
  rfl

end Cast

section CL

universe u w

variable {I : Type u} {ℓ : ℕ} {Λ : Fin ℓ → I →₀ ℕ} {C : CartanDatum I}
  {k : Type u} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {hQ : IsRouquierQ C Q}

local notation "RDc" => coordinateDatum Λ C
local notation "KL" => (CL.CLScalars.kl : CL.CLScalars C k)
local notation "T" => TensorProductAlgebra k (CL.qCL KL) Λ

variable (hstd : ∀ i j, i ≠ j → Q i j = CL.qCL (CL.CLScalars.kl : CL.CLScalars C k) i j)
  {P : Presentation.{u, u}
    (signature (coordinateDatum Λ C) (redWeight (cyclotomicCoverWeightDatum Λ C))) k}
  (hP : CoverRelsNegligible.{u, u, w} Λ C hQ (coverDotCentral Λ C hQ)
    (blockWeight (cyclotomicCoverWeightDatum Λ C) (cyclotomicCoverHighest (I := I) (ℓ := ℓ)) 0 :
      I ⊕ Fin ℓ → ℤ) P)
  (hwf : P.WFDom)

local notation "Pin" => addDownRelations (RDc) (Subtype.val ∘ coordinateRedWeights Λ C)
  (affineCoverQ (clDownwardQ KL) Λ) (signedCapKLPresentation (RDc)
    (redWeight (cyclotomicCoverWeightDatum Λ C)) P (clDownwardQ KL) Λ fun _ _ => 1)
local notation "PD" => clDownwardBlock Λ C P

/-- `clOpEquiv_appendBlack` with the content of the target given by an equality. -/
theorem clOpEquiv_appendBlackOfEq (j : I) {μ ν' : Multiset I} (hc : {j} + μ = ν')
    (hw : wt (RDc) (downRightWeight (RDc) (coordinateRedWeights Λ C) μ) [(false, j)] =
      downRightWeight (RDc) (coordinateRedWeights Λ C) ν') (z : (T μ)ᵐᵒᵖ) :
    KLR.Diagram.MatEnd.mapEmbOp (blackAct (PD) [(false, j)] hw)
        ((downIdxCast_injective hc).comp (appendDown_injective j))
        (blackAct_downObj_cast (PD) j hc hw) (clOpEquiv hstd hP hwf μ z) =
      clOpEquiv hstd hP hwf ν' (appendBlackOpOfEq (CL.qCL KL) Λ j hc z) := by
  subst hc
  exact clOpEquiv_appendBlack hstd hP hwf j μ z

variable (i j : I) (ρ : Multiset I) (M : Type u) [AddCommGroup M]
  [Module (TensorProductAlgebra k (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ ({j} + ρ))ᵐᵒᵖ M]

local notation "MV" => ClMatView hstd hP hwf j ρ M

/-- **`Eⱼ Fᵢ` against `Fᵢ Eⱼ` on `T^λ`-modules**, `i ≠ j` (Webster, arXiv:1309.3796v3,
Theorem 4.31, input of the proof of Proposition 5.5): for every right `T^λ_{j+ρ}`-module `M`,
`Eⱼ Fᵢ M ≅ Fᵢ Eⱼ M` as right `T^λ_{i+ρ}`-modules. Transported from the all-down matrix ring
(`blackModuleCrossEquiv`) through the repaired Lemma 4.29. -/
def clBlackModuleCrossEquiv (hji : j ≠ i) :
    InductionAlong.Res (appendBlackOpOfEq (CL.qCL KL) Λ j (cross_content i j ρ))
        (InductionAlong.Ind M (appendBlackOp (CL.qCL KL) Λ i ({j} + ρ))) ≃ₗ[(T ({i} + ρ))ᵐᵒᵖ]
      InductionAlong.Ind (InductionAlong.Res (appendBlackOp (CL.qCL KL) Λ j ρ) M)
        (appendBlackOp (CL.qCL KL) Λ i ρ) :=
  resIndCrossEquivTransport (clOpEquiv hstd hP hwf ρ) (clOpEquiv hstd hP hwf ({j} + ρ))
    (clOpEquiv hstd hP hwf ({i} + ρ)) (clOpEquiv hstd hP hwf ({i} + ({j} + ρ)))
    (clOpEquiv_appendBlack hstd hP hwf j ρ) (clOpEquiv_appendBlack hstd hP hwf i ({j} + ρ))
    (clOpEquiv_appendBlack hstd hP hwf i ρ)
    (clOpEquiv_appendBlackOfEq hstd hP hwf j (cross_content i j ρ)
      (cross_wt_down (Λ := coordinateRedWeights Λ C) i j ρ))
    (toClMatView hstd hP hwf j ρ M) (toClMatView_smul hstd hP hwf j ρ M)
    (blackModuleCrossEquiv (Pin) (KL).t i j ρ hji (clDownwardBlock_reflectedBlack P) (MV))

end CL

end Categorification.Stendhal
