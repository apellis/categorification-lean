/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongCrossTransportNaturality
import Categorification.WeightedKLR.RedStrands.DoubleCLBlackActionQ
import Categorification.Diagrams.KLR.MatEndModuleCrossNaturality
import Categorification.WeightedKLR.RedStrands.BlackModuleCrossLeftQ
import Categorification.WeightedKLR.RedStrands.BlackModuleEFLeftNaturalityQ

/-!
# Naturality of the commutation of `Eⱼ` and `Fᵢ`, `i ≠ j`

The isomorphisms `Eⱼ Fᵢ M ≅ Fᵢ Eⱼ M` (`i ≠ j`) of right and left modules over the tensor
product algebra `T^λ` (`clBlackModuleCrossEquivQ`, `clLeftBlackModuleCrossEquivQ`; Webster,
arXiv:1309.3796v3, Theorem 4.31 on modules, at standard Khovanov–Lauda black scalars) are
natural in the module (`clBlackModuleCrossEquiv_mapQ`, `clLeftBlackModuleCrossEquiv_mapQ`).
This makes them compatible with an action on `M` commuting with `T^λ`, as used for the tensor
factors in the proof of Proposition 5.5 there.

This is the version of `BlackModuleCrossNaturality` in which the black strands carry the relations of
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

universe u w

section CL

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
  (i j : I) (ρ : Multiset I)

local notation "Sj" => (Singleton.singleton j : Multiset I)
local notation "Si" => (Singleton.singleton i : Multiset I)

local notation "Pin" => addDownRelations (RDc) (Subtype.val ∘ coordinateRedWeights Λ C)
  (affineCoverQ (clDownwardQ KL) Λ) (signedCapPresentationOf (RDc) (redWeight (cyclotomicCoverWeightDatum Λ C)) (CLQ.pres (RDc) k KL) P (clDownwardQ KL) Λ fun i j => (CL.CLScalars.t KL i j : k))

section Right

variable {M M₂ : Type u} [AddCommGroup M] [AddCommGroup M₂]
  [Module (TensorProductAlgebra k (Q) Λ ({j} + ρ))ᵐᵒᵖ M]
  [Module (TensorProductAlgebra k (Q) Λ
    ({j} + ρ))ᵐᵒᵖ M₂]

/-- **Naturality of `clBlackModuleCrossEquivQ`**: it carries `Eⱼ Fᵢ f` to `Fᵢ Eⱼ f`. -/
theorem clBlackModuleCrossEquiv_mapQ (hji : j ≠ i) (f : M →ₗ[(T (Sj + ρ))ᵐᵒᵖ] M₂)
    (x : Res (appendBlackOpOfEq (Q) Λ j (cross_content i j ρ))
      (Ind M (appendBlackOp (Q) Λ i (Sj + ρ)))) :
    clBlackModuleCrossEquivQ hP hwf i j ρ M₂ hji (Res.map (Ind.map f) x) =
      Ind.map (Res.map f) (clBlackModuleCrossEquivQ hP hwf i j ρ M hji x) := by
  kernel_exact resIndCrossEquivTransport_map (clOpEquivQ hP hwf ρ)
    (clOpEquivQ hP hwf ({j} + ρ))
    (clOpEquivQ hP hwf ({i} + ρ)) (clOpEquivQ hP hwf ({i} + ({j} + ρ)))
    (clOpEquiv_appendBlackQ hP hwf j ρ) (clOpEquiv_appendBlackQ hP hwf i ({j} + ρ))
    (clOpEquiv_appendBlackQ hP hwf i ρ)
    (clOpEquiv_appendBlackOfEqQ hP hwf j (cross_content i j ρ)
      (cross_wt_down (Λ := coordinateRedWeights Λ C) i j ρ))
    (toClMatViewQ hP hwf j ρ M) (toClMatView_smulQ hP hwf j ρ M)
    (toClMatViewQ hP hwf j ρ M₂) (toClMatView_smulQ hP hwf j ρ M₂)
    f (clMatViewMapQ hP hwf j ρ f) (fun _ => rfl)
    (blackModuleCrossEquivQ (Pin) (CL.CLScalars.t KL) i j ρ hji (clDownwardBlockQ_reflectedBlack P)
      (ClMatViewQ hP hwf j ρ M))
    (blackModuleCrossEquivQ (Pin) (CL.CLScalars.t KL) i j ρ hji (clDownwardBlockQ_reflectedBlack P)
      (ClMatViewQ hP hwf j ρ M₂))
    (fun y => by
      delta blackModuleCrossEquivQ
      apply KLR.Diagram.MatEnd.resIndEquivIndResCross_map) x

end Right

section Left

variable {M M₂ : Type u} [AddCommGroup M] [AddCommGroup M₂]
  [Module (TensorProductAlgebra k (Q) Λ ({j} + ρ)) M]
  [Module (TensorProductAlgebra k (Q) Λ
    ({j} + ρ)) M₂]

/-- **Naturality of `clLeftBlackModuleCrossEquivQ`**: it carries `Eⱼ Fᵢ f` to `Fᵢ Eⱼ f`. -/
theorem clLeftBlackModuleCrossEquiv_mapQ (hji : j ≠ i) (f : M →ₗ[T (Sj + ρ)] M₂)
    (x : Res (appendBlackNUOfEq (Q) Λ j (cross_content i j ρ))
      (Ind M (appendBlackNU (Q := Q) (Λ := Λ) i (Sj + ρ)))) :
    clLeftBlackModuleCrossEquivQ hP hwf i j ρ M₂ hji (Res.map (Ind.map f) x) =
      Ind.map (Res.map f) (clLeftBlackModuleCrossEquivQ hP hwf i j ρ M hji x) := by
  kernel_exact resIndCrossEquivTransport_map (tensorFlipRingEquiv (Q := Q) (Λ := Λ) ρ)
    (tensorFlipRingEquiv (Q := Q) (Λ := Λ) (Sj + ρ))
    (tensorFlipRingEquiv (Q := Q) (Λ := Λ) (Si + ρ))
    (tensorFlipRingEquiv (Q := Q) (Λ := Λ) (Si + (Sj + ρ)))
    (appendBlackOp_tensorFlipRingEquiv (Q) Λ ρ j)
    (appendBlackOp_tensorFlipRingEquiv (Q) Λ (Sj + ρ) i)
    (appendBlackOp_tensorFlipRingEquiv (Q) Λ ρ i)
    (appendBlackOpOfEq_tensorFlipRingEquiv (Q) Λ j (cross_content i j ρ))
    (toFlipView (Q) Λ (Sj + ρ) M) (toFlipView_smul (Q) Λ (Sj + ρ) M)
    (toFlipView (Q) Λ (Sj + ρ) M₂) (toFlipView_smul (Q) Λ (Sj + ρ) M₂)
    f (flipViewMap (Q) Λ (Sj + ρ) f) (fun _ => rfl)
    (clBlackModuleCrossEquivQ hP hwf i j ρ (FlipView (Q) Λ (Sj + ρ) M) hji)
    (clBlackModuleCrossEquivQ hP hwf i j ρ (FlipView (Q) Λ (Sj + ρ) M₂) hji)
    (fun y => by
      kernel_exact clBlackModuleCrossEquiv_mapQ hP hwf i j ρ hji
        (flipViewMap (Q) Λ (Sj + ρ) f) y) x

end Left

end CL

end Categorification.Stendhal
