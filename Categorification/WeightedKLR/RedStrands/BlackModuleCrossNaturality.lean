/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongCrossTransportNaturality
import Categorification.Diagrams.KLR.MatEndModuleCrossNaturality
import Categorification.WeightedKLR.RedStrands.BlackModuleCrossLeft
import Categorification.WeightedKLR.RedStrands.BlackModuleEFLeftNaturality

/-!
# Naturality of the commutation of `Eⱼ` and `Fᵢ`, `i ≠ j`

The isomorphisms `Eⱼ Fᵢ M ≅ Fᵢ Eⱼ M` (`i ≠ j`) of right and left modules over the tensor
product algebra `T^λ` (`clBlackModuleCrossEquiv`, `clLeftBlackModuleCrossEquiv`; Webster,
arXiv:1309.3796v3, Theorem 4.31 on modules, at standard Khovanov–Lauda black scalars) are
natural in the module (`clBlackModuleCrossEquiv_map`, `clLeftBlackModuleCrossEquiv_map`).
This makes them compatible with an action on `M` commuting with `T^λ`, as used for the tensor
factors in the proof of Proposition 5.5 there.
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
local notation "KL" => (CL.CLScalars.kl : CL.CLScalars C k)
local notation "T" => TensorProductAlgebra k (CL.qCL KL) Λ

variable (hstd : ∀ i j, i ≠ j → Q i j = CL.qCL (CL.CLScalars.kl : CL.CLScalars C k) i j)
  {P : Presentation.{u, u}
    (signature (coordinateDatum Λ C) (redWeight (cyclotomicCoverWeightDatum Λ C))) k}
  (hP : CoverRelsNegligible.{u, u, w} Λ C hQ (coverDotCentral Λ C hQ)
    (blockWeight (cyclotomicCoverWeightDatum Λ C) (cyclotomicCoverHighest (I := I) (ℓ := ℓ)) 0 :
      I ⊕ Fin ℓ → ℤ) P)
  (hwf : P.WFDom)
  (i j : I) (ρ : Multiset I)

local notation "Sj" => (Singleton.singleton j : Multiset I)
local notation "Si" => (Singleton.singleton i : Multiset I)

local notation "Pin" => addDownRelations (RDc) (Subtype.val ∘ coordinateRedWeights Λ C)
  (affineCoverQ (clDownwardQ KL) Λ) (signedCapKLPresentation (RDc)
    (redWeight (cyclotomicCoverWeightDatum Λ C)) P (clDownwardQ KL) Λ fun _ _ => 1)

section Right

variable {M M₂ : Type u} [AddCommGroup M] [AddCommGroup M₂]
  [Module (TensorProductAlgebra k (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ ({j} + ρ))ᵐᵒᵖ M]
  [Module (TensorProductAlgebra k (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ
    ({j} + ρ))ᵐᵒᵖ M₂]

/-- **Naturality of `clBlackModuleCrossEquiv`**: it carries `Eⱼ Fᵢ f` to `Fᵢ Eⱼ f`. -/
theorem clBlackModuleCrossEquiv_map (hji : j ≠ i) (f : M →ₗ[(T (Sj + ρ))ᵐᵒᵖ] M₂)
    (x : Res (appendBlackOpOfEq (CL.qCL KL) Λ j (cross_content i j ρ))
      (Ind M (appendBlackOp (CL.qCL KL) Λ i (Sj + ρ)))) :
    clBlackModuleCrossEquiv hstd hP hwf i j ρ M₂ hji (Res.map (Ind.map f) x) =
      Ind.map (Res.map f) (clBlackModuleCrossEquiv hstd hP hwf i j ρ M hji x) := by
  kernel_exact resIndCrossEquivTransport_map (clOpEquiv hstd hP hwf ρ)
    (clOpEquiv hstd hP hwf ({j} + ρ))
    (clOpEquiv hstd hP hwf ({i} + ρ)) (clOpEquiv hstd hP hwf ({i} + ({j} + ρ)))
    (clOpEquiv_appendBlack hstd hP hwf j ρ) (clOpEquiv_appendBlack hstd hP hwf i ({j} + ρ))
    (clOpEquiv_appendBlack hstd hP hwf i ρ)
    (clOpEquiv_appendBlackOfEq hstd hP hwf j (cross_content i j ρ)
      (cross_wt_down (Λ := coordinateRedWeights Λ C) i j ρ))
    (toClMatView hstd hP hwf j ρ M) (toClMatView_smul hstd hP hwf j ρ M)
    (toClMatView hstd hP hwf j ρ M₂) (toClMatView_smul hstd hP hwf j ρ M₂)
    f (clMatViewMap hstd hP hwf j ρ f) (fun _ => rfl)
    (blackModuleCrossEquiv (Pin) (KL).t i j ρ hji (clDownwardBlock_reflectedBlack P)
      (ClMatView hstd hP hwf j ρ M))
    (blackModuleCrossEquiv (Pin) (KL).t i j ρ hji (clDownwardBlock_reflectedBlack P)
      (ClMatView hstd hP hwf j ρ M₂))
    (fun y => by
      delta blackModuleCrossEquiv
      apply KLR.Diagram.MatEnd.resIndEquivIndResCross_map) x

end Right

section Left

variable {M M₂ : Type u} [AddCommGroup M] [AddCommGroup M₂]
  [Module (TensorProductAlgebra k (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ ({j} + ρ)) M]
  [Module (TensorProductAlgebra k (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ
    ({j} + ρ)) M₂]

/-- **Naturality of `clLeftBlackModuleCrossEquiv`**: it carries `Eⱼ Fᵢ f` to `Fᵢ Eⱼ f`. -/
theorem clLeftBlackModuleCrossEquiv_map (hji : j ≠ i) (f : M →ₗ[T (Sj + ρ)] M₂)
    (x : Res (appendBlackNUOfEq (CL.qCL KL) Λ j (cross_content i j ρ))
      (Ind M (appendBlackNU (Q := CL.qCL KL) (Λ := Λ) i (Sj + ρ)))) :
    clLeftBlackModuleCrossEquiv hstd hP hwf i j ρ M₂ hji (Res.map (Ind.map f) x) =
      Ind.map (Res.map f) (clLeftBlackModuleCrossEquiv hstd hP hwf i j ρ M hji x) := by
  kernel_exact resIndCrossEquivTransport_map (tensorFlipRingEquiv (Q := CL.qCL KL) (Λ := Λ) ρ)
    (tensorFlipRingEquiv (Q := CL.qCL KL) (Λ := Λ) (Sj + ρ))
    (tensorFlipRingEquiv (Q := CL.qCL KL) (Λ := Λ) (Si + ρ))
    (tensorFlipRingEquiv (Q := CL.qCL KL) (Λ := Λ) (Si + (Sj + ρ)))
    (appendBlackOp_tensorFlipRingEquiv (CL.qCL KL) Λ ρ j)
    (appendBlackOp_tensorFlipRingEquiv (CL.qCL KL) Λ (Sj + ρ) i)
    (appendBlackOp_tensorFlipRingEquiv (CL.qCL KL) Λ ρ i)
    (appendBlackOpOfEq_tensorFlipRingEquiv (CL.qCL KL) Λ j (cross_content i j ρ))
    (toFlipView (CL.qCL KL) Λ (Sj + ρ) M) (toFlipView_smul (CL.qCL KL) Λ (Sj + ρ) M)
    (toFlipView (CL.qCL KL) Λ (Sj + ρ) M₂) (toFlipView_smul (CL.qCL KL) Λ (Sj + ρ) M₂)
    f (flipViewMap (CL.qCL KL) Λ (Sj + ρ) f) (fun _ => rfl)
    (clBlackModuleCrossEquiv hstd hP hwf i j ρ (FlipView (CL.qCL KL) Λ (Sj + ρ) M) hji)
    (clBlackModuleCrossEquiv hstd hP hwf i j ρ (FlipView (CL.qCL KL) Λ (Sj + ρ) M₂) hji)
    (fun y => by
      kernel_exact clBlackModuleCrossEquiv_map hstd hP hwf i j ρ hji
        (flipViewMap (CL.qCL KL) Λ (Sj + ρ) f) y) x

end Left

end CL

end Categorification.Stendhal
