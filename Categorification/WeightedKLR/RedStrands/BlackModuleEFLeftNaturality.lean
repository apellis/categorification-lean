/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackModuleEFLeft
import Categorification.WeightedKLR.RedStrands.BlackModuleEFTransportNaturality

/-!
# Naturality of the commutation of `Eᵢ` and `Fᵢ` on left modules over `T^λ`

The isomorphisms `Eᵢ Fᵢ M ≅ Fᵢ Eᵢ M ⊕ M^{⊕ n}` (`clLeftBlackModuleEFEquiv`) and
`Fᵢ Eᵢ M ≅ Eᵢ Fᵢ M ⊕ M^{⊕ -n}` (`clLeftBlackModuleFEEquiv`) of left modules over the tensor
product algebra `T^λ` (Webster, arXiv:1309.3796v3, Thm 4.31 on modules, at standard
Khovanov–Lauda black scalars) are natural in the module (`clLeftBlackModuleEFEquiv_map`,
`clLeftBlackModuleFEEquiv_map`). So they commute with an action on `M` commuting with `T^λ`,
as for the tensor factors in the proof of Proposition 5.5 there.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory CategoryTheory.Idempotents QuantumGroup QuantumGroup.UDot StringDiagrams
  KLR TwoRep CyclotomicAction DoubleDiagram KL3.Diagram InductionAlong MulOpposite

open scoped Classical

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe u w

section Flip

variable {I : Type u} [DecidableEq I] {k : Type u} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (ν : Multiset I)
  {M M₂ : Type w} [AddCommGroup M] [Module (TensorProductAlgebra k Q Λ ν) M]
  [AddCommGroup M₂] [Module (TensorProductAlgebra k Q Λ ν) M₂]

/-- A map of left `T^λ_ν`-modules, as a map of their reflected right-module views. -/
def flipViewMap (f : M →ₗ[TensorProductAlgebra k Q Λ ν] M₂) :
    FlipView Q Λ ν M →ₗ[(TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ] FlipView Q Λ ν M₂ where
  toFun := f
  map_add' := f.map_add
  map_smul' t m := f.map_smul ((tensorFlipRingEquiv (Q := Q) (Λ := Λ) ν).symm t) m

end Flip

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
  (i : I) (ν : Multiset I)
  {M M₂ : Type u} [AddCommGroup M] [AddCommGroup M₂]
  [Module (TensorProductAlgebra k (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ ({i} + ν)) M]
  [Module (TensorProductAlgebra k (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ ({i} + ν)) M₂]

local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "ψo" => appendBlackNU (Q := CL.qCL KL) (Λ := Λ) i (Si + ν)
local notation "ψi" => appendBlackNU (Q := CL.qCL KL) (Λ := Λ) i ν

/-- **Naturality of `clLeftBlackModuleEFEquiv`**: it carries `Eᵢ Fᵢ f` to `Fᵢ Eᵢ f × f^n`. -/
theorem clLeftBlackModuleEFEquiv_map (f : M →ₗ[T (Si + ν)] M₂)
    (hn : 0 ≤ ip (RDc) i (downRightWeight (RDc) (coordinateRedWeights Λ C) (Si + ν)))
    (x : Res (ψo) (Ind M (ψo))) :
    clLeftBlackModuleEFEquiv hstd hP hwf i ν M₂ hn (Res.map (Ind.map f) x) =
      (Ind.map (Res.map f) (clLeftBlackModuleEFEquiv hstd hP hwf i ν M hn x).1,
        fun s => f ((clLeftBlackModuleEFEquiv hstd hP hwf i ν M hn x).2 s)) := by
  kernel_exact resIndEquivTransport_map (tensorFlipRingEquiv (Q := CL.qCL KL) (Λ := Λ) ν)
    (tensorFlipRingEquiv (Q := CL.qCL KL) (Λ := Λ) (Si + ν))
    (tensorFlipRingEquiv (Q := CL.qCL KL) (Λ := Λ) (Si + (Si + ν)))
    (appendBlackOp_tensorFlipRingEquiv (CL.qCL KL) Λ ν i)
    (appendBlackOp_tensorFlipRingEquiv (CL.qCL KL) Λ (Si + ν) i)
    (toFlipView (CL.qCL KL) Λ (Si + ν) M) (toFlipView_smul (CL.qCL KL) Λ (Si + ν) M)
    (toFlipView (CL.qCL KL) Λ (Si + ν) M₂) (toFlipView_smul (CL.qCL KL) Λ (Si + ν) M₂)
    f (flipViewMap (CL.qCL KL) Λ (Si + ν) f) (fun _ => rfl) _
    (clBlackModuleEFEquiv hstd hP hwf i ν (FlipView (CL.qCL KL) Λ (Si + ν) M) hn)
    (clBlackModuleEFEquiv hstd hP hwf i ν (FlipView (CL.qCL KL) Λ (Si + ν) M₂) hn)
    (fun y => by
      kernel_exact clBlackModuleEFEquiv_map hstd hP hwf i ν
        (flipViewMap (CL.qCL KL) Λ (Si + ν) f) hn y) x

/-- **Naturality of `clLeftBlackModuleFEEquiv`**: it carries `Fᵢ Eᵢ f` to `Eᵢ Fᵢ f × f^{-n}`. -/
theorem clLeftBlackModuleFEEquiv_map (f : M →ₗ[T (Si + ν)] M₂)
    (hn : ip (RDc) i (downRightWeight (RDc) (coordinateRedWeights Λ C) (Si + ν)) ≤ 0)
    (x : Ind (Res (ψi) M) (ψi)) :
    clLeftBlackModuleFEEquiv hstd hP hwf i ν M₂ hn (Ind.map (Res.map f) x) =
      (Res.map (Ind.map f) (clLeftBlackModuleFEEquiv hstd hP hwf i ν M hn x).1,
        fun s => f ((clLeftBlackModuleFEEquiv hstd hP hwf i ν M hn x).2 s)) := by
  kernel_exact indResEquivTransport_map (tensorFlipRingEquiv (Q := CL.qCL KL) (Λ := Λ) ν)
    (tensorFlipRingEquiv (Q := CL.qCL KL) (Λ := Λ) (Si + ν))
    (tensorFlipRingEquiv (Q := CL.qCL KL) (Λ := Λ) (Si + (Si + ν)))
    (appendBlackOp_tensorFlipRingEquiv (CL.qCL KL) Λ ν i)
    (appendBlackOp_tensorFlipRingEquiv (CL.qCL KL) Λ (Si + ν) i)
    (toFlipView (CL.qCL KL) Λ (Si + ν) M) (toFlipView_smul (CL.qCL KL) Λ (Si + ν) M)
    (toFlipView (CL.qCL KL) Λ (Si + ν) M₂) (toFlipView_smul (CL.qCL KL) Λ (Si + ν) M₂)
    f (flipViewMap (CL.qCL KL) Λ (Si + ν) f) (fun _ => rfl) _
    (clBlackModuleFEEquiv hstd hP hwf i ν (FlipView (CL.qCL KL) Λ (Si + ν) M) hn)
    (clBlackModuleFEEquiv hstd hP hwf i ν (FlipView (CL.qCL KL) Λ (Si + ν) M₂) hn)
    (fun y => by
      kernel_exact clBlackModuleFEEquiv_map hstd hP hwf i ν
        (flipViewMap (CL.qCL KL) Λ (Si + ν) f) hn y) x

end CL

end Categorification.Stendhal
