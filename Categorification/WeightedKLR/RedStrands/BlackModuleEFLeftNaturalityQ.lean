/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackModuleEFLeftNaturality
import Categorification.WeightedKLR.RedStrands.DoubleCLBlackActionQ
import Categorification.WeightedKLR.RedStrands.BlackModuleEFLeftQ
import Categorification.WeightedKLR.RedStrands.BlackModuleEFTransportNaturalityQ

/-!
# Naturality of the commutation of `Eᵢ` and `Fᵢ` on left modules over `T^λ`

The isomorphisms `Eᵢ Fᵢ M ≅ Fᵢ Eᵢ M ⊕ M^{⊕ n}` (`clLeftBlackModuleEFEquivQ`) and
`Fᵢ Eᵢ M ≅ Eᵢ Fᵢ M ⊕ M^{⊕ -n}` (`clLeftBlackModuleFEEquivQ`) of left modules over the tensor
product algebra `T^λ` (Webster, arXiv:1309.3796v3, Thm 4.31 on modules, at standard
Khovanov–Lauda black scalars) are natural in the module (`clLeftBlackModuleEFEquiv_mapQ`,
`clLeftBlackModuleFEEquiv_mapQ`). So they commute with an action on `M` commuting with `T^λ`,
as for the tensor factors in the proof of Proposition 5.5 there.

This is the version of `BlackModuleEFLeftNaturality` in which the black strands carry the relations of
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

section Flip

variable {I : Type u} [DecidableEq I] {k : Type u} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (ν : Multiset I)
  {M M₂ : Type w} [AddCommGroup M] [Module (TensorProductAlgebra k Q Λ ν) M]
  [AddCommGroup M₂] [Module (TensorProductAlgebra k Q Λ ν) M₂]

end Flip

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
  (i : I) (ν : Multiset I)
  {M M₂ : Type u} [AddCommGroup M] [AddCommGroup M₂]
  [Module (TensorProductAlgebra k (Q) Λ ({i} + ν)) M]
  [Module (TensorProductAlgebra k (Q) Λ ({i} + ν)) M₂]

local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "ψo" => appendBlackNU (Q := Q) (Λ := Λ) i (Si + ν)
local notation "ψi" => appendBlackNU (Q := Q) (Λ := Λ) i ν

/-- **Naturality of `clLeftBlackModuleEFEquivQ`**: it carries `Eᵢ Fᵢ f` to `Fᵢ Eᵢ f × f^n`. -/
theorem clLeftBlackModuleEFEquiv_mapQ (f : M →ₗ[T (Si + ν)] M₂)
    (hn : 0 ≤ ip (RDc) i (downRightWeight (RDc) (coordinateRedWeights Λ C) (Si + ν)))
    (x : Res (ψo) (Ind M (ψo))) :
    clLeftBlackModuleEFEquivQ hP hwf i ν M₂ hn (Res.map (Ind.map f) x) =
      (Ind.map (Res.map f) (clLeftBlackModuleEFEquivQ hP hwf i ν M hn x).1,
        fun s => f ((clLeftBlackModuleEFEquivQ hP hwf i ν M hn x).2 s)) := by
  kernel_exact resIndEquivTransport_map (tensorFlipRingEquiv (Q := Q) (Λ := Λ) ν)
    (tensorFlipRingEquiv (Q := Q) (Λ := Λ) (Si + ν))
    (tensorFlipRingEquiv (Q := Q) (Λ := Λ) (Si + (Si + ν)))
    (appendBlackOp_tensorFlipRingEquiv (Q) Λ ν i)
    (appendBlackOp_tensorFlipRingEquiv (Q) Λ (Si + ν) i)
    (toFlipView (Q) Λ (Si + ν) M) (toFlipView_smul (Q) Λ (Si + ν) M)
    (toFlipView (Q) Λ (Si + ν) M₂) (toFlipView_smul (Q) Λ (Si + ν) M₂)
    f (flipViewMap (Q) Λ (Si + ν) f) (fun _ => rfl) _
    (clBlackModuleEFEquivQ hP hwf i ν (FlipView (Q) Λ (Si + ν) M) hn)
    (clBlackModuleEFEquivQ hP hwf i ν (FlipView (Q) Λ (Si + ν) M₂) hn)
    (fun y => by
      kernel_exact clBlackModuleEFEquiv_mapQ hP hwf i ν
        (flipViewMap (Q) Λ (Si + ν) f) hn y) x

/-- **Naturality of `clLeftBlackModuleFEEquivQ`**: it carries `Fᵢ Eᵢ f` to `Eᵢ Fᵢ f × f^{-n}`. -/
theorem clLeftBlackModuleFEEquiv_mapQ (f : M →ₗ[T (Si + ν)] M₂)
    (hn : ip (RDc) i (downRightWeight (RDc) (coordinateRedWeights Λ C) (Si + ν)) ≤ 0)
    (x : Ind (Res (ψi) M) (ψi)) :
    clLeftBlackModuleFEEquivQ hP hwf i ν M₂ hn (Ind.map (Res.map f) x) =
      (Res.map (Ind.map f) (clLeftBlackModuleFEEquivQ hP hwf i ν M hn x).1,
        fun s => f ((clLeftBlackModuleFEEquivQ hP hwf i ν M hn x).2 s)) := by
  kernel_exact indResEquivTransport_map (tensorFlipRingEquiv (Q := Q) (Λ := Λ) ν)
    (tensorFlipRingEquiv (Q := Q) (Λ := Λ) (Si + ν))
    (tensorFlipRingEquiv (Q := Q) (Λ := Λ) (Si + (Si + ν)))
    (appendBlackOp_tensorFlipRingEquiv (Q) Λ ν i)
    (appendBlackOp_tensorFlipRingEquiv (Q) Λ (Si + ν) i)
    (toFlipView (Q) Λ (Si + ν) M) (toFlipView_smul (Q) Λ (Si + ν) M)
    (toFlipView (Q) Λ (Si + ν) M₂) (toFlipView_smul (Q) Λ (Si + ν) M₂)
    f (flipViewMap (Q) Λ (Si + ν) f) (fun _ => rfl) _
    (clBlackModuleFEEquivQ hP hwf i ν (FlipView (Q) Λ (Si + ν) M) hn)
    (clBlackModuleFEEquivQ hP hwf i ν (FlipView (Q) Λ (Si + ν) M₂) hn)
    (fun y => by
      kernel_exact clBlackModuleFEEquiv_mapQ hP hwf i ν
        (flipViewMap (Q) Λ (Si + ν) f) hn y) x

end CL

end Categorification.Stendhal
