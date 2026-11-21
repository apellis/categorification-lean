/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongTransportNaturality
import Categorification.WeightedKLR.RedStrands.BlackModuleEFTransport
import Categorification.WeightedKLR.RedStrands.BlackModuleNaturality
import Categorification.TwoRep.KernelExact

/-!
# Naturality of the commutation of `Eᵢ` and `Fᵢ` on modules over `T^λ`

The isomorphisms `Eᵢ Fᵢ M ≅ Fᵢ Eᵢ M ⊕ M^{⊕ n}` (`clBlackModuleEFEquiv`) and
`Fᵢ Eᵢ M ≅ Eᵢ Fᵢ M ⊕ M^{⊕ -n}` (`clBlackModuleFEEquiv`) of right modules over the tensor
product algebra `T^λ` (Webster, arXiv:1309.3796v3, Thm 4.31 on modules, at standard
Khovanov–Lauda black scalars) are natural in the module (`clBlackModuleEFEquiv_map`,
`clBlackModuleFEEquiv_map`). This makes them compatible with an action on `M` commuting with
`T^λ`, as used for the tensor factors in the proof of Proposition 5.5 there.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory CategoryTheory.Idempotents QuantumGroup QuantumGroup.UDot StringDiagrams
  KLR TwoRep CyclotomicAction DoubleDiagram KL3.Diagram InductionAlong MulOpposite

open scoped Classical

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

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
  (i : I) (ν : Multiset I)
  {M M₂ : Type u} [AddCommGroup M] [AddCommGroup M₂]
  [Module (TensorProductAlgebra k (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ ({i} + ν))ᵐᵒᵖ M]
  [Module (TensorProductAlgebra k (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ
    ({i} + ν))ᵐᵒᵖ M₂]

local notation "PD" => clDownwardBlock Λ C P

local notation "Pin" => addDownRelations (RDc) (Subtype.val ∘ coordinateRedWeights Λ C)
  (affineCoverQ (clDownwardQ KL) Λ) (signedCapKLPresentation (RDc)
    (redWeight (cyclotomicCoverWeightDatum Λ C)) P (clDownwardQ KL) Λ fun _ _ => 1)

local notation "φo" => appendBlackOp (CL.qCL KL) Λ i (Singleton.singleton i + ν)
local notation "φi" => appendBlackOp (CL.qCL KL) Λ i ν

/-- A module map of right `T^λ_{i+ν}`-modules, as a map of their matrix-ring views. -/
def clMatViewMap (f : M →ₗ[(T ({i} + ν))ᵐᵒᵖ] M₂) :
    ClMatView hstd hP hwf i ν M →ₗ[(downwardMatrix (PD) ({i} + ν))ᵐᵒᵖ]
      ClMatView hstd hP hwf i ν M₂ where
  toFun := f
  map_add' := f.map_add
  map_smul' t m := f.map_smul ((clOpEquiv hstd hP hwf ({i} + ν)).symm t) m

/-- `Fᵢ f` for a map `f` of right `T^λ_{i+ν}`-modules. -/
def clIndMap (f : M →ₗ[(T ({i} + ν))ᵐᵒᵖ] M₂) := Ind.map (φ := φo) f

/-- `Eᵢ f` for a map `f` of right `T^λ_{i+ν}`-modules. -/
def clResMap (f : M →ₗ[(T ({i} + ν))ᵐᵒᵖ] M₂) := Res.map (φ := φi) (M := M) (M' := M₂) f

/-- `Eᵢ Fᵢ f` for a map `f` of right `T^λ_{i+ν}`-modules. -/
def clEFMap (f : M →ₗ[(T ({i} + ν))ᵐᵒᵖ] M₂) := Res.map (φ := φo) (clIndMap i ν f)

/-- `Fᵢ Eᵢ f` for a map `f` of right `T^λ_{i+ν}`-modules. -/
def clFEMap (f : M →ₗ[(T ({i} + ν))ᵐᵒᵖ] M₂) := Ind.map (φ := φi) (clResMap i ν f)

/-- **Naturality of `clBlackModuleEFEquiv`**: it carries `Eᵢ Fᵢ f` to `Fᵢ Eᵢ f × f^n`. -/
theorem clBlackModuleEFEquiv_map (f : M →ₗ[(T (Singleton.singleton i + ν : Multiset I))ᵐᵒᵖ] M₂)
    (hn : 0 ≤ ip (RDc) i (downRightWeight (RDc) (coordinateRedWeights Λ C) ({i} + ν)))
    (x : Res (φo) (Ind M (φo))) :
    clBlackModuleEFEquiv hstd hP hwf i ν M₂ hn (clEFMap i ν f x) =
      (clFEMap i ν f (clBlackModuleEFEquiv hstd hP hwf i ν M hn x).1,
        fun s => f ((clBlackModuleEFEquiv hstd hP hwf i ν M hn x).2 s)) := by
  kernel_exact resIndEquivTransport_map (clOpEquiv hstd hP hwf ν)
    (clOpEquiv hstd hP hwf ({i} + ν))
    (clOpEquiv hstd hP hwf ({i} + ({i} + ν))) (clOpEquiv_appendBlack hstd hP hwf i ν)
    (clOpEquiv_appendBlack hstd hP hwf i ({i} + ν)) (toClMatView hstd hP hwf i ν M)
    (toClMatView_smul hstd hP hwf i ν M) (toClMatView hstd hP hwf i ν M₂)
    (toClMatView_smul hstd hP hwf i ν M₂) f (clMatViewMap hstd hP hwf i ν f) (fun _ => rfl) _
    (blackModuleEFEquiv (Pin) (KL).t i ν (clDownwardBlock_reflectedBlack P)
      (ClMatView hstd hP hwf i ν M) hn)
    (blackModuleEFEquiv (Pin) (KL).t i ν (clDownwardBlock_reflectedBlack P)
      (ClMatView hstd hP hwf i ν M₂) hn)
    (fun y => by
      kernel_exact blackModuleEFEquiv_map (Pin) (KL).t i ν (clDownwardBlock_reflectedBlack P)
        (clMatViewMap hstd hP hwf i ν f) hn y) x

/-- **Naturality of `clBlackModuleFEEquiv`**: it carries `Fᵢ Eᵢ f` to `Eᵢ Fᵢ f × f^{-n}`. -/
theorem clBlackModuleFEEquiv_map (f : M →ₗ[(T (Singleton.singleton i + ν : Multiset I))ᵐᵒᵖ] M₂)
    (hn : ip (RDc) i (downRightWeight (RDc) (coordinateRedWeights Λ C) ({i} + ν)) ≤ 0)
    (x : Ind (Res (φi) M) (φi)) :
    clBlackModuleFEEquiv hstd hP hwf i ν M₂ hn (clFEMap i ν f x) =
      (clEFMap i ν f (clBlackModuleFEEquiv hstd hP hwf i ν M hn x).1,
        fun s => f ((clBlackModuleFEEquiv hstd hP hwf i ν M hn x).2 s)) := by
  kernel_exact indResEquivTransport_map (clOpEquiv hstd hP hwf ν)
    (clOpEquiv hstd hP hwf ({i} + ν))
    (clOpEquiv hstd hP hwf ({i} + ({i} + ν))) (clOpEquiv_appendBlack hstd hP hwf i ν)
    (clOpEquiv_appendBlack hstd hP hwf i ({i} + ν)) (toClMatView hstd hP hwf i ν M)
    (toClMatView_smul hstd hP hwf i ν M) (toClMatView hstd hP hwf i ν M₂)
    (toClMatView_smul hstd hP hwf i ν M₂) f (clMatViewMap hstd hP hwf i ν f) (fun _ => rfl) _
    (blackModuleFEEquiv (Pin) (KL).t i ν (clDownwardBlock_reflectedBlack P)
      (ClMatView hstd hP hwf i ν M) hn)
    (blackModuleFEEquiv (Pin) (KL).t i ν (clDownwardBlock_reflectedBlack P)
      (ClMatView hstd hP hwf i ν M₂) hn)
    (fun y => by
      kernel_exact blackModuleFEEquiv_map (Pin) (KL).t i ν (clDownwardBlock_reflectedBlack P)
        (clMatViewMap hstd hP hwf i ν f) hn y) x

end CL

end Categorification.Stendhal
