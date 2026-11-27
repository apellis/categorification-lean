/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongTransportNaturality
import Categorification.WeightedKLR.RedStrands.DoubleCLBlackActionQ
import Categorification.WeightedKLR.RedStrands.BlackModuleEFTransportQ
import Categorification.WeightedKLR.RedStrands.BlackModuleNaturalityQ
import Categorification.TwoRep.KernelExact

/-!
# Naturality of the commutation of `Eᵢ` and `Fᵢ` on modules over `T^λ`

The isomorphisms `Eᵢ Fᵢ M ≅ Fᵢ Eᵢ M ⊕ M^{⊕ n}` (`clBlackModuleEFEquivQ`) and
`Fᵢ Eᵢ M ≅ Eᵢ Fᵢ M ⊕ M^{⊕ -n}` (`clBlackModuleFEEquivQ`) of right modules over the tensor
product algebra `T^λ` (Webster, arXiv:1309.3796v3, Thm 4.31 on modules, at standard
Khovanov–Lauda black scalars) are natural in the module (`clBlackModuleEFEquiv_mapQ`,
`clBlackModuleFEEquiv_mapQ`). This makes them compatible with an action on `M` commuting with
`T^λ`, as used for the tensor factors in the proof of Proposition 5.5 there.

This is the version of `BlackModuleEFTransportNaturality` in which the black strands carry the relations of
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
  (i : I) (ν : Multiset I)
  {M M₂ : Type u} [AddCommGroup M] [AddCommGroup M₂]
  [Module (TensorProductAlgebra k (Q) Λ ({i} + ν))ᵐᵒᵖ M]
  [Module (TensorProductAlgebra k (Q) Λ
    ({i} + ν))ᵐᵒᵖ M₂]

local notation "PD" => clDownwardBlockQ Λ C hQ P

local notation "Pin" => addDownRelations (RDc) (Subtype.val ∘ coordinateRedWeights Λ C)
  (affineCoverQ (clDownwardQ KL) Λ) (signedCapPresentationOf (RDc) (redWeight (cyclotomicCoverWeightDatum Λ C)) (CLQ.pres (RDc) k KL) P (clDownwardQ KL) Λ fun i j => (CL.CLScalars.t KL i j : k))

local notation "φo" => appendBlackOp (Q) Λ i (Singleton.singleton i + ν)
local notation "φi" => appendBlackOp (Q) Λ i ν

/-- A module map of right `T^λ_{i+ν}`-modules, as a map of their matrix-ring views. -/
def clMatViewMapQ (f : M →ₗ[(T ({i} + ν))ᵐᵒᵖ] M₂) :
    ClMatViewQ hP hwf i ν M →ₗ[(downwardMatrix (PD) ({i} + ν))ᵐᵒᵖ]
      ClMatViewQ hP hwf i ν M₂ where
  toFun := f
  map_add' := f.map_add
  map_smul' t m := f.map_smul ((clOpEquivQ hP hwf ({i} + ν)).symm t) m

/-- `Fᵢ f` for a map `f` of right `T^λ_{i+ν}`-modules. -/
def clIndMapQ (f : M →ₗ[(T ({i} + ν))ᵐᵒᵖ] M₂) := Ind.map (φ := φo) f

/-- `Eᵢ f` for a map `f` of right `T^λ_{i+ν}`-modules. -/
def clResMapQ (f : M →ₗ[(T ({i} + ν))ᵐᵒᵖ] M₂) := Res.map (φ := φi) (M := M) (M' := M₂) f

/-- `Eᵢ Fᵢ f` for a map `f` of right `T^λ_{i+ν}`-modules. -/
def clEFMapQ (f : M →ₗ[(T ({i} + ν))ᵐᵒᵖ] M₂) := Res.map (φ := φo) (clIndMapQ i ν f)

/-- `Fᵢ Eᵢ f` for a map `f` of right `T^λ_{i+ν}`-modules. -/
def clFEMapQ (f : M →ₗ[(T ({i} + ν))ᵐᵒᵖ] M₂) := Ind.map (φ := φi) (clResMapQ i ν f)

/-- **Naturality of `clBlackModuleEFEquivQ`**: it carries `Eᵢ Fᵢ f` to `Fᵢ Eᵢ f × f^n`. -/
theorem clBlackModuleEFEquiv_mapQ (f : M →ₗ[(T (Singleton.singleton i + ν : Multiset I))ᵐᵒᵖ] M₂)
    (hn : 0 ≤ ip (RDc) i (downRightWeight (RDc) (coordinateRedWeights Λ C) ({i} + ν)))
    (x : Res (φo) (Ind M (φo))) :
    clBlackModuleEFEquivQ hP hwf i ν M₂ hn (clEFMapQ i ν f x) =
      (clFEMapQ i ν f (clBlackModuleEFEquivQ hP hwf i ν M hn x).1,
        fun s => f ((clBlackModuleEFEquivQ hP hwf i ν M hn x).2 s)) := by
  kernel_exact resIndEquivTransport_map (clOpEquivQ hP hwf ν)
    (clOpEquivQ hP hwf ({i} + ν))
    (clOpEquivQ hP hwf ({i} + ({i} + ν))) (clOpEquiv_appendBlackQ hP hwf i ν)
    (clOpEquiv_appendBlackQ hP hwf i ({i} + ν)) (toClMatViewQ hP hwf i ν M)
    (toClMatView_smulQ hP hwf i ν M) (toClMatViewQ hP hwf i ν M₂)
    (toClMatView_smulQ hP hwf i ν M₂) f (clMatViewMapQ hP hwf i ν f) (fun _ => rfl) _
    (blackModuleEFEquivQ (Pin) (CL.CLScalars.t KL) i ν (clDownwardBlockQ_reflectedBlack P)
      (ClMatViewQ hP hwf i ν M) hn)
    (blackModuleEFEquivQ (Pin) (CL.CLScalars.t KL) i ν (clDownwardBlockQ_reflectedBlack P)
      (ClMatViewQ hP hwf i ν M₂) hn)
    (fun y => by
      kernel_exact blackModuleEFEquiv_mapQ (Pin) (CL.CLScalars.t KL) i ν (clDownwardBlockQ_reflectedBlack P)
        (clMatViewMapQ hP hwf i ν f) hn y) x

/-- **Naturality of `clBlackModuleFEEquivQ`**: it carries `Fᵢ Eᵢ f` to `Eᵢ Fᵢ f × f^{-n}`. -/
theorem clBlackModuleFEEquiv_mapQ (f : M →ₗ[(T (Singleton.singleton i + ν : Multiset I))ᵐᵒᵖ] M₂)
    (hn : ip (RDc) i (downRightWeight (RDc) (coordinateRedWeights Λ C) ({i} + ν)) ≤ 0)
    (x : Ind (Res (φi) M) (φi)) :
    clBlackModuleFEEquivQ hP hwf i ν M₂ hn (clFEMapQ i ν f x) =
      (clEFMapQ i ν f (clBlackModuleFEEquivQ hP hwf i ν M hn x).1,
        fun s => f ((clBlackModuleFEEquivQ hP hwf i ν M hn x).2 s)) := by
  kernel_exact indResEquivTransport_map (clOpEquivQ hP hwf ν)
    (clOpEquivQ hP hwf ({i} + ν))
    (clOpEquivQ hP hwf ({i} + ({i} + ν))) (clOpEquiv_appendBlackQ hP hwf i ν)
    (clOpEquiv_appendBlackQ hP hwf i ({i} + ν)) (toClMatViewQ hP hwf i ν M)
    (toClMatView_smulQ hP hwf i ν M) (toClMatViewQ hP hwf i ν M₂)
    (toClMatView_smulQ hP hwf i ν M₂) f (clMatViewMapQ hP hwf i ν f) (fun _ => rfl) _
    (blackModuleFEEquivQ (Pin) (CL.CLScalars.t KL) i ν (clDownwardBlockQ_reflectedBlack P)
      (ClMatViewQ hP hwf i ν M) hn)
    (blackModuleFEEquivQ (Pin) (CL.CLScalars.t KL) i ν (clDownwardBlockQ_reflectedBlack P)
      (ClMatViewQ hP hwf i ν M₂) hn)
    (fun y => by
      kernel_exact blackModuleFEEquiv_mapQ (Pin) (CL.CLScalars.t KL) i ν (clDownwardBlockQ_reflectedBlack P)
        (clMatViewMapQ hP hwf i ν f) hn y) x

end CL

end Categorification.Stendhal
