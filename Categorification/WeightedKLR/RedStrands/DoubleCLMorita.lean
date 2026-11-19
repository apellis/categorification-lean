/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCLDownInjectiveOrdinary
import Categorification.WeightedKLR.RedStrands.DoubleProjective

/-!
# The Morita equivalence between `T^λ` and `DT^λ`

Webster, arXiv:1309.3796v3, §4.6, Theorem 4.30, at the standard Khovanov–Lauda black
parameters over a field, with the downward KLR relations at the Cautis–Lauda dual parameters
(the repair of Lemma 4.29 recorded in the README).

`DT^λ` is the violating quotient of the double Stendhal diagrams in the fibre of the right
weight `λ - ν`, presented by the downward block `clDownwardBlock P`. The theorem has two parts.
* Lemma 4.29: `T^λ` is the endomorphism ring of the sum of the all-down boundaries
  (`clToDownwardMatrixKLEquiv` composed with `downwardMatrixEquivEnd`).
* The idempotent of every signed boundary factors through all-down boundaries, so the
  all-down inclusion is an equivalence on additive idempotent completions
  (`allDownCompletionInclusion_isEquivalence_addRelations`).
Webster states the Morita equivalence for the algebras; here it is the equivalence of the
idempotent completions of the additive envelopes, the form in which `DT^λ` is a category.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory QuantumGroup QuantumGroup.UDot StringDiagrams KLR TwoRep CyclotomicAction
  DoubleDiagram KL3.Diagram Diagrams.BicatInterp KLRAlgebra

open scoped Classical

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe u v w

variable {I : Type u} {ℓ : ℕ} {Λ : Fin ℓ → I →₀ ℕ} {C : CartanDatum I}
  {k : Type v} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {hQ : IsRouquierQ C Q}

local notation "Wgt" => cyclotomicCoverWeightDatum Λ C
local notation "wt₀" => (blockWeight Wgt (cyclotomicCoverHighest (I := I) (ℓ := ℓ)) 0 :
  I ⊕ Fin ℓ → ℤ)
local notation "RDc" => coordinateDatum Λ C
local notation "KL" => (CL.CLScalars.kl : CL.CLScalars C k)

variable (Λ C) in
/-- The presentation of `DT^λ` at the standard Khovanov–Lauda black parameters: the signed cap
presentation over `P`, the downward KLR relations at the Cautis–Lauda dual parameters, the
mixed black relations (2.3c), (2.4a), and the red/upward relations (4.4e). -/
abbrev clDownwardBlock (P : Presentation.{v, u} (signature (RDc) (redWeight Wgt)) k) :=
  addRedUpRelations (RDc) (Subtype.val ∘ coordinateRedWeights Λ C) k
    (addMixedBlackRelations (RDc) (Subtype.val ∘ coordinateRedWeights Λ C) k (KL).t
      (addDownRelations (RDc) (Subtype.val ∘ coordinateRedWeights Λ C)
        (affineCoverQ (clDownwardQ KL) Λ)
        (signedCapKLPresentation (RDc) (redWeight Wgt) P (clDownwardQ KL) Λ fun _ _ => 1)))

/-- **Webster, arXiv:1309.3796v3, Theorem 4.30, repaired**, at the standard Khovanov–Lauda
parameters over a field: `T^λ` is the endomorphism ring of the sum of the all-down boundaries
of `DT^λ`, and the inclusion of the all-down boundaries induces an equivalence of the
idempotent completions of the additive envelopes. -/
theorem clTensorProduct_moritaEquivalent (ν : Multiset I)
    (hstd : ∀ i j, i ≠ j → Q i j = CL.qCL KL i j)
    {P : Presentation.{v, u} (signature (RDc) (redWeight Wgt)) k}
    (hP : CoverRelsNegligible.{u, v, w} Λ C hQ (coverDotCentral Λ C hQ) wt₀ P)
    (hwf : P.WFDom) :
    Nonempty (TensorProductAlgebra k (CL.qCL KL) Λ ν ≃+*
        End (downSum (clDownwardBlock Λ C P) ν)) ∧
      (allDownCompletionInclusion (clDownwardBlock Λ C P)
        (right := downRightWeight (RDc) (coordinateRedWeights Λ C) ν)).IsEquivalence :=
  ⟨⟨(clToDownwardMatrixKLEquiv (ν := ν) hstd hP hwf).toRingEquiv.trans
      (downwardMatrixEquivEnd _ ν)⟩,
    allDownCompletionInclusion_isEquivalence_addRelations _ _⟩

end Categorification.Stendhal
