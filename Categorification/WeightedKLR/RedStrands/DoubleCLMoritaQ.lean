/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCLDownBijectiveQ
import Categorification.WeightedKLR.RedStrands.DoubleCLMorita
import Categorification.WeightedKLR.RedStrands.TensorRescale

/-!
# The Morita equivalence between `T^λ` and `DT^λ` for every Kang–Kashiwara family

Webster, arXiv:1309.3796v3, §4.6, Theorem 4.30, over a field for every homogeneous Rouquier
(Kang–Kashiwara) family `Q`. `DT^λ` is presented by the downward block `clDownwardBlockQ P`:
the signed cap presentation over `P` whose black strands carry Cautis–Lauda's `U_Q(g)`
(arXiv:1111.1431v3, Definition 1.1) at the black scalars `Sb = blackScalarsQ`, the downward
KLR relations at the Cautis–Lauda dual parameters of `Sb` (equal to `Q` off the diagonal), the
mixed black relations (2.3c), (2.4a) at `Sb.t`, and the red/upward relations (4.4e).
* Lemma 4.29: `T^λ(Q)` is the endomorphism ring of the sum of the all-down boundaries
  (`ordinaryToDownwardMatrixEquivQ`, after identifying `T^λ(Q)` with `T^λ` at the dual
  parameters, which agree with `Q` off the diagonal).
* The all-down inclusion is an equivalence on additive idempotent completions
  (`allDownCompletionInclusion_isEquivalence_addRelations`).
As at the Khovanov–Lauda parameters (`clTensorProduct_moritaEquivalent`), Webster states the
equivalence for algebras; here `DT^λ` is a category and the statement is the equivalence of the
idempotent completions of the additive envelopes.
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
local notation "Sb" => blackScalarsQ Λ C hQ

variable (Λ C hQ) in
/-- The presentation of `DT^λ` for a Kang–Kashiwara family `Q`: the signed cap presentation over
`P` with `U_Q(g)` black relations at `Sb`, the downward KLR relations at the Cautis–Lauda dual
parameters of `Sb`, the mixed black relations (2.3c), (2.4a) at `Sb.t`, and the red/upward
relations (4.4e). -/
abbrev clDownwardBlockQ (P : Presentation.{v, u} (signature (RDc) (redWeight Wgt)) k) :=
  addRedUpRelations (RDc) (Subtype.val ∘ coordinateRedWeights Λ C) k
    (addMixedBlackRelations (RDc) (Subtype.val ∘ coordinateRedWeights Λ C) k (Sb).t
      (addDownRelations (RDc) (Subtype.val ∘ coordinateRedWeights Λ C)
        (affineCoverQ (clDownwardQ (Sb)) Λ)
        (signedCapPresentationOf (RDc) (redWeight Wgt) (CLQ.pres (RDc) k (Sb)) P
          (clDownwardQ (Sb)) Λ fun i j => ((Sb).t i j : k))))

/-- `T^λ(Q)` is `T^λ` at the Cautis–Lauda dual parameters of the black scalars, which agree
with `Q` off the diagonal. -/
def tensorProductBlackScalarsEquiv (ν : Multiset I) :
    TensorProductAlgebra k Q Λ ν ≃ₐ[k] TensorProductAlgebra k (clDownwardQ (Sb)) Λ ν :=
  tensorRescale Λ ν (s := fun _ _ => 1) (fun _ => rfl) fun a b h => by
    rw [clDownwardQ_blackScalarsQ Λ C hQ h, mul_one, Units.val_one, map_one, one_mul]

/-- **Webster, arXiv:1309.3796v3, Theorem 4.30, for every Kang–Kashiwara family** over a field:
`T^λ(Q)` is the endomorphism ring of the sum of the all-down boundaries of `DT^λ` (presented by
`clDownwardBlockQ`), and the inclusion of the all-down boundaries induces an equivalence of the
idempotent completions of the additive envelopes. -/
theorem tensorProduct_moritaEquivalentQ (ν : Multiset I)
    {P : Presentation.{v, u} (signature (RDc) (redWeight Wgt)) k}
    (hP : CoverRelsNegligible.{u, v, w} Λ C hQ (coverDotCentral Λ C hQ) wt₀ P)
    (hwf : P.WFDom) :
    Nonempty (TensorProductAlgebra k Q Λ ν ≃+*
        End (downSum (clDownwardBlockQ Λ C hQ P) ν)) ∧
      (allDownCompletionInclusion (clDownwardBlockQ Λ C hQ P)
        (right := downRightWeight (RDc) (coordinateRedWeights Λ C) ν)).IsEquivalence :=
  ⟨⟨(tensorProductBlackScalarsEquiv ν).toRingEquiv.trans
      ((ordinaryToDownwardMatrixEquivQ (ν := ν) hP hwf).toRingEquiv.trans
        (downwardMatrixEquivEnd _ ν))⟩,
    allDownCompletionInclusion_isEquivalence_addRelations _ _⟩

end Categorification.Stendhal
