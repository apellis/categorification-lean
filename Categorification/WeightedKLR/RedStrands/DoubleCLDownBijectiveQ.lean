/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCLDownInjectiveOrdinaryQ
import Categorification.WeightedKLR.RedStrands.DoubleCapSurjectivityQ

/-!
# Webster's Lemma 4.29 for every Kang–Kashiwara family

Webster, arXiv:1309.3796v3, §4.6, Lemma 4.29, for every Kang–Kashiwara family `Q` over a field
(no restriction to the Khovanov–Lauda parameters). The black strands of the all-down block carry
the relations of Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3, Definition 1.1) at the black
scalars `Sb = blackScalarsQ`, and the downward KLR relations use the Cautis–Lauda dual parameters
of `Sb`, which are `Q` on distinct colours. The map `ordinaryToDownwardMatrix` from `T^λ` to the
all-down block is injective (`ordinaryToDownwardMatrix_injectiveQ`) and surjective
(`signedCapKL_ordinaryToDownwardMatrix_surjectiveQ`), so it is an algebra isomorphism
(`ordinaryToDownwardMatrix_bijectiveQ`, `ordinaryToDownwardMatrixEquivQ`).

## Main results

* `ordinaryToDownwardMatrix_bijectiveQ`: Lemma 4.29 at general `Q`.
* `ordinaryToDownwardMatrixEquivQ`: the resulting algebra isomorphism.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory QuantumGroup QuantumGroup.UDot StringDiagrams KLR TwoRep CyclotomicAction
  DoubleDiagram KL3.Diagram Diagrams.BicatInterp KLRAlgebra

universe u v w

open scoped Classical

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type u} {ℓ : ℕ} {Λ : Fin ℓ → I →₀ ℕ} {C : CartanDatum I}
  {k : Type v} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {hQ : IsRouquierQ C Q} {ν : Multiset I}

local notation "Wgt" => cyclotomicCoverWeightDatum Λ C
local notation "L" => cyclotomicCoverHighest (I := I) (ℓ := ℓ)
local notation "wt₀" => (blockWeight Wgt L 0 : I ⊕ Fin ℓ → ℤ)
local notation "RDc" => coordinateDatum Λ C
local notation "Sb" => blackScalarsQ Λ C hQ

/-- **Webster, arXiv:1309.3796v3, Lemma 4.29, for every Kang–Kashiwara family** over a field:
the map `ordinaryToDownwardMatrix` from `T^λ` to the all-down block, whose black strands carry
`U_Q(g)` at the black scalars `Sb` and whose downward relations use the Cautis–Lauda dual
parameters of `Sb` (which are `Q` on distinct colours), is bijective. -/
theorem ordinaryToDownwardMatrix_bijectiveQ
    {P : Presentation.{v, u} (signature (RDc) (redWeight Wgt)) k}
    (hP : CoverRelsNegligible.{u, v, w} Λ C hQ (coverDotCentral Λ C hQ) wt₀ P) (hwf : P.WFDom) :
    Function.Bijective (ordinaryToDownwardMatrix (Λ := coordinateRedWeights Λ C)
      (signedCapPresentationOf (RDc) (redWeight Wgt) (CLQ.pres (RDc) k (Sb)) P
        (clDownwardQ (Sb)) Λ fun i j => ((Sb).t i j : k))
      (clDownwardQ (Sb)) Λ (Sb).t (ν := ν)) :=
  ⟨ordinaryToDownwardMatrix_injectiveQ _ hP hwf,
    DoubleDiagram.signedCapKL_ordinaryToDownwardMatrix_surjectiveQ
      (weights := coordinateRedWeights Λ C) (sc := Sb) (ν := ν) P (clDownwardQ (Sb)) Λ
      (fun i j => ((Sb).t i j : k)) (Sb).t fun r i => (coordinateRedWeights_pair Λ C r i).symm⟩

/-- The algebra isomorphism of Lemma 4.29 (arXiv:1309.3796v3) between `T^λ` and the all-down
block, for every Kang–Kashiwara family over a field. -/
noncomputable def ordinaryToDownwardMatrixEquivQ
    {P : Presentation.{v, u} (signature (RDc) (redWeight Wgt)) k}
    (hP : CoverRelsNegligible.{u, v, w} Λ C hQ (coverDotCentral Λ C hQ) wt₀ P) (hwf : P.WFDom) :=
  AlgEquiv.ofBijective _ (ordinaryToDownwardMatrix_bijectiveQ (ν := ν) hP hwf)

end Categorification.Stendhal
