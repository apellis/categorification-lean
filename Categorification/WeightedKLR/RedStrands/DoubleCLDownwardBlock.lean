/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCLRelationFamilies
import Categorification.WeightedKLR.RedStrands.DoubleCapPresentation
import Categorification.WeightedKLR.RedStrands.DoubleDownCLComparison

/-!
# The downward block relations after the cover functor

Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29. The downward block whose ordinary
diagrams span (`signedCapKL_ordinaryToDownwardMatrix_surjective`) is presented by the signed
cap presentation with reflected KL III black relations, the downward KLR relations, the mixed
black relations and the red/upward bigons. At the standard Khovanov–Lauda scalars, with the
downward KLR relations at the Cautis–Lauda dual parameters, every relation of this
presentation has a cover red-negligible reflected image, provided the relations of the base
presentation do (`CoverRelsNegligible.downwardBlock_signedCapKL`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory Bicategory QuantumGroup QuantumGroup.UDot StringDiagrams KLR TwoRep
  CyclotomicAction Diagrams.BicatInterp DoubleDiagram KL3.Diagram

universe u v w

variable {I : Type u} {k : Type v} [Field k] {ℓ : ℕ} {Λ : Fin ℓ → I →₀ ℕ} {C : CartanDatum I}
  [DecidableEq I] {Q : I → I → MvPolynomial (Fin 2) k} {hQ : IsRouquierQ C Q}
  {hc : CoverDotCentral Λ C Q} {o : I ⊕ Fin ℓ → ℤ}

local notation "Wgt" => cyclotomicCoverWeightDatum Λ C
local notation "RDc" => coordinateDatum Λ C
local notation "KL" => (CL.CLScalars.kl : CL.CLScalars C k)

variable (ho : ∀ i : I, (cyclotomicCoverWeightDatum Λ C).pair
    ((cyclotomicCoverWeightDatum Λ C).iY (Sum.inl i)) o = 0)
  (ht : ∀ i j : I, (cyclotomicScalars (IsRouquierQ.klrSymm (isRouquierQ_cyclotomicCoverQ C Λ Q hQ))
    (IsRouquierQ.polyInY_leading (isRouquierQ_cyclotomicCoverQ C Λ Q hQ))
    (cyclotomicCoverWeightDatum Λ C) (IsRouquierQ.polyInY_degree_pair
      (isRouquierQ_cyclotomicCoverQ C Λ Q hQ) (cyclotomicCoverWeightDatum Λ C))).t
      (Sum.inl i) (Sum.inl j) = 1)
  (hs : ∀ (i j : I) (p q : ℕ), p < C.dij i j → q < C.dij j i → (cyclotomicScalars
    (IsRouquierQ.klrSymm (isRouquierQ_cyclotomicCoverQ C Λ Q hQ))
    (IsRouquierQ.polyInY_leading (isRouquierQ_cyclotomicCoverQ C Λ Q hQ))
    (cyclotomicCoverWeightDatum Λ C) (IsRouquierQ.polyInY_degree_pair
      (isRouquierQ_cyclotomicCoverQ C Λ Q hQ) (cyclotomicCoverWeightDatum Λ C))).s
      (Sum.inl i) (Sum.inl j) p q = 0)

include ho ht hs

/-- **All relation families of the downward block.** If the relations of a base presentation
`P` have cover red-negligible images, so do all relations of the downward block built from
`signedCapKLPresentation P` at the standard KL III scalars: the signed cap presentation with
`tⱼᵢ = 1`, the downward KLR relations at the Cautis–Lauda dual of the standard scalars, the
mixed black relations and the red/upward bigons. -/
theorem CoverRelsNegligible.downwardBlock_signedCapKL
    (hstd : ∀ i j, i ≠ j → Q i j = CL.qCL KL i j)
    {P : Presentation.{v, u} (signature (RDc) (redWeight Wgt)) k}
    (hP : CoverRelsNegligible.{u, v, w} Λ C hQ hc o P) :
    CoverRelsNegligible.{u, v, w} Λ C hQ hc o
      (DoubleDiagram.addRedUpRelations (RDc) (redWeight Wgt) k
        (DoubleDiagram.addMixedBlackRelations (RDc) (redWeight Wgt) k (KL).t
          (DoubleDiagram.addDownRelations (RDc) (redWeight Wgt)
            (affineCoverQ (clDownwardQ KL) Λ)
            (signedCapKLPresentation (RDc) (redWeight Wgt) P (clDownwardQ KL) Λ
              fun _ _ => 1)))) := by
  have h₁ := hP.addRedCupRelations.addRedCapRelations.addRedUpSlideRelations.addRedUpRelations
  have h₂ := ((h₁.addMixedCupPitchforkRelations ho ht hs).addBlackAdjunctionRelations
    ho ht hs).addDownRelations_kl hstd
  have h₃ := (hP.addRedUpRelations.addDownRelations_kl hstd).addRedCapRelations
  have h₄ := (hP.addBlackKLRelations ho ht hs).addRedCupRelations.addRedCapRelations
  have h₅ := (h₄.addRedUpRelations).addDownRelations_kl hstd
  have h₆ := (h₂.union h₃).union h₅
  exact ((h₆.addDownRelations_kl hstd).addMixedBlackRelations_kl ho ht hs).addRedUpRelations

end Categorification.Stendhal
