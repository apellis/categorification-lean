/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCLRelationFamiliesQ
import Categorification.WeightedKLR.RedStrands.DoubleCapPresentationQ
import Categorification.WeightedKLR.RedStrands.DoubleWFDom

/-!
# The downward block with general parameters after the cover functor

Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29, for every Kang–Kashiwara family `Q`.
The downward block is presented by the signed cap presentation in which the black strands carry
the reflected relations of a black presentation `𝔅` (`signedCapPresentationOf`); for general
`Q` this is `U_{Sb}(g)` (Cautis–Lauda, arXiv:1111.1431v3, Definition 1.1, `r = 1`) at the black
scalars `Sb = blackScalarsQ`, with the downward KLR relations at the Cautis–Lauda dual
parameters of `Sb` (which are `Q`), the mixed black relations and the cup pitchforks at `Sb.t`,
and the red/upward bigons. Every relation of this presentation has a cover red-negligible
reflected image, provided the relations of the base presentation do
(`CoverRelsNegligible.downwardBlock_signedCapQ`). There is no hypothesis on `Q`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot StringDiagrams KL3.Diagram

universe u v w

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (Λ : Fin ℓ → X)
  {k : Type w} [CommRing k] (𝔅 : Presentation.{w, max u v} (psig RD) k)
  (P : Presentation.{w, max u v} (signature RD Λ) k)
  (Q : I → I → MvPolynomial (Fin 2) k) (exponents : Fin ℓ → I →₀ ℕ) (t : I → I → k)

variable {RD Λ 𝔅 P}

theorem addBlackRelationsOf_wfDom (h𝔅 : 𝔅.WFDom) (hP : P.WFDom) :
    (addBlackRelationsOf RD Λ 𝔅 P).WFDom :=
  Presentation.addRels_wfDom hP _ _ _ _ fun r => ((blackMirror RD Λ).ok_word (h𝔅 r)).1

theorem signedCapPresentationOf_wfDom (h𝔅 : 𝔅.WFDom) (hP : P.WFDom) :
    (signedCapPresentationOf RD Λ 𝔅 P Q exponents t).WFDom :=
  union_wfDom (union_wfDom
    (addDownRelations_wfDom _ (addBlackAdjunctionRelations_wfDom
      (addMixedCupPitchforkRelations_wfDom _ (addRedUpRelations_wfDom
        (addRedUpSlideRelations_wfDom (addRedCapRelations_wfDom (addRedCupRelations_wfDom hP)))))))
    (addRedCapRelations_wfDom (addDownRelations_wfDom _ (addRedUpRelations_wfDom hP))))
    (addDownRelations_wfDom _ (addRedUpRelations_wfDom (addRedCapRelations_wfDom
      (addRedCupRelations_wfDom (addBlackRelationsOf_wfDom h𝔅 hP)))))

end Categorification.Stendhal.DoubleDiagram

namespace Categorification.Stendhal

open CategoryTheory Bicategory QuantumGroup QuantumGroup.UDot StringDiagrams KLR TwoRep
  CyclotomicAction Diagrams.BicatInterp DoubleDiagram KL3.Diagram

universe u v w

variable {I : Type u} {k : Type v} [Field k] {ℓ : ℕ} {Λ : Fin ℓ → I →₀ ℕ} {C : CartanDatum I}
  [DecidableEq I] {Q : I → I → MvPolynomial (Fin 2) k} {hQ : IsRouquierQ C Q}
  {hc : CoverDotCentral Λ C Q} {o : I ⊕ Fin ℓ → ℤ}

local notation "Wgt" => cyclotomicCoverWeightDatum Λ C
local notation "RDc" => coordinateDatum Λ C
local notation "Sb" => blackScalarsQ Λ C hQ

variable (ho : ∀ i : I, (cyclotomicCoverWeightDatum Λ C).pair
    ((cyclotomicCoverWeightDatum Λ C).iY (Sum.inl i)) o = 0)

include ho

/-- **All relation families of the downward block for general `Q`.** If the relations of a
base presentation `P` have cover red-negligible images, so do all relations of the downward
block built from the signed cap presentation with the reflected relations of `U_{Sb}(g)` at the
black scalars `Sb`: cup pitchforks at `Sb.t`, the downward KLR relations at the Cautis–Lauda
dual parameters of `Sb`, the mixed black relations at `Sb.t` and the red/upward bigons. -/
theorem CoverRelsNegligible.downwardBlock_signedCapQ
    {P : Presentation.{v, u} (signature (RDc) (redWeight Wgt)) k}
    (hP : CoverRelsNegligible.{u, v, w} Λ C hQ hc o P) :
    CoverRelsNegligible.{u, v, w} Λ C hQ hc o
      (DoubleDiagram.addRedUpRelations (RDc) (redWeight Wgt) k
        (DoubleDiagram.addMixedBlackRelations (RDc) (redWeight Wgt) k (Sb).t
          (DoubleDiagram.addDownRelations (RDc) (redWeight Wgt)
            (affineCoverQ (clDownwardQ (Sb)) Λ)
            (signedCapPresentationOf (RDc) (redWeight Wgt) (CLQ.pres (RDc) k (Sb)) P
              (clDownwardQ (Sb)) Λ fun i j => ((Sb).t i j : k))))) := by
  have h₁ := hP.addRedCupRelations.addRedCapRelations.addRedUpSlideRelations.addRedUpRelations
  have h₂ := ((h₁.addMixedCupPitchforkRelationsQ ho).addBlackAdjunctionRelationsQ
    ho).addDownRelationsQ
  have h₃ := (hP.addRedUpRelations.addDownRelationsQ).addRedCapRelations
  have h₄ := (hP.addBlackRelationsQ ho).addRedCupRelations.addRedCapRelations
  have h₅ := (h₄.addRedUpRelations).addDownRelationsQ
  have h₆ := (h₂.union h₃).union h₅
  exact ((h₆.addDownRelationsQ).addMixedBlackRelationsQ ho).addRedUpRelations

end Categorification.Stendhal
