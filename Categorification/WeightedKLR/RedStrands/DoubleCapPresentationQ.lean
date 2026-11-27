/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCapPresentation
import Categorification.WeightedKLR.RedStrands.DoubleBlackSuffixQ

/-!
# Common presentations for moving a signed cap, for a general black presentation

Webster, arXiv:1309.3796v3, Definition 4.27 and the proof of Lemma 4.29, with the black strands
carrying the reflected relations of an arbitrary black presentation `𝔅`
(`signedCapPresentationOf`), in particular of Cautis–Lauda's `U_Q(g)`
(`signedCapKLPresentationQ`, `𝔅 = CLQ.pres RD k sc`). For `𝔅` the KL III presentation this
is `signedCapKLPresentation`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot StringDiagrams KL3.Diagram

universe u v w

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (Λ : Fin ℓ → X)
  {k : Type w} [CommRing k] (sc : CL.CLScalars C k) (𝔅 : Presentation.{w, max u v} (psig RD) k)
  (P : Presentation.{w, max u v} (signature RD Λ) k)
  (Q : I → I → MvPolynomial (Fin 2) k) (exponents : Fin ℓ → I →₀ ℕ) (t : I → I → k)

/-- The presentation in which real and fake bubbles adjacent to red are normalized by the
reflected relations of a black presentation `𝔅`. -/
abbrev signedCapBubblePresentationOf : Presentation.{w, max u v} (signature RD Λ) k :=
  addDownRelations RD Λ (affineCoverQ Q exponents)
    (addRedUpRelations RD Λ k
      (addRedCapRelations RD Λ (addRedCupRelations RD Λ (addBlackRelationsOf RD Λ 𝔅 P))))

/-- The common signed cap presentation with the reflected relations of a black presentation
`𝔅` (for `𝔅` the KL III presentation this is `signedCapKLPresentation`). -/
abbrev signedCapPresentationOf : Presentation.{w, max u v} (signature RD Λ) k :=
  (signedCapPresentation RD Λ P Q exponents t).union
    (signedCapBubblePresentationOf RD Λ 𝔅 P Q exponents)

theorem signedCapOf_ideal_le (a b : Obj (signature RD Λ)) :
    (signedCapPresentation RD Λ P Q exponents t).ideal a b ≤
      (signedCapPresentationOf RD Λ 𝔅 P Q exponents t).ideal a b := by
  rw [(signedCapPresentation RD Λ P Q exponents t).union_ideal_eq_sup
    (signedCapBubblePresentationOf RD Λ 𝔅 P Q exponents) a b]
  exact le_sup_left

theorem signedCapBubbleOf_ideal_le (a b : Obj (signature RD Λ)) :
    (signedCapBubblePresentationOf RD Λ 𝔅 P Q exponents).ideal a b ≤
      (signedCapPresentationOf RD Λ 𝔅 P Q exponents t).ideal a b := by
  rw [(signedCapPresentation RD Λ P Q exponents t).union_ideal_eq_sup
    (signedCapBubblePresentationOf RD Λ 𝔅 P Q exponents) a b]
  exact le_sup_right

/-- The reflected relations of `𝔅` hold in the common presentation. -/
theorem signedCapOf_reflectedBlack (j : 𝔅.Rel) :
    (signedCapPresentationOf RD Λ 𝔅 P Q exponents t).lin
      (blackMirrorLinear RD Λ (𝔅.rel j)) = 0 := by
  have hB := signedCapBubbleOf_ideal_le RD Λ 𝔅 P Q exponents t
  have he := (Presentation.relationsHold_iff_ideal_le
    (signedCapBubblePresentationOf RD Λ 𝔅 P Q exponents)
    (signedCapPresentationOf RD Λ 𝔅 P Q exponents t)).mpr hB
  exact he (.inl (.inl (.inl (.inl (.inr j)))))

/-- The common signed cap presentation with the reflected relations of `U_Q(g)`. -/
abbrev signedCapKLPresentationQ : Presentation.{w, max u v} (signature RD Λ) k :=
  signedCapPresentationOf RD Λ (CLQ.pres RD k sc) P Q exponents t

theorem signedCap_ideal_le_KLQ (a b : Obj (signature RD Λ)) :
    (signedCapPresentation RD Λ P Q exponents t).ideal a b ≤
      (signedCapKLPresentationQ RD Λ sc P Q exponents t).ideal a b :=
  signedCapOf_ideal_le RD Λ _ P Q exponents t a b

theorem signedCapKL_reflectedBlackQ (j : (CLQ.pres RD k sc).Rel) :
    (signedCapKLPresentationQ RD Λ sc P Q exponents t).lin
      (blackMirrorLinear RD Λ ((CLQ.pres RD k sc).rel j)) = 0 :=
  signedCapOf_reflectedBlack RD Λ _ P Q exponents t j

end Categorification.Stendhal.DoubleDiagram
