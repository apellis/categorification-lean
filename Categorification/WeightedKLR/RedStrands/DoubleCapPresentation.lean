/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleBlackPresentation
import Categorification.WeightedKLR.RedStrands.DoubleMixedRedPitchfork
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapInterleave
import Categorification.WeightedKLR.RedStrands.DoubleSpanningQuotient

/-!
# Common presentations for moving a signed cap

Webster, arXiv:1309.3796v3, Definition 4.26 and the proof of Lemma 4.29.
The mixed red braid and passing a cap across red use overlapping families
of local relations. Their union has exactly the
sum of the two ideals. The extension with the reflected KL III relations
also contains the presentation used to normalize real and fake bubbles.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot StringDiagrams

universe u v w

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (Λ : Fin ℓ → X)
  {k : Type w} [CommRing k]

section Transfer

variable (P P' : Presentation.{w, max u v} (signature RD Λ) k)
  (h : ∀ a b : Obj (signature RD Λ), P.ideal a b ≤ P'.ideal a b)
  (μ : X) (s t : List (DoubleStrand I ℓ))

/-- An inclusion of presentation ideals preserves evaluation of signed moves. -/
@[simp] theorem extension_map_signedDg (A : List (SignedLayer I ℓ)) :
    (P.extension P' h).map (signedDg RD Λ P μ s t A) = signedDg RD Λ P' μ s t A := by
  classical
  by_cases ht : signedChain s A t
  · rw [signedDg_of RD Λ P μ ht, signedDg_of RD Λ P' μ ht, Presentation.extension_map_diag]
  · simp [signedDg, ht]

include h in
/-- An equality of signed move lists remains valid after adjoining relations. -/
theorem signedDg_eq_of_ideal_le {A B : List (SignedLayer I ℓ)}
    (he : signedDg RD Λ P μ s t A = signedDg RD Λ P μ s t B) :
    signedDg RD Λ P' μ s t A = signedDg RD Λ P' μ s t B := by
  simpa only [extension_map_signedDg] using congrArg (P.extension P' h).map he

/-- The crossing filtration on a signed Hom maps onto the same stage in the
larger quotient. The raw diagram representatives and crossing bound agree. -/
theorem signedCrossingSpan_map_extension (n : ℕ) :
    (signedCrossingSpan RD Λ P μ s t n).map ((P.extension P' h).mapLinearMap k) =
      signedCrossingSpan RD Λ P' μ s t n := by
  unfold signedCrossingSpan
  rw [Submodule.map_span]
  congr 1
  ext f
  constructor
  · rintro ⟨_, ⟨d, hd, rfl⟩, rfl⟩
    exact ⟨d, hd, rfl⟩
  · rintro ⟨d, hd, rfl⟩
    exact ⟨P.diag d, ⟨d, hd, rfl⟩, rfl⟩

include h in
/-- A crossing bound for the difference of two signed move lists survives
adjoining relations, with the same bound. -/
theorem signedDg_sub_mem_signedCrossingSpan_of_ideal_le {A B : List (SignedLayer I ℓ)} {n : ℕ}
    (hm : signedDg RD Λ P μ s t A - signedDg RD Λ P μ s t B ∈
      signedCrossingSpan RD Λ P μ s t n) :
    signedDg RD Λ P' μ s t A - signedDg RD Λ P' μ s t B ∈
      signedCrossingSpan RD Λ P' μ s t n := by
  let F := (P.extension P' h).mapLinearMap k
    (X := P.obj (obj RD Λ μ s)) (Y := P.obj (obj RD Λ μ t))
  have hf := Submodule.mem_map_of_mem (f := F) hm
  dsimp only [F] at hf
  rw [signedCrossingSpan_map_extension RD Λ P P' h μ s t n] at hf
  change (P.extension P' h).map (signedDg RD Λ P μ s t A - signedDg RD Λ P μ s t B) ∈ _ at hf
  simpa only [Functor.map_sub, extension_map_signedDg] using hf

end Transfer

section CapPresentation

variable (P : Presentation.{w, max u v} (signature RD Λ) k)
  (Q : I → I → MvPolynomial (Fin 2) k) (exponents : Fin ℓ → I →₀ ℕ) (t : I → I → k)

/-- The presentation for the mixed and upward red braid moves, with black
adjunction, red cup and cap relations, and the ordinary downward relations. -/
abbrev signedCapBraidPresentation : Presentation.{w, max u v} (signature RD Λ) k :=
  addDownRelations RD Λ (affineCoverQ Q exponents)
    (addBlackAdjunctionRelations RD Λ (addMixedCupPitchforkRelations RD Λ
      (addRedUpRelations RD Λ k (addRedUpSlideRelations RD Λ
        (addRedCapRelations RD Λ (addRedCupRelations RD Λ P)))) t))

/-- The presentation in which the cap-pass formulas are proved. -/
abbrev signedCapPassPresentation : Presentation.{w, max u v} (signature RD Λ) k :=
  addRedCapRelations RD Λ
    (addDownRelations RD Λ (affineCoverQ Q exponents) (addRedUpRelations RD Λ k P))

/-- The presentation in which the real and fake bubbles adjacent to red are
normalized by the reflected black KL III relations. -/
abbrev signedCapBubblePresentation : Presentation.{w, max u v} (signature RD Λ) k :=
  addDownRelations RD Λ (affineCoverQ Q exponents)
    (addRedUpRelations RD Λ k
      (addRedCapRelations RD Λ (addRedCupRelations RD Λ (addBlackKLRelations RD Λ P))))

local notation "braidP" => signedCapBraidPresentation RD Λ P Q exponents t
local notation "passP" => signedCapPassPresentation RD Λ P Q exponents
local notation "bubbleP" => signedCapBubblePresentation RD Λ P Q exponents

/-- The common presentation for the red braid and cap-pass lemmas. -/
abbrev signedCapPresentation : Presentation.{w, max u v} (signature RD Λ) k :=
  (braidP).union (passP)

/-- The common presentation with the reflected KL III normalization used in
black spans and in the coefficients of the real and fake bubble series. -/
abbrev signedCapKLPresentation : Presentation.{w, max u v} (signature RD Λ) k :=
  (signedCapPresentation RD Λ P Q exponents t).union bubbleP

local notation "capP" => signedCapPresentation RD Λ P Q exponents t
local notation "capKLP" => signedCapKLPresentation RD Λ P Q exponents t

/-- The common cap presentation imposes precisely the sum of its input ideals. -/
theorem signedCapPresentation_ideal (a b : Obj (signature RD Λ)) :
    (capP).ideal a b = (braidP).ideal a b ⊔ (passP).ideal a b :=
  (braidP).union_ideal_eq_sup (passP) a b

/-- The version with reflected KL III is also the least common quotient of
the three stated presentations. -/
theorem signedCapKLPresentation_ideal (a b : Obj (signature RD Λ)) :
    (capKLP).ideal a b = ((braidP).ideal a b ⊔ (passP).ideal a b) ⊔ (bubbleP).ideal a b := by
  rw [show (capKLP).ideal a b = (capP).ideal a b ⊔ (bubbleP).ideal a b from
    (capP).union_ideal_eq_sup (bubbleP) a b, signedCapPresentation_ideal]

theorem signedCapBraid_ideal_le (a b : Obj (signature RD Λ)) :
    (braidP).ideal a b ≤ (capP).ideal a b := by
  rw [signedCapPresentation_ideal]
  exact le_sup_left

theorem signedCapPass_ideal_le (a b : Obj (signature RD Λ)) :
    (passP).ideal a b ≤ (capP).ideal a b := by
  rw [signedCapPresentation_ideal]
  exact le_sup_right

theorem signedCap_ideal_le_KL (a b : Obj (signature RD Λ)) :
    (capP).ideal a b ≤ (capKLP).ideal a b := by
  rw [(capP).union_ideal_eq_sup (bubbleP) a b]
  exact le_sup_left

theorem signedCapBubble_ideal_le_KL (a b : Obj (signature RD Λ)) :
    (bubbleP).ideal a b ≤ (capKLP).ideal a b := by
  rw [(capP).union_ideal_eq_sup (bubbleP) a b]
  exact le_sup_right

/-- Reflection of the black KL relations is available in the normalized
common presentation. This is the hypothesis of the local black braid law. -/
theorem signedCapKL_reflectedBlack (j : (KL3.Diagram.pres RD k).Rel) :
    (capKLP).lin (blackMirrorLinear RD Λ ((KL3.Diagram.pres RD k).rel j)) = 0 := by
  have hB := signedCapBubble_ideal_le_KL RD Λ P Q exponents t
  have he := (Presentation.relationsHold_iff_ideal_le (bubbleP) (capKLP)).mpr hB
  exact he (.inl (.inl (.inl (.inl (.inr j)))))

end CapPresentation

end Categorification.Stendhal.DoubleDiagram
