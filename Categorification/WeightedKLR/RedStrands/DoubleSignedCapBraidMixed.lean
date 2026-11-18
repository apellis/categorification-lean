/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapInterleave
import Categorification.WeightedKLR.RedStrands.DoubleMixedRedCorrection

/-!
# The mixed red braid in a black cap sweep

In the crossing reduction for Webster, arXiv:1309.3796v2, Lemma 4.28,
a signed cap sweep can meet a red strand and an oppositely oriented black
strand. The local braid substitution then has crossing-free correction
terms by the mated ordinary red braid relation (4.1a).
-/
noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe w u v
variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (Λ : Fin ℓ → X)
  {k : Type w} [CommRing k] (P : Presentation.{w,max u v} (signature RD Λ) k)
  (Q : I → I → MvPolynomial (Fin 2) k) (exponents : Fin ℓ → I →₀ ℕ) (t : I → I → k)
  (μ : X) (L : List (DoubleStrand I ℓ)) (r : Fin ℓ) (l u : Letter I) (R : List (DoubleStrand I ℓ))

local notation "Pm" => addRedUpRelations RD Λ k (addRedUpSlideRelations RD Λ
  (addRedCapRelations RD Λ (addRedCupRelations RD Λ P)))
local notation "Pf" => addBlackAdjunctionRelations RD Λ (addMixedCupPitchforkRelations RD Λ (Pm) t)
local notation "Pc" => addDownRelations RD Λ (affineCoverQ Q exponents) (Pf)

/-- Zero-crossing terms lie in every stage of the crossing filtration. -/
theorem crossingFreeSpan_le_signedCrossingSpan (s z : List (DoubleStrand I ℓ)) (n : ℕ) :
    crossingFreeSpan RD Λ μ P s z ≤ signedCrossingSpan RD Λ P μ s z n := by
  apply Submodule.span_mono
  rintro f ⟨d, hd, rfl⟩
  exact ⟨d, hd.le.trans (Nat.zero_le _), rfl⟩

local notation "leftBraid" => fun (x y : DoubleStrand I ℓ) => signedDg RD Λ (Pc) μ (L ++ [x,y,Sum.inl l] ++ R)
  (L ++ [Sum.inl l,y,x] ++ R) (signedCapBraidLeft L x y l R)
local notation "rightBraid" => fun (x y : DoubleStrand I ℓ) => signedDg RD Λ (Pc) μ (L ++ [x,y,Sum.inl l] ++ R)
  (L ++ [Sum.inl l,y,x] ++ R) (signedCapBraidRight L x y l R)
local notation "span₂" => fun (x y : DoubleStrand I ℓ) => signedCrossingSpan RD Λ (Pc) μ (L ++ [x,y,Sum.inl l] ++ R)
  (L ++ [Sum.inl l,y,x] ++ R) 2
local notation "red" => (Sum.inr r : DoubleStrand I ℓ)
local notation "strand" => (Sum.inl u : DoubleStrand I ℓ)

/-- In a cap sweep across a red/black pair, the internal black strand and
the cap leg have opposite orientation. The red mixed braid gives the
required lower-crossing error, also when both black colours agree. -/
theorem signedCapBraid_redBlack_mixed (h : u.1 ≠ l.1) :
    (leftBraid) red strand - (rightBraid) red strand ∈ (span₂) red strand := by
  apply crossingFreeSpan_le_signedCrossingSpan RD Λ (Pc) μ _ _ 2
  obtain ⟨e,i⟩ := l
  obtain ⟨d,j⟩ := u
  cases e <;> cases d
  · exact (h rfl).elim
  · exact mixedRed_triplePoint_mod_crossingFree RD Λ μ L r j R Q exponents P t i .REF
  · exact mixedRed_triplePoint_mod_crossingFree RD Λ μ L r i R Q exponents P t j .RFE
  · exact (h rfl).elim

/-- The cap sweep across a black/red pair has the same crossing bound for
oppositely oriented black strands. -/
theorem signedCapBraid_blackRed_mixed (h : u.1 ≠ l.1) :
    (leftBraid) strand red - (rightBraid) strand red ∈ (span₂) strand red := by
  apply crossingFreeSpan_le_signedCrossingSpan RD Λ (Pc) μ _ _ 2
  obtain ⟨e,i⟩ := l
  obtain ⟨d,j⟩ := u
  cases e <;> cases d
  · exact (h rfl).elim
  · exact mixedRed_triplePoint_mod_crossingFree RD Λ μ L r j R Q exponents P t i .ERF
  · exact mixedRed_triplePoint_mod_crossingFree RD Λ μ L r i R Q exponents P t j .FRE
  · exact (h rfl).elim

end Categorification.Stendhal.DoubleDiagram
