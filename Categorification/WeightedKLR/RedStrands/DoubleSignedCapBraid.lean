/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCapPresentation
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapInsideInduction
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapBraidBlack
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapBraidDown
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapBraidUp
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapBraidMixed

/-!
# The interior crossing of a signed cap block

Webster, arXiv:1309.3796v2, §4.5, Lemma 4.28, using the cap elimination from
Khovanov–Lauda III, arXiv:0807.3250v1, Proposition 3.11. In the common
presentation with reflected black KL relations, every admissible interior
crossing has the required three-strand move modulo at most two crossings.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe w u v
variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (Λ : Fin ℓ → X)
  {k : Type w} [CommRing k] (P : Presentation.{w,max u v} (signature RD Λ) k)
  (Q : I → I → MvPolynomial (Fin 2) k) (exponents : Fin ℓ → I →₀ ℕ) (t : I → I → k)
  (μ : X) (L : List (DoubleStrand I ℓ)) (x y : DoubleStrand I ℓ) (l : Letter I)
  (R : List (DoubleStrand I ℓ))

local notation "U" => addRedUpRelations RD Λ k (addRedUpSlideRelations RD Λ
  (addRedCapRelations RD Λ (addRedCupRelations RD Λ P)))
local notation "B" => addBlackAdjunctionRelations RD Λ (addMixedCupPitchforkRelations RD Λ (U) t)
local notation "braidP" => signedCapBraidPresentation RD Λ P Q exponents t
local notation "capP" => signedCapKLPresentation RD Λ P Q exponents t

private theorem hasCapBraidBound_to_KL (h : HasCapBraidBound RD Λ (braidP) μ L x y l R) :
    HasCapBraidBound RD Λ (capP) μ L x y l R := by
  exact signedDg_sub_mem_signedCrossingSpan_of_ideal_le RD Λ (braidP) (capP)
    (fun a b => (signedCapBraid_ideal_le RD Λ P Q exponents t a b).trans
      (signedCap_ideal_le_KL RD Λ P Q exponents t a b)) μ _ _ h

/-- An admissible crossing inside the cap block satisfies the local
Reidemeister III crossing bound in the reflected KL normalization. -/
theorem signedCapKL_hasCapBraidBound (h : CanCross x y) :
    HasCapBraidBound RD Λ (capP) μ L x y l R := by
  rcases x with a | r
  · rcases y with b | r
    · exact signedCapBraid_black RD Λ (capP) (signedCapKL_reflectedBlack RD Λ P Q exponents t)
        μ L R a b l
    · apply hasCapBraidBound_to_KL RD Λ P Q exponents t
      obtain ⟨ε,i⟩ := a
      obtain ⟨δ,j⟩ := l
      cases ε <;> cases δ
      · exact signedCapBraid_blackRed_down RD Λ (B) Q exponents μ L R r i j
      · exact signedCapBraid_blackRed_mixed RD Λ P Q exponents t μ L r (true,j) (false,i) R (by simp)
      · exact signedCapBraid_blackRed_mixed RD Λ P Q exponents t μ L r (false,j) (true,i) R (by simp)
      · exact signedCapBraid_blackRed_up RD Λ P Q exponents t μ L r i j R
  · rcases y with b | s
    · apply hasCapBraidBound_to_KL RD Λ P Q exponents t
      obtain ⟨ε,i⟩ := b
      obtain ⟨δ,j⟩ := l
      cases ε <;> cases δ
      · exact signedCapBraid_redBlack_down RD Λ (B) Q exponents μ L R r i j
      · exact signedCapBraid_redBlack_mixed RD Λ P Q exponents t μ L r (true,j) (false,i) R (by simp)
      · exact signedCapBraid_redBlack_mixed RD Λ P Q exponents t μ L r (false,j) (true,i) R (by simp)
      · exact signedCapBraid_redBlack_up RD Λ P Q exponents t μ L r i j R
    · exact h.elim

end Categorification.Stendhal.DoubleDiagram
