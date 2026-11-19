/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCLRepeatedRed
import Categorification.WeightedKLR.RedStrands.DoubleCLRedNegligibleIdeal

/-!
# Repeated red strands are cover red-negligible

Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29. A morphism of the Cautis–Lauda
presentation of the extended datum into a word containing an upward red strand of one colour
twice (and no downward strand of that colour) lands, on every admissible component, in blocks
that vanish on red-bounded inputs; so it is cover red-negligible
(`coverRedNegligible_of_repeated_red`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v w

namespace Categorification.Stendhal

open CategoryTheory Bicategory QuantumGroup QuantumGroup.UDot StringDiagrams KLR TwoRep
  CyclotomicAction Diagrams.BicatInterp DoubleDiagram KL3.Diagram

variable {I : Type u} {k : Type v} [Field k] {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) (C : CartanDatum I)
  [DecidableEq I] {Q : I → I → MvPolynomial (Fin 2) k} (hQ : IsRouquierQ C Q)
  (hc : CoverDotCentral Λ C Q)

local notation "Wgt" => cyclotomicCoverWeightDatum Λ C
local notation "hS" => isRouquierQ_cyclotomicCoverQ C Λ Q hQ
local notation "sym" => IsRouquierQ.klrSymm hS
local notation "lead" => IsRouquierQ.polyInY_leading hS
local notation "deg" => IsRouquierQ.polyInY_degree_pair hS Wgt
local notation "Sc" => cyclotomicScalars sym lead Wgt deg
local notation "PCL" => KL3.Diagram.CL.presCL Wgt k Sc

/-- **A morphism into a word with an upward red strand of the same colour twice, and no
downward strand of that colour, is cover red-negligible.** Its components land in blocks
containing that red colour twice. -/
theorem coverRedNegligible_of_repeated_red {c d : Obj (psig Wgt)} (φ : (PCL).obj c ⟶ (PCL).obj d)
    (r : Fin ℓ) (htwo : 2 ≤ d.word.countP fun col => col.l = (true, Sum.inr r))
    (hdown : ∀ col ∈ d.word, col.l ≠ (false, Sum.inr r)) :
    CoverRedNegligible.{u, v, w} Λ C hQ hc φ := fun {_ _} _ hb =>
  RedNegligible.of_zeroBelow _ ⟨r, rfl⟩ fun M =>
    (zeroBelow_word sym lead (cyclotomicCoverPolynomial_monic (k := k))
      (cyclotomicCoverPolynomial_natDegree (k := k) Λ C) deg d.word hb.1 hb.2.1 hdown
      (zeroBelow_zero _ M)).mono (by rw [zero_add]; exact htwo)

end Categorification.Stendhal
