/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCLRedNegligibleIdeal

/-!
# Upward red dots are cover red-negligible

Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29. A layer of the Cautis–Lauda
presentation of the extended datum whose generator acts red-negligibly on the cyclotomic weight
spaces, and whose strands to the left of the generator are upward or black, is cover
red-negligible (`coverRedNegligible_diag_layer`). In particular a dot on an upward red strand is
cover red-negligible (`coverRedNegligible_redDot`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory Bicategory QuantumGroup QuantumGroup.UDot StringDiagrams KLR TwoRep
  CyclotomicAction Diagrams.BicatInterp DoubleDiagram KL3.Diagram

universe u v w

variable {I : Type u} {k : Type v} [Field k] {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) (C : CartanDatum I)
  [DecidableEq I] {Q : I → I → MvPolynomial (Fin 2) k} (hQ : IsRouquierQ C Q)
  (hc : CoverDotCentral Λ C Q)

local notation "Wgt" => cyclotomicCoverWeightDatum Λ C
local notation "hS" => isRouquierQ_cyclotomicCoverQ C Λ Q hQ
local notation "sym" => IsRouquierQ.klrSymm hS
local notation "lead" => IsRouquierQ.polyInY_leading hS
local notation "deg" => IsRouquierQ.polyInY_degree_pair hS Wgt
local notation "Sc" => cyclotomicScalars sym lead Wgt deg
local notation "L" => cyclotomicCoverHighest (I := I) (ℓ := ℓ)
set_option quotPrecheck false in
set_option hygiene false in
local notation "Fam" => cyclotomicFamily.{u, v, w} sym lead
  (cyclotomicCoverPolynomial_monic (k := k)) Wgt L (cyclotomicCoverPolynomial_natDegree (k := k) Λ C) deg
local notation "PCL" => KL3.Diagram.CL.presCL Wgt k Sc

/-- **A layer with a red-negligible generator is cover red-negligible**, provided the strands to
the left of its generator are upward or black. -/
theorem coverRedNegligible_diag_layer (Ly : Layer (psig Wgt)) (hv : Ly.Valid)
    (hl : ∀ c ∈ Ly.left, RedAllowed (Set.range (Sum.inr : Fin ℓ → I ⊕ Fin ℓ)) c)
    (hgen : ∀ m n ha hb hd hde hcd hce,
      CoverRed.{u, v, w} Λ C hQ hc
        ((RouqFamily.genImg Fam Sc).gen Ly.gen m n ha hb hd hde hcd hce)) :
    CoverRedNegligible.{u, v, w} Λ C hQ hc ((PCL).diag (Diagram.ofLayer Ly hv)) := by
  intro s t ha hb
  change CoverRed.{u, v, w} Λ C hQ hc
    (admissibleMap (RouqFamily.genImg Fam Sc) ha hb (LinDiagram.of (Diagram.ofLayer Ly hv)))
  rw [admissibleMap_of, admissibleInterp_layer, coreC_eq]
  unfold core
  refine CoverRed.comp_left _ (CoverRed.comp_right _ ?_)
  unfold CoverRed midK
  refine RedNegligible.whiskerLeft _ ?_
  exact RedNegligible.whiskerRight_word sym lead (cyclotomicCoverPolynomial_monic (k := k)) _ deg
    _ _ _ _ _ hl (hgen _ _ _ _ _ _ _ _)

/-- **A dot on an upward red strand is cover red-negligible**, in any context whose strands to
the left of the dot are upward or black. -/
theorem coverRedNegligible_redDot (Ly : Layer (psig Wgt)) (hv : Ly.Valid) (r : Fin ℓ)
    (x : I ⊕ Fin ℓ → ℤ) (hg : Ly.gen = .gen (.dot ⟨(true, Sum.inr r), x⟩))
    (hl : ∀ c ∈ Ly.left, RedAllowed (Set.range (Sum.inr : Fin ℓ → I ⊕ Fin ℓ)) c) :
    CoverRedNegligible.{u, v, w} Λ C hQ hc ((PCL).diag (Diagram.ofLayer Ly hv)) := by
  refine coverRedNegligible_diag_layer Λ C hQ hc Ly hv hl ?_
  obtain ⟨st, lf, g, rt⟩ := Ly
  dsimp only at hg
  subst hg
  intro m n ha hb hd hde hcd hce
  exact redNegligible_globalDot (hc := hc) (Rd := Set.range Sum.inr) ⟨r, rfl⟩ _

end Categorification.Stendhal
