/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCLDownKLR
import Categorification.WeightedKLR.RedStrands.DoubleCLLayerIdealOn
import Categorification.WeightedKLR.RedStrands.DoubleCLRedUp
import Categorification.WeightedKLR.RedStrands.DoubleCLRedDot
import Categorification.Diagrams.CL.NoMix
import Categorification.Diagrams.KL3.SymmetrySigmaSymm

/-!
# Downward KLR relations with at most one red strand

Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29. Under the cover functor, the downward
translation of a KLR diagram with at most one red strand agrees, layer by layer and up to red
dots, with the reflected upward KLR diagram in the Cautis–Lauda presentation of the extended
datum.
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
local notation "RDc" => coordinateDatum Λ C
local notation "hS" => isRouquierQ_cyclotomicCoverQ C Λ Q hQ
local notation "sym" => IsRouquierQ.klrSymm hS
local notation "lead" => IsRouquierQ.polyInY_leading hS
local notation "deg" => IsRouquierQ.polyInY_degree_pair hS Wgt
local notation "Sc" => cyclotomicScalars sym lead Wgt deg
local notation "PCL" => KL3.Diagram.CL.presCL Wgt k Sc

/-- The upward KLR relations with the Cautis–Lauda parameters hold in the Cautis–Lauda
presentation of the extended datum. -/
theorem presCL_cover_klr : CL.KLRHolds PCL (CL.qCL Sc) := by
  intro μ r
  have h := (PCL).lin_rel_self (.inr (.klr μ r))
  have hr' : (fun i => ((CL.CLScalars.r (Sc) i : k))) = fun _ => 1 := funext fun _ => rfl
  change (PCL).lin (upLin Wgt k μ (CL.relationR k (CL.qCL Sc)
    (fun i => ((CL.CLScalars.r (Sc) i : k))) r)) = 0 at h
  rwa [hr', CL.relationR_one] at h

end Categorification.Stendhal
