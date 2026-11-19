/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCLCoordinate
import Categorification.WeightedKLR.RedStrands.DoubleCLRedUp

/-!
# Red/upward bigons in the cyclotomic evaluation

Webster, arXiv:1309.3796v3, (4.4e), as used in the proof of Lemma 4.29. The
Cautis–Lauda scalar `t` between a black vertex and a red vertex of the extended
datum is the extremal coefficient of `u^{Λ_r(i)} + v^{…}`, which is one
(`cyclotomicScalars_cover_t_inl_inr`). Hence the reflected image of every
red/upward bigon relation vanishes in the Cautis–Lauda presentation used by
`coverEval` (`coverCL_redUpRel`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory QuantumGroup QuantumGroup.UDot StringDiagrams KLR TwoRep CyclotomicAction
  Diagrams.BicatInterp DoubleDiagram

universe u v w

variable {I : Type u} {k : Type v} [Field k] {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) (C : CartanDatum I)
  [DecidableEq I] {Q : I → I → MvPolynomial (Fin 2) k} (hQ : IsRouquierQ C Q)

local notation "Wgt" => cyclotomicCoverWeightDatum Λ C
local notation "S" => cyclotomicCoverQ C Λ Q
local notation "hS" => isRouquierQ_cyclotomicCoverQ C Λ Q hQ
local notation "sym" => IsRouquierQ.klrSymm hS
local notation "lead" => IsRouquierQ.polyInY_leading hS
local notation "deg" => IsRouquierQ.polyInY_degree_pair hS Wgt
local notation "Sc" => cyclotomicScalars sym lead Wgt deg

/-- The Cautis–Lauda scalar between a black and a red vertex of the extended datum is one. -/
theorem cyclotomicScalars_cover_t_inl_inr (j : I) (r : Fin ℓ) :
    (Sc).t (.inl j) (.inr r) = 1 := by
  have hne : (Sum.inl j : I ⊕ Fin ℓ) ≠ Sum.inr r := Sum.inl_ne_inr
  refine Units.ext ?_
  unfold cyclotomicScalars kkScalars
  dsimp only
  rw [dite_eq_right hne, IsUnit.unit_spec, extremalCoeff]
  exact coeff_dij_cyclotomicCoverQ_inl_inr C Λ Q j r

/-- **The red/upward bigon relations hold in the cyclotomic evaluation**: their reflected image
in the Cautis–Lauda presentation of the extended datum is zero. -/
theorem coverCL_redUpRel (o : I ⊕ Fin ℓ → ℤ) (a : RedUpRelation (I ⊕ Fin ℓ → ℤ) I ℓ) :
    coverCL Λ C hQ o (LinDiagram.of (bareBigon (coordinateDatum Λ C) (redWeight Wgt)
      a.leftWeight a.red a.up a.side) - LinDiagram.of (𝟙 _)) = 0 :=
  coverLin_redUpRel_presCL Wgt (extendedCartanDatum_dot_inl Λ C) o Sc
    (cyclotomicScalars_cover_t_inl_inr Λ C hQ) a

end Categorification.Stendhal
