/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.AppendRedCrossingTest
import Categorification.WeightedKLR.RedStrands.FiveSlotLeftTopPrincipal
import Categorification.WeightedKLR.RedStrands.TwoRedCrossingInjectivity

/-!
# The five-slot ordinary crossing test at standard parameters

Webster, arXiv:1309.3796v2, Lemma 5.23 and the proof of Lemma 6.8 at (6.21).
The maximal loading and its neighboring retained loading are obtained by
appending the spectator red to the two-red crossing.
-/

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR KLRAlgebra TypeA QuantumGroup KL3.Diagram

local notation "ν₀" => ({()} + {()} : Multiset Unit)
local notation "μ" => stendhalWeight 3 ν₀
local notation "v₀" => fixedTopFourExitCut 0
local notation "jA" => sadj (Multiset.card μ) 2 • v₀

private abbrev θ : Multiset Unit := {()}
private def oneRedPrefix : Seq (stendhalWeight 1 (θ + 0)) :=
  KLRAlgebra.Seq.ofList [.inr 0, .inl ()] (by decide)
private theorem prefix_ordered : IsRedOrdered oneRedPrefix := by unfold IsRedOrdered; decide
private abbrev lowHigh := appendRedLoading (appendBlackLoading () (θ + 0) oneRedPrefix)
private abbrev lowSource := appendBlackLoading () (θ + 0) (appendRedLoading oneRedPrefix)
private theorem appendLowHigh : appendRedLoading lowHigh = v₀ := by
  apply Subtype.ext; funext a; fin_cases a <;> decide
private theorem appendLowSource : appendRedLoading lowSource = jA := by
  apply Subtype.ext; funext a; fin_cases a <;> decide

variable {F : Type} [Field F] {C : CartanDatum Unit}

local notation "QL" => CL.qCL (CL.CLScalars.kl : CL.CLScalars C F)
private abbrev ν : Multiset Unit := ({()} : Multiset Unit) + (θ + 0)

/-- The ordinary right-multiplication test at the next retained five-slot crossing. -/
theorem fiveSlotNextRetained_rightMultiplication_eq_zero
    (hR : IsRouquierQ C QL) (hQ : KLRSymm QL) (Λ : Fin 3 → Unit →₀ ℕ)
    (x : TensorProductAlgebra F QL Λ ν₀)
    (hx : x * tensorOfKLR QL Λ _ (e v₀) = x)
    (hc : x * tensorOfKLR QL Λ _ (ψ 2 * e jA) = 0) : x = 0 := by
  let x' : TensorProductAlgebra F QL Λ (ν + 0) := x
  have hx' : x * tensorOfKLR QL Λ ν₀ (e (appendRedLoading lowHigh)) = x :=
    (congrArg (fun t : Seq μ => x * tensorOfKLR QL Λ ν₀ (e t)) appendLowHigh).trans hx
  let cross : KLRAlgebra F (stendhalQ QL Λ) μ := ψ 2
  have hc' : x * tensorOfKLR QL Λ ν₀ (cross * e (appendRedLoading lowSource)) = 0 :=
    (congrArg (fun t : Seq μ => x * tensorOfKLR QL Λ ν₀ (cross * e t)) appendLowSource).trans hc
  exact eq_zero_of_mul_appendRedCrossing QL Λ ν hQ lowHigh lowSource
    ((appendRedLoading_ordered_iff _).2 (appendBlackLoading_ordered () (θ + 0) _ prefix_ordered))
    (appendBlackLoading_ordered () (θ + 0) _ ((appendRedLoading_ordered_iff _).2 prefix_ordered))
    2 (by decide)
    (eq_zero_of_mul_secondRedCrossing_at_right hR hQ (Λ ∘ Fin.castSucc) () θ oneRedPrefix prefix_ordered)
    x' hx' hc'

end Categorification.Stendhal.BraidedStendhalAlgebra
