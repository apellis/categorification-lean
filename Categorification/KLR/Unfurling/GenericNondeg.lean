/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Unfurling.GenericEvaluation
/-!
# The nondegeneracy consumer of the constructed generic evaluation

Webster, arXiv:1603.06311v3, theorem labelled `nondegenerate`, “Triviality
of a relation”; KL III, arXiv:0807.3250v1, Theorem 1.2.

The strand, bubble and truncation levels are fixed here as `ν.card`, `N+1`
and `N+1`. The sole remaining input is the categorical scalar bubble law
at those levels. No evaluation, basis-image, coordinate, action-relation
or weight-transport hypothesis is assumed. The field nondegeneracy result
with that scalar-law input discharged is a subsequent specialization.
-/

noncomputable section
namespace Categorification.KLR.Unfurling.GenericFields
open QuantumGroup QuantumGroup.UDot KL3.Diagram
universe u v w
variable {I : Type u} [DecidableEq I] (k : Type v) [Field k]
  {C : CartanDatum I} {X Y : Type w} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y)
  (d : I → ℕ) (hdpos : ∀ i, 0 < d i) (hd : ∀ i, (d i : k) ≠ 0)
  (hsym : ∀ i j, C.dot i j ≠ 0 → (d i : ℤ) * C.dot j j = d j * C.dot i i)

/-- Choose all finite levels for the concrete evaluation. -/
def unfurledEvalOfScalarLaw (μ : X) {ν : Multiset I} (i j : Seq ν) (N : ℕ)
    (hb : bubbleScalarLaw k RD μ ν.card (N+1) (N+1) d hdpos hd hsym) :
    UnfurledEval RD k μ i j N :=
  evaluationFromScalar k RD μ ν.card (N+1) (N+1) d hdpos hd hsym
    i j le_rfl N (Nat.le_succ N) (Nat.le_succ N) hb

/-- Consume the constructed generic representations to obtain KL nondegeneracy. -/
theorem calculusNondeg_of_scalarLaw [Finite I]
    (hb : ∀ (μ : X) (s N : ℕ),
      bubbleScalarLaw k RD μ s (N+1) (N+1) d hdpos hd hsym) :
    CalculusNondeg RD k :=
  calculusNondeg_of_unfurledEval fun μ ν i j N =>
    ⟨unfurledEvalOfScalarLaw k RD d hdpos hd hsym μ i j N (hb μ ν.card N)⟩

end Categorification.KLR.Unfurling.GenericFields
