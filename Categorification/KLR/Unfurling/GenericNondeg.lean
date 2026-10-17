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
and `N+1`. The categorical scalar bubble law is proved at those levels.
`calculusNondeg_of_symmetrizer` has only the positive invertible symmetrizer
hypotheses required by direct unfurling; `calculusNondeg_charZero` supplies
them from the Cartan datum. No evaluation, scalar-law, basis-image, coordinate,
action-relation or weight-transport hypothesis occurs in these conclusions.
The general Cartan scope follows Webster; KL III states nondegeneracy in type A.
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

/-- The generic evaluation with every categorical scalar law supplied. -/
def unfurledEval (μ : X) {ν : Multiset I} (i j : Seq ν) (N : ℕ) :
    UnfurledEval RD k μ i j N :=
  unfurledEvalOfScalarLaw k RD d hdpos hd hsym μ i j N
    (bubbleScalarLaw_proved k RD μ ν.card (N+1) (N+1) d hdpos hd hsym
      (Nat.succ_pos N))

include d hdpos hd hsym in
/-- KL nondegeneracy over a field with an invertible positive symmetrizer.
This is the intermediate direct-unfurling result in Webster's proof; the
characteristic restriction is removed by rational-to-integral descent. -/
theorem calculusNondeg_of_symmetrizer [Finite I] : CalculusNondeg RD k :=
  calculusNondeg_of_unfurledEval fun μ _ i j N =>
    ⟨unfurledEval k RD d hdpos hd hsym μ i j N⟩

/-- Characteristic-zero KL nondegeneracy, using positive diagonal Cartan
lengths as the explicit power-series symmetrizer. No evaluation or scalar
bubble law is assumed. -/
theorem calculusNondeg_charZero [Finite I] [CharZero k] : CalculusNondeg RD k := by
  obtain ⟨d, hdpos, hd, hsym⟩ := exists_symmetrizer_of_charZero (C := C) (k := k)
  exact calculusNondeg_of_symmetrizer k RD d hdpos hd hsym

end Categorification.KLR.Unfurling.GenericFields
