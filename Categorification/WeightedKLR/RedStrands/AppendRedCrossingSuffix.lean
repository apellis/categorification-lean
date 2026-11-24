/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.AppendRedCrossingTest
import Categorification.WeightedKLR.RedStrands.RightmostRedCrossingInjectivity

/-!
# Crossing injectivity through a finite red suffix

Webster, arXiv:1309.3796v2, Lemma 5.23 and its use at (6.21).
The ordinary injectivity test for the rightmost crossing remains injective
after appending any finite list of uncrossed red strands.
-/

namespace Categorification.Stendhal

open KLR KLRAlgebra
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type} [DecidableEq I] [Field k] {ℓ : ℕ}

/-- Two red-ordered loadings and the position of the crossing tested between them. -/
structure OrderedCrossingTest (ℓ : ℕ) (content : Multiset I) where
  top : Seq (stendhalWeight ℓ content)
  bottom : Seq (stendhalWeight ℓ content)
  top_ordered : IsRedOrdered top
  bottom_ordered : IsRedOrdered bottom
  index : ℕ
  index_valid : index + 1 < (stendhalWeight ℓ content).card

namespace OrderedCrossingTest

variable {θ : Multiset I} (c : OrderedCrossingTest ℓ θ)

/-- The crossing test in the ordinary ordered algebra of a fixed red order. -/
def InjectiveAt (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) : Prop :=
  ∀ x : TensorProductAlgebra k Q Λ θ,
    x * tensorOfKLR Q Λ θ (e c.top) = x →
    x * tensorOfKLR Q Λ θ (ψ c.index * e c.bottom) = 0 →
    x = 0

/-- Append the same uncrossed red strand to both loadings. -/
def appendRed : OrderedCrossingTest (ℓ + 1) θ where
  top := appendRedLoading c.top
  bottom := appendRedLoading c.bottom
  top_ordered := (appendRedLoading_ordered_iff _).2 c.top_ordered
  bottom_ordered := (appendRedLoading_ordered_iff _).2 c.bottom_ordered
  index := c.index
  index_valid := c.index_valid.trans_le (by simp [stendhalWeight])

/-- Append a finite suffix of uncrossed red strands to the crossing test. -/
def appendReds : (n : ℕ) → OrderedCrossingTest (ℓ + n) θ
  | 0 => c
  | n + 1 => (appendReds n).appendRed

/-- The weights of the original red strands, after omitting the appended suffix. -/
def prefixWeights : (n : ℕ) → (Fin (ℓ + n) → I →₀ ℕ) → Fin ℓ → I →₀ ℕ
  | 0, Λ => Λ
  | n + 1, Λ => prefixWeights n (Λ ∘ Fin.castSucc)

variable (Q : I → I → MvPolynomial (Fin 2) k)

private theorem appendReds_injectiveAt_of_step
    (step : ∀ (m : ℕ) (d : OrderedCrossingTest m θ) (Λ : Fin (m + 1) → I →₀ ℕ),
      d.InjectiveAt Q (Λ ∘ Fin.castSucc) → d.appendRed.InjectiveAt Q Λ)
    (n : ℕ) (Λ : Fin (ℓ + n) → I →₀ ℕ) (h : c.InjectiveAt Q (prefixWeights n Λ)) :
    (c.appendReds n).InjectiveAt Q Λ := by
  induction n with
  | zero => exact h
  | succ n ih =>
    exact step (ℓ + n) (c.appendReds n) Λ (ih (Λ ∘ Fin.castSucc) h)

private theorem appendRed_injectiveAt_of_content_eq
    {content : Multiset I} (hcontent : θ + 0 = content) {m : ℕ}
    (hQ : KLRSymm Q) (d : OrderedCrossingTest m content) (Λ : Fin (m + 1) → I →₀ ℕ)
    (h : d.InjectiveAt Q (Λ ∘ Fin.castSucc)) : d.appendRed.InjectiveAt Q Λ := by
  subst content
  exact eq_zero_of_mul_appendRedCrossing Q Λ θ hQ
    d.top d.bottom d.top_ordered d.bottom_ordered d.index d.index_valid h

/-- The ordinary crossing test survives appending any finite red suffix. -/
theorem injectiveAt_appendReds (hQ : KLRSymm Q)
    (n : ℕ) (Λ : Fin (ℓ + n) → I →₀ ℕ) (h : c.InjectiveAt Q (prefixWeights n Λ)) :
    (c.appendReds n).InjectiveAt Q Λ := by
  apply appendReds_injectiveAt_of_step c Q _ n Λ h
  intro m d weights hstep
  exact appendRed_injectiveAt_of_content_eq Q (add_zero θ) hQ d weights hstep

/-- The crossing of a final red with a single black next to the prefix. -/
def rightmost (i : I) (θ : Multiset I) (s : Seq (stendhalWeight ℓ (θ + 0))) (hs : IsRedOrdered s) :
    OrderedCrossingTest (ℓ + 1) ({i} + (θ + 0)) where
  top := appendRedLoading (appendBlackLoading i (θ + 0) s)
  bottom := appendBlackLoading i (θ + 0) (appendRedLoading s)
  top_ordered :=
    (appendRedLoading_ordered_iff _).2 (appendBlackLoading_ordered i (θ + 0) s hs)
  bottom_ordered :=
    appendBlackLoading_ordered i (θ + 0) _ ((appendRedLoading_ordered_iff s).2 hs)
  index := (stendhalWeight ℓ (θ + 0)).card
  index_valid := by simp [stendhalWeight]

section Standard

open QuantumGroup KL3.Diagram

variable {D : CartanDatum I}
local notation "QL" => CL.qCL (CL.CLScalars.kl : CL.CLScalars D k)

/-- At standard parameters the rightmost crossing stays injective with any
number of red spectators appended on its right. -/
theorem rightmost_appendReds_standard (hR : IsRouquierQ D QL) (hQ : KLRSymm QL)
    (i : I) (θ : Multiset I) (s : Seq (stendhalWeight ℓ (θ + 0))) (hs : IsRedOrdered s)
    (n : ℕ) (Λ : Fin (ℓ + 1 + n) → I →₀ ℕ) :
    ((rightmost i θ s hs).appendReds n).InjectiveAt QL Λ :=
  (rightmost i θ s hs).injectiveAt_appendReds QL hQ n Λ
    (eq_zero_of_mul_rightmostRedCrossing (k := k) (C := D) (ℓ := ℓ)
      hR hQ (prefixWeights n Λ) i θ s hs)

end Standard

end OrderedCrossingTest

end Categorification.Stendhal
