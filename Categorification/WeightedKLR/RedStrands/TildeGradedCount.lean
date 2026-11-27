/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PrependRedStandardDegree

/-!
# The graded dimension identity for `T̃^λ e(s)`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
Corollary 5.23, the dimension count in a fixed degree. Webster obtains the count for `T̃^λ`
from the one for `T^λ` by adding a red strand of sufficiently dominant label `λ₀` on the left:
in a fixed degree this changes neither the projective `T̃^λ e(s)` nor the standard modules.
Here: for `λ₀` large relative to the degrees involved,

`dim (T̃^λ e(s))_n = ∑_φ dim (S̃_t)_{n - deg x_φ}`,

the sum running over the block assignments `φ` of `λ₀ s`, where `t` is the loading with
`φ • (λ₀ s) = λ₀ t`; the assignments whose bottom does not begin with `λ₀` contribute zero
(`finrank_tilde_lIdeal_grade_eq_sum`). Route hypothesis: `AllFiniteDeltaInjective`, as for
`phiLayerEquiv`.

## Main definitions

* `tildeTerm`: the contribution of a loading of `T^{(λ₀, λ)}`.

## Main results

* `stdGradedRank_eq_tildeTerm`, `finrank_tilde_lIdeal_grade_eq_sum`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR DirectSum _root_.Categorification.Graded _root_.Module TypeA Equiv

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I)
  (G : KLR.GradingDatum (stendhalQ Q Λ))

local notation "μ" => stendhalWeight ℓ ν
local notation "μ'" => stendhalWeight (ℓ + 1) ν
local notation "G₀" => restrictFirstRedGrading Q Λ G

open Classical in
/-- The contribution of a red-ordered loading `t'` of `T^{(λ₀, λ)}`: the degree-`m` dimension
of the standard module `S̃_t` of `T̃^λ` when `t' = λ₀ t`, and zero otherwise. -/
def tildeTerm (G' : KLR.GradingDatum (stendhalQ Q (Λ ∘ Fin.succ))) (t' : Seq μ')
    (ht' : IsRedOrdered t') (m : ℤ) : ℕ :=
  if h : ∃ t, prependRedLoading t = t' then
    tildeStdGradedRank Q Λ ν G' h.choose
      ((prependRedLoading_ordered_iff _).1 (by rw [h.choose_spec]; exact ht')) m
  else 0

private theorem stdGradedRank_congr {t₁ t₂ : Seq μ'} (h : t₁ = t₂) (h₁ : IsRedOrdered t₁)
    (h₂ : IsRedOrdered t₂) (m : ℤ) :
    stdGradedRank G t₁ h₁ m = stdGradedRank G t₂ h₂ m := by
  subst h
  rfl

/-- For `λ₀` large relative to `m`, the degree-`m` dimension of `S_{t'}` is the contribution
`tildeTerm` of `t'`. -/
theorem stdGradedRank_eq_tildeTerm {c m : ℤ} (hc : ∀ m' < -c, allOrdersGrade G₀ ν m' = ⊥)
    (hΛ : ∀ i ∈ ν, m + 2 * c < Λ 0 i * G.degX (.inl i)) (t' : Seq μ') (ht' : IsRedOrdered t') :
    stdGradedRank G t' ht' m = tildeTerm Q Λ ν G₀ t' ht' m := by
  classical
  rw [tildeTerm]
  split_ifs with h
  · rw [tildeStdGradedRank_eq Q Λ ν G hc hΛ]
    exact stdGradedRank_congr Q Λ ν G h.choose_spec.symm _ _ m
  · push Not at h
    have h0 := seqIdem_eq_zero_of_not_prepend Q Λ ν t' ht' h
    have hbot : (lIdeal (seqIdem Q Λ t' ht')).restrictScalars k ⊓ tensorProductGrade G ν m =
        ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      have hy' : y * seqIdem Q Λ t' ht' = y := hy.1
      rw [h0, mul_zero] at hy'
      exact (Submodule.mem_bot k).2 hy'.symm
    rw [stdGradedRank, hbot, finrank_bot, Nat.zero_sub]

/-- **Graded dimension identity for `T̃^λ e(s)`** (Webster, arXiv:1309.3796v3, Corollary 5.23,
the count in degree `n`). Let the grading of all red orders of `T̃^λ` vanish below `-c`, and let
`⟨α_i^∨, λ₀⟩ · deg x_i > N + 2c` for every black label `i`, where `N` bounds `n` and every
`n - deg x_φ`. Then `dim (T̃^λ e(s))_n` is the sum, over the block assignments `φ` of `λ₀ s`,
of the degree-`(n - deg x_φ)` dimensions of the standard modules `S̃_t` with
`φ • (λ₀ s) = λ₀ t`. Route hypothesis: `AllFiniteDeltaInjective`, as for `phiLayerEquiv`. -/
theorem finrank_tilde_lIdeal_grade_eq_sum {C : QuantumGroup.CartanDatum I} (hQ : KLRSymm Q)
    (hR : IsRouquierQ C Q)
    (hall : ∀ (n : ℕ) (Λ' : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective Q Λ' hQ)
    (ρ : Perm (Fin (Multiset.card μ')) → List ℕ)
    (hρ : ∀ w : Perm (Fin (Multiset.card μ')),
      TypeA.IsReduced (Multiset.card μ') (ρ w) ∧ TypeA.wordProd (Multiset.card μ') (ρ w) = w)
    {c N n : ℤ} (hc : ∀ m' < -c, allOrdersGrade G₀ ν m' = ⊥)
    (hΛ : ∀ i ∈ ν, N + 2 * c < Λ 0 i * G.degX (.inl i)) (s : Seq μ) (hs : IsRedOrdered s)
    (hnN : n ≤ N)
    (hN : ∀ g : PhiIndex (prependRedLoading s),
      n - G.degW (ρ (phiPerm (prependRedLoading s) g.1)) (prependRedLoading s) ≤ N) :
    finrank k ((lIdeal (StendhalAlgebra.e s hs)).restrictScalars k ⊓ stendhalGrade G₀ ν n :) =
      ∑ g : PhiIndex (prependRedLoading s),
        tildeTerm Q Λ ν G₀ (phiBottom (prependRedLoading s) g.1)
          (g.isRedOrdered ((prependRedLoading_ordered_iff s).2 hs))
          (n - G.degW (ρ (phiPerm (prependRedLoading s) g.1)) (prependRedLoading s)) := by
  have hle : ∀ m ≤ N, ∀ i ∈ ν, m + 2 * c < Λ 0 i * G.degX (.inl i) :=
    fun m hm i hi => lt_of_le_of_lt (by omega) (hΛ i hi)
  rw [finrank_lIdeal_grade_prependRed Q Λ ν G hc (hle n hnN) s hs,
    finrank_lIdeal_grade_eq_sum G hQ hR hall ρ hρ ((prependRedLoading_ordered_iff s).2 hs) n]
  exact Finset.sum_congr rfl fun g _ =>
    stdGradedRank_eq_tildeTerm Q Λ ν G hc (hle _ (hN g)) _ _

end Categorification.Stendhal
