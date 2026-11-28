/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721WindowMid
import Categorification.WeightedKLR.Rigidity.CupCapMidGenerators

/-!
# The appended diagrams at the maximum as a left multiple

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, for a cap not at the right end (`j < ℓ`). In the model of `K̃^{λ⁺}_λ` the
idempotent `e(t)` of a loading `t` of `λ` acts through the window idempotent `E_t` of `λ⁺`
(`CupCap.midIdem`). The diagrams at the maximum with a black strand appended at the right are the
diagrams at the maximum at the black weight `{i} + ν`, cut on the left by the window idempotents
of the appended loadings `s i` (`CupCap.appendPlus_midMapKLR_eq_mul`): on the left this is the
action of `𝔉_i`'s idempotent `e' = ∑_s e(s i)` of `T̃^λ` in the model.

## Main results

* `CupCap.appendPlus_midMapKLR_eq_mul`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)
  (j : ℕ) (hj : j ≤ ℓ) (ν ν₀ : Multiset I) (i : I)

local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)

/-- **The appended diagrams at the maximum** (arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21), for `j < ℓ`: appending a black strand `i` at the right of `midMapKLR x` gives
`midMapKLR x` at the black weight `{i} + ν`, multiplied on the left by the window idempotents of
the appended loadings `s i`. -/
theorem appendPlus_midMapKLR_eq_mul (h : j < ℓ)
    (x : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) :
    appendPlus Q Λ Λc j hj ν ν₀ i (midMapKLR j hj Q Λ Λc ν ν₀ x) =
      (∑ s : Seq (stendhalWeight ℓ ν), midIdem j hj Q Λ Λc νᵢ ν₀ (appendBlackLoading i ν s)) *
        midMapKLR j hj Q Λ Λc νᵢ ν₀ x := by
  rw [appendPlus_midMapKLR_of_lt Q Λ Λc j hj ν ν₀ i h, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  exact (eSum_mul_midMapKLR (appendBlackLoading i ν s) x).symm

end Categorification.Stendhal.CupCap
