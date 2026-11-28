/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.RigidityExtHead

/-!
# The coevaluation labels at the dual weight

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.22 (gap (c)). The S-move pairs a module over the red labels `(λ, λ*)` with one
over `(λ*, λ)`. The coevaluation standard module of Lemma 7.3 is set up with the labels
`coevaluationLabels ν = (λ, λ*)`, where `λ*` is read off the black weight `ν` as
`⟨α_i^∨, λ*⟩ = -⟨α_i^∨, λ - ν⟩` (`dualRedLabel`). The other order comes from the same
construction at the highest weight `λ' = ν - λ`: its dual label at the same black weight `ν`
is `-⟨α_i^∨, λ' - ν⟩ = ⟨α_i^∨, λ⟩`, i.e. `λ` again. For the coevaluation word of `w₀`,
`ν = λ - w₀λ`, so `λ' = -w₀λ = λ*` and `ν = λ* - w₀λ*` is also the black weight of the
coevaluation word of `λ*` (as an element of the weight lattice; the word itself differs).

The identity is formal (it uses only the additivity of the pairing). The rest of the bookkeeping
for the X side of the S-move is in the library: the reversed divided coevaluation word `d.reverse`
is the divided coevaluation word of `λ*` along the reversed reduced expression
(`Stendhal.coevaluationDividedWord_reverse`), with the same black weight `ν`, and
`pair_dualHighest_coevaluation` identifies `⟨α_i^∨, ν - λ⟩` with `⟨α_i^∨, -w₀λ⟩`, which is
nonnegative (the hypothesis of `dualHighest_pair`). So the X-side module `L` over `(λ*, λ)` is the
coevaluation head of Lemma 7.3 at the highest weight `dualHighest RD highest ν`, the labels
`dualRedLabel RD highest ν`, and the word `d.reverse`.

## Main results

* `dualRedLabel_dualHighest`: the dual label of `ν - λ` at `ν` is `λ`.
* `dualHighest_pair`: `⟨α_i^∨, ν - λ⟩` is the dual label `λ*_i` when it is nonnegative.
* `coevaluationLabels_dualHighest`: the coevaluation labels at `ν - λ` are `(λ*, λ)`.
-/

noncomputable section

namespace Categorification.KLR.CycKLR

open QuantumGroup QuantumGroup.UDot

variable {I : Type} [Fintype I] {C : CartanDatum I} (Λ : I → ℕ)
    {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y)
    (highest : X) (hΛ : ∀ i, (Λ i : ℤ) = RD.pair (RD.iY i) highest)

/-- The highest weight `ν - λ` of the dual coevaluation: for the coevaluation word of `w₀`
this is `λ* = -w₀λ`. -/
def dualHighest (ν : Multiset I) : X := (ν.map RD.iX).sum - highest

include hΛ in
/-- **The dual label of the dual is the original label**: the dual red label of the highest
weight `ν - λ` at the black weight `ν` is `λ`. -/
theorem dualRedLabel_dualHighest (ν : Multiset I) :
    dualRedLabel RD (dualHighest RD highest ν) ν = Finsupp.equivFunOnFinite.symm Λ := by
  ext i
  simp only [dualRedLabel, dualHighest, Finsupp.coe_equivFunOnFinite_symm,
    sub_sub_cancel_left, map_neg, neg_neg]
  rw [← hΛ i, Int.toNat_natCast]

/-- **The pairing with the dual highest weight** is the dual red label, when the latter is
read without truncation: if `⟨α_i^∨, λ - ν⟩ ≤ 0` for all `i` (`λ*` dominant), then
`⟨α_i^∨, ν - λ⟩ = λ*_i`. This is the hypothesis `hΛ` of the coevaluation results at `λ*`. -/
theorem dualHighest_pair (ν : Multiset I)
    (hdom : ∀ i, RD.pair (RD.iY i) (highest - (ν.map RD.iX).sum) ≤ 0) (i : I) :
    ((dualRedLabel RD highest ν i : ℕ) : ℤ) = RD.pair (RD.iY i) (dualHighest RD highest ν) := by
  simp only [dualRedLabel, dualHighest, Finsupp.coe_equivFunOnFinite_symm]
  rw [Int.toNat_of_nonneg (by linarith [hdom i]), ← map_neg, neg_sub]

include hΛ in
/-- **The coevaluation labels at the dual highest weight** are `(λ*, λ)`: the first label is
`λ*` (the labels `dualRedLabel RD highest ν`, which satisfy the hypothesis `hΛ` at `ν - λ` by
`dualHighest_pair`) and the second is `λ` (`dualRedLabel_dualHighest`). -/
theorem coevaluationLabels_dualHighest (ν : Multiset I) :
    coevaluationLabels (fun i => dualRedLabel RD highest ν i) RD (dualHighest RD highest ν) ν =
      ![dualRedLabel RD highest ν, Finsupp.equivFunOnFinite.symm Λ] := by
  rw [coevaluationLabels, dualRedLabel_dualHighest Λ RD highest hΛ]
  congr 1

end Categorification.KLR.CycKLR
