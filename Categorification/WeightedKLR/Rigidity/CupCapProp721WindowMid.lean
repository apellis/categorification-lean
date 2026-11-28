/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721Window
import Categorification.WeightedKLR.Rigidity.CupCapMidDescent

/-!
# Appending a black strand and the diagrams at the maximum at `midPos`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21. In the model of `K̃^{λ⁺}_λ` (`CupCap.MidModel`) the diagrams at the maximum are
placed, below the cap generators at every loading `s` of `λ`, on the window at `midPos s`, just
before the red strand `λ_{j+1}` (`CupCap.midMapKLR`). Appending a black strand of colour `i` at the
right of these diagrams gives the diagrams on the same windows below the cap generators at the
appended loadings `s i` (`CupCap.appendPlus_midMapKLR`). When the cap is not at the right end
(`j < ℓ`) the appended strand lies right of `λ_{j+1}`, so these windows are again at `midPos (s i)`
(`CupCap.midPos_appendBlackLoading`, `CupCap.appendPlus_midMapKLR_of_lt`). When `j = ℓ` the window
at `midPos (s i)` lies right of the new strand, and the two placements differ by passing the new
strand under the window; that case is Webster's use of (max1) and (max2) and is not treated here.

## Main results

* `CupCap.midPos_appendBlackLoading`: for `j < ℓ`, `midPos (s i) = midPos s`.
* `CupCap.appendPlus_midMapKLR`: appending the strand to `midMapKLR`, any `j`.
* `CupCap.appendPlus_midMapKLR_of_lt`: the same with the windows at `midPos (s i)`, for `j < ℓ`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)
  (j : ℕ) (hj : j ≤ ℓ) (ν ν₀ : Multiset I) (i : I)

local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "m" => Multiset.card (stendhalWeight ℓ ν)

/-- Appending the black strand at the right keeps the position of the red strand `λ_{j+1}`,
for `j < ℓ`. -/
theorem midPos_appendBlackLoading (h : j < ℓ) (s : Seq (stendhalWeight ℓ ν)) :
    midPos j (appendBlackLoading i ν s) = midPos j s := by
  obtain ⟨a, ha, hla⟩ := midPos_of_lt j s h
  obtain ⟨b, hb, hlb⟩ := midPos_of_lt j (appendBlackLoading i ν s) h
  have hm := card_appendBlackWeight (ℓ := ℓ) (ν := ν) (i := i)
  have hab : b = ⟨a.val, by omega⟩ := by
    refine lbl_eq_inr_unique hlb ?_
    rw [appendBlackLoading_lbl_of_lt i ν s _ a.2]
    exact hla
  rw [← hb, ← ha, hab]

omit [DecidableEq I] in
theorem midPos_le_appendBlackLoading (s : Seq (stendhalWeight ℓ ν)) :
    midPos j s ≤ Multiset.card (stendhalWeight ℓ νᵢ) := by
  have hm := card_appendBlackWeight (ℓ := ℓ) (ν := ν) (i := i)
  have := midPos_le j s
  omega

/-- **Appending a black strand to the diagrams at the maximum** (arXiv:1309.3796v3, §7.3, proof
of Proposition 7.21): the diagram `midMapKLR x` with a black strand appended at the right is the
sum, over the loadings `s` of `λ`, of the diagrams on the window at `midPos s` below the cap
generators at the appended loadings `s i`. -/
theorem appendPlus_midMapKLR (x : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) :
    appendPlus Q Λ Λc j hj ν ν₀ i (midMapKLR j hj Q Λ Λc ν ν₀ x) =
      ∑ s : Seq (stendhalWeight ℓ ν), insertMap (j := j) (hj := hj) Q Λ Λc
        (appendBlackLoading i ν s) (midPos j s) (midPos_le_appendBlackLoading j ν i s) x := by
  rw [midMapKLR, map_sum]
  exact Finset.sum_congr rfl fun s _ => appendPlus_insertMap s _ _ _ x

/-- For a cap not at the right end (`j < ℓ`): the diagram `midMapKLR x` with a black strand
appended at the right is the sum, over the appended loadings `s i`, of the diagrams on the window
at `midPos (s i)`. -/
theorem appendPlus_midMapKLR_of_lt (h : j < ℓ)
    (x : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) :
    appendPlus Q Λ Λc j hj ν ν₀ i (midMapKLR j hj Q Λ Λc ν ν₀ x) =
      ∑ s : Seq (stendhalWeight ℓ ν), insertMap (j := j) (hj := hj) Q Λ Λc
        (appendBlackLoading i ν s) (midPos j (appendBlackLoading i ν s))
          (midPos_le j (appendBlackLoading i ν s)) x := by
  rw [appendPlus_midMapKLR]
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 1
  exact (midPos_appendBlackLoading j ν i h s).symm

end Categorification.Stendhal.CupCap
