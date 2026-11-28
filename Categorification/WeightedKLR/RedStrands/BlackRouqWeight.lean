/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.CoordinateWeightPairing
import Categorification.KLR.CyclotomicAction.Global

/-!
# The Brundan weight of a block of `T^λ`

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §4.6 and §5.1;
Brundan, arXiv:1501.00350v1, Definition 1.1. Rouquier's local data at a weight `b` are taken at
the integer `⟨h_i, b⟩` (`TwoRep.RouqFamily.loc`). For the weight-indexed generators of
`blackRouqData` a content `β` has weight `blockWeight RD Λ₀ β = Σ_{j ∈ β} j_X - Λ₀`, while the
inversion relations on `T^λ`-modules (`clBlackModuleSumInvToQ`, `clBlackModuleSumInvFromQ`) are
stated at the coordinate pairing `⟨i, λ - β⟩` of the coordinate weight datum.

* `pair_blockWeight_eq_neg_ip`: if `⟨h_i, Λ₀⟩ = Σ_r Λ_r(i)` for every `i` (the compatibility
  `hΛ₀` of the weight `Λ₀` with the red labels `Λ`), then `⟨h_i, blockWeight RD Λ₀ β⟩` is minus the
  coordinate pairing `⟨i, λ - β⟩`;
* `coordinateHighest Λ C`, the sum `λ = Σ_r λ_r` of the red weights in the coordinate datum,
  satisfies the compatibility (`pair_coordinateHighest`); with it `blockWeight` is minus the
  coordinate weight `λ - β` itself (`blockWeight_coordinateHighest`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open QuantumGroup QuantumGroup.UDot KL3.Diagram DoubleDiagram KLR CyclotomicAction

variable {I : Type*} {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) (C : CartanDatum I)

/-- The weight `λ = Σ_r λ_r` of the red strands in the coordinate weight datum. -/
def coordinateHighest : I ⊕ Fin ℓ → ℤ :=
  (List.ofFn (Subtype.val ∘ coordinateRedWeights Λ C)).sum

/-- The coroot `i` pairs with `λ = Σ_r λ_r` to `Σ_r Λ_r(i)`. -/
theorem pair_coordinateHighest (i : I) :
    (coordinateDatum Λ C).pair ((coordinateDatum Λ C).iY i) (coordinateHighest Λ C) =
      ∑ r : Fin ℓ, (Λ r i : ℤ) := by
  have h := ip_downRightWeight C i Λ 0
  simpa [ip, downRightWeight, coordinateHighest] using h

/-- With `Λ₀ = λ`, the weight of a content `β` is minus the coordinate weight `λ - β`. -/
theorem blockWeight_coordinateHighest (β : Multiset I) :
    blockWeight (coordinateDatum Λ C) (coordinateHighest Λ C) β =
      -downRightWeight (coordinateDatum Λ C) (coordinateRedWeights Λ C) β := by
  simp only [blockWeight, downRightWeight, coordinateHighest, neg_sub]

universe u₁

variable {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (Λ₀ : X)

/-- **The Brundan weight of a block.** If `⟨h_i, Λ₀⟩ = Σ_r Λ_r(i)` for all `i` (the
compatibility `hΛ₀`), then `⟨h_i, Σ_{j ∈ β} j_X - Λ₀⟩ = -⟨i, λ - β⟩`, the right side computed in
the coordinate weight datum. -/
theorem pair_blockWeight_eq_neg_ip (hΛ₀ : ∀ i, RD.pair (RD.iY i) Λ₀ = ∑ r : Fin ℓ, (Λ r i : ℤ))
    (i : I) (β : Multiset I) :
    RD.pair (RD.iY i) (blockWeight RD Λ₀ β) =
      -ip (coordinateDatum Λ C) i
        (downRightWeight (coordinateDatum Λ C) (coordinateRedWeights Λ C) β) := by
  rw [ip_downRightWeight, blockWeight, map_sub, hΛ₀, map_multiset_sum, Multiset.map_map]
  simp only [Function.comp_def, WeightDatum.pair_iY_iX]
  ring

end Categorification.Stendhal
