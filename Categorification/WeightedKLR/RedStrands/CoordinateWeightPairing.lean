/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCLCoordinate
import Categorification.WeightedKLR.RedStrands.DoubleAllDownBoundary

/-!
# The coroot pairing of the weight of a black content

In the coordinate weight datum of a family of dominant weights `Λ`, the coroot `i` pairs with the
weight `λ - ν` of a black content `ν` to `Σ_r Λ_r(i) - Σ_{j ∈ ν} ⟨i, α_j⟩`
(`ip_downRightWeight`). Splitting the red strands into the first `ℓ` and the last one splits the
pairing additively (`ip_downRightWeight_split`). This is the weight identity `n = n₁ + n₂`
used in the dimension count of Webster, arXiv:1309.3796v3, proof of Proposition 5.5.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open QuantumGroup QuantumGroup.UDot KL3.Diagram DoubleDiagram

variable {I : Type*} {ℓ : ℕ} (C : CartanDatum I) (i : I)

/-- The pairing `⟨i, λ - ν⟩` in coordinates. -/
theorem ip_downRightWeight (Λ : Fin ℓ → I →₀ ℕ) (ν : Multiset I) :
    ip (coordinateDatum Λ C) i (downRightWeight (coordinateDatum Λ C)
        (coordinateRedWeights Λ C) ν) =
      (∑ r : Fin ℓ, (Λ r i : ℤ)) -
        (ν.map fun j => (coordinateDatum Λ C).pair ((coordinateDatum Λ C).iY i)
          ((coordinateDatum Λ C).iX j)).sum := by
  simp only [ip, downRightWeight, map_sub, map_multiset_sum, Multiset.map_map,
    Function.comp_def, List.sum_ofFn]
  congr 1
  rw [map_sum]
  exact Finset.sum_congr rfl fun r _ => coordinateRedWeights_pair Λ C r i

/-- The pairing `⟨i, λ - ν⟩` splits along the first `ℓ` red strands and the last one: for black
contents `θ` and `β`, `⟨i, λ - θ - β⟩ = ⟨i, λ' - θ⟩ + ⟨i, λ_ℓ - β⟩`. -/
theorem ip_downRightWeight_split (Λ : Fin (ℓ + 1) → I →₀ ℕ) (θ β : Multiset I) :
    ip (coordinateDatum Λ C) i (downRightWeight (coordinateDatum Λ C)
        (coordinateRedWeights Λ C) (θ + β)) =
      ip (coordinateDatum (Λ ∘ Fin.castSucc) C) i (downRightWeight
        (coordinateDatum (Λ ∘ Fin.castSucc) C) (coordinateRedWeights (Λ ∘ Fin.castSucc) C) θ) +
      ip (coordinateDatum (fun _ : Fin 1 => Λ (Fin.last ℓ)) C) i (downRightWeight
        (coordinateDatum (fun _ : Fin 1 => Λ (Fin.last ℓ)) C)
        (coordinateRedWeights (fun _ : Fin 1 => Λ (Fin.last ℓ)) C) β) := by
  rw [ip_downRightWeight, ip_downRightWeight, ip_downRightWeight, Fin.sum_univ_castSucc,
    Fin.sum_univ_one, Multiset.map_add, Multiset.sum_add]
  simp only [WeightDatum.pair_iY_iX, Function.comp_apply]
  ring

end Categorification.Stendhal
