/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FiveSlotLastRedSquare
import Categorification.WeightedKLR.RedStrands.FirstPairOneAfterSpectator

/-!
# Projectivity for one black beyond the final spectator

Webster, arXiv:1309.3796v2, Lemma 6.8 at (6.21).
The two principal higher kernels are projective for arbitrary red weights.
-/

noncomputable section

namespace Categorification.Stendhal.FiveSlotFlag

open KLR KLRAlgebra MvPolynomial TypeA Equiv PolyRep
open BraidedStendhalAlgebra TwoBlackFlag

variable {k : Type} [CommRing k]
  (Q : Unit → Unit → MvPolynomial (Fin 2) k) (Λ : Fin 3 → Unit →₀ ℕ)

local notation "ν" => ({()} + {()} : Multiset Unit)
local notation "N" => Multiset.card weight
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) weight
local notation "F" => AlgHom.comp (violMk k Q Λ ν) (ofKLR k Q Λ ν)
local notation "V" => ViolQuotient k Q Λ ν
local notation "D" => sadj N 1 • (sadj N 2 • fixedTopFourExitCut 0)
local notation "C" => fixedTopFourExitCut 1


local notation "A₀" => fixedTopFourExitCut 0
local notation "jA" => fiveSlotHigherLoading 2
local notation "E" => F (redIdem k Q Λ (redWord A₀))
local notation "p" => fun t : Seq weight => F (e t)
local notation "β" => F (ψw [3] * e D)
local notation "λ₀" => F (ψw [1] * e C)
local notation "Cδ" => F (ψ 1 * e jA : R)

/-- The rightward crossing of the final red is injective on the actual
fixed-order projective with both black strands before that red. -/
theorem fiveSlotLastRed_rightwardCrossing_cancel (hQ : KLRSymm Q)
    (u : V) (hu : p D * u = u) (hur : u * E = u)
    (zero : β * u = 0) : u = 0 := by
  have eqD : D = fiveSlotRightLoading 2 := by decide +kernel
  obtain ⟨z,hzl,hzr,huδ⟩ := fiveSlotLastRed_square_reflects_earlierCrossing Q Λ hQ
    u 0 (by simpa only [eqD] using hu) (mul_zero _) hur (zero_mul _)
    (by rw [← eqD, zero, mul_zero])
  let α := F (ψw [3] * e jA)
  have topD : wordProd N [1] • jA = D := by decide +kernel
  have topC : wordProd N [3] • jA = C := by decide +kernel
  have commutes : β * Cδ = λ₀ * α := by
    have singleton : Cδ = F (ψw [1] * e jA) := by simp only [ψw_cons, ψw_nil, mul_one]
    rw [singleton, ← map_mul F, ← map_mul F, cut_word_mul Q Λ [3] [1] jA D topD,
      cut_word_mul Q Λ [1] [3] jA C topC]
    congr 1
    simp only [List.cons_append, List.nil_append, ψw_cons, ψw_nil, mul_one]
    rw [ψ_mul_ψ (Q := stendhalQ Q Λ) 1 3 (by decide)]
  have huδ' : u = Cδ * z := huδ
  have zero' : λ₀ * (α * z) = 0 := by
    rw [← mul_assoc, ← commutes, mul_assoc, ← huδ', zero]
  have left : p C * (α * z) = α * z := by
    have hleft : p C * α = α := by
      rw [← map_mul F, ← topC]
      exact congrArg F (word_leftCut Q Λ [3] jA)
    rw [← mul_assoc, hleft]
  have right : (α * z) * E = α * z := by rw [mul_assoc, hzr]
  have ha := fiveSlotMiddleRight_centralCrossing_cancel_on_orderCorner Q Λ hQ (α * z) left right zero'
  have hz : z = 0 := fiveSlotNearby_toCentral_cancel_on_orderCorner Q Λ hQ z hzl hzr ha
  rw [huδ, hz, mul_zero]



attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

/-- Both one-after-spectator kernels for the first red pair are projective
over the original red-order corner. -/
theorem firstPairOneAfter_blockKernel_projective (side : Bool) (hQ : KLRSymm Q) :
    Module.Projective
      (isIdempotentElem_violMk_redProj k Q Λ ν (redWord (firstPairOneAfterSpectator side))).Cornerᵐᵒᵖ
      (blockLoadingKernel Q Λ (firstPairOneAfterSpectator side) 0 1) := by
  apply firstPairOneAfter_blockKernel_projective_of_cancellation Q Λ side hQ
  cases side
  · have top : sadj N 3 • firstPairOneAfterSpectator false = jA := by decide +kernel
    have order : redWord (firstPairOneAfterSpectator false) = redWord A₀ := by decide
    intro y hy hr hz
    rw [top] at hy hz
    rw [order] at hr
    have nearby : jA = sadj N 2 • A₀ := by decide +kernel
    exact fiveSlotNearby_toCentral_cancel_on_orderCorner Q Λ hQ y hy hr
      (by simpa only [ψw_cons, ψw_nil, mul_one, ← nearby] using hz)
  · have top : sadj N 3 • firstPairOneAfterSpectator true = D := by decide +kernel
    have order : redWord (firstPairOneAfterSpectator true) = redWord A₀ := by decide
    intro y hy hr hz
    rw [top] at hy hz
    rw [order] at hr
    exact fiveSlotLastRed_rightwardCrossing_cancel Q Λ hQ y hy hr
      (by simpa only [ψw_cons, ψw_nil, mul_one] using hz)

end Categorification.Stendhal.FiveSlotFlag
