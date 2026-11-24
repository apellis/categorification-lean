/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FiveSlotFlagStability
import Categorification.WeightedKLR.RedStrands.FiveSlotFlagReadout

/-!
# The balanced five-slot column at the central loading

Webster, arXiv:1309.3796v2, §6.1, proof of Lemma 6.8 after (6.21).
For two equal black strands, a last exchanged red pair and one spectator,
the central two-crossing word is injective on the left-extreme corner over
the fixed exchanged bottom. The flag representation detects the two source
PBW coefficients after imposing global violation, with arbitrary red weights.
The principal tensor criterion gives the actual balanced column inclusion.
-/

noncomputable section
namespace Categorification.Stendhal.BraidedStendhalAlgebra
open KLR KLRAlgebra MvPolynomial FiveSlotFlag
variable {k : Type} [CommRing k] (Q : Unit → Unit → MvPolynomial (Fin 2) k) (Λ : Fin 3 → Unit →₀ ℕ)
local notation "ν₀" => ({()} + {()} : Multiset Unit)
local notation "N" => Multiset.card weight
local notation "v₀" => fixedTopFourExitCut 0
local notation "v₁" => fixedTopFourExitCut 1
local notation "bot" => fixedTopFourExitBottom
local notation "F" => AlgHom.comp (violMk k Q Λ ν₀) (ofKLR k Q Λ ν₀)

private theorem central_flag_ideal :
    loadingIdeal (k := k) Λ v₁ =
      TwoBlackFlag.ideal (⟨1,by decide⟩ : Fin N) ⟨4,by decide⟩
        (Λ 0 ()) (Λ 0 ()+(Λ 1 ()+Λ 2 ())) := by
  have h₁ : redsBefore v₁ (firstBlack v₁)={0} := by decide
  have h₂ : redsBefore v₁ (secondBlack v₁)=Finset.univ := by decide
  unfold loadingIdeal flagBound
  rw [h₁,h₂,show firstBlack v₁=⟨1,by decide⟩ by decide,
    show secondBlack v₁=⟨4,by decide⟩ by decide,Finset.sum_singleton,Fin.sum_univ_three,Nat.add_assoc]

/-- At the central top, the two PBW rows reflect zero after imposing global
violation for every choice of the three red pairings. -/
theorem fiveSlotCentral_rowReflection (hQ : KLRSymm Q) : FiveSlotCentralRowReflection Q Λ := by
  apply fiveSlotCentral_rowReflection_of_flagAction Λ Q hQ (flagP_factor Q Λ) rfl rfl (by simp [flagP])
  intro z hz p
  rw [← central_flag_ideal (k := k) Λ]
  exact eval_mem_flag_of_violMk_eq_zero Q Λ (loadingIdeal Λ)
    (loadingIdeal_preservesFlags Λ) (loadingIdeal_eq_top_of_violated Λ) hz (Pi.single bot p) v₁

/-- The two-crossing word through both exchanged reds is injective on the
left-extreme corner over the fixed interleaved bottom in the violated quotient. -/
theorem fiveSlotCentral_leftWord_cancel (hQ : KLRSymm Q)
    (y : ViolQuotient k Q Λ ν₀) (hy : F (e v₀)*y*F (e bot)=y)
    (zero : F (ψw [3,2]*e v₀)*y=0) : y=0 :=
  (fiveSlotCentral_leftWord_cancel_iff Q Λ hQ).2 (fiveSlotCentral_rowReflection Q Λ hQ) y hy zero

/-- Webster, Lemma 6.8 after (6.21), at the central upper loading and the
five-slot bottom with both equal blacks between the exchanged reds. -/
theorem fiveSlotCentral_blockKernelColumnInclusion_injective (hQ : KLRSymm Q) :
    Function.Injective (blockKernelColumnInclusion Q Λ v₁ 1 2 bot) :=
  fiveSlotCentral_columnInclusion_of_rowReflection Q Λ hQ (fiveSlotCentral_rowReflection Q Λ hQ)

end Categorification.Stendhal.BraidedStendhalAlgebra
