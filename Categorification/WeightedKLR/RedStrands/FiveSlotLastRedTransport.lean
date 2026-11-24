/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FiveSlotNearbyCornerFlag

/-!
# Moving the final red past both black strands

Webster, arXiv:1309.3796v2, Lemma 6.8 at (6.21).
Moving the last red across the two black strands identifies the relevant
crossing tests with those at the rightmost loading. Both tests use cancellation
for the single crossing from the nearby to the central loading.
-/

noncomputable section

namespace Categorification.Stendhal.FiveSlotFlag

open KLR KLRAlgebra TypeA BraidedStendhalAlgebra

variable {k : Type} [CommRing k]
  (Q : Unit → Unit → MvPolynomial (Fin 2) k) (Λ : Fin 3 → Unit →₀ ℕ)

local notation "ν" => ({()} + {()} : Multiset Unit)
local notation "μ" => stendhalWeight 3 ν
local notation "N" => Multiset.card μ
local notation "E₀" => fixedTopFourExitCut 0
local notation "E₁" => fixedTopFourExitCut 1
local notation "E₂" => fixedTopFourExitCut 2
local notation "jA" => sadj N 2 • E₀
local notation "t" => sadj N 3 • (sadj N 2 • E₂)
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ
local notation "V" => ViolQuotient k Q Λ ν
local notation "F" => AlgHom.comp (violMk k Q Λ ν) (ofKLR k Q Λ ν)
local notation "C" => fun l : List ℕ => fun s : Seq μ => (ψw l * e s : R)
local notation "p" => fun s : Seq μ => F (e s)
local notation "E" => F (redIdem k Q Λ (redWord E₀))

theorem word_leftCut (l : List ℕ) (s : Seq μ) :
    (e (wordProd N l • s) : R) * C l s = C l s := by
  rw [← mul_assoc, e_mul_ψw, inv_smul_smul, mul_assoc, e_mul_self]

theorem cut_word_mul (l r : List ℕ) (s u : Seq μ)
    (h : wordProd N r • s = u) :
    C l u * C r s = C (l ++ r) s := by
  change (ψw l * e u : R) * (ψw r * e s) = ψw (l ++ r) * e s
  rw [mul_assoc, ← h, word_leftCut Q Λ r s, ψw_append, mul_assoc]

theorem crossing_braid_ne (j : ℕ) (hj : j + 2 < N) (s : Seq μ)
    (hne : s.lbl ⟨j, by omega⟩ ≠ s.lbl ⟨j+2,hj⟩) :
    C [j,j+1,j] s = C [j+1,j,j+1] s := by
  have h := KLRAlgebra.braid (Q := stendhalQ Q Λ) j hj s
  rw [ite_eq_right (fun hh => hne hh.1), sub_mul, sub_eq_zero] at h
  simpa only [ψw_cons, ψw_nil, mul_one, mul_assoc] using h

private theorem first_square :
    C [2,3] t * C [1] jA = C [2,1] E₁ * C [3] jA := by
  rw [cut_word_mul Q Λ _ _ _ _ (by decide), cut_word_mul Q Λ _ _ _ _ (by decide)]
  change (ψw [2,3,1] * e jA : R) = ψw [2,1,3] * e jA
  simp only [ψw_cons, ψw_nil, mul_one, mul_assoc]
  rw [← mul_assoc (ψ 3) (ψ 1), ← ψ_mul_ψ (Q := stendhalQ Q Λ) 1 3 (by decide), mul_assoc]

private theorem second_square :
    C [2,3] t * C [2,1] jA = C [3,2,1] E₁ * C [3] jA := by
  rw [cut_word_mul Q Λ _ _ _ _ (by decide), cut_word_mul Q Λ _ _ _ _ (by decide)]
  change C [2,3,2,1] jA = C [3,2,1,3] jA
  have h : C [2,3,2] t = C [3,2,3] t := crossing_braid_ne Q Λ 2 (by decide) t (by decide)
  have cut : C [2,3,2] t * C [1] jA = C [2,3,2,1] jA :=
    cut_word_mul Q Λ _ _ _ _ (by decide)
  have cut' : C [3,2,3] t * C [1] jA = C [3,2,3,1] jA :=
    cut_word_mul Q Λ _ _ _ _ (by decide)
  rw [← cut, h, cut']
  change (ψw [3,2,3,1] * e jA : R) = ψw [3,2,1,3] * e jA
  simp only [ψw_cons, ψw_nil, mul_one, mul_assoc]
  rw [← mul_assoc (ψ 3) (ψ 1), ← ψ_mul_ψ (Q := stendhalQ Q Λ) 1 3 (by decide), mul_assoc]

/-- Injectivity at the loading with both black strands before the final red
follows from the rightmost crossing test and the nearby-to-central crossing. -/
theorem fiveSlotLastRed_firstCrossing_cancel (hQ : KLRSymm Q)
    (y : V) (hl : p jA * y = y) (hr : y * E = y)
    (hz : F (C [1] jA) * y = 0) : y = 0 := by
  apply fiveSlotNearby_toCentral_cancel_on_orderCorner Q Λ hQ y hl hr
  let a := F (C [3] jA)
  have ha : p E₁ * a = a := by
    rw [← map_mul]
    rw [← show wordProd N [3] • jA = E₁ by decide]
    exact congrArg F (word_leftCut Q Λ [3] jA)
  have hb : F (C [2,1] E₁) * (a * y) = 0 := by
    rw [← mul_assoc, ← map_mul F, ← first_square Q Λ, map_mul, mul_assoc, hz, mul_zero]
  exact fiveSlotRightmost_firstCrossing_cancel_on_orderCorner Q Λ hQ (a * y)
    (by rw [← mul_assoc, ha]) (by rw [mul_assoc, hr]) hb

/-- The second crossing at the loading with both black strands before the
final red has kernel contained in the principal image from the left extreme. -/
theorem fiveSlotLastRed_secondCrossing_mem_leftExtremeImage (hQ : KLRSymm Q)
    (y : V) (hl : p jA * y = y) (hr : y * E = y) (hz : F (C [2,1] jA) * y = 0) :
    ∃ b : V, p E₀ * b = b ∧ b * E = b ∧ y = F (C [2] E₀) * b := by
  let a := F (C [3] jA)
  have ha : p E₁ * a = a := by
    rw [← map_mul]
    rw [← show wordProd N [3] • jA = E₁ by decide]
    exact congrArg F (word_leftCut Q Λ [3] jA)
  have hb : F (C [3,2,1] E₁) * (a * y) = 0 := by
    rw [← mul_assoc, ← map_mul F, ← second_square Q Λ, map_mul, mul_assoc, hz, mul_zero]
  obtain ⟨b, hbl, hbr, hby⟩ := fiveSlotRightmost_secondCrossing_kernel_mem_leftExtremeImage Q Λ hQ
    (a * y) (by rw [← mul_assoc, ha]) (by rw [mul_assoc, hr]) hb
  let c := F (C [2] E₀)
  have hc : p jA * c = c := by
    rw [← map_mul]
    rw [← show wordProd N [2] • E₀ = jA by decide]
    exact congrArg F (word_leftCut Q Λ [2] E₀)
  have hca : a * c = F (C [3,2] E₀) := by
    rw [← map_mul F, cut_word_mul Q Λ _ _ _ _ (by decide)]
    rfl
  have hdiff : y - c * b = 0 := by
    apply fiveSlotNearby_toCentral_cancel_on_orderCorner Q Λ hQ
    · rw [mul_sub, hl, ← mul_assoc, hc]
    · rw [sub_mul, hr, mul_assoc, hbr]
    · rw [mul_sub, ← mul_assoc a c, hca, hby, sub_self]
  exact ⟨b, hbl, hbr, sub_eq_zero.mp hdiff⟩

/-- The second crossing on the principal image is the first crossing after
the left-extreme nilHecke operator. -/
theorem fiveSlotLastRed_secondCrossing_on_leftExtreme (y : V) :
    F (C [2,1] jA) * (F (C [2] E₀) * y) =
      F (C [1] jA) * (F (C [2] E₀) * (F (C [1] E₀) * y)) := by
  have h : C [2,1] jA * C [2] E₀ = C [1] jA * (C [2] E₀ * C [1] E₀) := by
    rw [cut_word_mul Q Λ _ _ _ _ (by decide),
      cut_word_mul Q Λ _ _ _ _ (by decide),
      cut_word_mul Q Λ _ _ _ _ (by decide)]
    change C [2,1,2] E₀ = C [1,2,1] E₀
    exact (crossing_braid_ne Q Λ 1 (by decide) E₀ (by decide)).symm
  simpa only [map_mul, mul_assoc] using congrArg (fun z => F z * y) h

end Categorification.Stendhal.FiveSlotFlag
