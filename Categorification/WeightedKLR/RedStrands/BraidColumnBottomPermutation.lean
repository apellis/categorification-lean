/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidColumnBlockPermutation

/-!
# Bottom-block permutations in a braid column

Webster, arXiv:1309.3796v3, Lemma 6.12, p. 66. This version puts the red-led
block permutation at the bottom of each projective wiring. With permutations
acting on loadings from bottom to top, this fixes the top and precomposes
the wiring with the inverse block permutation. It gives the prescribed
bottom red word and preserves ascents between a red and its following
black strands within its relocated block.
-/

namespace Categorification.Stendhal
open KLR KLRAlgebra TypeA Equiv
open scoped BigOperators

variable {I : Type} {ℓ : ℕ} {ν : Multiset I}
local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card μ

/-- A bottom-block move changes the input coordinates of an eligible wiring.
The target loading is kept fixed. -/
def braidColumnBottomBlockIndex (n : Fin ℓ → ℕ) {d : ℕ}
    (hn : (∑ r, (n r + 1)) = d) (σ : Perm (Fin ℓ)) (φ : Perm (Fin d)) : Perm (Fin d) :=
  φ * (braidBlockPermutation n hn σ)⁻¹

theorem braidColumnBottomBlockIndex_bottom (s : Seq μ) (n : Fin ℓ → ℕ)
    (hn : (∑ r, (n r + 1)) = m) (σ : Perm (Fin ℓ)) (φ : Perm (Fin m)) :
    (braidColumnBottomBlockIndex n hn σ φ)⁻¹ • s = braidBlockPermutation n hn σ • (φ⁻¹ • s) := by
  rw [braidColumnBottomBlockIndex, mul_inv_rev, inv_inv, mul_smul]

theorem braidColumnBottomBlockIndex_apply (n : Fin ℓ → ℕ) {d : ℕ}
    (hn : (∑ r, (n r + 1)) = d) (σ : Perm (Fin ℓ)) (φ : Perm (Fin d))
    (r : Fin ℓ) (a : Fin (n (σ r) + 1)) :
    braidColumnBottomBlockIndex n hn σ φ
      (braidBlockPositions (n ∘ σ) ((Equiv.sum_comp σ fun r => n r + 1).trans hn) ⟨r, a⟩) =
      φ (braidBlockPositions n hn ⟨σ r, a⟩) := by
  rw [← braidBlockPermutation_apply n hn σ r a, braidColumnBottomBlockIndex, Perm.mul_apply]
  simp

variable [DecidableEq I]

/-- The direct bottom composition of arXiv:1309.3796v3, p. 66, lands in
the column with fixed top and permuted bottom red order. -/
theorem redWord_braidColumnBottomBlockIndex_bottom (s : Seq μ) (n : Fin ℓ → ℕ)
    (hn : (∑ r, (n r + 1)) = m) (σ : Perm (Fin ℓ)) (φ : Perm (Fin m))
    (hr : ∀ r : Fin ℓ, (φ⁻¹ • s).lbl (braidBlockPositions n hn ⟨r, 0⟩) = .inr r) :
    redWord ((braidColumnBottomBlockIndex n hn σ φ)⁻¹ • s) = (List.finRange ℓ).map σ := by
  rw [braidColumnBottomBlockIndex_bottom]
  exact redWord_braidBlockPermutation_smul _ _ _ _ hr

/-- The wiring attached to the bottom-block move has no right descent
between the red and any later black position in the same block, provided
the original wiring is eligible. -/
theorem braidColumnBottomBlockIndex_lt_red_black (s : Seq μ) (n : Fin ℓ → ℕ)
    (hn : (∑ r, (n r + 1)) = m) (σ : Perm (Fin ℓ))
    {φ : Perm (Fin m)} (hφ : ProjectiveBlockIndex s φ)
    (hs : ∀ r : Fin ℓ, (φ⁻¹ • s).lbl (braidBlockPositions n hn ⟨r, 0⟩) = .inr r)
    (r : Fin ℓ) (a : Fin (n (σ r) + 1)) (ha : 0 < a.val) {i : I}
    (hi : (φ⁻¹ • s).lbl (braidBlockPositions n hn ⟨σ r, a⟩) = .inl i) :
    braidColumnBottomBlockIndex n hn σ φ
      (braidBlockPositions (n ∘ σ) ((Equiv.sum_comp σ fun r => n r + 1).trans hn) ⟨r, 0⟩) <
    braidColumnBottomBlockIndex n hn σ φ
      (braidBlockPositions (n ∘ σ) ((Equiv.sum_comp σ fun r => n r + 1).trans hn) ⟨r, a⟩) := by
  rw [braidColumnBottomBlockIndex_apply, braidColumnBottomBlockIndex_apply]
  have hsource : braidBlockPositions n hn ⟨σ r, 0⟩ = redPos (φ⁻¹ • s) (σ r) :=
    eq_redPos (hs (σ r))
  have htarget : φ (braidBlockPositions n hn ⟨σ r, 0⟩) = redPos s (σ r) := by
    apply eq_redPos
    rw [← show φ • (φ⁻¹ • s) = s from smul_inv_smul _ _,
      BraidedStendhalAlgebra.lbl_smul]
    simpa only [Perm.inv_def, Equiv.symm_apply_apply] using hs (σ r)
  rw [htarget]
  apply hφ.only_rightwards _ _ _ hi
  rw [← hsource]
  simp only [braidBlockPositions, Equiv.trans_apply, Fin.lt_def, finCongr_apply, Fin.val_cast,
    finSigmaFinEquiv_apply, Fin.val_zero, add_zero]
  omega

end Categorification.Stendhal
