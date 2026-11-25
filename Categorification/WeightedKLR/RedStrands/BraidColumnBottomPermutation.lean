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

namespace Categorification.Stendhal
open KLR KLRAlgebra TypeA Equiv
open scoped BigOperators

private def braidBlockPrefix {ℓ : ℕ} (n : Fin ℓ → ℕ) (j : ℕ) (hj : j ≤ ℓ) : ℕ :=
  ∑ r : Fin j, (n (Fin.castLE hj r) + 1)

private theorem braidBlockPrefix_succ {ℓ : ℕ} (n : Fin ℓ → ℕ) (r : Fin ℓ) :
    braidBlockPrefix n (r.val + 1) r.isLt =
      braidBlockPrefix n r.val r.isLt.le + (n r + 1) := by
  unfold braidBlockPrefix
  rw [Fin.sum_univ_castSucc]
  rfl

/-- The red positions, together with the full row length, determine all block sizes. -/
theorem braidBlockAmounts_eq_of_red_positions {ℓ m : ℕ} (n n' : Fin ℓ → ℕ)
    (hn : (∑ r, (n r + 1)) = m) (hn' : (∑ r, (n' r + 1)) = m)
    (hred : ∀ r : Fin ℓ,
      braidBlockPositions n hn ⟨r,0⟩ = braidBlockPositions n' hn' ⟨r,0⟩) :
    n = n' := by
  have hp (j : ℕ) (hj : j ≤ ℓ) :
      braidBlockPrefix n j hj = braidBlockPrefix n' j hj := by
    rcases hj.eq_or_lt with rfl | hj'
    · simpa only [braidBlockPrefix, Fin.castLE_refl] using hn.trans hn'.symm
    · simpa only [braidBlockPositions, Equiv.trans_apply, finCongr_apply, Fin.val_cast,
        finSigmaFinEquiv_apply, Fin.val_zero, add_zero, braidBlockPrefix] using
          congrArg Fin.val (hred ⟨j,hj'⟩)
  funext r
  have h := hp (r.val + 1) r.isLt
  rw [braidBlockPrefix_succ n r, braidBlockPrefix_succ n' r, hp r.val r.isLt.le] at h
  omega

variable {I : Type} [DecidableEq I] {ℓ : ℕ} {ν : Multiset I}
local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card μ

/-- Reordering whole bottom blocks preserves the multiplicity of eligible indices.
The transported red positions determine the marked block sizes, so equality
of the reordered wirings forces equality of the original wirings. -/
theorem braidColumnBottomBlockIndex_eq_of_eq (s : Seq μ) (σ : Perm (Fin ℓ))
    (n n' : Fin ℓ → ℕ) (hn : (∑ r, (n r + 1)) = m)
    (hn' : (∑ r, (n' r + 1)) = m) (φ φ' : Perm (Fin m))
    (hred : ∀ r : Fin ℓ, (φ⁻¹ • s).lbl (braidBlockPositions n hn ⟨r,0⟩) = .inr r)
    (hred' : ∀ r : Fin ℓ, (φ'⁻¹ • s).lbl (braidBlockPositions n' hn' ⟨r,0⟩) = .inr r)
    (h : braidColumnBottomBlockIndex n hn σ φ = braidColumnBottomBlockIndex n' hn' σ φ') :
    n = n' ∧ φ = φ' := by
  have hloading := congrArg (fun w : Perm (Fin m) => w⁻¹ • s) h
  rw [braidColumnBottomBlockIndex_bottom, braidColumnBottomBlockIndex_bottom] at hloading
  have hpos (r : Fin ℓ) :
      braidBlockPositions (n ∘ σ) ((Equiv.sum_comp σ fun q => n q + 1).trans hn) ⟨r,0⟩ =
      braidBlockPositions (n' ∘ σ) ((Equiv.sum_comp σ fun q => n' q + 1).trans hn') ⟨r,0⟩ := by
    have hr := (lbl_braidBlockPermutation_smul (φ⁻¹ • s) n hn σ r 0).trans (hred (σ r))
    have hr' := (lbl_braidBlockPermutation_smul (φ'⁻¹ • s) n' hn' σ r 0).trans (hred' (σ r))
    rw [hloading] at hr
    exact lbl_eq_inr_unique hr hr'
  have he := braidBlockAmounts_eq_of_red_positions (n ∘ σ) (n' ∘ σ) _ _ hpos
  have hnEq : n = n' := by
    funext r
    obtain ⟨q,rfl⟩ := σ.surjective r
    exact congrFun he q
  subst n'
  exact ⟨rfl, mul_right_cancel h⟩

end Categorification.Stendhal
