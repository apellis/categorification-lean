/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FiveSlotLeftTopIdeal
import Categorification.KLR.EqualBlackReturnKernel

/-!
# PBW reductions at the right five-slot tops

Webster, arXiv:1309.3796v2, Lemma 6.8 at (6.21).
Two reduced words suffice for each supported cut between a right loading
and one of its three surviving higher loadings. At the rightmost loading,
both words can be factored through the central loading. Sliding the
polynomial coefficients to the right gives two fixed crossing maps.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR KLRAlgebra TypeA Equiv MvPolynomial

local notation "ν₀" => ({()} + {()} : Multiset Unit)
local notation "μ₀" => stendhalWeight 3 ν₀
local notation "n₀" => Multiset.card μ₀
local notation "v₀" => fixedTopFourExitCut 0
local notation "v₁" => fixedTopFourExitCut 1
local notation "v₂" => fixedTopFourExitCut 2
local notation "jA" => sadj n₀ 2 • v₀

def fiveSlotHigherLoading : Fin 3 → Seq μ₀
  | 0 => v₀
  | 1 => v₁
  | _ => jA

def fiveSlotRightLoading : Fin 3 → Seq μ₀
  | 0 => v₂
  | 1 => sadj n₀ 2 • v₂
  | _ => sadj n₀ 3 • (sadj n₀ 2 • v₂)

/-- Reduced words for the two black matchings from a higher loading to a right top. -/
def fiveSlotRightHigherWords : Fin 3 → Fin 3 → List ℕ × List ℕ
  | 0, 0 => ([2,1,3,2], [3,2,1,3,2])
  | 0, 1 => ([3,1,2], [3,1,2,1])
  | 0, 2 => ([1,2], [1,2,1])
  | 1, 0 => ([2,1], [3,2,1])
  | 1, 1 => ([1], [2,3,2,1])
  | 1, 2 => ([3,1], [2,3,1])
  | 2, 0 => ([2,1,3], [3,2,1,3])
  | 2, 1 => ([3,1], [3,2,1])
  | 2, 2 => ([1], [2,1])

local notation "W" => fiveSlotRightHigherWords
local notation "S" => fiveSlotHigherLoading
local notation "T" => fiveSlotRightLoading

theorem fiveSlotRightHigherWords_spec (i j : Fin 3) :
    IsReduced n₀ (W i j).1 ∧ IsReduced n₀ (W i j).2 ∧
      wordProd n₀ (W i j).1 ≠ wordProd n₀ (W i j).2 ∧
      ∀ p : Perm (Fin n₀), p • S i = T j ↔
        p = wordProd n₀ (W i j).1 ∨ p = wordProd n₀ (W i j).2 := by
  fin_cases i <;> fin_cases j <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    first
    | exact ⟨by simp [ValidWord, fiveSlotRightHigherWords]; decide, by rw [length_eq_invCount]; decide +kernel⟩
    | decide +kernel

variable {k : Type} [CommRing k]
  (Q : Unit → Unit → MvPolynomial (Fin 2) k) (Λ : Fin 3 → Unit →₀ ℕ)

local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ₀

/-- The nine affine cuts controlling the right-top kernel each have the two
explicit PBW terms of the corresponding black matching. -/
theorem fiveSlotRightHigher_exists_pbw (hQ : KLRSymm Q) (i j : Fin 3) (x : R)
    (hl : e (T j) * x = x) (hr : x * e (S i) = x) :
    ∃ f g : MvPolynomial (Fin n₀) k,
      x = pol f * (ψw (W i j).1 * e (S i)) + pol g * (ψw (W i j).2 * e (S i)) := by
  obtain ⟨h₁, h₂, hne, hmatch⟩ := fiveSlotRightHigherWords_spec i j
  exact exists_two_corner_coefficients_of_words (stendhalQ_symm Q Λ hQ)
    (S i) (T j) (W i j).1 (W i j).2 h₁ h₂ hne hmatch x hl hr


private def centralTail : Fin 3 → List ℕ
  | 0 => [3,2]
  | 1 => []
  | _ => [3]

private theorem centralTail_loading (i : Fin 3) : wordProd n₀ (centralTail i) • S i = v₁ := by
  fin_cases i <;> decide

private theorem rightmost_words (i : Fin 3) :
    W i 0 = ([2,1] ++ centralTail i, [3,2,1] ++ centralTail i) := by
  fin_cases i <;> rfl

private theorem factor_rightmost_word (l : List ℕ) (i : Fin 3) :
    (ψw (l ++ centralTail i) * e (S i) : R) =
      (ψw l * e v₁) * (ψw (centralTail i) * e (S i)) := by
  have hcut : (e v₁ : R) * (ψw (centralTail i) * e (S i)) =
      ψw (centralTail i) * e (S i) := by
    rw [← centralTail_loading i, ← mul_assoc, e_mul_ψw, inv_smul_smul, mul_assoc, e_mul_self]
  rw [ψw_append, mul_assoc, mul_assoc _ (e v₁), hcut]

/-- At the rightmost top the PBW terms from all three higher cuts use the
same two leading words from E1. The second applies the final nilHecke crossing. -/
theorem fiveSlotRightmostHigher_exists_central_factors (hQ : KLRSymm Q) (i : Fin 3) (x : R)
    (hl : e v₂ * x = x) (hr : x * e (S i) = x) :
    ∃ f g : MvPolynomial (Fin n₀) k,
      x = pol f * ((ψw [2,1] * e v₁) * (ψw (centralTail i) * e (S i))) +
          pol g * ((ψw [3,2,1] * e v₁) * (ψw (centralTail i) * e (S i))) := by
  have hl' : e (T 0) * x = x := hl
  obtain ⟨f, g, h⟩ := fiveSlotRightHigher_exists_pbw Q Λ hQ i 0 x hl' hr
  rw [rightmost_words i] at h
  exact ⟨f, g, h.trans (congrArg₂ (· + ·)
    (congrArg (pol f * ·) (factor_rightmost_word Q Λ [2,1] i))
    (congrArg (pol g * ·) (factor_rightmost_word Q Λ [3,2,1] i)))⟩


local notation "P" => MvPolynomial (Fin n₀) k

private theorem slide_pol_from_left (j : ℕ) (hj : j + 1 < n₀) (s : Seq μ₀)
    (f : P) (z : R) (hz : e s * z = z) :
    pol f * (ψ j * z) =
      ψ j * (pol (swapPol j hj f) * z) -
        if s.lbl ⟨j, by omega⟩ = s.lbl ⟨j+1, hj⟩
          then pol (NilHecke.dd k n₀ j (swapPol j hj f)) * z else 0 := by
  classical
  have he : (eqIdem j hj * e s : R) =
      if s.lbl ⟨j, by omega⟩ = s.lbl ⟨j+1, hj⟩ then e s else 0 := by
    rw [eqIdem, Finset.sum_mul, Finset.sum_eq_single s]
    · split_ifs
      · exact e_mul_self _
      · exact zero_mul _
    · intro u _ hu
      split_ifs
      · rw [e_mul_e, ite_eq_right hu]
      · exact zero_mul _
    · intro hn
      exact (hn (Finset.mem_univ _)).elim
  have hh : (eqIdem j hj * z : R) =
      if s.lbl ⟨j, by omega⟩ = s.lbl ⟨j+1, hj⟩ then z else 0 := by
    rw [← hz, ← mul_assoc, he, hz]
    split_ifs
    · exact hz
    · exact zero_mul _
  rw [← mul_assoc, pol_mul_ψ j hj f, sub_mul, mul_assoc, mul_assoc, hh]
  split_ifs
  · rfl
  · rw [mul_zero]

local notation "c₀" => (ψw [2,1] * e v₁ : R)
local notation "c₁" => (ψw [3,2,1] * e v₁ : R)

private theorem centralCrossing_leftSlide (f : P) (z : R) (hz : e v₁ * z = z) :
    ∃ y : R, e v₁ * y = y ∧ pol f * (c₀ * z) = c₀ * y := by
  let s := sadj n₀ 1 • v₁
  have hs : (e s : R) * (ψ 1 * z) = ψ 1 * z := by
    rw [← mul_assoc, e_mul_ψ, sadj_smul_smul, mul_assoc, hz]
  have h₂ := slide_pol_from_left Q Λ 2 (by decide) s f (ψ 1 * z) hs
  have h₁ := slide_pol_from_left Q Λ 1 (by decide) v₁ (swapPol 2 (by decide) f) z hz
  have hn₂ : s.lbl ⟨2, by decide⟩ ≠ s.lbl ⟨3, by decide⟩ := by decide
  have hn₁ : (v₁).lbl ⟨1, by decide⟩ ≠ (v₁).lbl ⟨2, by decide⟩ := by decide
  simp only [hn₂, ite_false, sub_zero] at h₂
  simp only [hn₁, ite_false, sub_zero] at h₁
  let g := swapPol 1 (by decide : 1+1<n₀) (swapPol 2 (by decide : 2+1<n₀) f)
  refine ⟨pol g * z, ?_, ?_⟩
  · rw [← pol_e_comm_assoc, hz]
  · have hzg : (e v₁ : R) * (pol g * z) = pol g * z := by rw [← pol_e_comm_assoc, hz]
    simp only [ψw_cons, ψw_nil, mul_one, mul_assoc, hz, hzg]
    exact h₂.trans (congrArg (ψ 2 * ·) h₁)

private theorem rightmostCrossing_leftSlide (f : P) (z : R) (hz : e v₁ * z = z) :
    ∃ y x : R, e v₁ * y = y ∧ e v₁ * x = x ∧
      pol f * (c₁ * z) = c₀ * y + c₁ * x := by
  have ht : (e v₂ : R) * (c₀ * z) = c₀ * z := by
    rw [← mul_assoc, ← show wordProd n₀ [2,1] • v₁ = v₂ by decide,
      ← mul_assoc (e _) (ψw _), e_mul_ψw, inv_smul_smul, mul_assoc _ (e v₁), hz]
  have h₃ := slide_pol_from_left Q Λ 3 (by decide) v₂ f (c₀ * z) ht
  have he : (v₂).lbl ⟨3, by decide⟩ = (v₂).lbl ⟨4, by decide⟩ := by decide
  simp only [he, ite_true] at h₃
  obtain ⟨x, hx, hxp⟩ := centralCrossing_leftSlide Q Λ (swapPol 3 (by decide) f) z hz
  obtain ⟨y, hy, hyp⟩ := centralCrossing_leftSlide Q Λ (NilHecke.dd k n₀ 3 (swapPol 3 (by decide) f)) z hz
  refine ⟨-y, x, by rw [mul_neg, hy], hx, ?_⟩
  have hc : c₁ = ψ 3 * c₀ := by rw [ψw_cons, mul_assoc]
  rw [hc, mul_assoc, h₃, hxp, hyp, mul_neg, sub_eq_add_neg]
  calc
    _ = -(c₀ * y) + ψ 3 * (c₀ * x) := add_comm _ _
    _ = _ := congrArg (-(c₀ * y) + ·) (mul_assoc (ψ 3) c₀ x).symm

/-- At the rightmost top every cut from a higher loading factors through the
same two maps from the central loading projective, with supported right coefficients. -/
theorem fiveSlotRightmostHigher_exists_two_right_factors (hQ : KLRSymm Q) (i : Fin 3) (z : R)
    (hl : e v₂ * z = z) (hr : z * e (S i) = z) :
    ∃ y x : R, e v₁ * y = y ∧ e v₁ * x = x ∧ z = c₀ * y + c₁ * x := by
  let w : R := ψw (centralTail i) * e (S i)
  have hw : (e v₁ : R) * w = w := by
    change e v₁ * (ψw (centralTail i) * e (S i)) = _
    rw [← centralTail_loading i, ← mul_assoc, e_mul_ψw, inv_smul_smul, mul_assoc, e_mul_self]
  obtain ⟨f, g, h⟩ := fiveSlotRightmostHigher_exists_central_factors Q Λ hQ i z hl hr
  obtain ⟨a, ha, hfa⟩ := centralCrossing_leftSlide Q Λ f w hw
  obtain ⟨b, c, hb, hc, hgc⟩ := rightmostCrossing_leftSlide Q Λ g w hw
  refine ⟨a + b, c, by rw [mul_add, ha, hb], hc, ?_⟩
  change z = pol f * (c₀ * w) + pol g * (c₁ * w) at h
  rw [h, hfa, hgc, ← add_assoc, ← mul_add]

end Categorification.Stendhal.BraidedStendhalAlgebra
