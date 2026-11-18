/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.BubbleSlidesAll
import Categorification.WeightedKLR.RedStrands.AffineCover
import Mathlib.Algebra.TrivSqZeroExt.Basic

/-!
# Normalized bubble coefficients at a red strand

Webster, arXiv:1309.3796v2, §4.5, proof of Theorem 4.25. The two real
red-bubble slides only compare coefficients for which the relevant dot
counts are nonnegative. Across a sign change this leaves a range where
an inverse-series identity with one factor on each side would complete
the comparison, as in the mixed Grassmannian calculation of
Brundan–Ellis, arXiv:1701.04133v2, proof of Proposition 7.3(iii).

The results here are statements about normalized coefficients. The last
example shows that inverse-series identities separately on each side
and both real-slide equations do not imply the missing comparisons.
-/

namespace Categorification.Stendhal.DoubleDiagram

open KL3.Diagram

private theorem sconv_succ_edges {A : Type*} [Ring A] (u v : ℕ → A)
    (hu : u 0 = 1) (hv : v 0 = 1) (n : ℕ) :
    sconv u v (n + 1) =
      (∑ a ∈ Finset.range n, u (a + 1) * v (n + 1 - (a + 1))) + v (n + 1) + u (n + 1) := by
  rw [sconv, Finset.sum_range_succ, Nat.sub_self, hv, mul_one, Finset.sum_range_succ', hu,
    Nat.sub_zero, one_mul]

/-- At each normalized degree it suffices to know either direct equality of
one bubble orientation or the mixed convolution equation. The
Grassmannian equations on the two sides then compare both orientations. -/
theorem redBubbleCoefficients_eq {A : Type*} [Ring A]
    (cwL ccwL cwR ccwR : ℕ → A)
    (hcwL : cwL 0 = 1) (hccwL : ccwL 0 = 1) (hcwR : cwR 0 = 1) (hccwR : ccwR 0 = 1)
    (hL : ∀ d, sconv cwL ccwL d = if d = 0 then 1 else 0)
    (hR : ∀ d, sconv cwR ccwR d = if d = 0 then 1 else 0)
    (h : ∀ d, 0 < d → cwL d = cwR d ∨ ccwL d = ccwR d ∨ sconv cwL ccwR d = 0)
      (d : ℕ) : cwL d = cwR d ∧ ccwL d = ccwR d := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    rcases d with _ | n
    · rw [hcwL, hcwR, hccwL, hccwR]
      exact ⟨rfl, rfl⟩
    have hsum (v : ℕ → A) (hv : ∀ a, a < n + 1 → v a = ccwL a) :
        (∑ a ∈ Finset.range n, cwR (a + 1) * v (n + 1 - (a + 1))) =
        ∑ a ∈ Finset.range n, cwL (a + 1) * ccwL (n + 1 - (a + 1)) := by
      apply Finset.sum_congr rfl
      intro a ha
      have hlt := Finset.mem_range.mp ha
      rw [← (ih (a + 1) (by omega)).1, hv _ (by omega)]
    have hsum' :
        (∑ a ∈ Finset.range n, cwL (a + 1) * ccwR (n + 1 - (a + 1))) =
        ∑ a ∈ Finset.range n, cwL (a + 1) * ccwL (n + 1 - (a + 1)) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [(ih (n + 1 - (a + 1)) (by omega)).2]
    have hsumR := hsum ccwR fun a ha => (ih a ha).2.symm
    have hl := hL (n + 1)
    have hr := hR (n + 1)
    rw [sconv_succ_edges _ _ hcwL hccwL, ite_eq_right (Nat.succ_ne_zero n)] at hl
    rw [sconv_succ_edges _ _ hcwR hccwR, hsumR, ite_eq_right (Nat.succ_ne_zero n)] at hr
    rcases h (n + 1) (Nat.succ_pos n) with hc | hu | hm
    · refine ⟨hc, ?_⟩
      rw [← hc, ← hl] at hr
      exact (add_left_cancel (add_right_cancel hr)).symm
    · refine ⟨?_, hu⟩
      rw [← hu, ← hl] at hr
      exact (add_left_cancel hr).symm
    · have hm' := hm
      rw [sconv_succ_edges _ _ hcwL hccwR, hsum', ← hl] at hm
      rw [sconv_succ_edges _ _ hcwL hccwR, hsum', ← hr] at hm'
      exact ⟨add_left_cancel hm', (add_left_cancel (add_right_cancel hm)).symm⟩

/-- For a left coroot coordinate `n` and red multiplicity `δ`, the clockwise
slide applies when the right clockwise label is nonnegative, and the
counterclockwise slide applies when the left counterclockwise label is
nonnegative. Only the range where both labels are negative requires
the mixed convolution. -/
theorem redBubbleCoefficients_eq_of_sign_change {A : Type*} [Ring A]
    (n : ℤ) (δ : ℕ) (cwL ccwL cwR ccwR : ℕ → A)
    (hcwL : cwL 0 = 1) (hccwL : ccwL 0 = 1) (hcwR : cwR 0 = 1) (hccwR : ccwR 0 = 1)
    (hL : ∀ d, sconv cwL ccwL d = if d = 0 then 1 else 0)
    (hR : ∀ d, sconv cwR ccwR d = if d = 0 then 1 else 0)
    (hCW : ∀ d : ℕ, 0 ≤ -(n + δ) - 1 + d → cwL d = cwR d)
    (hCCW : ∀ d : ℕ, 0 ≤ n - 1 + d → ccwL d = ccwR d)
    (hMixed : ∀ d : ℕ, 0 < d → (d : ℤ) ≤ -n → (d : ℤ) ≤ n + δ → sconv cwL ccwR d = 0)
    (d : ℕ) : cwL d = cwR d ∧ ccwL d = ccwR d := by
  apply redBubbleCoefficients_eq cwL ccwL cwR ccwR hcwL hccwL hcwR hccwR hL hR _ d
  intro a ha
  by_cases hc : 0 ≤ -(n + δ) - 1 + (a : ℤ)
  · exact Or.inl (hCW a hc)
  by_cases hu : 0 ≤ n - 1 + (a : ℤ)
  · exact Or.inr (Or.inl (hCCW a hu))
  · exact Or.inr (Or.inr (hMixed a ha (by omega) (by omega)))

open MvPolynomial in
/-- The correction in the all-down KLR braid on black, red, black is the
divided difference of the black dot power. This is the red relation of
Webster, arXiv:1309.3796v2, Definition 4.5 and equation (4.2), in the
affine-cover convention used by the signed presentation. -/
theorem qbar_affineCoverQ_black_red {I k : Type*} [CommRing k] {ℓ : ℕ}
    (Q : I → I → MvPolynomial (Fin 2) k) (exponents : Fin ℓ → I →₀ ℕ) (r : Fin ℓ) (i : I) :
    KLR.qbar (affineCoverQ Q exponents (.inl i) (.inr r)) =
      ∑ a ∈ Finset.range (exponents r i), X 0 ^ a * X 2 ^ (exponents r i - 1 - a) :=
  StendhalAlgebraAllOrders.qbar_X_zero_pow _

/-- In a capped downward red braid, the divided difference of the red power
puts `a` dots on the left loop and `L + R + 1 - a` on the right. Here `L` and
`R` are the dot counts of their degree-zero bubbles. Negative-degree
vanishing turns the closed correction with `N` extra left dots into the
mixed convolution in degree `N + 1`. -/
theorem closedRedBraidCorrection_eq_sconv {A : Type*} [Ring A] (w c : ℕ → A)
    (L R N : ℕ) (hN : N ≤ L) (hw : ∀ m, m < L → w m = 0) (hc : ∀ m, m < R → c m = 0) :
    (∑ a ∈ Finset.range (L + R + 2), w (N + a) * c (L + R + 1 - a)) =
      sconv (fun a => w (L + a)) (fun a => c (R + a)) (N + 1) := by
  let a₀ := L - N
  have hsub : Finset.Ico a₀ (L + 2) ⊆ Finset.range (L + R + 2) := by
    intro a ha
    simp only [Finset.mem_Ico, Finset.mem_range] at ha ⊢
    omega
  have hzero (a : ℕ) (haRange : a ∈ Finset.range (L + R + 2)) (ha : a ∉ Finset.Ico a₀ (L + 2)) :
      w (N + a) * c (L + R + 1 - a) = 0 := by
    simp only [Finset.mem_Ico, not_and_or, not_le, not_lt] at ha
    rcases ha with h | h
    · rw [hw _ (by omega), zero_mul]
    · by_cases hr : R = 0
      · subst R
        exfalso
        simp only [Finset.mem_range] at haRange
        omega
      · rw [hc _ (by omega), mul_zero]
  rw [← Finset.sum_subset hsub hzero, Finset.sum_Ico_eq_sum_range,
    show L + 2 - a₀ = N + 1 + 1 by omega, sconv]
  refine Finset.sum_congr rfl fun a ha => ?_
  have halt := Finset.mem_range.mp ha
  rw [show N + (a₀ + a) = L + a by omega,
    show L + R + 1 - (a₀ + a) = R + (N + 1 - a) by omega]

/-- At `n = -2` and `δ = 4`, the capped braid correction in degree one is
the sum of the first normalized clockwise and counterclockwise real bubbles
on opposite sides of the red strand. -/
theorem closedRedBraidCorrection_neg_two_four {A : Type*} [Ring A]
    (w c : ℕ → A) (hw0 : w 0 = 0) (hc0 : c 0 = 0) (hw1 : w 1 = 1) (hc1 : c 1 = 1) :
    (∑ a ∈ Finset.range 4, w a * c (3 - a)) = c 2 + w 2 := by
  norm_num [Finset.sum_range_succ, hw0, hc0, hw1, hc1]

/-- At the same sign change, a vanishing closed braid correction compares
the degree-one real bubbles with the corresponding fake bubbles. The
two equations containing the fake coefficients are the degree-one
Grassmannian equations on the respective sides. -/
theorem redBubbleSlide_degree_one_neg_two_four {A : Type*} [Ring A]
    (w c : ℕ → A) (cwRight ccwLeft : A)
    (hw0 : w 0 = 0) (hc0 : c 0 = 0) (hw1 : w 1 = 1) (hc1 : c 1 = 1)
    (hLeft : ccwLeft + w 2 = 0) (hRight : c 2 + cwRight = 0)
    (hClosed : (∑ a ∈ Finset.range 4, w a * c (3 - a)) = 0) :
    w 2 = cwRight ∧ ccwLeft = c 2 := by
  rw [closedRedBraidCorrection_neg_two_four w c hw0 hc0 hw1 hc1] at hClosed
  exact ⟨add_left_cancel (hClosed.trans hRight.symm),
    add_right_cancel (hLeft.trans hClosed.symm)⟩

private abbrev DualNumber := TrivSqZeroExt ℚ ℚ

private def epsilon : DualNumber := TrivSqZeroExt.inr 1

private theorem epsilon_sq : epsilon * epsilon = 0 := TrivSqZeroExt.inr_mul_inr ℚ 1 1

private def series (a : DualNumber) (d : ℕ) : DualNumber :=
  if d = 0 then 1 else if d = 1 then a else 0

private theorem sconv_series (a b : DualNumber) (hab : a * b = 0) (hsum : a + b = 0)
    (d : ℕ) : sconv (series a) (series b) d = if d = 0 then 1 else 0 := by
  change sconv (series a) (fun e => if e = 0 then 1 else if e = 1 then b else 0) d = _
  rw [sconv_two_right]
  rcases d with _ | _ | _ | d
  · simp [series]
  · simp [series, hsum]
  · simp [series, hab]
  · simp [series]

/-- At left coroot coordinate `−2` and red multiplicity `4`, both real-slide
conditions compare precisely the normalized coefficients of degree at least
three. Separate Grassmannian equations and both real-slide conditions can
hold while the normalized clockwise coefficients in degree one differ. -/
theorem realRedBubbleSlides_do_not_determine_degree_one :
    ∃ cwL ccwL cwR ccwR : ℕ → TrivSqZeroExt ℚ ℚ,
      cwL 0 = 1 ∧ ccwL 0 = 1 ∧ cwR 0 = 1 ∧ ccwR 0 = 1 ∧
      (∀ d, sconv cwL ccwL d = if d = 0 then 1 else 0) ∧
      (∀ d, sconv cwR ccwR d = if d = 0 then 1 else 0) ∧
      (∀ d, 3 ≤ d → cwL d = cwR d ∧ ccwL d = ccwR d) ∧ cwL 1 ≠ cwR 1 := by
  refine ⟨series epsilon, series (-epsilon), series 0, series 0, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · exact sconv_series epsilon (-epsilon) (by rw [mul_neg, epsilon_sq, neg_zero]) (add_neg_cancel _)
  · exact sconv_series 0 0 (by simp) (by simp)
  · intro d hd
    simp [series, show d ≠ 0 by omega, show d ≠ 1 by omega]
  · intro h
    have h' := congrArg TrivSqZeroExt.snd h
    norm_num [series, epsilon] at h'

end Categorification.Stendhal.DoubleDiagram
