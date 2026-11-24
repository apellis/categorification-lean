/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.Stendhal
import Categorification.KLR.DividedPowerIdempotents
import Categorification.KLR.CyclotomicExact

/-!
# Sliding between the exterior divided-power cuts

Webster, arXiv:1309.3796v2, §8.2. The two black strands slide past one
red strand with exact dot and crossing identities. The slide intertwines
the two nilHecke projectors and vanishes between complementary projectors.
-/

namespace Categorification.Stendhal
open KLR KLRAlgebra TypeA

noncomputable section

variable {k : Type} [CommRing k]
variable (Q : (Unit ⊕ Fin 2) → (Unit ⊕ Fin 2) → MvPolynomial (Fin 2) k)

local notation "μ" => stendhalWeight 2 (Multiset.replicate 2 ())
local notation "H" => KLRAlgebra k Q μ

/-- Both black strands lie between the red strands. -/
def labelTwoExteriorLeftLoading : KLR.Seq μ := ⟨![.inr 0,.inl (),.inl (),.inr 1], by decide⟩
/-- There is one black strand in each block. -/
def labelTwoMiddleLoading : KLR.Seq μ := ⟨![.inr 0,.inl (),.inr 1,.inl ()], by decide⟩
/-- Both black strands lie to the right of the second red strand. -/
def labelTwoExteriorRightLoading : KLR.Seq μ := ⟨![.inr 0,.inr 1,.inl (),.inl ()], by decide⟩

local notation "c" => labelTwoExteriorLeftLoading
local notation "b" => labelTwoMiddleLoading
local notation "a" => labelTwoExteriorRightLoading
local notation "x₁" => (x (⟨1, by decide⟩ : Fin (Multiset.card μ)) : H)
local notation "x₂" => (x (⟨2, by decide⟩ : Fin (Multiset.card μ)) : H)
local notation "W" => (ψ 1 * (ψ 2 * e c) : H)

/-- The return crossing from the left exterior is supported at the middle loading. -/
theorem labelTwo_middleCut_ψ : (e b * (ψ 2 * e c) : H) = ψ 2 * e c := by
  have h : sadj (Multiset.card μ) 2 • c = b := by decide
  rw [ψ_mul_e, h, ← mul_assoc, e_mul_self]

private theorem lastCut : (e a * W : H) = W := by
  have h : sadj (Multiset.card μ) 1 • b = a := by decide
  nth_rw 1 [← labelTwo_middleCut_ψ Q]
  rw [← mul_assoc _ _ (ψ 2 * e c), ψ_mul_e, h]
  simp only [← mul_assoc, e_mul_self]
  have h' := congrArg (fun z : H => z * (ψ 2 * e c)) (ψ_mul_e (Q := Q) 1 b)
  rw [h, mul_assoc, labelTwo_middleCut_ψ Q] at h'
  simpa only [mul_assoc] using h'.symm

/-- Sliding both black strands past the red takes the nilHecke crossing to
the corresponding nilHecke crossing on the other side. -/
theorem labelTwo_endpointSlide_cross :
    (ψ 2 * W : H) = ψ 1 * (ψ 2 * (ψ 1 * e c)) := by
  have h := braid (Q := Q) 1 (by decide : 3 < Multiset.card μ) c
  have hc : (c).lbl ⟨1, by decide⟩ ≠ (c).lbl ⟨3, by decide⟩ := by decide
  simp only [hc, false_and, ↓reduceIte, sub_mul, sub_eq_zero, mul_assoc] at h
  exact h.symm

/-- Sliding both black strands past the red transports the first black dot. -/
theorem labelTwo_endpointSlide_dot :
    (x₂ * W : H) = ψ 1 * (ψ 2 * (x₁ * e c)) := by
  have h := dot_cross_right (Q := Q) 1 (by decide : 2 < Multiset.card μ) b
  have hb : (b).lbl ⟨1, by decide⟩ ≠ (b).lbl ⟨2, by decide⟩ := by decide
  simp only [hb, ↓reduceIte, sub_mul, sub_eq_zero] at h
  calc
    _ = (x₂ * ψ 1 * e b) * (ψ 2 * e c) := by rw [mul_assoc, mul_assoc, labelTwo_middleCut_ψ Q]
    _ = (ψ 1 * x₁ * e b) * (ψ 2 * e c) := by rw [h]
    _ = ψ 1 * (x₁ * (ψ 2 * e c)) := by rw [mul_assoc, mul_assoc, labelTwo_middleCut_ψ Q]
    _ = _ := by rw [← mul_assoc x₁, x_mul_ψ _ _ (by decide) (by decide), mul_assoc]

/-- The full black slide intertwines the two exterior nilHecke projectors. -/
theorem labelTwo_endpointSlide_projector :
    (x₂ * ψ 2 * e a) * W = W * (x₁ * ψ 1 * e c) := by
  have hc : sadj (Multiset.card μ) 1 • c = c := by decide
  have hfix : (e c * (ψ 1 * e c) : H) = ψ 1 * e c := by
    rw [ψ_mul_e, hc, ← mul_assoc, e_mul_self]
  have hcross : (ψ 2 * W : H) = W * (ψ 1 * e c) := by
    rw [labelTwo_endpointSlide_cross Q]
    simp only [mul_assoc, hfix]
  have hdot : (x₂ * W : H) = W * x₁ := by
    rw [labelTwo_endpointSlide_dot Q]
    simp only [mul_assoc, x_mul_e]
  calc
    _ = x₂ * (ψ 2 * W) := by simp only [mul_assoc, lastCut Q]
    _ = (x₂ * W) * (ψ 1 * e c) := by simp only [hcross, mul_assoc]
    _ = _ := by rw [hdot]; simp only [mul_assoc]

/-- The full slide between complementary exterior cut projectors vanishes. -/
theorem labelTwo_endpointSlide_complement :
    ((e a - x₂ * ψ 2 * e a) * W) * (x₁ * ψ 1 * e c) = 0 := by
  have hc : IsConstOn c 1 2 := by
    unfold IsConstOn
    decide
  have hp := isIdempotentElem_blockIdem (Q := Q) (by decide : 1 + 2 ≤ Multiset.card μ) hc
  rw [blockIdem, blockElt_two (by decide : 1 + 1 < Multiset.card μ)] at hp
  calc
    _ = (W - W * (x₁ * ψ 1 * e c)) * (x₁ * ψ 1 * e c) := by
      rw [sub_mul, lastCut Q, labelTwo_endpointSlide_projector Q]
    _ = 0 := by rw [sub_mul, mul_assoc (W), hp.eq, sub_self]


/-- Both reduced permutations returning from the middle loading to the
left exterior loading are supported by the mixed crossing at position two. -/
theorem labelTwo_middleToLeftExterior_transporters (w : Equiv.Perm (Fin (Multiset.card μ)))
    (hw : w • b = c) :
    w = wordProd (Multiset.card μ) [2] ∨ w = wordProd (Multiset.card μ) [1, 2] := by
  have h : ∀ v : Equiv.Perm (Fin (Multiset.card μ)), v • b = c →
      v = wordProd (Multiset.card μ) [2] ∨ v = wordProd (Multiset.card μ) [1, 2] := by
    decide +kernel
  exact h w hw

/-- A polynomial between the two mixed returns moves to the exterior side
of the square with no correction. -/
theorem labelTwo_middleReturn_poly (p : MvPolynomial (Fin (Multiset.card μ)) k) :
    ((ψ 2 * pol p * e b) * (ψ 2 * e c) : H) =
      pol (swapPol 2 (by decide) p) * (ψ 2 * ψ 2 * e c) := by
  have hne : (b).lbl ⟨2, by decide⟩ ≠ (b).lbl ⟨3, by decide⟩ := by decide
  rw [ψ_mul_pol_mul_e_of_ne (Q := Q) 2 (by decide) hne p]
  simp only [mul_assoc, labelTwo_middleCut_ψ Q]

/-- An algebra quotient killing the mixed square kills both polynomial
return rows after the exterior-to-middle crossing. -/
theorem labelTwo_middleReturn_rows_eq_zero {R : Type*} [Ring R] (f : H →+* R)
    (hzero : f (ψ 2 * ψ 2 * e c) = 0) (p : MvPolynomial (Fin (Multiset.card μ)) k) :
    f ((ψ 2 * pol p * e b) * (ψ 2 * e c)) = 0 ∧
      f ((ψ 1 * (ψ 2 * pol p * e b)) * (ψ 2 * e c)) = 0 := by
  have h := labelTwo_middleReturn_poly Q p
  have h₁ : f ((ψ 2 * pol p * e b) * (ψ 2 * e c)) = 0 := by
    rw [h, map_mul, hzero, mul_zero]
  exact ⟨h₁, by rw [mul_assoc, map_mul, h₁, mul_zero]⟩

end

end Categorification.Stendhal
