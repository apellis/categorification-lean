/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoExteriorSlide

/-!
# The exterior-to-middle PBW rows

The two returns through the right exterior divided-power projector
factor through the equal-black mixed braid at the middle loading.
-/

namespace Categorification.Stendhal
open KLR KLRAlgebra TypeA

noncomputable section
variable {k : Type} [CommRing k] (param : (Unit ⊕ Fin 2) → (Unit ⊕ Fin 2) → MvPolynomial (Fin 2) k)

local notation "μ" => stendhalWeight 2 (Multiset.replicate 2 ())
local notation "H" => KLRAlgebra k param μ
local notation "A" => labelTwoExteriorRightLoading
local notation "B" => labelTwoMiddleLoading
local notation "m" => Multiset.card μ
local notation "h₁" => (show 1 + 1 < m by decide)
local notation "h₂" => (show 2 + 1 < m by decide)
local notation "W" => (ψ 2 * (ψ 1 * e B) : H)
local notation "J" => (ψ 1 * W : H)
local notation "X₂" => (x (⟨2, by decide⟩ : Fin m) : H)

private theorem outerCut_ψ : (e A * (ψ 1 * e B) : H) = ψ 1 * e B := by
  have h : sadj m 1 • B = A := by decide
  rw [ψ_mul_e, h, ← mul_assoc, e_mul_self]

private theorem outerCut_ψ_comm :
    (e A * ψ 2 : H) = ψ 2 * e A := by
  have h : sadj m 2 • A = A := by decide
  rw [ψ_mul_e, h]

private theorem outerCut_W : (e A * W : H) = W := by
  rw [← mul_assoc, outerCut_ψ_comm, mul_assoc, outerCut_ψ]

private theorem outerCut_ψW_eq_zero : (ψ 2 * W : H) = 0 := by
  have hnil := ψ_sq (Q := param) 2 h₂ A
  have heq : (A).lbl ⟨2, by decide⟩ = (A).lbl ⟨3, by decide⟩ := rfl
  simp only [heq, ↓reduceIte] at hnil
  have h : (ψ 2 * ψ 2 * e A) * (ψ 1 * e B) = (ψ 2 * W : H) := by
    simp only [mul_assoc, outerCut_ψ]
  rw [← h, hnil, zero_mul]

/-- The first row, with arbitrary polynomial coefficient, factors through
the mixed braid on the middle generator. -/
theorem labelTwo_otherExterior_firstRow (f : MvPolynomial (Fin m) k) :
    ((ψ 1 * pol f * e A) * W : H) = pol (swapPol 1 h₁ f) * J := by
  have hne : (A).lbl ⟨1, by decide⟩ ≠ (A).lbl ⟨2, by decide⟩ := by decide
  rw [ψ_mul_pol_mul_e_of_ne (Q := param) 1 h₁ hne f]
  simp only [mul_assoc, outerCut_W]

/-- The second row has a divided-difference coefficient. Its additional
term vanishes by the black-black square. -/
theorem labelTwo_otherExterior_secondRow (f : MvPolynomial (Fin m) k) :
    ((ψ 1 * (ψ 2 * pol f * e A)) * W : H) =
      pol (swapPol 1 h₁ (NilHecke.dd k m 2 f)) * J := by
  have heq : (A).lbl ⟨2, by decide⟩ = (A).lbl ⟨3, by decide⟩ := rfl
  rw [ψ_mul_pol_mul_e_of_eq (Q := param) 2 h₂ heq f, mul_add, add_mul]
  have hzero : ((ψ 1 * (pol (swapPol 2 h₂ f) * ψ 2 * e A)) * W : H) = 0 := by
    simp only [mul_assoc, outerCut_W, outerCut_ψW_eq_zero, mul_zero]
  rw [hzero, zero_add, ← mul_assoc (ψ 1), labelTwo_otherExterior_firstRow]

local notation "PA" => (X₂ * ψ 2 * e A : H)

/-- Inserting the divided-power projector incorporates its dot into the
polynomial and retains its nilHecke crossing. -/
theorem labelTwo_otherExterior_projectorRow
    (word : H) (f : MvPolynomial (Fin m) k) :
    ((word * pol f * e A) * (PA * (ψ 1 * e B))) =
      (word * pol (f * MvPolynomial.X ⟨2, by decide⟩) * e A) * W := by
  have hx : (e A * (X₂ * W) : H) = X₂ * W := by
    rw [← mul_assoc, ← x_mul_e, mul_assoc, outerCut_W]
  calc
    _ = (word * pol f) * (e A * (X₂ * W)) := by
      simp only [mul_assoc, outerCut_ψ]
    _ = _ := by
      rw [hx]
      simp only [map_mul, pol_X, mul_assoc, outerCut_W]

local notation "C" => labelTwoExteriorLeftLoading
local notation "V" => (ψ 1 * (ψ 2 * e C) : H)
local notation "PC" => (x (⟨1, by decide⟩ : Fin m) * ψ 1 * e C : H)

/-- The two chosen exterior projectors give a zero composite across the full
slide. The leftmost end uses the complement of the usual nilHecke projector. -/
theorem labelTwo_otherExterior_slide_complement :
    (PA * V) * (e C - PC) = 0 := by
  have hc : IsConstOn C 1 2 := by unfold IsConstOn; decide
  have hpc := isIdempotentElem_blockIdem (Q := param) (by decide : 1 + 2 ≤ m) hc
  rw [blockIdem, blockElt_two (by decide : 1 + 1 < m)] at hpc
  have he : PC * e C = PC := by simp only [mul_assoc, e_mul_self]
  rw [labelTwo_endpointSlide_projector, mul_assoc (V), mul_sub, he, hpc.eq, sub_self, mul_zero]

local notation "X₃" => (x (⟨3, by decide⟩ : Fin m) : H)

/-- The projected incoming generator is the sum of the elementary crossing
and the two-crossing row with a dot on the right black strand. -/
theorem labelTwo_otherExterior_generator_expansion :
    PA * (ψ 1 * e B) = ψ 1 * e B + ψ 2 * (ψ 1 * (X₃ * e B)) := by
  have h := dot_cross_left (Q := param) 2 h₂ A
  have heq : (A).lbl ⟨2, by decide⟩ = (A).lbl ⟨3, by decide⟩ := rfl
  simp only [heq, ↓reduceIte, sub_mul] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h, add_mul, outerCut_ψ]
  simp only [mul_assoc, outerCut_ψ]
  rw [← mul_assoc X₃, x_mul_ψ _ _ (by decide) (by decide), mul_assoc, add_comm]

/-- The black-crossing translate of the projected generator has only the
undotted two-crossing row. -/
theorem labelTwo_otherExterior_generator_translate :
    ψ 2 * (PA * (ψ 1 * e B)) = W := by
  rw [labelTwo_otherExterior_generator_expansion, mul_add]
  have hdot : (ψ 2 * (ψ 1 * (X₃ * e B)) : H) = W * X₃ := by
    simp only [mul_assoc, x_mul_e]
  rw [hdot, ← mul_assoc (ψ 2) (W) (X₃), outerCut_ψW_eq_zero, zero_mul, add_zero]

end
end Categorification.Stendhal
