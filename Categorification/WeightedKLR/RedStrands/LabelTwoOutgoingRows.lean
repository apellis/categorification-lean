/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoExteriorMiddleMap

/-!
# The outgoing two-shuffle diagram columns at label two

Webster, arXiv:1309.3796v2, §8.2, printed page 80. These are the
undotted and first-dot columns of the two terminal shuffles in the
outgoing crossing to the complementary exterior divided projective.
-/

namespace Categorification.Stendhal
open KLR KLRAlgebra TypeA

noncomputable section
variable {k : Type} [CommRing k]
variable (Q : (Unit ⊕ Fin 2) → (Unit ⊕ Fin 2) → MvPolynomial (Fin 2) k)

local notation "μ" => stendhalWeight 2 (Multiset.replicate 2 ())
local notation "m" => Multiset.card μ
local notation "H" => KLRAlgebra k Q μ
local notation "C" => labelTwoExteriorLeftLoading
local notation "X₁" => (x (⟨1, by decide⟩ : Fin m) : H)
local notation "X₂" => (x (⟨2, by decide⟩ : Fin m) : H)
local notation "q" => (e C - X₁ * ψ 1 * e C : H)
local notation "D" => (ψ 1 * e C : H)
local notation "W" => (ψ 1 * (ψ 2 * e C) : H)

private theorem cLoading_cross : (e C * ψ 1 : H) = ψ 1 * e C := by
  have hs : sadj m 1 • C = C := by decide
  rw [ψ_mul_e, hs]

private theorem cLoading_cross_projection : (e C * D : H) = D := by
  rw [← mul_assoc, cLoading_cross, mul_assoc, e_mul_self]

private theorem cLoading_cross_sq_zero : (ψ 1 * D : H) = 0 := by
  have h := ψ_sq (Q := Q) 1 (by decide : 2 < m) C
  have he : (C).lbl ⟨1, by decide⟩ = (C).lbl ⟨2, by decide⟩ := rfl
  simpa only [he, ↓reduceIte, mul_assoc] using h

private theorem cLoading_dot_cross :
    (ψ 1 * X₁ * e C : H) = X₂ * ψ 1 * e C + e C := by
  have h := dot_cross_right (Q := Q) 1 (by decide : 2 < m) C
  have he : (C).lbl ⟨1, by decide⟩ = (C).lbl ⟨2, by decide⟩ := rfl
  simp only [he, ↓reduceIte, sub_mul, sub_eq_iff_eq_add] at h
  simpa only [add_comm] using h

private theorem cLoading_support : (e C * q : H) = q := by
  have h : (e C * (X₁ * ψ 1 * e C) : H) = X₁ * ψ 1 * e C := by
    calc
      _ = X₁ * (e C * D) := by rw [← mul_assoc (e C), ← mul_assoc (e C), e_mul_x, mul_assoc, mul_assoc]
      _ = _ := by rw [cLoading_cross_projection Q, mul_assoc]
  rw [mul_sub, e_mul_self, h]

/-- The black crossing kills the complementary endpoint projector. -/
theorem labelTwo_complementaryExterior_cross_zero :
    (ψ 1 * q : H) = 0 := by
  have h : (ψ 1 * (X₁ * ψ 1 * e C) : H) = D := by
    calc
      _ = (ψ 1 * X₁ * e C) * D := by
        simp only [mul_assoc, cLoading_cross_projection Q]
      _ = D := by
        rw [cLoading_dot_cross Q, add_mul, cLoading_cross_projection Q]
        simp only [mul_assoc, cLoading_cross_projection Q, cLoading_cross_sq_zero Q, mul_zero, zero_add]
  rw [mul_sub, h, sub_self]

/-- After the first dot, the same crossing recovers the complementary projector. -/
theorem labelTwo_complementaryExterior_cross_dot :
    (ψ 1 * (X₁ * q) : H) = q := by
  calc
    _ = ψ 1 * (X₁ * (e C * q)) :=
      congrArg (fun z : H => ψ 1 * (X₁ * z)) (cLoading_support Q).symm
    _ = (ψ 1 * X₁ * e C) * q := by simp only [mul_assoc]
    _ = (X₂ * ψ 1 * e C) * q + e C * q := by rw [cLoading_dot_cross Q, add_mul]
    _ = X₂ * (ψ 1 * q) + q := by
      have h : ((X₂ * ψ 1 * e C) * q : H) = X₂ * (ψ 1 * q) := by
        calc
          _ = X₂ * (ψ 1 * (e C * q)) := by simp only [mul_assoc]
          _ = _ := congrArg (fun z : H => X₂ * (ψ 1 * z)) (cLoading_support Q)
      rw [h, cLoading_support Q]
    _ = _ := by rw [labelTwo_complementaryExterior_cross_zero Q, mul_zero, zero_add]

local notation "B" => labelTwoMiddleLoading

private theorem fullSlide_cross_product :
    (ψ 2 * W : H) = W * D := by
  rw [labelTwo_endpointSlide_cross Q]
  simp only [mul_assoc, cLoading_cross_projection Q]

private theorem outgoing_firstShuffle_mul (r : H) :
    ((ψ 1 * e B) * (ψ 2 * e C) * r : H) = W * r := by
  simp only [mul_assoc, labelTwo_middleCut_ψ Q]

private theorem outgoing_firstShuffle_dot_mul (r : H) :
    ((ψ 1 * (X₁ * e B)) * (ψ 2 * e C) * r : H) = W * (X₁ * r) := by
  have hf : (ψ 1 * (X₁ * (ψ 2 * e C)) : H) = W * X₁ := by
    rw [← mul_assoc X₁, x_mul_ψ _ _ (by decide) (by decide), mul_assoc]
    simp only [mul_assoc, x_mul_e]
  calc
    _ = (ψ 1 * (X₁ * (ψ 2 * e C))) * r := by
      simp only [mul_assoc, labelTwo_middleCut_ψ Q]
    _ = _ := by rw [hf, mul_assoc]

/-- The terminal two-shuffle readout of the outgoing crossing on the
undotted and first-dot basis diagrams. -/
theorem labelTwo_outgoing_terminal_affine_rows :
    ((ψ 1 * e B) * (ψ 2 * e C) * q : H) = W * q ∧
    (ψ 2 * ((ψ 1 * e B) * (ψ 2 * e C) * q) : H) = 0 ∧
    ((ψ 1 * (X₁ * e B)) * (ψ 2 * e C) * q : H) = W * (X₁ * q) ∧
    (ψ 2 * ((ψ 1 * (X₁ * e B)) * (ψ 2 * e C) * q) : H) = W * q := by
  refine ⟨outgoing_firstShuffle_mul Q q, ?_, outgoing_firstShuffle_dot_mul Q q, ?_⟩
  · rw [outgoing_firstShuffle_mul Q, ← mul_assoc (ψ 2), fullSlide_cross_product Q, mul_assoc]
    rw [show (D * q : H) = 0 by
      rw [mul_assoc, cLoading_support Q, labelTwo_complementaryExterior_cross_zero Q], mul_zero]
  · rw [outgoing_firstShuffle_dot_mul Q, ← mul_assoc (ψ 2), fullSlide_cross_product Q, mul_assoc]
    have h : (D * (X₁ * q) : H) = q := by
      rw [mul_assoc, ← mul_assoc (e C), e_mul_x, mul_assoc, cLoading_support Q,
        labelTwo_complementaryExterior_cross_dot Q]
    rw [h]

end
end Categorification.Stendhal

namespace Categorification.Stendhal
open KLR KLRAlgebra

noncomputable section
variable {k : Type} [Field k]
variable (param : Unit → Unit → MvPolynomial (Fin 2) k)
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

local notation "ν" => Multiset.replicate 2 ()
local notation "μ" => stendhalWeight 2 (Multiset.replicate 2 ())
local notation "m" => Multiset.card μ
local notation "wt" => fun (_ : Fin 2) => Finsupp.single () 2
local notation "Q" => stendhalQ param wt
local notation "H" => KLRAlgebra k Q μ
local notation "T" => TensorProductAlgebra k param wt ν
local notation "π" => tensorOfKLR param wt ν
local notation "B" => labelTwoMiddleLoading
local notation "C" => labelTwoExteriorLeftLoading
local notation "X₁" => (x (⟨1, by decide⟩ : Fin m) : H)
local notation "q" => (e C - X₁ * ψ 1 * e C : H)
local notation "W" => (ψ 1 * (ψ 2 * e C) : H)
local notation "D" => labelTwoMiddleExteriorDifferential param

private theorem out_middle_ordered : IsRedOrdered B := by unfold IsRedOrdered; decide +kernel
local notation "M" => leftStandard param wt B out_middle_ordered
local notation "g" => leftStandardUnit param wt B out_middle_ordered
local notation "V" => M ⧸ LinearMap.range (labelTwoMiddleDotSumEnd param)
local notation "gbar" => (Submodule.Quotient.mk g : V)

private theorem outgoing_generator :
    (D gbar).val = π ((ψ 2 * e C) * q) := by
  unfold labelTwoMiddleExteriorDifferential
  rw [labelTwoMiddleDotSumToExterior_mk, labelTwoMiddleToExterior_unit]
  change π (ψ 2 * e C) * π q = π ((ψ 2 * e C) * q)
  simp only [tensorOfKLR, map_mul]

/-- On an arbitrary affine word followed by the middle generator, the actual
outgoing map concatenates the mixed return and the complementary projector. -/
theorem labelTwo_outgoing_applyRaw (a : H) :
    (D (π a • gbar)).val = π (a * (ψ 2 * e C) * q) := by
  rw [map_smul]
  change π a * (D gbar).val = _
  rw [outgoing_generator]
  simp only [tensorOfKLR, map_mul, mul_assoc]

/-- The actual outgoing terminal columns on the two shuffles and their first
black dots. The second shuffle vanishes without a dot and recovers the
first shuffle after the dot. -/
theorem labelTwo_outgoing_terminal_diagram_columns :
    (D (π (ψ 1 * e B) • gbar)).val = π (W * q) ∧
    (D (π (ψ 2 * (ψ 1 * e B)) • gbar)).val = 0 ∧
    (D (π (ψ 1 * (X₁ * e B)) • gbar)).val = π (W * (X₁ * q)) ∧
    (D (π (ψ 2 * (ψ 1 * (X₁ * e B))) • gbar)).val = π (W * q) := by
  obtain ⟨r00,r10,r01,r11⟩ := labelTwo_outgoing_terminal_affine_rows Q
  refine ⟨?_,?_,?_,?_⟩
  · exact (labelTwo_outgoing_applyRaw param _).trans (congrArg (π) r00)
  · simp only [labelTwo_outgoing_applyRaw]
    have hh : ((ψ 2 * (ψ 1 * e B)) * (ψ 2 * e C) * q : H) = 0 := by
      simpa only [mul_assoc] using r10
    rw [hh]
    simp only [tensorOfKLR, map_zero]
  · exact (labelTwo_outgoing_applyRaw param _).trans (congrArg (π) r01)
  · apply (labelTwo_outgoing_applyRaw param _).trans
    apply congrArg (π)
    simpa only [mul_assoc] using r11

end
end Categorification.Stendhal
